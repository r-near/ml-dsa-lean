#!/usr/bin/env python3
"""Vector generator for the Cryptol differential (ours: lean/SpecTests/DiffCryptol.lean, theirs: cryptol_eval.py).

    gen_vectors.py --stage 0 --out DIR      components, SHAKE, samplers, key generation (no dependencies)
    gen_vectors.py --stage 1 --out DIR      signing cases, from the keys that stage 0 produced on our side (DIR/ours/kg_*.out)
    gen_vectors.py --stage 2 --out DIR      verification cases, from the signatures of stage 1 (DIR/ours/sgn_*.out)

Writes line-oriented vector files DIR/vec/<name>.txt (one case per line, `TAG field field ...`; formats in README.md)
and appends `<name> <chunk> [expectation]` lines to DIR/vec/manifest.txt: `chunk` is how many lines one Cryptol
process evaluates (1 for the expensive top-level cases), the optional expectation names a documented deviation
that `compare.py` accepts for that file.  Everything is deterministic (seeded); counts scale with DIFF_SCALE.
"""
import argparse
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import PARAMS, Q, hx, unhx, ints, rows_str, parse_rows, stamp_ok  # noqa: E402

SCALE = float(os.environ.get("DIFF_SCALE", "1.0"))
FF = b"\xff"


def n_(x):
    return max(1, int(round(x * SCALE)))


def rb(rng, n):
    return bytes(rng.getrandbits(8) for _ in range(n))


class Out:
    def __init__(self, d):
        self.d = os.path.join(d, "vec")
        os.makedirs(self.d, exist_ok=True)
        self.mpath = os.path.join(self.d, "manifest.txt")
        self.entries = {}
        if os.path.exists(self.mpath):
            for ln in open(self.mpath):
                f = ln.split()
                if f:
                    self.entries[f[0]] = ln.strip()
        self.counts = {}

    def write(self, name, lines, chunk, expect=""):
        lines = list(lines)
        if not lines:
            return
        with open(os.path.join(self.d, name + ".txt"), "w") as fh:
            fh.write("\n".join(lines) + "\n")
        self.entries[name] = f"{name} {chunk} {expect}".rstrip()
        with open(self.mpath, "w") as fh:
            fh.write("\n".join(self.entries.values()) + "\n")
        self.counts[name] = len(lines)
        print(f"{name}: {len(lines)} lines", file=sys.stderr)


# --------------------------------------------------------------------------- bit-level helpers (Python side only)

def bit_pack_signed(w, a, b):
    """BitPack: coefficient w_i in [-a, b] is stored as b - w_i in bitlen(a+b) bits, little-endian bit order."""
    c = (a + b).bit_length()
    acc, nb, out = 0, 0, bytearray()
    for x in w:
        acc |= (b - x) << nb
        nb += c
        while nb >= 8:
            out.append(acc & 255)
            acc >>= 8
            nb -= 8
    assert nb == 0
    return bytes(out)


def bit_unpack_signed(bs, a, b):
    c = (a + b).bit_length()
    v = int.from_bytes(bs, "little")
    return [b - ((v >> (i * c)) & ((1 << c) - 1)) for i in range(256)]


def simple_pack(w, b):
    c = b.bit_length()
    v = 0
    for i, x in enumerate(w):
        v |= x << (i * c)
    return v.to_bytes(32 * c, "little")


def hint_pack(P, rows):
    y = bytearray(P["omega"] + P["k"])
    idx = 0
    for i, r in enumerate(rows):
        for j in sorted(r):
            y[idx] = j
            idx += 1
        y[P["omega"] + i] = idx
    return bytes(y)


def rand_hint_rows(rng, P, weight):
    pos = rng.sample(range(P["k"] * 256), weight)
    rows = [[] for _ in range(P["k"])]
    for p in pos:
        rows[p // 256].append(p % 256)
    return [sorted(r) for r in rows]


# --------------------------------------------------------------------------- rounding edges

def rounding_edges(gamma2):
    alpha = 2 * gamma2
    m = (Q - 1) // alpha
    pts = {0, 1, 2, 3, Q - 1, Q - 2, Q - 3, (Q - 1) // 2, (Q + 1) // 2, (Q - 1) // 2 - 1, (Q + 1) // 2 + 1}
    for d in (4094, 4095, 4096, 4097, 4098, 8190, 8191, 8192, 8193, 8194):
        pts.add(d)
    for kk in {0, 1, 2, m // 2, m - 2, m - 1, m}:
        for delta in (-gamma2 - 1, -gamma2, -gamma2 + 1, -1, 0, 1, gamma2 - 1, gamma2, gamma2 + 1):
            pts.add(kk * alpha + delta)
    for delta in range(0, 4):
        pts.add(Q - 1 - delta)
        pts.add(Q - 1 - gamma2 + delta)
        pts.add(Q - 1 - gamma2 - delta)
    return sorted(x for x in pts if 0 <= x < Q)


def pad_to(vals, n, rng):
    vals = list(vals)
    while len(vals) % n:
        vals.append(rng.randrange(Q))
    return vals


def chunks(vals, n):
    for i in range(0, len(vals), n):
        yield vals[i:i + n]


# --------------------------------------------------------------------------- stage 0

def stage0(o, rng):
    # --- SHAKE at the rate boundaries and across blocks
    in_lens = [0, 1, 2, 31, 32, 64, 100, 134, 135, 136, 137, 138, 166, 167, 168, 169, 170, 271, 272, 273, 335, 336, 337,
               504, 1000, 2500]
    out_lens = [1, 32, 64, 135, 136, 137, 167, 168, 169, 200, 336, 337, 672]
    for name, tag in (("shake256", "H256"), ("shake128", "H128")):
        lines = []
        for L in in_lens:
            outs = {out_lens[rng.randrange(len(out_lens))] for _ in range(3)} | {32, 136 if tag == "H256" else 168}
            for ol in sorted(outs):
                lines.append(f"{tag} {ol} {hx(rb(rng, L))}")
        # a few long outputs from short inputs and the same input at neighboring output lengths
        base = rb(rng, 33)
        for ol in (167, 168, 169, 335, 336, 337, 500):
            lines.append(f"{tag} {ol} {hx(base)}")
        o.write(name, lines, 20)

    # --- NTT, NTT^-1, MultiplyNTT
    def polys_struct():
        ps = [[0] * 256, [1] * 256, [Q - 1] * 256, list(range(256)), [(Q - 1) // 2] * 256]
        for i in (0, 1, 2, 127, 128, 255):
            p = [0] * 256
            p[i] = 1
            ps.append(p)
        p = [0] * 256
        p[255] = Q - 1
        ps.append(p)
        return ps
    pl = polys_struct() + [[rng.randrange(Q) for _ in range(256)] for _ in range(n_(150))]
    o.write("ntt", [f"NTT {ints(p)}" for p in pl], 8)
    o.write("intt", [f"INTT {ints(p)}" for p in pl], 8)
    mp = [(rng.choice(pl), rng.choice(pl)) for _ in range(n_(60))] + [(pl[2], pl[2]), (pl[3], pl[1])]
    o.write("mul", [f"MUL {ints(a)} {ints(b)}" for a, b in mp], 8)

    # --- Rounding functions (k * 256 scalars per line)
    for s, P in PARAMS.items():
        n = P["k"] * 256
        edges = rounding_edges(P["gamma2"])
        alpha = 2 * P["gamma2"]
        rnd = [rng.randrange(Q) for _ in range(n_(24) * n)]
        nearm = [min(Q - 1, max(0, rng.randrange(0, P["m"] + 1) * alpha + rng.randint(-3, 3))) for _ in range(n)]
        near_d = [min(Q - 1, max(0, rng.randrange(0, (Q - 1) // 8192 + 1) * 8192 + rng.randint(-3, 3))) for _ in range(n)]
        vals = pad_to(edges + nearm + near_d + rnd, n, rng)
        o.write(f"p2r{s}", [f"P2R {s} {ints(c)}" for c in chunks(vals, n)], 4)
        o.write(f"dec{s}", [f"DEC {s} {ints(c)}" for c in chunks(vals, n)], 4)
        # MakeHint: z and r both from edges, plus the signing-like regime (z = -ct0 small, r anything)
        zs = sorted(set(edges[::3]) | {Q - P["gamma2"], P["gamma2"], Q - P["gamma2"] - 1, P["gamma2"] + 1, 1, Q - 1})
        pairs = [(z, r) for z in zs for r in edges]
        pairs += [(rng.choice(zs), rng.randrange(Q)) for _ in range(n_(12) * n)]
        pairs += [(rng.randint(-P["gamma2"], P["gamma2"]) % Q, rng.randrange(Q)) for _ in range(n_(12) * n)]
        while len(pairs) % n:
            pairs.append((rng.randrange(Q), rng.randrange(Q)))
        o.write(f"mh{s}", [f"MH {s} {ints([p[0] for p in c])} {ints([p[1] for p in c])}" for c in chunks(pairs, n)], 4)
        # UseHint: every edge r with h = 1 and h = 0, plus random
        hr = [(h, r) for r in edges for h in (0, 1)] + [(rng.randrange(2), rng.randrange(Q)) for _ in range(n_(24) * n)]
        while len(hr) % n:
            hr.append((1, rng.randrange(Q)))
        o.write(f"uh{s}", [f"UH {s} {''.join(str(p[0]) for p in c)} {ints([p[1] for p in c])}" for c in chunks(hr, n)], 4)

    # --- packers
    sbp, sbu, bp, bu = [], [], [], []
    for b in (1, 2, 3, 7, 15, 43, 255, 1023, 1024, (1 << 19) - 1):
        w = b.bit_length()
        for kind in ("zero", "max", "rand", "rand", "ramp"):
            if kind == "zero":
                c = [0] * 256
            elif kind == "max":
                c = [b] * 256
            elif kind == "ramp":
                c = [i % (b + 1) for i in range(256)]
            else:
                c = [rng.randint(0, b) for _ in range(256)]
            sbp.append(f"SBP {b} {ints(c)}")
        for h in (bytes(32 * w), b"\xff" * (32 * w), rb(rng, 32 * w), rb(rng, 32 * w)):
            sbu.append(f"SBU {b} {hx(h)}")
    for (a, b) in ((2, 2), (4, 4), (4095, 4096), (2**17 - 1, 2**17), (2**19 - 1, 2**19)):
        w = (a + b).bit_length()
        for kind in ("lo", "hi", "rand", "rand", "mix"):
            if kind == "lo":
                c = [-a] * 256
            elif kind == "hi":
                c = [b] * 256
            elif kind == "mix":
                c = [(-a, b, 0, 1, -1)[i % 5] for i in range(256)]
            else:
                c = [rng.randint(-a, b) for _ in range(256)]
            bp.append(f"BP {a} {b} {ints(c)}")
        for h in (bytes(32 * w), b"\xff" * (32 * w), rb(rng, 32 * w), rb(rng, 32 * w)):
            bu.append(f"BU {a} {b} {hx(h)}")
    o.write("sbp", sbp, 10)
    o.write("sbu", sbu, 10)
    o.write("bp", bp, 10)
    o.write("bu", bu, 10)

    # --- hint packing: valid and malformed
    for s, P in PARAMS.items():
        k, om = P["k"], P["omega"]
        hbp, hbu = [], []
        weights = [0, 1, 2, om // 2, om - 1, om] + [rng.randint(0, om) for _ in range(n_(30))]
        valids = []
        for wgt in weights:
            rows = rand_hint_rows(rng, P, wgt)
            valids.append(rows)
            hbp.append(f"HBP {s} {rows_str(rows)}")
        # rows hitting indices 0 and 255, first index of a row <= last index of the previous row
        edge = [[0, 255]] + [[0, 1, 255] if i % 2 else [255] for i in range(1, k)]
        valids.append(edge)
        hbp.append(f"HBP {s} {rows_str(edge)}")
        full = [list(range(0, 256))[:0] for _ in range(k)]
        for i in range(om):
            full[i % k].append((i // k) * 3)
        full = [sorted(r) for r in full]
        valids.append(full)
        hbp.append(f"HBP {s} {rows_str(full)}")
        for rows in valids:
            y = hint_pack(P, rows)
            hbu.append(f"HBU {s} {hx(y)}")
        # malformed: one violation each
        for _ in range(n_(20)):
            base = bytearray(hint_pack(P, rand_hint_rows(rng, P, rng.randint(4, om))))
            nz = base[om:om + k]
            counts = list(nz)
            # (1) a count byte smaller than the previous one
            i = rng.randrange(1, k)
            if counts[i - 1] > 0:
                m = bytearray(base)
                m[om + i] = counts[i - 1] - 1
                hbu.append(f"HBU {s} {hx(m)}")
            # (2) the last count byte greater than omega, and equal to omega + 1
            m = bytearray(base)
            m[om + k - 1] = om + 1
            hbu.append(f"HBU {s} {hx(m)}")
            m = bytearray(base)
            m[om + rng.randrange(k)] = 255
            hbu.append(f"HBU {s} {hx(m)}")
            # (3) two equal indices or a descent inside a row (needs a row with >= 2 indices)
            prev = 0
            for r in range(k):
                lo, hi = prev, counts[r]
                if hi - lo >= 2:
                    j = rng.randrange(lo, hi - 1)
                    m = bytearray(base)
                    m[j + 1] = m[j]
                    hbu.append(f"HBU {s} {hx(m)}")
                    m = bytearray(base)
                    m[j], m[j + 1] = m[j + 1], m[j]
                    hbu.append(f"HBU {s} {hx(m)}")
                    break
                prev = hi
            # (4) nonzero padding after the used region
            used = counts[k - 1]
            if used < om:
                m = bytearray(base)
                m[rng.randrange(used, om)] = rng.randint(1, 255)
                hbu.append(f"HBU {s} {hx(m)}")
                m = bytearray(base)
                m[om - 1] = 1
                hbu.append(f"HBU {s} {hx(m)}")
            # (5) a count byte that skips indices (claims more indices than the following row uses)
            m = bytearray(base)
            i = rng.randrange(k - 1)
            if m[om + i] < m[om + k - 1]:
                m[om + i] += 1
                hbu.append(f"HBU {s} {hx(m)}")
        for _ in range(n_(30)):
            hbu.append(f"HBU {s} {hx(rb(rng, om + k))}")
        hbu.append(f"HBU {s} {hx(bytes(om + k))}")
        hbu.append(f"HBU {s} {hx(FF * (om + k))}")
        o.write(f"hbp{s}", hbp, 20)
        o.write(f"hbu{s}", hbu, 20)

    # --- key, secret key, signature codecs
    for s, P in PARAMS.items():
        k, l, eta, g1 = P["k"], P["l"], P["eta"], P["gamma1"]
        pke, pkd, ske, skd, sge, sgd, w1e = [], [], [], [], [], [], []
        for it in range(n_(12)):
            rho = rb(rng, 32)
            if it == 0:
                t1 = [[0] * 256 for _ in range(k)]
            elif it == 1:
                t1 = [[1023] * 256 for _ in range(k)]
            else:
                t1 = [[rng.randint(0, 1023) for _ in range(256)] for _ in range(k)]
            pke.append(f"PKE {s} {hx(rho)} {ints([c for p in t1 for c in p])}")
            pkd.append(f"PKD {s} {hx(rho + b''.join(simple_pack(p, 1023) for p in t1))}")
            if it == 0:
                s1 = [[-eta] * 256 for _ in range(l)]
                s2 = [[eta] * 256 for _ in range(k)]
                t0 = [[-4095] * 256 for _ in range(k)]
            elif it == 1:
                s1 = [[eta] * 256 for _ in range(l)]
                s2 = [[-eta] * 256 for _ in range(k)]
                t0 = [[4096] * 256 for _ in range(k)]
            else:
                s1 = [[rng.randint(-eta, eta) for _ in range(256)] for _ in range(l)]
                s2 = [[rng.randint(-eta, eta) for _ in range(256)] for _ in range(k)]
                t0 = [[rng.randint(-4095, 4096) for _ in range(256)] for _ in range(k)]
            key, tr = rb(rng, 32), rb(rng, 64)
            flat = [c for grp in (s1, s2, t0) for p in grp for c in p]
            ske.append(f"SKE {s} {hx(rho)} {hx(key)} {hx(tr)} {ints(flat)}")
            skb = (rho + key + tr + b"".join(bit_pack_signed(p, eta, eta) for p in s1 + s2)
                   + b"".join(bit_pack_signed(p, 4095, 4096) for p in t0))
            assert len(skb) == P["sk_len"]
            skd.append(f"SKD {s} {hx(skb)}")
            ct = rb(rng, P["ct_len"])
            if it == 0:
                z = [[-(g1 - 1)] * 256 for _ in range(l)]
            elif it == 1:
                z = [[g1] * 256 for _ in range(l)]
            else:
                z = [[rng.randint(-(g1 - 1), g1) for _ in range(256)] for _ in range(l)]
            rows = rand_hint_rows(rng, P, rng.randint(0, P["omega"]))
            sge.append(f"SGE {s} {hx(ct)} {ints([c for p in z for c in p])} {rows_str(rows)}")
            sgb = ct + b"".join(bit_pack_signed(p, g1 - 1, g1) for p in z) + hint_pack(P, rows)
            assert len(sgb) == P["sig_len"]
            sgd.append(f"SGD {s} {hx(sgb)}")
            w1 = [[rng.randint(0, P["m"] - 1) for _ in range(256)] for _ in range(k)]
            w1e.append(f"W1E {s} {ints([c for p in w1 for c in p])}")
        # decoders on arbitrary bytes and boundary patterns
        for pat in (bytes(P["pk_len"]), b"\xff" * P["pk_len"], rb(rng, P["pk_len"]), rb(rng, P["pk_len"])):
            pkd.append(f"PKD {s} {hx(pat)}")
        for pat in (bytes(P["sk_len"]), b"\xff" * P["sk_len"], rb(rng, P["sk_len"]), rb(rng, P["sk_len"])):
            skd.append(f"SKD {s} {hx(pat)}")
        for pat in (bytes(P["sig_len"]), b"\xff" * P["sig_len"], rb(rng, P["sig_len"]), rb(rng, P["sig_len"])):
            sgd.append(f"SGD {s} {hx(pat)}")
        # signatures with a malformed hint section, valid z
        for _ in range(n_(3)):
            sgb = bytearray(rb(rng, P["ct_len"]) + b"".join(bit_pack_signed([rng.randint(-(g1 - 1), g1) for _ in range(256)], g1 - 1, g1)
                                                             for _ in range(l)) + hint_pack(P, rand_hint_rows(rng, P, 20)))
            sgb[-1] = 255
            sgd.append(f"SGD {s} {hx(sgb)}")
        o.write(f"pke{s}", pke, 4)
        o.write(f"pkd{s}", pkd, 4)
        o.write(f"ske{s}", ske, 2)
        o.write(f"skd{s}", skd, 2)
        o.write(f"sge{s}", sge, 2)
        o.write(f"sgd{s}", sgd, 2)
        o.write(f"w1e{s}", w1e, 4)

    # --- samplers
    for s, P in PARAMS.items():
        sib = [f"SIB {s} {hx(rb(rng, P['ct_len']))}" for _ in range(n_(150))]
        sib += [f"SIB {s} {hx(bytes(P['ct_len']))}", f"SIB {s} {hx(FF * P['ct_len'])}"]
        rbp = [f"RBP {s} {hx(rb(rng, 66))}" for _ in range(n_(150))]
        rbp += [f"RBP {s} {hx(bytes(66))}", f"RBP {s} {hx(FF * 66)}"]
        exs = [f"EXS {s} {hx(rb(rng, 64))}" for _ in range(n_(10))] + [f"EXS {s} {hx(bytes(64))}"]
        exm = []
        for kappa in (0, P["l"], 2 * P["l"], 255, 256, 1000, 65536 - P["l"], 65535 - 1):
            exm.append(f"EXM {s} {hx(rb(rng, 64))} {kappa}")
        for kappa in (65535, 65536, 65540):  # outside the signing loop; mod 2^16 in both encodings
            exm.append(f"EXM {s} {hx(rb(rng, 64))} {kappa}")
        exm.append(f"EXM {s} {hx(bytes(64))} 0")
        exa = [f"EXA {s} {hx(rb(rng, 32))}" for _ in range(n_(4))] + [f"EXA {s} {hx(bytes(32))}"]
        o.write(f"sib{s}", sib, 10)
        o.write(f"rbp{s}", rbp, 10)
        o.write(f"exs{s}", exs, 4)
        o.write(f"exm{s}", exm, 4)
        o.write(f"exa{s}", exa, 1)
    rn = [f"RNTT {hx(rb(rng, 34))}" for _ in range(n_(150))] + [f"RNTT {hx(bytes(34))}", f"RNTT {hx(FF * 34)}"]
    o.write("rntt", rn, 10)

    # --- key generation: three Cryptol variants (Specification, OptimizedSpecification, ML_DSA TestAPI)
    for s, P in PARAMS.items():
        seeds = [bytes(32), bytes(range(32))] + [rb(rng, 32) for _ in range(n_(4))]
        o.write(f"kg_{s}", [f"KG {s} {hx(x)}" for x in seeds], 1)
        # the same seeds through the other two Cryptol entry points; ours repeats the same computation
        o.write(f"kgo_{s}", [f"KGO {s} {hx(x)}" for x in seeds[:n_(3)]], 1)
        o.write(f"kgt_{s}", [f"KGT {s} {hx(x)}" for x in seeds[:n_(2)]], 1)


# --------------------------------------------------------------------------- stage 1 and 2 (need ours' outputs)

def ours_lines(d, name):
    """The lines of our side's output for vector file `name`, only if that output is bound to the current vector file."""
    out = os.path.join(d, "ours", name + ".out")
    if not stamp_ok(out, os.path.join(d, "vec", name + ".txt")):
        sys.exit(f"gen_vectors: {out} is missing or was computed from another {name}.txt (stale); run the earlier stage again")
    return [ln for ln in open(out).read().split("\n") if ln]


def read_kg(d, s):
    vec = [ln.split(" ") for ln in open(os.path.join(d, "vec", f"kg_{s}.txt")).read().split("\n") if ln]
    outs = ours_lines(d, f"kg_{s}")
    res = []
    for f, ln in zip(vec, outs):
        pk, sk = ln.split(" ; ")
        res.append((unhx(f[2]), unhx(pk), unhx(sk)))
    return res


def stage1(o, rng, d):
    ctx255 = rb(rng, 255)
    for s, P in PARAMS.items():
        keys = read_kg(d, s)
        nk = min(len(keys), n_(3))
        sg, sgi = [], []
        msgs = [(b"", b""), (rb(rng, 33), b""), (b"\x00", rb(rng, 5)), (rb(rng, 100), ctx255), (rb(rng, 17), rb(rng, 1))]
        for ki in range(nk):
            xi, pk, sk = keys[ki + 2] if ki + 2 < len(keys) else keys[ki]
            for mi, (m, ctx) in enumerate(msgs[:n_(3) if ki else n_(5)]):
                rnd = bytes(32) if (ki + mi) % 3 else rb(rng, 32)
                sg.append(f"SGN {s} {hx(sk)} {hx(m)} {hx(ctx)} {hx(rnd)}")
        xi, pk, sk = keys[0]
        # a context of 256 bytes: both sides refuse to sign (Algorithm 2, steps 1-3)
        sg.append(f"SGN {s} {hx(sk)} {hx(b'abc')} {hx(rb(rng, 256))} {hx(bytes(32))}")
        o.write(f"sgn_{s}", sg, 1)
        # the number of attempts of Algorithm 7's loop in each signing case (our side only; reported by compare.py)
        o.write(f"sga_{s}", [ln.replace("SGN", "SGA", 1) for ln in sg if len(ln.split(" ")[4]) <= 510], 1, "oursonly")
        # Sign_internal on a raw M'
        mp = rb(rng, 40)
        o.write(f"sgi_{s}", [f"SGI {s} {hx(sk)} {hx(mp)} {hx(bytes(32))}"], 1)
        # boundary of the z-norm check: forged attempts with ||z|| exactly gamma1 - beta - 1 (valid) and gamma1 - beta
        # (rejected by Verify step 13 although the commitment hash is consistent); our side only, Cryptol verifies them in stage 2
        xi, pk, sk = keys[min(1, len(keys) - 1)]
        fl = []
        for kind in ("lt", "eq", "gt"):
            for r in range(n_(2)):
                fl.append(f"SGF {s} {hx(sk)} {hx(rb(rng, 9 + r))} {hx(b'')} {hx(rb(rng, 32) if r else bytes(32))} {kind}")
        o.write(f"sgf_{s}", fl, 1, "oursonly")


def flip(b, bit):
    m = bytearray(b)
    m[bit // 8] ^= 1 << (bit % 8)
    return bytes(m)


def stage2(o, rng, d):
    for s, P in PARAMS.items():
        keys = read_kg(d, s)
        vec = [ln.split(" ") for ln in open(os.path.join(d, "vec", f"sgn_{s}.txt")).read().split("\n") if ln]
        outs = ours_lines(d, f"sgn_{s}")
        skmap = {sk: (pk, xi) for (xi, pk, sk) in keys}
        cases = []
        for f, ln in zip(vec, outs):
            if ln == "none":
                continue
            sk, m, ctx = unhx(f[2]), unhx(f[3]), unhx(f[4])
            pk = skmap[sk][0]
            cases.append((pk, m, ctx, unhx(ln)))
        nbase = min(len(cases), n_(4))
        k, l, g1, beta, om = P["k"], P["l"], P["gamma1"], P["beta"], P["omega"]
        zlen = 32 * (1 + (g1 - 1).bit_length())
        ct_len = P["ct_len"]
        ver = []
        verx = []

        def add(pk, m, sig, ctx):
            ver.append(f"VER {s} {hx(pk)} {hx(m)} {hx(sig)} {hx(ctx)}")

        # all stored signatures verify (unchanged)
        for (pk, m, ctx, sig) in cases[:n_(6)]:
            add(pk, m, sig, ctx)
        for (pk, m, ctx, sig) in cases[:nbase]:
            # message, context
            add(pk, flip(m, 0) if m else b"\x00", sig, ctx)
            add(pk, m + b"\x00", sig, ctx)
            add(pk, m, sig, ctx + b"\x00")
            if ctx:
                add(pk, m, sig, flip(ctx, 0))
            # c~
            add(pk, m, flip(sig, 0), ctx)
            add(pk, m, flip(sig, ct_len * 8 - 1), ctx)
            add(pk, m, flip(sig, rng.randrange(ct_len * 8)), ctx)
            # z
            zbits = (ct_len * 8, (ct_len + l * zlen) * 8)
            for _ in range(3):
                add(pk, m, flip(sig, rng.randrange(*zbits)), ctx)
            add(pk, m, flip(sig, zbits[1] - 1), ctx)
            # z coefficient at the bound g1 - beta (and one either side), both signs
            zs = [bit_unpack_signed(sig[ct_len + i * zlen:ct_len + (i + 1) * zlen], g1 - 1, g1) for i in range(l)]
            for val in (g1 - beta - 1, g1 - beta, g1 - beta + 1, -(g1 - beta - 1), -(g1 - beta), -(g1 - beta + 1), g1, -(g1 - 1)):
                z2 = [list(p) for p in zs]
                z2[0][0] = val
                sig2 = sig[:ct_len] + b"".join(bit_pack_signed(p, g1 - 1, g1) for p in z2) + sig[ct_len + l * zlen:]
                add(pk, m, sig2, ctx)
            # hint section: flips, and non-canonical re-encodings of the same hint
            hoff = ct_len + l * zlen
            y = bytearray(sig[hoff:])
            counts = list(y[om:om + k])
            used = counts[-1]
            add(pk, m, flip(sig, (hoff + rng.randrange(om)) * 8 + rng.randrange(8)), ctx)
            add(pk, m, flip(sig, (hoff + om + rng.randrange(k)) * 8 + rng.randrange(3)), ctx)
            prev = 0
            done = 0
            for r in range(k):
                lo, hi = prev, counts[r]
                if hi - lo >= 2 and done < 2:
                    j = rng.randrange(lo, hi - 1)
                    y2 = bytearray(y)
                    y2[j], y2[j + 1] = y2[j + 1], y2[j]       # same set of indices, descending order
                    add(pk, m, sig[:hoff] + bytes(y2), ctx)
                    y3 = bytearray(y)
                    y3[j + 1] = y3[j]                          # a repeated index
                    add(pk, m, sig[:hoff] + bytes(y3), ctx)
                    done += 1
                prev = hi
            if used < om:
                y4 = bytearray(y)
                y4[om - 1] = 1                                 # nonzero padding
                add(pk, m, sig[:hoff] + bytes(y4), ctx)
                y5 = bytearray(y)
                y5[used] = y5[used - 1] if used else 5          # padding that repeats the last index
                add(pk, m, sig[:hoff] + bytes(y5), ctx)
            y6 = bytearray(y)
            y6[om + k - 1] = om + 1                            # count > omega
            add(pk, m, sig[:hoff] + bytes(y6), ctx)
            # exactly omega hints
            y7 = hint_pack(P, rand_hint_rows(rng, P, om))
            add(pk, m, sig[:hoff] + y7, ctx)
            add(pk, m, sig[:hoff] + hint_pack(P, [[] for _ in range(k)]), ctx)
            # public key
            add(flip(pk, 0), m, sig, ctx)
            add(flip(pk, 32 * 8), m, sig, ctx)
            add(flip(pk, len(pk) * 8 - 1), m, sig, ctx)
            add(flip(pk, rng.randrange(len(pk) * 8)), m, sig, ctx)
        # forged boundary signatures (stage 1, our side): z at gamma1 - beta - 1 must verify, at gamma1 - beta and above must not
        fp = os.path.join(d, "vec", f"sgf_{s}.txt")
        if os.path.exists(fp):
            fvec = [ln.split(" ") for ln in open(fp).read().split("\n") if ln]
            fouts = ours_lines(d, f"sgf_{s}")
            for f, ln in zip(fvec, fouts):
                if ln == "none":
                    print(f"warning: no forged signature for {f[0:2]} {f[-1]}", file=sys.stderr)
                    continue
                pk = skmap[unhx(f[2])][0]
                add(pk, unhx(f[3]), unhx(ln), unhx(f[4]))
        # a signature under another key
        other = [c for c in cases if c[0] != cases[0][0]]
        if other:
            add(other[0][0], cases[0][1], cases[0][3], cases[0][2])
        # verification with a 256-byte context: ours false (errata), Cryptol None (the original pseudocode)
        pk, m, ctx, sig = cases[0]
        verx.append(f"VER {s} {hx(pk)} {hx(m)} {hx(sig)} {hx(rb(rng, 256))}")
        o.write(f"ver_{s}", ver, 1)
        o.write(f"verx_{s}", verx, 1, "erratum-alg3:ours=false,theirs=none")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", type=int, required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=204)
    a = ap.parse_args()
    rng = random.Random(a.seed * 10 + a.stage)
    o = Out(a.out)
    if a.stage == 0:
        stage0(o, rng)
    elif a.stage == 1:
        stage1(o, rng, a.out)
    elif a.stage == 2:
        stage2(o, rng, a.out)
    total = sum(o.counts.values())
    print(f"stage {a.stage}: {total} lines in {len(o.counts)} files", file=sys.stderr)


if __name__ == "__main__":
    main()
