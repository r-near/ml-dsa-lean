#!/usr/bin/env python3
"""Test-vector generator for the FIPS 204 differential check (ours vs VCVio).

Writes line-oriented vector files into an output directory.  Both evaluators
(`lean/SpecTests/DiffVCVio.lean` in this repo and `DiffEval.lean` in the VCVio
clone) read the same files and print one canonical output line per input line.
`compare.py` then diffs the two outputs line by line.

Line format: `TAG field field ...`, fields separated by single spaces.

  P2R r                       Power2Round, r in [0, q)
  DEC S r                     Decompose / HighBits / LowBits (S in 44, 65, 87)
  MH S z r                    MakeHint
  UH S h r                    UseHint, h in {0, 1}
  SWEEP kind S chunk          digest of a 65536-value block of r in [0, q); kind in P2R DEC UH0 UH1
  NTT c0..c255 / INTT c0..c255 / MUL a0..a255 b0..b255
  SBP b c0..c255              SimpleBitPack (coefficients in [0, b])
  SBU b hex                   SimpleBitUnpack
  BP a b c0..c255             BitPack (coefficients in [-a, b])
  BU a b hex                  BitUnpack
  HBP S row*k                 HintBitPack; a row is `-` or comma-separated ascending indices
  HBPX S row*k                HintBitPack with more than omega ones (outside the precondition)
  HBU S hex                   HintBitUnpack (omega + k bytes)
  PKE S rho t1[k*256]         pkEncode;    PKD S hex       pkDecode
  SKE S rho K tr s1 s2 t0     skEncode;    SKD S hex       skDecode
  SGE S ctilde z[l*256] row*k sigEncode;   SGD S hex       sigDecode (correct length only)
  W1E S w1[k*256]             w1Encode

Also writes `hint.expected`: for each HBU line of `hint.txt`, the verdict of an
independent Python reference of Algorithm 21 (a third opinion for adjudication).
"""
import argparse
import os
import random

Q = 8380417
PARAMS = {
    44: dict(k=4, l=4, eta=2, gamma1=2**17, gamma2=(Q - 1) // 88, omega=80, lam=128),
    65: dict(k=6, l=5, eta=4, gamma1=2**19, gamma2=(Q - 1) // 32, omega=55, lam=192),
    87: dict(k=8, l=7, eta=2, gamma1=2**19, gamma2=(Q - 1) // 32, omega=75, lam=256),
}


def bitlen(x):
    return x.bit_length()


def hexs(bs):
    return bytes(bs).hex()


def rand_bytes(rng, n):
    return bytes(rng.getrandbits(8) for _ in range(n))


def ints(xs):
    return " ".join(str(x) for x in xs)


def rows_str(rows):
    return " ".join(",".join(map(str, r)) if r else "-" for r in rows)


# --------------------------------------------------------------------------- rounding

def rounding_edges(gamma2):
    alpha = 2 * gamma2
    m = (Q - 1) // alpha
    pts = {0, 1, 2, 3, Q - 1, Q - 2, Q - 3, (Q - 1) // 2, (Q + 1) // 2, (Q - 1) // 2 - 1, (Q + 1) // 2 + 1}
    for d in (4094, 4095, 4096, 4097, 4098, 8190, 8191, 8192, 8193, 8194):
        pts.add(d)
    for kk in {0, 1, 2, 3, m // 2, m - 2, m - 1, m}:
        for delta in (-gamma2 - 2, -gamma2 - 1, -gamma2, -gamma2 + 1, -2, -1, 0, 1, 2,
                      gamma2 - 2, gamma2 - 1, gamma2, gamma2 + 1, gamma2 + 2):
            pts.add(kk * alpha + delta)
    # the Decompose corner case r - r0 = q - 1 is r in (q - 1 - gamma2, q - 1]
    for delta in range(0, 6):
        pts.add(Q - 1 - delta)
        pts.add(Q - 1 - gamma2 + delta)
        pts.add(Q - 1 - gamma2 - delta)
    return sorted(p for p in pts if 0 <= p < Q)


def p2r_edges():
    pts = {0, 1, 2, Q - 1, Q - 2, (Q - 1) // 2, (Q + 1) // 2}
    for kk in {0, 1, 2, 1022, 1023, 1024, 512}:
        for delta in range(-4100, 4101, 1):
            if abs(delta) in (0, 1, 2, 3, 4095, 4096, 4097, 4098, 4099, 4100) or delta in (-4094, -4093):
                pts.add(kk * 8192 + delta)
    return sorted(p for p in pts if 0 <= p < Q)


def gen_rounding(rng, out, n_random):
    lines = []
    for r in p2r_edges():
        lines.append(f"P2R {r}")
    for _ in range(2 * n_random):
        lines.append(f"P2R {rng.randrange(Q)}")
    for S, P in PARAMS.items():
        g2 = P["gamma2"]
        edges = rounding_edges(g2)
        for r in edges:
            lines.append(f"DEC {S} {r}")
        for _ in range(n_random):
            lines.append(f"DEC {S} {rng.randrange(Q)}")
        # random r in the corner window and near the top of each block
        for _ in range(2000):
            lines.append(f"DEC {S} {Q - 1 - rng.randrange(g2 + 3)}")
        for r in edges:
            for h in (0, 1):
                lines.append(f"UH {S} {h} {r}")
        for _ in range(n_random):
            lines.append(f"UH {S} {rng.randrange(2)} {rng.randrange(Q)}")
        for _ in range(5000):
            lines.append(f"UH {S} {rng.randrange(2)} {rng.choice(edges)}")
        zs = {0, 1, Q - 1, 2, Q - 2, g2, g2 + 1, g2 - 1, Q - g2, Q - g2 - 1, Q - g2 + 1,
              2 * g2, 2 * g2 + 1, 2 * g2 - 1, Q - 2 * g2, Q - 2 * g2 + 1, Q - 2 * g2 - 1,
              (Q - 1) // 2, (Q + 1) // 2, 4096, Q - 4096}
        zs = sorted(z for z in zs if 0 <= z < Q)
        for z in zs:
            for r in edges:
                lines.append(f"MH {S} {z} {r}")
        for _ in range(n_random):
            lines.append(f"MH {S} {rng.randrange(Q)} {rng.randrange(Q)}")
        # z small (as in Sign: ||z|| <= gamma2), r random or edge: hint bit is often 1 near boundaries
        for _ in range(n_random // 2):
            z = rng.randrange(-2 * g2 - 2, 2 * g2 + 3) % Q
            r = rng.choice(edges) if rng.random() < 0.5 else rng.randrange(Q)
            lines.append(f"MH {S} {z} {r}")
    with open(os.path.join(out, "rounding.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


def gen_sweep(out):
    lines = []
    nchunks = (Q + 65535) // 65536
    for c in range(nchunks):
        lines.append(f"SWEEP P2R - {c}")
    for S in PARAMS:
        for kind in ("DEC", "UH0", "UH1"):
            for c in range(nchunks):
                lines.append(f"SWEEP {kind} {S} {c}")
    with open(os.path.join(out, "sweep.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


# --------------------------------------------------------------------------- NTT

def poly_edges():
    polys = []
    polys.append([0] * 256)
    polys.append([Q - 1] * 256)
    polys.append([1] * 256)
    polys.append([(Q - 1) // 2] * 256)
    polys.append([(Q + 1) // 2] * 256)
    polys.append([(i * 37) % Q for i in range(256)])
    polys.append([(Q - 1) if i % 2 else 0 for i in range(256)])
    polys.append([i for i in range(256)])
    polys.append([Q - 1 - i for i in range(256)])
    for pos in (0, 1, 2, 127, 128, 254, 255):
        p = [0] * 256
        p[pos] = 1
        polys.append(p)
        p = [0] * 256
        p[pos] = Q - 1
        polys.append(p)
    return polys


def gen_ntt(rng, out, n_random):
    lines = []
    edges = poly_edges()
    rpolys = [[rng.randrange(Q) for _ in range(256)] for _ in range(n_random)]
    small = [[rng.randrange(-4, 5) % Q for _ in range(256)] for _ in range(100)]
    sparse = []
    for _ in range(100):
        p = [0] * 256
        for _ in range(rng.randrange(1, 40)):
            p[rng.randrange(256)] = rng.randrange(Q)
        sparse.append(p)
    allp = edges + rpolys + small + sparse
    for p in allp:
        lines.append("NTT " + ints(p))
    for p in allp:
        lines.append("INTT " + ints(p))
    for a, b in zip(edges, reversed(edges)):
        lines.append("MUL " + ints(a) + " " + ints(b))
    for a in edges:
        for b in edges[:6]:
            lines.append("MUL " + ints(a) + " " + ints(b))
    for _ in range(n_random):
        a = [rng.randrange(Q) for _ in range(256)]
        b = [rng.randrange(Q) for _ in range(256)]
        lines.append("MUL " + ints(a) + " " + ints(b))
    with open(os.path.join(out, "ntt.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


# --------------------------------------------------------------------------- hints

def py_hint_pack(S, rows):
    P = PARAMS[S]
    y = [0] * (P["omega"] + P["k"])
    idx = 0
    for i, row in enumerate(rows):
        for j in row:
            y[idx] = j
            idx += 1
        y[P["omega"] + i] = idx
    return bytes(y)


def py_hint_unpack(S, y):
    """Independent reference of Algorithm 21.  Returns rows or None."""
    P = PARAMS[S]
    om, k = P["omega"], P["k"]
    assert len(y) == om + k
    rows = [[] for _ in range(k)]
    index = 0
    for i in range(k):
        if y[om + i] < index or y[om + i] > om:
            return None
        first = index
        while index < y[om + i]:
            if index > first:
                if y[index - 1] >= y[index]:
                    return None
            rows[i].append(y[index])
            index += 1
    for i in range(index, om):
        if y[i] != 0:
            return None
    return rows


def rand_hint(rng, S, weight):
    P = PARAMS[S]
    k = P["k"]
    pos = rng.sample(range(k * 256), weight)
    rows = [[] for _ in range(k)]
    for p in pos:
        rows[p // 256].append(p % 256)
    return [sorted(r) for r in rows]


def hint_edge_rows(S):
    P = PARAMS[S]
    k, om = P["k"], P["omega"]
    cases = []
    cases.append([[] for _ in range(k)])
    full0 = [list(range(om))] + [[] for _ in range(k - 1)]
    cases.append(full0)
    last = [[] for _ in range(k - 1)] + [list(range(256 - om, 256))]
    cases.append(last)
    cases.append([[0, 255]] + [[] for _ in range(k - 1)])
    cases.append([[255]] * 1 + [[0]] * (k - 1))
    # weight omega spread one per row, then the rest in the last row
    rows = [[i] for i in range(k - 1)] + [list(range(om - (k - 1)))]
    cases.append(rows)
    # a full row of 256 ones (weight 256 > omega: outside the precondition)
    return cases


def mutate_hint_bytes(rng, S, y):
    """Return a list of (kind, bytes) malformed or near-malformed variants of a valid encoding y."""
    P = PARAMS[S]
    om, k = P["omega"], P["k"]
    y = bytearray(y)
    out = []
    counts = [y[om + i] for i in range(k)]
    total = counts[-1]
    # indices not increasing (swap two adjacent indices within a row, or duplicate)
    for _ in range(3):
        z = bytearray(y)
        i = rng.randrange(k)
        lo = counts[i - 1] if i > 0 else 0
        hi = counts[i]
        if hi - lo >= 2:
            a = rng.randrange(lo, hi - 1)
            if rng.random() < 0.5:
                z[a], z[a + 1] = z[a + 1], z[a]
            else:
                z[a + 1] = z[a]
            out.append(("order", bytes(z)))
    # counts out of order (decreasing), counts above omega
    if k >= 2:
        z = bytearray(y)
        i = rng.randrange(1, k)
        z[om + i] = rng.randrange(0, max(1, z[om + i - 1])) if z[om + i - 1] > 0 else 0
        if z[om + i] < z[om + i - 1]:
            out.append(("count_decr", bytes(z)))
        z = bytearray(y)
        i = rng.randrange(k)
        z[om + i] = om + 1 + rng.randrange(0, 256 - om - 1)
        out.append(("count_gt_omega", bytes(z)))
        z = bytearray(y)
        z[om + k - 1] = om + 1
        out.append(("count_omega_plus_1", bytes(z)))
    # nonzero padding after the last used index
    if total < om:
        z = bytearray(y)
        p = rng.randrange(total, om)
        z[p] = rng.randrange(1, 256)
        out.append(("padding", bytes(z)))
        z = bytearray(y)
        z[om - 1] = 1
        out.append(("padding_last", bytes(z)))
    # counts all bumped by one (claims one more index than present)
    z = bytearray(y)
    for i in range(k):
        z[om + i] = min(255, z[om + i] + 1)
    out.append(("count_bump", bytes(z)))
    # random byte flips anywhere
    z = bytearray(y)
    for _ in range(rng.randrange(1, 4)):
        z[rng.randrange(om + k)] = rng.getrandbits(8)
    out.append(("flip", bytes(z)))
    return out


def gen_hint(rng, out, n_random):
    lines = []
    expect = []

    def add_hbu(S, y):
        lines.append(f"HBU {S} {hexs(y)}")
        r = py_hint_unpack(S, y)
        expect.append("none" if r is None else rows_str(r))

    for S, P in PARAMS.items():
        om, k = P["omega"], P["k"]
        valids = []
        for w in (0, 1, om - 1, om):
            for _ in range(5):
                valids.append(rand_hint(rng, S, w))
        valids += hint_edge_rows(S)
        for _ in range(n_random):
            valids.append(rand_hint(rng, S, rng.randrange(0, om + 1)))
        for rows in valids:
            lines.append(f"HBP {S} {rows_str(rows)}")
        # weight omega + 1 and larger: outside the precondition of HintBitPack
        for w in (om + 1, om + 1, om + 2, om + 5, 2 * om, k * 40):
            for _ in range(20):
                lines.append(f"HBPX {S} {rows_str(rand_hint(rng, S, min(w, k * 256)))}")
        lines.append(f"HBPX {S} {rows_str([list(range(256))] + [[] for _ in range(k - 1)])}")
        # HintBitUnpack: valid encodings round trip
        for rows in valids:
            add_hbu(S, py_hint_pack(S, rows))
        # malformed variants
        for rows in valids[: max(300, n_random // 3)]:
            y = py_hint_pack(S, rows)
            for _kind, z in mutate_hint_bytes(rng, S, y):
                add_hbu(S, z)
        # fully random bytes, and random bytes with plausible counts
        for _ in range(n_random // 2):
            add_hbu(S, rand_bytes(rng, om + k))
        for _ in range(n_random // 2):
            y = bytearray(rand_bytes(rng, om + k))
            acc = 0
            for i in range(k):
                acc = min(om, acc + rng.randrange(0, om // k + 3))
                y[om + i] = acc
            add_hbu(S, bytes(y))
        # structured malformed corner cases
        zero = bytearray(om + k)
        add_hbu(S, bytes(zero))
        z = bytearray(zero)
        z[0] = 5  # nonzero padding with all counts zero
        add_hbu(S, bytes(z))
        z = bytearray(zero)
        z[om] = 2; z[0] = 7; z[1] = 7  # duplicate index
        for i in range(1, k):
            z[om + i] = 2
        add_hbu(S, bytes(z))
        z = bytearray(zero)
        z[om] = 2; z[0] = 9; z[1] = 3  # decreasing index
        for i in range(1, k):
            z[om + i] = 2
        add_hbu(S, bytes(z))
        # same index repeated across rows is legal (rows are independent)
        z = bytearray(zero)
        for i in range(k):
            z[i] = 7
            z[om + i] = i + 1
        add_hbu(S, bytes(z))
        # index 0 first in a later row after a nonzero index in an earlier row is legal
        z = bytearray(zero)
        z[0] = 200; z[1] = 0
        z[om] = 1
        for i in range(1, k):
            z[om + i] = 2
        add_hbu(S, bytes(z))
        # counts: row 0 = omega exactly, remaining equal omega
        z = bytearray(zero)
        for i in range(om):
            z[i] = i
        for i in range(k):
            z[om + i] = om
        add_hbu(S, bytes(z))
        # counts decreasing at the end
        z = bytearray(zero)
        z[om + k - 1] = 0
        z[om + 0] = 1; z[0] = 4
        for i in range(1, k - 1):
            z[om + i] = 1
        add_hbu(S, bytes(z))
        # count 255 / 0xFF padding
        z = bytearray(b"\xff" * (om + k))
        add_hbu(S, bytes(z))
        # byte 255 as an index is legal
        z = bytearray(zero)
        z[0] = 255
        for i in range(k):
            z[om + i] = 1
        add_hbu(S, bytes(z))
    with open(os.path.join(out, "hint.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    hb = [l for l in lines if l.startswith("HBU")]
    assert len(hb) == len(expect)
    with open(os.path.join(out, "hint.expected"), "w") as f:
        f.write("\n".join(expect) + "\n")
    return len(lines)


# --------------------------------------------------------------------------- bit packing

def gen_bitpack(rng, out, n_random):
    lines = []
    # SimpleBitPack: t1 (b = 1023), w1 for gamma2 = (q-1)/88 (b = 43) and (q-1)/32 (b = 15)
    for b in (1023, 43, 15, 1, 7):
        polys = [[0] * 256, [b] * 256, [b if i % 2 else 0 for i in range(256)], list(range(256 if b >= 255 else 0)) or [i % (b + 1) for i in range(256)]]
        polys += [[rng.randrange(b + 1) for _ in range(256)] for _ in range(n_random)]
        for p in polys:
            lines.append(f"SBP {b} " + ints(p))
        w = 32 * bitlen(b)
        bys = [bytes(w), b"\xff" * w, b"\x55" * w, b"\xaa" * w] + [rand_bytes(rng, w) for _ in range(n_random)]
        for bs in bys:
            lines.append(f"SBU {b} {hexs(bs)}")
    # BitPack: (eta, eta), t0, z
    for a, b in ((2, 2), (4, 4), (4095, 4096), (2**17 - 1, 2**17), (2**19 - 1, 2**19)):
        polys = [[-a] * 256, [b] * 256, [0] * 256, [-a if i % 2 else b for i in range(256)]]
        polys += [[rng.randrange(-a, b + 1) for _ in range(256)] for _ in range(n_random)]
        for p in polys:
            lines.append(f"BP {a} {b} " + ints(p))
        w = 32 * bitlen(a + b)
        bys = [bytes(w), b"\xff" * w, b"\x55" * w, b"\xaa" * w] + [rand_bytes(rng, w) for _ in range(n_random)]
        for bs in bys:
            lines.append(f"BU {a} {b} {hexs(bs)}")
    with open(os.path.join(out, "bitpack.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


# --------------------------------------------------------------------------- key and signature codecs

def gen_codecs(rng, out, n_random):
    lines = []
    for S, P in PARAMS.items():
        k, l, eta, g1, om, lam = P["k"], P["l"], P["eta"], P["gamma1"], P["omega"], P["lam"]
        m = (Q - 1) // (2 * P["gamma2"])
        t1len = 32 + 32 * k * 10
        szeta = 32 * bitlen(2 * eta)
        sklen = 128 + 32 * ((l + k) * bitlen(2 * eta) + 13 * k)
        szz = 32 * (1 + bitlen(g1 - 1))
        siglen = lam // 4 + l * szz + om + k

        def vec(n, lo, hi, mode):
            if mode == "lo":
                return [[lo] * 256 for _ in range(n)]
            if mode == "hi":
                return [[hi] * 256 for _ in range(n)]
            if mode == "zero":
                return [[0] * 256 for _ in range(n)]
            return [[rng.randrange(lo, hi + 1) for _ in range(256)] for _ in range(n)]

        def flat(v):
            return ints(c for p in v for c in p)

        modes = ["lo", "hi", "zero"] + ["rand"] * n_random
        # pk
        pks = []
        for mode in modes:
            rho = rand_bytes(rng, 32)
            t1 = vec(k, 0, 1023, mode)
            lines.append(f"PKE {S} {hexs(rho)} {flat(t1)}")
        pk_bytes = [bytes(t1len), b"\xff" * t1len] + [rand_bytes(rng, t1len) for _ in range(n_random)]
        for bs in pk_bytes:
            lines.append(f"PKD {S} {hexs(bs)}")
        # sk
        for mode in modes:
            rho, K, tr = rand_bytes(rng, 32), rand_bytes(rng, 32), rand_bytes(rng, 64)
            s1 = vec(l, -eta, eta, mode)
            s2 = vec(k, -eta, eta, mode)
            t0 = vec(k, -4095, 4096, mode)
            lines.append(f"SKE {S} {hexs(rho)} {hexs(K)} {hexs(tr)} {flat(s1)} {flat(s2)} {flat(t0)}")
        sk_bytes = [bytes(sklen), b"\xff" * sklen] + [rand_bytes(rng, sklen) for _ in range(n_random)]
        for bs in sk_bytes:
            lines.append(f"SKD {S} {hexs(bs)}")
        # signature
        for idx, mode in enumerate(modes):
            ct = rand_bytes(rng, lam // 4)
            z = vec(l, -(g1 - 1), g1, mode)
            if idx % 7 == 0:
                rows = [[] for _ in range(k)]
            elif idx % 7 == 1:
                rows = rand_hint(rng, S, om)
            else:
                rows = rand_hint(rng, S, rng.randrange(0, om + 1))
            lines.append(f"SGE {S} {hexs(ct)} {flat(z)} {rows_str(rows)}")
        for i in range(n_random):
            ct_z = rand_bytes(rng, lam // 4 + l * szz)
            kind = i % 4
            if kind == 0:  # valid hint
                y = py_hint_pack(S, rand_hint(rng, S, rng.randrange(0, om + 1)))
            elif kind == 1:  # malformed hint
                base = py_hint_pack(S, rand_hint(rng, S, rng.randrange(1, om + 1)))
                y = rng.choice(mutate_hint_bytes(rng, S, base))[1]
            elif kind == 2:  # random hint section
                y = rand_bytes(rng, om + k)
            else:  # hint section of zeros (valid, weight 0)
                y = bytes(om + k)
            lines.append(f"SGD {S} {hexs(ct_z + y)}")
        ff = b"\xff" * siglen
        lines.append(f"SGD {S} {hexs(bytes(siglen))}")
        lines.append(f"SGD {S} {hexs(ff)}")
        # w1Encode
        for mode in ["lo", "hi", "zero"] + ["rand"] * n_random:
            w1 = vec(k, 0, m - 1, mode)
            lines.append(f"W1E {S} {flat(w1)}")
    with open(os.path.join(out, "codecs.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="output directory (created)")
    ap.add_argument("--seed", type=int, default=204)
    ap.add_argument("--n-coeff", type=int, default=100000, help="random coefficients per function per parameter set")
    ap.add_argument("--n-poly", type=int, default=2000, help="random polynomials for NTT / NTT^-1 / MultiplyNTT / packers")
    ap.add_argument("--n-codec", type=int, default=1000, help="random cases per codec per parameter set")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rng = random.Random(a.seed)
    counts = {
        "rounding": gen_rounding(rng, a.out, a.n_coeff),
        "sweep": gen_sweep(a.out),
        "ntt": gen_ntt(rng, a.out, a.n_poly),
        "bitpack": gen_bitpack(rng, a.out, 1000),
        "hint": gen_hint(rng, a.out, a.n_codec),
        "codecs": gen_codecs(rng, a.out, a.n_codec),
    }
    for k, v in counts.items():
        print(f"{k}.txt: {v} lines")


if __name__ == "__main__":
    main()
