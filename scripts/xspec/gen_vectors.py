#!/usr/bin/env python3
"""Vector generator for the FIPS 204 differential (our spec versus ocaml-pq).

Writes line-oriented vector files into an output directory; `xspec-diff ours|theirs` reads them and prints one
canonical output line per input line, `compare.py` diffs the outputs.

The leaf vectors (rounding, sweeps, NTT, bit packers, hints, codecs) come from the generator of the VCVio
differential (`scripts/diff-vcvio/gen_vectors.py`, imported by path).  New here:

  C3B b0 b1 b2 / SWEEPC3B c      CoeffFromThreeBytes (all 2^24 triples, in 256 digest chunks, plus edges)
  CHB eta b / SWEEPCHB eta       CoeffFromHalfByte
  SHK w msg d                    SHAKE128 / SHAKE256 (w = 128 / 256) of msg, d output bytes
  RNTT F rho                     RejNTTPoly with F loop iterations (rho: 34 bytes)
  RBND S F rho                   RejBoundedPoly (rho: 66 bytes);  SIB S F rho: SampleInBall (rho: lambda/4 bytes)
  EXA S F rho / EXS S F rho / EXM S rho kappa     ExpandA, ExpandS, ExpandMask
  KGI S xi                       KeyGen_internal
  SGI S sk M' rnd / SGN S sk M ctx rnd           Sign_internal / Sign
  VRI S pk M' sig / VRF S pk M sig ctx           Verify_internal / Verify

Top-level lines come from the NIST ACVP vectors in tests/data/acvp (all parameter sets, pure ML-DSA) plus random
messages, contexts, randomness and mutated signatures.  `*.expected` files carry the ACVP answers (one line per
input line, `?` where there is none).
"""
import argparse
import gzip
import importlib.util
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
spec = importlib.util.spec_from_file_location("gv", os.path.join(ROOT, "scripts", "diff-vcvio", "gen_vectors.py"))
gv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gv)

Q = gv.Q
PARAMS = gv.PARAMS
SETS = {"ML-DSA-44": 44, "ML-DSA-65": 65, "ML-DSA-87": 87}


def hexs(b):
    return bytes(b).hex() if len(b) else "-"


def rb(rng, n):
    return bytes(rng.getrandbits(8) for _ in range(n))


def write(out, name, lines, expected=None):
    with open(os.path.join(out, name + ".txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    if expected is not None:
        assert len(expected) == len(lines)
        with open(os.path.join(out, name + ".expected"), "w") as f:
            f.write("\n".join(expected) + "\n")
    return len(lines)


def gen_coeff(rng, out):
    lines = [f"SWEEPC3B {c}" for c in range(256)]
    lines += [f"SWEEPCHB {e}" for e in (2, 4)]
    edges = [0, 1, 127, 128, 224, 225, 255]
    for b2 in (0, 1, 126, 127, 128, 129, 254, 255):
        for b1 in (0, 1, 223, 224, 225, 255):
            for b0 in (0, 1, 2, 254, 255):
                lines.append(f"C3B {b0} {b1} {b2}")
    for _ in range(5000):
        lines.append(f"C3B {rng.randrange(256)} {rng.randrange(256)} {rng.randrange(256)}")
    for e in (2, 4):
        for b in range(0, 300):
            lines.append(f"CHB {e} {b}")
    return write(out, "coeff", lines)


def gen_shake(rng, out):
    lines = []
    for w, rate in ((128, 168), (256, 136)):
        lens = {0, 1, 2, 3, 7, 8, 31, 32, 33, 34, 63, 64, 65, 66, 100, rate - 2, rate - 1, rate, rate + 1,
                rate + 2, 2 * rate - 1, 2 * rate, 2 * rate + 1, 3 * rate + 5}
        douts = (0, 1, 3, 32, 64, 128, rate - 1, rate, rate + 1, 2 * rate, 2 * rate + 7, 840, 1000)
        for n in sorted(lens):
            for d in douts:
                lines.append(f"SHK {w} {hexs(rb(rng, n))} {d}")
        for _ in range(150):
            lines.append(f"SHK {w} {hexs(rb(rng, rng.randrange(0, 500)))} {rng.randrange(0, 1200)}")
        for byte in (0x00, 0xff, 0x1f, 0x80, 0x9f):
            for n in (rate - 1, rate, rate + 1):
                lines.append(f"SHK {w} {hexs(bytes([byte]) * n)} 300")
    return write(out, "shake", lines)


def gen_samplers(rng, out, n):
    lines = []
    for _ in range(n):
        lines.append(f"RNTT 1000 {hexs(rb(rng, 34))}")
    for F in (1, 2, 3, 10, 50, 100, 200, 254, 255, 256, 257, 258, 260, 270, 300, 400):
        for _ in range(max(4, n // 20)):
            lines.append(f"RNTT {F} {hexs(rb(rng, 34))}")
    for S in (44, 65, 87):
        P = PARAMS[S]
        for _ in range(n):
            lines.append(f"RBND {S} 1000 {hexs(rb(rng, 66))}")
        for F in (1, 5, 64, 100, 128, 130, 135, 136, 137, 140, 150, 200, 256, 300):
            for _ in range(max(4, n // 20)):
                lines.append(f"RBND {S} {F} {hexs(rb(rng, 66))}")
        for _ in range(n):
            lines.append(f"SIB {S} 1000 {hexs(rb(rng, P['lam'] // 4))}")
    return write(out, "samplers", lines)


def gen_expand(rng, out, n):
    lines = []
    for S in (44, 65, 87):
        for _ in range(n):
            lines.append(f"EXA {S} 1000 {hexs(rb(rng, 32))}")
            lines.append(f"EXS {S} 1000 {hexs(rb(rng, 64))}")
            lines.append(f"EXM {S} {hexs(rb(rng, 64))} {rng.choice([0, 1, 4, 5, 7, 100, 1000, 65000, 65528])}")
    return write(out, "expand", lines)


def load(name):
    with gzip.open(os.path.join(ROOT, "tests", "data", "acvp", f"{name}.json.gz"), "rt") as f:
        return json.load(f)


def mutate(rng, b):
    b = bytearray(b)
    if not b:
        return bytes(b)
    kind = rng.randrange(3)
    if kind == 0:
        b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    elif kind == 1:
        for _ in range(rng.randrange(1, 4)):
            b[rng.randrange(len(b))] = rng.getrandbits(8)
    else:
        b[-1] ^= 0xff
    return bytes(b)


def gen_top(rng, out, n_rand, n_sign):
    kgl, kge = [], []
    for g in load("keyGen")["testGroups"]:
        S = SETS[g["parameterSet"]]
        for t in g["tests"]:
            kgl.append(f"KGI {S} {t['seed'].lower()}")
            kge.append(f"{t['pk'].lower()} {t['sk'].lower()}")
    for S in (44, 65, 87):
        for _ in range(n_rand):
            kgl.append(f"KGI {S} {hexs(rb(rng, 32))}")
            kge.append("?")
    write(out, "keygen", kgl, kge)

    sl, se = [], []
    vl, ve = [], []
    seen_sk = {}
    for g in load("sigGen")["testGroups"]:
        if g["externalMu"] or g["preHash"] == "preHash":
            continue
        S = SETS[g["parameterSet"]]
        det = bool(g["deterministic"])
        for t in g["tests"]:
            sk = t["sk"].lower()
            seen_sk.setdefault(S, []).append(sk)
            rnd = "00" * 32 if det else t["rnd"].lower()
            msg = t["message"].lower() or "-"
            sig = t["signature"].lower()
            if g["signatureInterface"] == "internal":
                sl.append(f"SGI {S} {sk} {msg} {rnd}")
                se.append(sig)
                if "pk" in t:
                    vl.append(f"VRI {S} {t['pk'].lower()} {msg} {sig}")
                    ve.append("1")
            else:
                ctx = t.get("context", "").lower() or "-"
                sl.append(f"SGN {S} {sk} {msg} {ctx} {rnd}")
                se.append(sig)
                if "pk" in t:
                    vl.append(f"VRF {S} {t['pk'].lower()} {msg} {sig} {ctx}")
                    ve.append("1")
    # more random signing: ACVP keys with fresh messages, contexts, randomness (no expected answer)
    for S, sks in seen_sk.items():
        for _ in range(n_sign):
            sk = rng.choice(sks)
            msg = hexs(rb(rng, rng.randrange(0, 100)))
            ctx = hexs(rb(rng, rng.randrange(0, 20)))
            sl.append(f"SGN {S} {sk} {msg} {ctx} {hexs(rb(rng, 32))}")
            se.append("?")
            sl.append(f"SGI {S} {sk} {msg} {hexs(rb(rng, 32))}")
            se.append("?")
        # context longer than 255 bytes: Sign returns bottom
        sl.append(f"SGN {S} {rng.choice(sks)} {hexs(rb(rng, 10))} {hexs(rb(rng, 256))} {'00' * 32}")
        se.append("?")
    for g in load("sigVer")["testGroups"]:
        if g["externalMu"] or g["preHash"] == "preHash":
            continue
        S = SETS[g["parameterSet"]]
        for t in g["tests"]:
            msg = t["message"].lower() or "-"
            pk = t["pk"].lower()
            sig = t["signature"].lower()
            if g["signatureInterface"] == "internal":
                vl.append(f"VRI {S} {pk} {msg} {sig}")
            else:
                ctx = t.get("context", "").lower() or "-"
                vl.append(f"VRF {S} {pk} {msg} {sig} {ctx}")
            ve.append("1" if t["testPassed"] else "0")
    # mutated copies of the valid verification lines, and wrong lengths
    base = [l for l, e in zip(vl, ve) if e == "1"]
    for l in base:
        f = l.split(" ")
        for _ in range(3):
            g = list(f)
            what = rng.randrange(4)
            if what == 0:
                g[4] = mutate(rng, bytes.fromhex(g[4])).hex()          # signature
            elif what == 1:
                g[3] = hexs(mutate(rng, bytes.fromhex(g[3]) if g[3] != "-" else b"\x00"))  # message
            elif what == 2:
                g[2] = mutate(rng, bytes.fromhex(g[2])).hex()          # public key
            else:
                g[4] = g[4][:-2] if rng.random() < 0.5 else g[4] + "00"    # wrong length
            vl.append(" ".join(g))
            ve.append("?")
    write(out, "sign", sl, se)
    write(out, "verify", vl, ve)
    return len(kgl), len(sl), len(vl)


def pack_bits(vals, width):
    """Little-endian bit packing of non-negative `width`-bit values (the BitPack layout of FIPS 204 Algorithm 17)."""
    acc = 0
    for i, v in enumerate(vals):
        acc |= v << (i * width)
    return acc.to_bytes((len(vals) * width + 7) // 8, "little")


def gen_skd_valid(rng, out, n_valid, n_bad):
    """SKD lines the random-byte generator of codecs does not reach: secret keys whose s1/s2 coefficients are all
    in [-eta, eta] (n_valid per parameter set, both sides must decode them identically), and the same with exactly
    one s1/s2 coefficient pushed out of range (n_bad; ocaml-pq rejects such keys, FIPS-literal Algorithm 25 decodes)."""
    lines = []
    for S, P in PARAMS.items():
        k, l, eta = P["k"], P["l"], P["eta"]
        w = gv.bitlen(2 * eta)
        for i in range(n_valid + n_bad):
            bad = i >= n_valid
            parts = [rb(rng, 32), rb(rng, 32), rb(rng, 64)]
            nsec = l + k
            zs = [[rng.randrange(0, 2 * eta + 1) for _ in range(256)] for _ in range(nsec)]
            if bad:
                zs[rng.randrange(nsec)][rng.randrange(256)] = rng.randrange(2 * eta + 1, 1 << w)
            parts += [pack_bits(z, w) for z in zs]
            parts += [pack_bits([rng.randrange(0, 1 << 13) for _ in range(256)], 13) for _ in range(k)]
            lines.append(f"SKD {S} {gv.hexs(b''.join(parts))}")
    with open(os.path.join(out, "codecs.txt"), "a") as f:
        f.write("\n".join(lines) + "\n")
    return len(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=204)
    ap.add_argument("--n-coeff", type=int, default=100000)
    ap.add_argument("--n-poly", type=int, default=2000, help="random polynomials for NTT / NTT^-1 / MultiplyNTT")
    ap.add_argument("--n-codec", type=int, default=1000)
    ap.add_argument("--n-sampler", type=int, default=300)
    ap.add_argument("--n-top", type=int, default=100, help="random seeds per parameter set for KGI")
    ap.add_argument("--n-sign", type=int, default=6, help="random sign cases per ACVP key")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rng = random.Random(a.seed)
    counts = {
        "rounding": gv.gen_rounding(rng, a.out, a.n_coeff),
        "sweep": gv.gen_sweep(a.out),
        "ntt": gv.gen_ntt(rng, a.out, a.n_poly),
        "bitpack": gv.gen_bitpack(rng, a.out, 1000),
        "hint": gv.gen_hint(rng, a.out, a.n_codec),
        "codecs": gv.gen_codecs(rng, a.out, a.n_codec),
        "coeff": gen_coeff(rng, a.out),
        "shake": gen_shake(rng, a.out),
        "samplers": gen_samplers(rng, a.out, a.n_sampler),
        "expand": gen_expand(rng, a.out, max(5, a.n_sampler // 10)),
    }
    counts["codecs"] += gen_skd_valid(random.Random(a.seed + 1), a.out, 200, 100)
    kg, sg, vr = gen_top(rng, a.out, a.n_top, a.n_sign)
    counts.update({"keygen": kg, "sign": sg, "verify": vr})
    for k, v in counts.items():
        print(f"{k}.txt: {v} lines")


if __name__ == "__main__":
    main()
