#!/usr/bin/env python3
"""Generate the input vectors for the Impl differential evaluation (see scripts/impl-eval.sh).

Usage: python3 -I scripts/gen-impl-eval-inputs.py OUT_DIR [--scale F]

Writes OUT_DIR/inputs.txt (one case per line: `op arg arg ...`) and OUT_DIR/expected.txt (one line per case: the
expected output from an independent source such as the NIST ACVP vectors, or `?` when there is none).
Deterministic: a fixed PRNG seed, standard library only. `--scale` multiplies the random-case counts.

Encodings: bytes are lower-case hex (`-` for empty); integers are decimal; a polynomial is 256 coefficients as
8 hex digits each (big-endian); a boolean polynomial is 256 characters `0`/`1`; vectors concatenate their
polynomials. Every op name for a parameter set ends in 44, 65 or 87.
"""
import argparse
import gzip
import hashlib
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
Q = 8380417

# name: (K, L, eta, eta_bits, tau, gamma1, gamma1_bits, gamma2, w1_bits, omega, c_tilde_len)
SETS = {
    "44": dict(K=4, L=4, eta=2, eta_bits=3, tau=39, gamma1=1 << 17, g1bits=18, gamma2=95232, w1bits=6, omega=80, ct=32),
    "65": dict(K=6, L=5, eta=4, eta_bits=4, tau=49, gamma1=1 << 19, g1bits=20, gamma2=261888, w1bits=4, omega=55, ct=48),
    "87": dict(K=8, L=7, eta=2, eta_bits=3, tau=60, gamma1=1 << 19, g1bits=20, gamma2=261888, w1bits=4, omega=75, ct=64),
}
NAME = {"ML-DSA-44": "44", "ML-DSA-65": "65", "ML-DSA-87": "87"}


def pk_len(s):
    return 32 + 320 * s["K"]


def sk_len(s):
    return 128 + 32 * ((s["K"] + s["L"]) * s["eta_bits"] + 13 * s["K"])


def sig_len(s):
    return s["ct"] + s["L"] * 32 * s["g1bits"] + s["omega"] + s["K"]


rng = random.Random(0x4D4C445341)  # fixed seed
cases = []  # (line, expected)


def rb(n):
    return rng.getrandbits(8 * n).to_bytes(n, "little") if n else b""


def hx(b):
    return b.hex() if b else "-"


def add(op, *args, expected="?"):
    cases.append((" ".join([op] + [str(a) for a in args]), expected))


def poly_hex(cs):
    assert len(cs) == 256
    return "".join("%08x" % c for c in cs)


def bool_hex(bs):
    return "".join("1" if b else "0" for b in bs)


EDGE = [0, 1, 2, 3, Q - 1, Q - 2, Q - 3, Q // 2, Q // 2 + 1, Q // 2 - 1, (Q - 1) // 2, 1 << 12, 1 << 13, (1 << 13) - 1,
        (1 << 22), (1 << 22) - 1, (1 << 23) - 1, 95232, 2 * 95232, 261888, 2 * 261888, 2 * 261888 - 1, 2 * 95232 - 1,
        Q - 2 * 95232, Q - 2 * 261888]


def coeff(bound):
    """A coefficient in [0, bound): uniform most of the time, an edge value some of the time."""
    if rng.random() < 0.15:
        e = [x for x in EDGE if x < bound]
        if e:
            return rng.choice(e)
    return rng.randrange(bound)


def poly(bound=Q):
    return [coeff(bound) for _ in range(256)]


def polys(n, bound=Q):
    return [poly(bound) for _ in range(n)]


def vhex(ps):
    return "".join(poly_hex(p) for p in ps)


def signed_poly(lo, hi):
    """Canonical representatives of integers in [lo, hi]."""
    out = []
    for _ in range(256):
        r = rng.random()
        v = lo if r < 0.05 else hi if r < 0.10 else rng.randint(lo, hi)
        out.append(v % Q)
    return out


def bool_poly(density):
    return [rng.random() < density for _ in range(256)]


def hint_bytes(s, valid=True):
    """A HintBitUnpack input (omega + K bytes): valid structure when `valid`, else random bytes."""
    K, omega = s["K"], s["omega"]
    if not valid:
        return rb(omega + K)
    out = bytearray(omega + K)
    idx = 0
    for i in range(K):
        room = omega - idx
        cnt = rng.randint(0, min(room, rng.choice([0, 1, 3, 8, 20, room])))
        pos = sorted(rng.sample(range(256), cnt))
        for j, p in enumerate(pos):
            out[idx + j] = p
        idx += cnt
        out[omega + i] = idx
    return bytes(out)


def mutate(b, k=1):
    b = bytearray(b)
    for _ in range(k):
        if not b:
            break
        b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    return bytes(b)


def load(name):
    with gzip.open(ROOT / "tests" / "data" / "acvp" / f"{name}.json.gz", "rt") as f:
        return json.load(f)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out_dir")
    ap.add_argument("--scale", type=float, default=1.0)
    a = ap.parse_args()
    N = max(1, int(1000 * a.scale))  # polynomial-level families
    NS = max(1, int(10000 * a.scale))  # scalar families

    # ------------------------------------------------------------------ Keccak
    for _ in range(N):
        add("keccak_f1600", hx(rb(200)))
    add("keccak_f1600", hx(bytes(200)))
    add("keccak_f1600", hx(b"\xff" * 200))
    for fam, rate in (("shake128", 168), ("shake256", 136)):
        for i in range(N):
            near = rng.choice([rate - 1, rate, rate + 1, 2 * rate - 1, 2 * rate, 2 * rate + 1, 0, 1])
            ml = near if rng.random() < 0.5 else rng.randrange(0, 3 * rate)
            ol = rng.choice([0, 1, rate - 1, rate, rate + 1, 2 * rate, 2 * rate + 1]) if rng.random() < 0.5 else rng.randrange(0, 3 * rate)
            add(fam, hx(rb(ml)), ol, rng.choice([1, 2, 7, 13, 64, 1000]))

    # ------------------------------------------------------------------ field
    for _ in range(NS):
        add("f_add", coeff(Q), coeff(Q))
        add("f_sub", coeff(Q), coeff(Q))
        add("f_mul", coeff(Q), coeff(Q))
        add("f_neg", coeff(Q))
        add("f_small_reduce", coeff(2 * Q))
        add("f_barrett_reduce", rng.choice([coeff(Q * Q), rng.randrange(Q * Q), Q * Q - 1, (Q - 1) * (Q - 1)]))
        add("f_ct_lt_mask", rng.getrandbits(rng.choice([8, 23, 32, 46, 63])), rng.getrandbits(rng.choice([8, 23, 32, 46, 63])))
        add("f_ct_select", rng.getrandbits(32), rng.getrandbits(32), rng.choice([0, 0xFFFFFFFF, rng.getrandbits(32)]))

    # ------------------------------------------------------------------ NTT
    for _ in range(N):
        add("ntt", poly_hex(poly()))
        add("ntt_inverse", poly_hex(poly()))
        add("multiply_ntt", poly_hex(poly()), poly_hex(poly()))
        add("add_poly", poly_hex(poly()), poly_hex(poly()))
        add("sub_poly", poly_hex(poly()), poly_hex(poly()))
    add("ntt", poly_hex([0] * 256))
    add("ntt", poly_hex([Q - 1] * 256))
    add("ntt_inverse", poly_hex([Q - 1] * 256))
    for sn, s in SETS.items():
        for _ in range(N // 3 + 1):
            add(f"matrix_vector_ntt{sn}", vhex([p for _ in range(s['K']) for p in polys(s['L'])]), vhex(polys(s["L"])))
        for _ in range(N // 3 + 1):
            add(f"vec_infinity_norm{sn}", vhex(polys(s["K"])))

    # ------------------------------------------------------------------ rounding
    def edge_r(sn):
        g2 = SETS[sn]["gamma2"]
        k = rng.randrange(0, (Q - 1) // (2 * g2) + 1)
        return max(0, min(Q - 1, k * 2 * g2 + rng.randint(-3, 3)))

    for _ in range(NS):
        add("power2round", coeff(Q))
        add("infinity_norm", coeff(Q))
    for sn in SETS:
        for _ in range(NS):
            r = edge_r(sn) if rng.random() < 0.3 else coeff(Q)
            add(f"decompose{sn}", r)
            add(f"high_bits{sn}", r)
            add(f"low_bits{sn}", coeff(Q))
            add(f"make_hint{sn}", coeff(Q), coeff(Q))
            add(f"use_hint{sn}", rng.randrange(2), r)
        for _ in range(N):
            add(f"poly_high_bits{sn}", poly_hex(poly()))
            add(f"poly_low_bits{sn}", poly_hex(poly()))
            add(f"poly_use_hint{sn}", bool_hex(bool_poly(rng.choice([0.1, 0.5, 0.9]))), poly_hex(poly()))
    for _ in range(N):
        add("poly_power2round", poly_hex(poly()))

    # ------------------------------------------------------------------ sampling
    for _ in range(N):
        add("rej_ntt_poly", hx(rb(34)))
    for b in range(256):
        for sn in SETS:
            add(f"coeff_from_half_byte{sn}", b)
    for _ in range(NS):
        add("coeff_from_three_bytes", rng.randrange(256), rng.randrange(256), rng.choice([rng.randrange(256), 0x7F, 0x7E, 0xFF, 0x80]))
    for sn, s in SETS.items():
        for _ in range(N):
            add(f"rej_bounded_poly{sn}", hx(rb(66)))
        for _ in range(N):
            add(f"expand_s{sn}", hx(rb(64)))
        for _ in range(N):
            add(f"expand_a{sn}", hx(rb(32)))
        for _ in range(N):
            add(f"expand_mask{sn}", hx(rb(64)), rng.choice([0, 1, 255, 256, 65535, rng.randrange(65536)]))
        for _ in range(N):
            add(f"sample_in_ball{sn}", hx(rb(s["ct"])))

    # ------------------------------------------------------------------ codecs
    for c in (3, 4, 6, 10, 13, 18, 20, 1, 8, 23):
        for _ in range(N):
            add("bit_pack", poly_hex(poly(1 << c)), c)
        for _ in range(N):
            add("bit_unpack", hx(rb(32 * c)), c)
    for z in range(Q - 3, Q + 4):  # boundary of the rejection test, with and without the (ignored) top bit
        for hi in (0, 0x80):
            add("coeff_from_three_bytes", z & 255, (z >> 8) & 255, ((z >> 16) & 127) | hi)
    for sn, s in SETS.items():
        K, L = s["K"], s["L"]
        eta = s["eta"]
        g1 = s["gamma1"]
        rho = lambda: rb(32)
        for _ in range(N):
            add(f"pk_encode{sn}", hx(rho()), vhex(polys(K, 1 << 10)))
            add(f"pk_decode{sn}", hx(rb(pk_len(s))))
            add(f"sk_encode{sn}", hx(rho()), hx(rb(32)), hx(rb(64)),
                vhex([signed_poly(-eta, eta) for _ in range(L)]), vhex([signed_poly(-eta, eta) for _ in range(K)]),
                vhex([signed_poly(-(1 << 12) + 1, 1 << 12) for _ in range(K)]))
            add(f"sk_decode{sn}", hx(rb(sk_len(s))))
            hs = [bool_poly(rng.choice([0.0, 0.01, 0.05])) for _ in range(K)]
            # sig_encode requires at most omega hints in total
            while sum(sum(h) for h in hs) > s["omega"]:
                hs = [bool_poly(0.01) for _ in range(K)]
            add(f"sig_encode{sn}", hx(rb(s["ct"])), vhex([signed_poly(-g1 + 1, g1) for _ in range(L)]),
                "".join(bool_hex(h) for h in hs))
            add(f"w1_encode{sn}", vhex(polys(K, (Q - 1) // (2 * s["gamma2"]))))
            add(f"hint_bit_pack{sn}", "".join(bool_hex(h) for h in hs))
        for _ in range(N):
            valid = rng.random() < 0.7
            hb = hint_bytes(s, valid)
            if valid and rng.random() < 0.4:
                hb = mutate(hb, rng.choice([1, 2]))
            add(f"hint_bit_unpack{sn}", hx(hb))
        for _ in range(N):
            body = rb(sig_len(s) - s["omega"] - K)
            hb = hint_bytes(s, rng.random() < 0.8)
            if rng.random() < 0.3:
                hb = mutate(hb)
            add(f"sig_decode{sn}", hx(body + hb))

    # ------------------------------------------------------------------ ACVP and API level
    kg = load("keyGen")
    keys = {sn: [] for sn in SETS}  # (xi, pk, sk) from the vectors, used to seed the extra cases
    for g in kg["testGroups"]:
        sn = NAME[g["parameterSet"]]
        for t in g["tests"]:
            xi, pk, sk = bytes.fromhex(t["seed"]), bytes.fromhex(t["pk"]), bytes.fromhex(t["sk"])
            keys[sn].append((xi, pk, sk))
            add(f"keygen{sn}", hx(xi), expected=hx(pk) + " " + hx(sk))
    sg = load("sigGen")
    gen_ver = {sn: [] for sn in SETS}  # (kind, pk, msg, ctx, sig): valid by construction (NIST signatures)
    for g in sg["testGroups"]:
        if g["externalMu"] or g["preHash"] == "preHash":
            continue
        sn = NAME[g["parameterSet"]]
        det = bool(g["deterministic"])
        for t in g["tests"]:
            msg = bytes.fromhex(t["message"])
            sk = bytes.fromhex(t["sk"])
            rnd = bytes(32) if det else bytes.fromhex(t["rnd"])
            sig = t["signature"].lower()
            if g["signatureInterface"] == "internal":
                add(f"sign_internal{sn}", hx(sk), hx(msg), hx(rnd), expected=sig)
                gen_ver[sn].append(("i", bytes.fromhex(t["pk"]), msg, b"", bytes.fromhex(sig)))
            else:
                ctx = bytes.fromhex(t.get("context", ""))
                add(f"sign{sn}", hx(sk), hx(msg), hx(ctx), hx(rnd), expected=sig)
                gen_ver[sn].append(("e", bytes.fromhex(t["pk"]), msg, ctx, bytes.fromhex(sig)))
    sv = load("sigVer")
    valid_ver = {sn: [] for sn in SETS}
    skipped = 0
    for g in sv["testGroups"]:
        if g["externalMu"] or g["preHash"] == "preHash":
            continue
        sn = NAME[g["parameterSet"]]
        s = SETS[sn]
        for t in g["tests"]:
            pk, msg, sig = bytes.fromhex(t["pk"]), bytes.fromhex(t["message"]), bytes.fromhex(t["signature"])
            if len(pk) != pk_len(s) or len(sig) != sig_len(s):
                skipped += 1
                continue
            exp = "1" if t["testPassed"] else "0"
            if g["signatureInterface"] == "internal":
                add(f"verify_internal{sn}", hx(pk), hx(msg), hx(sig), expected=exp)
                if t["testPassed"]:
                    valid_ver[sn].append(("i", pk, msg, b"", sig))
            else:
                ctx = bytes.fromhex(t.get("context", ""))
                add(f"verify{sn}", hx(pk), hx(msg), hx(ctx), hx(sig), expected=exp)
                if t["testPassed"]:
                    valid_ver[sn].append(("e", pk, msg, ctx, sig))
    print(f"acvp sigVer cases skipped for wrong lengths: {skipped}", file=sys.stderr)

    # Extra top-level cases (no independent expected value; the two implementations are compared).
    for sn, s in SETS.items():
        for xi in [bytes(32), b"\xff" * 32] + [rb(32) for _ in range(max(1, int(60 * a.scale)))]:
            add(f"keygen{sn}", hx(xi))
        for _ in range(max(1, int(60 * a.scale))):
            xi, pk, sk = rng.choice(keys[sn])
            ctxlen = rng.choice([0, 1, 5, 255, 256, 300])
            add(f"sign{sn}", hx(sk), hx(rb(rng.choice([0, 1, 17, 100, 300, 1000]))), hx(rb(ctxlen)), hx(rng.choice([bytes(32), rb(32)])))
        for _ in range(max(1, int(30 * a.scale))):
            xi, pk, sk = rng.choice(keys[sn])
            add(f"sign_internal{sn}", hx(sk), hx(rb(rng.choice([0, 3, 64, 200]))), hx(rb(32)))
        # verify the NIST sigGen signatures as they are (valid), then mutated valid vectors (message, context,
        # signature, public key), and random garbage
        for kind, pk, msg, ctx, sig in gen_ver[sn]:
            if kind == "i":
                add(f"verify_internal{sn}", hx(pk), hx(msg), hx(sig), expected="1")
            else:
                add(f"verify{sn}", hx(pk), hx(msg), hx(ctx), hx(sig), expected="1")
        for kind, pk, msg, ctx, sig in valid_ver[sn] + gen_ver[sn]:
            for _ in range(max(1, int(12 * a.scale))):
                which = rng.choice(["sig", "sig", "sig", "msg", "ctx", "pk", "sig2"])
                m2, c2, s2, p2 = msg, ctx, sig, pk
                if which == "sig":
                    s2 = mutate(sig)
                elif which == "sig2":
                    s2 = mutate(sig, 4)
                elif which == "msg":
                    m2 = mutate(msg) if msg else b"x"
                elif which == "ctx":
                    c2 = mutate(ctx) if ctx else b"c"
                else:
                    p2 = mutate(pk)
                if kind == "i":
                    add(f"verify_internal{sn}", hx(p2), hx(m2), hx(s2))
                else:
                    add(f"verify{sn}", hx(p2), hx(m2), hx(c2), hx(s2))
        for _ in range(max(1, int(30 * a.scale))):
            add(f"verify{sn}", hx(rb(pk_len(s))), hx(rb(20)), hx(rb(rng.choice([0, 10, 256]))), hx(rb(sig_len(s))))
        # a context longer than 255 on a real valid vector
        for kind, pk, msg, ctx, sig in valid_ver[sn][:2]:
            add(f"verify{sn}", hx(pk), hx(msg), hx(rb(256)), hx(sig))

    out = Path(a.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / "inputs.txt").write_text("".join(c + "\n" for c, _ in cases))
    (out / "expected.txt").write_text("".join(e + "\n" for _, e in cases))
    h = hashlib.sha256((out / "inputs.txt").read_bytes()).hexdigest()
    print(f"wrote {len(cases)} cases to {out}/inputs.txt (sha256 {h})", file=sys.stderr)


if __name__ == "__main__":
    main()
