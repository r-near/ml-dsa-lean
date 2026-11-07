#!/usr/bin/env python3
"""Prints the unrolled body of `round` in src/keccak4.rs (one Keccak-f[1600] round on four states at once).

The operations are those of the scalar round of `keccak::keccak_f1600` (theta C and D, rho and pi fused with the theta
xor, chi, iota); the association order of the xors is the same. State lane k = x + 5y is `src[k]`, a `[u64; 4]` holding
lane k of the four states (lane i of the vector = state i). The result goes to `dst` (all 25 entries are written), row by
row: for each row of the output, the five `b` values it needs are computed from `src` and `d`, then chi is applied and
the row stored. That keeps at most d0..d4, five `b` values and a few temporaries live (16 AVX2 registers), where the
all-at-once shape (25 `b` values live before chi) spilled about 110 times per round.
Usage: python3 scripts/gen_keccak4_round.py   (paste the output into `round` in src/keccak4.rs)
"""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
out = []
w = out.append
for x in range(5):
    t = f"src[{x}]"
    for y in range(1, 5):
        t = f"L::xor({t}, src[{x + 5 * y}])"
    w(f"let c{x} = {t};")
for x in range(5):
    w(f"let d{x} = L::xor(c{(x + 4) % 5}, L::rotl::<1, 63>(c{(x + 1) % 5}));")
# rho and pi: b[y + 5 * ((2x + 3y) % 5)] = rotl(a[x + 5y] ^ d[x], RHO[x + 5y]). Output row yp needs b[5yp + c], c = 0..4,
# which comes from a[x + 5c] with (2x + 3c) % 5 = yp, i.e. x = (3 yp + c) % 5.
for yp in range(5):
    for c in range(5):
        x = (3 * yp + c) % 5
        src = x + 5 * c
        r = RHO[src]
        e = f"L::xor(src[{src}], d{x})"
        w(f"let b{yp}_{c} = " + (f"L::rotl::<{r}, {64 - r}>({e});" if r else f"{e};"))
    for x in range(5):
        k = x + 5 * yp
        e = f"L::xor(b{yp}_{x}, L::andnot(b{yp}_{(x + 1) % 5}, b{yp}_{(x + 2) % 5}))"
        w(f"dst[{k}] = " + (f"L::xor({e}, L::splat(rc));" if k == 0 else f"{e};"))
print("\n".join("    " + l for l in out))
