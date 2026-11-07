#!/usr/bin/env python3
"""Prints the unrolled body of `round` in src/keccak4.rs (one Keccak-f[1600] round on four states at once).

The body is the scalar round of `keccak::keccak_f1600`, operation for operation and in the same association order:
theta (C, D), then rho and pi fused with the theta xor, chi, iota. State lane k = x + 5y is `s[k]`, a `[u64; 4]`
holding lane k of the four states (lane i of the vector = state i).
Usage: python3 scripts/gen_keccak4_round.py   (paste the output into `round` in src/keccak4.rs)
"""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
out = []
w = out.append
for k in range(25):
    w(f"let a{k} = s[{k}];")
for x in range(5):
    t = f"a{x}"
    for y in range(1, 5):
        t = f"L::xor({t}, a{x + 5 * y})"
    w(f"let c{x} = {t};")
for x in range(5):
    w(f"let d{x} = L::xor(c{(x + 4) % 5}, L::rotl::<1, 63>(c{(x + 1) % 5}));")
# rho and pi: b[y + 5 * ((2x + 3y) % 5)] = rotl(a[x + 5y] ^ d[x], RHO[x + 5y])
for x in range(5):
    for y in range(5):
        src, dst = x + 5 * y, y + 5 * ((2 * x + 3 * y) % 5)
        r = RHO[src]
        e = f"L::xor(a{src}, d{x})"
        w(f"let b{dst} = " + (f"L::rotl::<{r}, {64 - r}>({e});" if r else f"{e};"))
for x in range(5):
    for y in range(5):
        k = x + 5 * y
        n1, n2 = (x + 1) % 5 + 5 * y, (x + 2) % 5 + 5 * y
        e = f"L::xor(b{k}, L::andnot(b{n1}, b{n2}))"
        w(f"s[{k}] = " + (f"L::xor({e}, L::splat(rc));" if k == 0 else f"{e};"))
print("\n".join("    " + l for l in out))
