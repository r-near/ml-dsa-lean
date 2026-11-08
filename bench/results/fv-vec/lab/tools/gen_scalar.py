#!/usr/bin/env python3
"""Emits src/gen_scalar.rs: straight-line scalar Keccak round `rs(a, o, rc)` (row by row, as the 4-way generator)
plus the 'lv' variants that run it per state inside a loop over the 4 states (loop-vectorizer shape)."""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
def rot(e, r): return f"(({e}) << {r} | ({e}) >> {64 - r})" if r else e
w = ["#[inline(always)]", "pub fn rs(a: &[u64; 25], o: &mut [u64; 25], rc: u64) {"]
for x in range(5):
    w.append(f"let c{x} = a[{x}] ^ a[{x+5}] ^ a[{x+10}] ^ a[{x+15}] ^ a[{x+20}];")
for x in range(5):
    w.append(f"let d{x} = c{(x+4)%5} ^ {rot(f'c{(x+1)%5}', 1)};")
for yp in range(5):
    for c in range(5):
        x = (3 * yp + c) % 5
        s = x + 5 * c
        w.append(f"let b{yp}_{c} = {rot(f'(a[{s}] ^ d{x})', RHO[s])};")
    for x in range(5):
        k = x + 5 * yp
        e = f"b{yp}_{x} ^ (!b{yp}_{(x+1)%5} & b{yp}_{(x+2)%5})"
        w.append(f"o[{k}] = " + (f"{e} ^ rc;" if k == 0 else f"{e};"))
w.append("}")
open("src/gen_scalar.rs", "w").write("\n".join(w) + "\n")
