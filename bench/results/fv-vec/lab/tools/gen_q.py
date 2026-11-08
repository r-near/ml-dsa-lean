#!/usr/bin/env python3
"""Emits src/q.rs: `round25(a: &[u64; 25], rc) -> [u64; 25]` (one round, straight line) and `lane_rounds2_q` built from it."""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
def rot(v, r, paren=True):
    e = f"{v} << {r}u32 | {v} >> {64 - r}u32"
    return (f"({e})" if paren else e) if r else v
w = ["#[inline(always)]", "pub fn round25(a: &[u64; 25], rc: u64) -> [u64; 25] {"]
for x in range(5):
    w.append(f"let c{x} = a[{x}] ^ a[{x+5}] ^ a[{x+10}] ^ a[{x+15}] ^ a[{x+20}];")
for x in range(5):
    w.append(f"let d{x} = c{(x+4)%5} ^ {rot(f'c{(x+1)%5}', 1)};")
for yp in range(5):
    for c in range(5):
        x = (3 * yp + c) % 5; k = x + 5 * c
        if RHO[k]:
            w.append(f"let t{yp}_{c} = a[{k}] ^ d{x};")
            w.append(f"let b{yp}_{c} = {rot(f't{yp}_{c}', RHO[k], False)};")
        else:
            w.append(f"let b{yp}_{c} = a[{k}] ^ d{x};")
    for x in range(5):
        k = x + 5 * yp
        e = f"b{yp}_{x} ^ (!b{yp}_{(x+1)%5} & b{yp}_{(x+2)%5})"
        w.append(f"let o{k} = " + (f"{e} ^ rc;" if k == 0 else f"{e};"))
w.append("[" + ", ".join(f"o{k}" for k in range(25)) + "]")
w.append("}")
w.append("#[inline(always)]\npub fn lane_rounds2_q(s: &mut [[u64; 4]; 25], i: usize, rc0: u64, rc1: u64) {")
w.append("let a = [" + ", ".join(f"s[{k}][i]" for k in range(25)) + "];")
w.append("let m = round25(&a, rc0);")
w.append("let z = round25(&m, rc1);")
for k in range(25):
    w.append(f"s[{k}][i] = z[{k}];")
w.append("}")
open("src/q.rs", "w").write("\n".join(w) + "\n")
