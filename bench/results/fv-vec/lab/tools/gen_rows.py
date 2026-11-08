#!/usr/bin/env python3
"""Emits src/rows.rs: round-prefix probes `rows_N` (theta + the first N output rows) over Shim4."""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
out = ["use crate::keccak4::{Lanes4, Shim4 as L};", "type St = [[u64; 4]; 25];"]
for n in range(1, 6):
    w = [f"#[target_feature(enable = \"avx2\")]\n#[inline(never)]\npub fn rows_{n}(src: &St, dst: &mut St) {{"]
    for x in range(5):
        t = f"src[{x}]"
        for y in range(1, 5):
            t = f"L::xor({t}, src[{x + 5 * y}])"
        w.append(f"let c{x} = {t};")
    for x in range(5):
        w.append(f"let d{x} = L::xor(c{(x + 4) % 5}, L::rotl::<1, 63>(c{(x + 1) % 5}));")
    for yp in range(n):
        for c in range(5):
            x = (3 * yp + c) % 5
            s = x + 5 * c
            r = RHO[s]
            e = f"L::xor(src[{s}], d{x})"
            w.append(f"let b{yp}_{c} = " + (f"L::rotl::<{r}, {64 - r}>({e});" if r else f"{e};"))
        for x in range(5):
            k = x + 5 * yp
            e = f"L::xor(b{yp}_{x}, L::andnot(b{yp}_{(x + 1) % 5}, b{yp}_{(x + 2) % 5}))"
            w.append(f"dst[{k}] = " + (f"L::xor({e}, L::splat(0x8000000080008008));" if k == 0 else f"{e};"))
    w.append("}")
    out.append("\n".join(w))
open("src/rows.rs", "w").write("\n".join(out) + "\n")
