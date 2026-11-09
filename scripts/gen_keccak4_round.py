#!/usr/bin/env python3
"""Prints the generated part of src/keccak4.rs: `round25` (one Keccak-f[1600] round on a scalar state) and `lane_rounds2`
(two rounds on state `i` of a 4-way state).

`round25` is straight-line scalar code with the operations and the association order of the scalar round of
`keccak::keccak_f1600` (theta C and D, rho and pi fused with the theta xor, chi, iota); the output of the round is
produced row by row, so that few values are live at a time. `lane_rounds2` loads the 25 lanes `s[k][i]`, applies
`round25` twice and stores them back.

Usage: python3 scripts/gen_keccak4_round.py            print the block
       python3 scripts/gen_keccak4_round.py --check    exit 1 unless src/keccak4.rs holds exactly this block between its
                                                       `// BEGIN GENERATED` and `// END GENERATED` lines
"""
import sys
from pathlib import Path

RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
out = []
w = out.append


def rot(v, r, paren=True):
    """`v` rotated left by `r`, `v` being a variable name (r = 0: `v` itself)."""
    e = f"{v} << {r}u32 | {v} >> {64 - r}u32"
    return (f"({e})" if paren else e) if r else v


w("#[allow(clippy::manual_rotate)] // explicit shifts: they are what the extraction and the proof are about")
w("fn round25(a: &[u64; 25], rc: u64) -> [u64; 25] {")
for x in range(5):
    w(f"    let c{x} = a[{x}] ^ a[{x + 5}] ^ a[{x + 10}] ^ a[{x + 15}] ^ a[{x + 20}];")
for x in range(5):
    w(f"    let d{x} = c{(x + 4) % 5} ^ {rot(f'c{(x + 1) % 5}', 1)};")
# rho and pi: b[y + 5 * ((2x + 3y) % 5)] = rotl(a[x + 5y] ^ d[x], RHO[x + 5y]). Output row yp needs b[5yp + c], c = 0..4,
# which comes from a[x + 5c] with (2x + 3c) % 5 = yp, i.e. x = (3 yp + c) % 5.
for yp in range(5):
    for c in range(5):
        x = (3 * yp + c) % 5
        k = x + 5 * c
        if RHO[k]:
            w(f"    let t{yp}_{c} = a[{k}] ^ d{x};")
            w(f"    let b{yp}_{c} = {rot(f't{yp}_{c}', RHO[k], False)};")
        else:
            w(f"    let b{yp}_{c} = a[{k}] ^ d{x};")
    for x in range(5):
        k = x + 5 * yp
        e = f"b{yp}_{x} ^ (!b{yp}_{(x + 1) % 5} & b{yp}_{(x + 2) % 5})"
        w(f"    let o{k} = " + (f"{e} ^ rc;" if k == 0 else f"{e};"))
w("    [" + ", ".join(f"o{k}" for k in range(25)) + "]")
w("}")
w("")
w("/// Two rounds (`rc0` then `rc1`) on state `i` of the 4-way state `s`: lane `k` of state `i` is `s[k][i]`, and the other three")
w("/// states are untouched. Requires `i < 4`.")
w("fn lane_rounds2(s: &mut [[u64; 4]; 25], i: usize, rc0: u64, rc1: u64) {")
w("    let a = [" + ", ".join(f"s[{k}][i]" for k in range(25)) + "];")
w("    let m = round25(&a, rc0);")
w("    let z = round25(&m, rc1);")
for k in range(25):
    w(f"    s[{k}][i] = z[{k}];")
w("}")

block = "\n".join(out) + "\n"
if "--check" in sys.argv:
    src = (Path(__file__).resolve().parent.parent / "src/keccak4.rs").read_text()
    b, e = "// BEGIN GENERATED\n", "// END GENERATED\n"
    if b not in src or e not in src or src[src.index(b) + len(b):src.index(e)] != block:
        sys.exit("src/keccak4.rs: the generated block differs from scripts/gen_keccak4_round.py's output")
    print("src/keccak4.rs: generated block up to date")
else:
    print(block, end="")
