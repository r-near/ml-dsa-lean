#!/usr/bin/env python3
"""Prints the body of `lane_rounds2` in src/keccak4.rs: two Keccak-f[1600] rounds on state `i` of a 4-way state.

The body is straight-line scalar code: 25 loads `s[k][i]`, two rounds on locals, 25 stores. The operations and their
association order are those of the scalar round of `keccak::keccak_f1600` (theta C and D, rho and pi fused with the theta
xor, chi, iota); the output of a round is produced row by row, so that few values are live at a time. `rc0` is the constant
of the first round, `rc1` of the second.

Why this shape: `keccak_f1600_x4` calls it in a loop over the four states, so the loop vectorizer (not the SLP vectorizer)
turns the loop body into 256-bit code (one lane per state); see the module documentation.
Usage: python3 scripts/gen_keccak4_round.py   (paste the output into `lane_rounds2` in src/keccak4.rs)
"""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
out = []
w = out.append


def rot(v, r, paren=True):
    """`v` rotated left by `r`, `v` being a variable name (r = 0: `v` itself)."""
    e = f"{v} << {r}u32 | {v} >> {64 - r}u32"
    return (f"({e})" if paren else e) if r else v


def rnd(src, dst, rc, tag):
    for x in range(5):
        w(f"let {tag}c{x} = {src}{x} ^ {src}{x + 5} ^ {src}{x + 10} ^ {src}{x + 15} ^ {src}{x + 20};")
    for x in range(5):
        w(f"let {tag}d{x} = {tag}c{(x + 4) % 5} ^ {rot(f'{tag}c{(x + 1) % 5}', 1)};")
    # rho and pi: b[y + 5 * ((2x + 3y) % 5)] = rotl(a[x + 5y] ^ d[x], RHO[x + 5y]). Output row yp needs b[5yp + c], c = 0..4,
    # which comes from a[x + 5c] with (2x + 3c) % 5 = yp, i.e. x = (3 yp + c) % 5.
    for yp in range(5):
        for c in range(5):
            x = (3 * yp + c) % 5
            k = x + 5 * c
            if RHO[k]:
                w(f"let {tag}t{yp}_{c} = {src}{k} ^ {tag}d{x};")
                w(f"let {tag}b{yp}_{c} = {rot(f'{tag}t{yp}_{c}', RHO[k], False)};")
            else:
                w(f"let {tag}b{yp}_{c} = {src}{k} ^ {tag}d{x};")
        for x in range(5):
            k = x + 5 * yp
            e = f"{tag}b{yp}_{x} ^ (!{tag}b{yp}_{(x + 1) % 5} & {tag}b{yp}_{(x + 2) % 5})"
            w(f"let {dst}{k} = " + (f"{e} ^ {rc};" if k == 0 else f"{e};"))


for k in range(25):
    w(f"let a{k} = s[{k}][i];")
rnd("a", "m", "rc0", "p")
rnd("m", "z", "rc1", "q")
for k in range(25):
    w(f"s[{k}][i] = z{k};")
print("\n".join("    " + l for l in out))
