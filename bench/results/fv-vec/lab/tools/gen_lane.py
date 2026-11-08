#!/usr/bin/env python3
"""Emits src/lane.rs: `lane_rounds_N(s, i, rcs...)`, N rounds of Keccak on state `i` of the 4-way state `s`, straight line:
25 loads s[k][i], N rounds on locals, 25 stores. Rounds as the scalar keccak_f1600 (row-by-row b/chi order)."""
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
def rot(e, r): return f"(({e}) << {r} | ({e}) >> {64 - r})" if r else e
def rnd(w, src, dst, rc, tag):
    for x in range(5):
        w.append(f"let {tag}c{x} = {src}{x} ^ {src}{x+5} ^ {src}{x+10} ^ {src}{x+15} ^ {src}{x+20};")
    for x in range(5):
        w.append(f"let {tag}d{x} = {tag}c{(x+4)%5} ^ {rot(f'{tag}c{(x+1)%5}', 1)};")
    for yp in range(5):
        for c in range(5):
            x = (3 * yp + c) % 5
            s = x + 5 * c
            w.append(f"let {tag}b{yp}_{c} = {rot(f'({src}{s} ^ {tag}d{x})', RHO[s])};")
        for x in range(5):
            k = x + 5 * yp
            e = f"{tag}b{yp}_{x} ^ (!{tag}b{yp}_{(x+1)%5} & {tag}b{yp}_{(x+2)%5})"
            w.append(f"let {dst}{k} = " + (f"{e} ^ {rc};" if k == 0 else f"{e};"))
out = []
for n in (1, 2, 4):
    w = ["#[inline(always)]", f"pub fn lane_rounds_{n}(s: &mut [[u64; 4]; 25], i: usize, rc: [u64; {n}]) {{"]
    for k in range(25):
        w.append(f"let a{k} = s[{k}][i];")
    for j in range(n):
        src = "a" if j == 0 else ("p" if j % 2 == 1 else "a")
        # ping-pong names: round j reads X, writes Y
        rn = f"r{j}_"
        srcn = "a" if j == 0 else f"q{j-1}_"
        dstn = f"q{j}_"
        rnd(w, srcn, dstn, f"rc[{j}]", rn)
    last = f"q{n-1}_"
    for k in range(25):
        w.append(f"s[{k}][i] = {last}{k};")
    w.append("}")
    out.append("\n".join(w))
open("src/lane.rs", "w").write("\n".join(out) + "\n")
