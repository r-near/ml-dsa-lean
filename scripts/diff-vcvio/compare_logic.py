#!/usr/bin/env python3
"""Compare vcv-logic's output (structural NTT / NTT^-1 definitions) with the loop kernels' output.
usage: compare_logic.py RUN_DIR N     (the N first NTT and N first INTT vectors of vec/ntt.txt)"""
import os
import sys

run, n = sys.argv[1], int(sys.argv[2])
inp = open(os.path.join(run, "vec", "ntt.txt")).read().split("\n")[:-1]
loop = open(os.path.join(run, "theirs", "ntt.out")).read().split("\n")[:-1]
ours = open(os.path.join(run, "ours", "ntt.out")).read().split("\n")[:-1]
logic = open(os.path.join(run, "logic.out")).read().split("\n")[:-1]
sel = []
for tag in ("NTT", "INTT"):
    sel += [i for i, l in enumerate(inp) if l.split(" ", 1)[0] == tag][:n]
assert len(sel) == len(logic), (len(sel), len(logic))
bad = 0
for i, lg in zip(sel, logic):
    if lg != loop[i]:
        bad += 1
        print(f"MISMATCH line {i + 1}: {inp[i][:200]}\n  structural: {lg[:200]}\n  loop kernel: {loop[i][:200]}")
    if ours[i] != lg:
        print(f"line {i + 1}: ours differs from structural")
print(f"structural vs loop kernel: {len(sel)} vectors, {bad} mismatches")
sys.exit(1 if bad else 0)
