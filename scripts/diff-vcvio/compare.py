#!/usr/bin/env python3
"""Compare the outputs of the two evaluators line by line.

usage: compare.py RUN_DIR   (RUN_DIR has vec/*.txt, ours/*.out, theirs/*.out, and vec/hint.expected)

Prints a per-operation table (cases, mismatches) and, for each operation, the first mismatches with the full
input (long lines are truncated to --width characters in the console; the complete record of every mismatch is
written to RUN_DIR/mismatches.txt).  HBPX (HintBitPack with more than omega ones, outside the precondition of
Algorithm 20) is tallied separately.  HBU lines are also checked against the independent Python reference of
Algorithm 21 in vec/hint.expected.  Exit code 1 iff there is a mismatch outside HBPX.
"""
import argparse
import collections
import os
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--show", type=int, default=5, help="mismatches shown per operation")
    ap.add_argument("--width", type=int, default=400)
    a = ap.parse_args()
    vec = os.path.join(a.run, "vec")
    stats = collections.OrderedDict()  # key -> [cases, mismatches]
    shown = collections.Counter()
    full = open(os.path.join(a.run, "mismatches.txt"), "w")
    bad_outside = 0
    ref_stats = [0, 0, 0]  # HBU cases, ours != reference, theirs != reference
    expected = None
    exp_path = os.path.join(vec, "hint.expected")
    if os.path.exists(exp_path):
        expected = open(exp_path).read().split("\n")
    hbu_idx = 0
    for name in sorted(f for f in os.listdir(vec) if f.endswith(".txt")):
        inp = open(os.path.join(vec, name)).read().split("\n")
        if inp and inp[-1] == "":
            inp.pop()
        ours = open(os.path.join(a.run, "ours", name[:-4] + ".out")).read().split("\n")
        theirs = open(os.path.join(a.run, "theirs", name[:-4] + ".out")).read().split("\n")
        if ours and ours[-1] == "":
            ours.pop()
        if theirs and theirs[-1] == "":
            theirs.pop()
        if not (len(inp) == len(ours) == len(theirs)):
            print(f"{name}: line count mismatch: input {len(inp)}, ours {len(ours)}, theirs {len(theirs)}")
            bad_outside += 1
            continue
        for i, (l, o, t) in enumerate(zip(inp, ours, theirs), 1):
            f = l.split(" ")
            tag = f[0]
            key = tag
            if tag in ("DEC", "MH", "UH", "HBP", "HBPX", "HBU", "PKE", "PKD", "SKE", "SKD", "SGE", "SGD", "W1E"):
                key = f"{tag} {f[1]}"
            elif tag == "SWEEP":
                key = f"SWEEP {f[1]} {f[2]}"
            elif tag in ("SBP", "SBU"):
                key = f"{tag} b={f[1]}"
            elif tag in ("BP", "BU"):
                key = f"{tag} a={f[1]} b={f[2]}"
            st = stats.setdefault(key, [0, 0])
            st[0] += 1
            if tag == "HBU" and expected is not None:
                ref = expected[hbu_idx]
                hbu_idx += 1
                ref_stats[0] += 1
                ref_stats[1] += o != ref
                ref_stats[2] += t != ref
            if o != t:
                st[1] += 1
                if tag != "HBPX":
                    bad_outside += 1
                full.write(f"{name}:{i}: {key}\n  input : {l}\n  ours  : {o}\n  theirs: {t}\n")
                if shown[key] < a.show:
                    shown[key] += 1
                    cut = lambda s: s if len(s) <= a.width else s[: a.width] + f"... ({len(s)} chars)"
                    print(f"MISMATCH {name}:{i} {key}\n  input : {cut(l)}\n  ours  : {cut(o)}\n  theirs: {cut(t)}")
    full.close()
    print()
    print(f"{'operation':<24}{'cases':>10}{'mismatches':>12}")
    tot = [0, 0]
    for k, (n, m) in stats.items():
        print(f"{k:<24}{n:>10}{m:>12}")
        tot[0] += n
        tot[1] += m
    print(f"{'TOTAL':<24}{tot[0]:>10}{tot[1]:>12}")
    if expected is not None:
        print(f"HBU against the Python reference of Algorithm 21: {ref_stats[0]} cases, "
              f"ours differs in {ref_stats[1]}, theirs differs in {ref_stats[2]}")
    print(f"mismatch details: {os.path.join(a.run, 'mismatches.txt')}")
    return 1 if bad_outside else 0


if __name__ == "__main__":
    sys.exit(main())
