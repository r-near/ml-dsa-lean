#!/usr/bin/env python3
"""Compare the outputs of the two evaluators line by line.

usage: compare.py RUN_DIR   (RUN_DIR has vec/*.txt, ours/*.out, theirs/*.out, vec/*.expected)

Prints a per-operation table (cases, mismatches) and, for each operation, the first mismatches with the input
(long lines truncated to --width characters; every mismatch is written in full to RUN_DIR/mismatches.txt).
HBPX (HintBitPack with more than omega ones, outside the precondition of Algorithm 20) is tallied separately.
Lines of `vec/<file>.expected` that are not `?` (ACVP answers, and the Python reference of Algorithm 21 in
`hint.expected`) are third opinions: the table also counts, for each side, the lines on which it disagrees with
them.  Exit code 1 iff the two sides differ outside HBPX, or either differs from a third opinion.
"""
import argparse
import collections
import os
import sys

TWO = ("DEC", "MH", "UH", "HBP", "HBPX", "HBU", "PKE", "PKD", "SKE", "SKD", "SGE", "SGD", "W1E", "RBND", "SIB",
       "EXA", "EXS", "EXM", "KGI", "SGI", "SGN", "VRI", "VRF", "CHB")


def read(path):
    xs = open(path).read().split("\n")
    if xs and xs[-1] == "":
        xs.pop()
    return xs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--show", type=int, default=4)
    ap.add_argument("--width", type=int, default=300)
    a = ap.parse_args()
    vec = os.path.join(a.run, "vec")
    stats = collections.OrderedDict()  # key -> [cases, mismatches, ours!=expected, theirs!=expected, expected cases]
    shown = collections.Counter()
    full = open(os.path.join(a.run, "mismatches.txt"), "w")
    bad = 0
    skd_strict = 0
    for name in sorted(f for f in os.listdir(vec) if f.endswith(".txt")):
        base = name[:-4]
        inp = read(os.path.join(vec, name))
        ours = read(os.path.join(a.run, "ours", base + ".out"))
        theirs = read(os.path.join(a.run, "theirs", base + ".out"))
        ep = os.path.join(vec, base + ".expected")
        exp = read(ep) if os.path.exists(ep) else None
        if exp is not None and len(exp) != len(inp):
            # hint.expected (Algorithm 21 reference) has one answer per HBU line, in order
            hbu = [k for k, l in enumerate(inp) if l.startswith("HBU ")]
            assert len(hbu) == len(exp), f"{base}.expected does not align with the HBU lines"
            full_exp = ["?"] * len(inp)
            for k, e in zip(hbu, exp):
                full_exp[k] = e
            exp = full_exp
        if not (len(inp) == len(ours) == len(theirs)):
            print(f"{name}: line count mismatch: input {len(inp)}, ours {len(ours)}, theirs {len(theirs)}")
            bad += 1
            continue
        hbu = 0
        for i, (l, o, t) in enumerate(zip(inp, ours, theirs), 1):
            f = l.split(" ")
            tag = f[0]
            key = tag
            if tag in TWO:
                key = f"{tag} {f[1]}"
            elif tag == "SWEEP":
                key = f"SWEEP {f[1]} {f[2]}"
            elif tag in ("SBP", "SBU"):
                key = f"{tag} b={f[1]}"
            elif tag in ("BP", "BU"):
                key = f"{tag} a={f[1]} b={f[2]}"
            elif tag in ("SHK",):
                key = f"SHK {f[1]}"
            elif tag in ("RNTT",):
                key = "RNTT"
            st = stats.setdefault(key, [0, 0, 0, 0, 0])
            st[0] += 1
            e = exp[i - 1] if exp is not None else "?"
            if e != "?":
                st[4] += 1
                st[2] += o != e
                st[3] += t != e
                if o != e or t != e:
                    bad += 1
                    full.write(f"{name}:{i}: {key} DISAGREES WITH EXPECTED\n  input   : {l}\n  expected: {e}\n"
                               f"  ours    : {o}\n  theirs  : {t}\n")
            if o != t:
                st[1] += 1
                if tag == "SKD" and t == "none":
                    skd_strict += 1  # ocaml-pq rejects an out-of-range s1/s2/t0 coefficient; FIPS-literal Algorithm 25 does not
                elif tag != "HBPX":
                    bad += 1
                full.write(f"{name}:{i}: {key}\n  input : {l}\n  ours  : {o}\n  theirs: {t}\n")
                if shown[key] < a.show:
                    shown[key] += 1
                    cut = lambda s: s if len(s) <= a.width else s[: a.width] + f"... ({len(s)} chars)"
                    print(f"MISMATCH {name}:{i} {key}\n  input : {cut(l)}\n  ours  : {cut(o)}\n  theirs: {cut(t)}")
    full.close()
    print()
    print(f"{'operation':<22}{'cases':>10}{'ours!=theirs':>14}{'3rd-opinion':>13}{'ours!=3rd':>11}{'theirs!=3rd':>13}")
    tot = [0, 0]
    for k, (n, m, om, tm, ne) in stats.items():
        print(f"{k:<22}{n:>10}{m:>14}{ne:>13}{om:>11}{tm:>13}")
        tot[0] += n
        tot[1] += m
    print(f"{'TOTAL':<22}{tot[0]:>10}{tot[1]:>14}")
    print(f"SKD lines where ocaml-pq rejects (none) and ours decodes (counted above, not as failures): {skd_strict}")
    print(f"mismatch details: {os.path.join(a.run, 'mismatches.txt')}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
