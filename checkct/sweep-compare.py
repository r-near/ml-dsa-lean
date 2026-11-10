#!/usr/bin/env python3
"""Compares two `*.verdicts.tsv` files (checkct/verdicts-tsv.py) probe by probe: verdict, pending paths, visited instructions and
control-flow checks (passed/total). Prints the probes whose verdict differs, then those with the same verdict and different counts,
then the probes present in only one file, and a one-line total.

    python3 -I checkct/sweep-compare.py OLD.verdicts.tsv NEW.verdicts.tsv

Exit status 0 always: a difference is information (the tree changed), not an error of the script."""
import sys


def rows(path):
    d = {}
    for line in open(path, encoding="utf-8"):
        f = line.rstrip("\n").split("\t")
        if len(f) >= 5:
            d[f[0]] = f
    return d


old, new = rows(sys.argv[1]), rows(sys.argv[2])
vd = [p for p in sorted(old.keys() & new.keys()) if old[p][1] != new[p][1]]
cd = [p for p in sorted(old.keys() & new.keys()) if old[p][1] == new[p][1] and old[p][2:5] != new[p][2:5]]
for p in vd:
    print(f"VERDICT  {p}: {old[p][1]} -> {new[p][1]}   (old: {' '.join(old[p][2:5])}; new: {' '.join(new[p][2:5])})")
for p in cd:
    print(f"COUNTS   {p}: {new[p][1]}   old: {' '.join(old[p][2:5])}; new: {' '.join(new[p][2:5])}")
for p in sorted(old.keys() - new.keys()):
    print(f"ONLY-OLD {p}: {old[p][1]}")
for p in sorted(new.keys() - old.keys()):
    print(f"ONLY-NEW {p}: {new[p][1]}")
both = len(old.keys() & new.keys())
print(f"{both} probes in both: {both - len(vd) - len(cd)} identical in verdict and counts, {len(cd)} same verdict with different counts, "
      f"{len(vd)} different verdict; only in old {len(old.keys() - new.keys())}, only in new {len(new.keys() - old.keys())}")
