#!/usr/bin/env python3
"""Markdown table of an interleaved A/B (bench/ab.sh run with PAD set) from the per-pass TSV files it leaves.

Usage: ab_table.py DIR REF NAME... -- PAD...
  DIR   the AB_DIR of the run (files out-NAME-padPAD-PASS.tsv)
  REF   the binary the last columns compare with (one of the NAMEs)
  NAME  the binaries, in column order; PAD the paddings (bytes).
Prints, for each padding, parameter set and operation (one-shot verify, verifying_key, prepared-key verify), the median over the
passes of each binary's per-pass median in microseconds, then each non-reference binary over REF, and the largest absolute
difference. Also prints the min-to-max spread of a cell over the passes as a percentage of its median (largest over all cells).
"""
import statistics
import sys
from pathlib import Path

OPS = {("verify", "ours"): "one-shot", ("verifying-key", "ours+verifying-key"): "verifying_key",
       ("verify", "ours+prepared-vk"): "prepared-key verify"}


def load(d, name, pad):
    cells = {}
    for p in sorted(Path(d).glob(f"out-{name}-pad{pad}-*.tsv")):
        for line in open(p):
            f = line.rstrip("\n").split("\t")
            if f[0] == "ROW" and f[1] != "label" and (f[3], f[4]) in OPS:
                cells.setdefault((int(f[2]), OPS[(f[3], f[4])]), []).append(float(f[5]) / 1000)
    return cells


def main(argv):
    if "--" not in argv or len(argv) < 6:
        print(__doc__, file=sys.stderr)
        return 2
    cut = argv.index("--")
    d, ref, names, pads = argv[1], argv[2], argv[3:cut], argv[cut + 1:]
    others = [n for n in names if n != ref]
    print("| pad | set | op | " + " | ".join(names) + " | " + " | ".join(f"{n} / {ref}" for n in others) + " |")
    print("|---|---|---|" + "---|" * (len(names) + len(others)))
    worst = {n: 0.0 for n in others}
    spread = 0.0
    for pad in pads:
        data = {n: load(d, n, pad) for n in names}
        for key in sorted(data[ref], key=lambda k: (k[0], ["one-shot", "verifying_key", "prepared-key verify"].index(k[1]))):
            meds = {n: statistics.median(data[n][key]) for n in names}
            for n in names:
                v = data[n][key]
                spread = max(spread, (max(v) - min(v)) / meds[n])
            ratios = []
            for n in others:
                r = meds[n] / meds[ref] - 1
                worst[n] = max(worst[n], abs(r))
                ratios.append(f"{r * 100:+.1f}%")
            print(f"| {pad} | {key[0]} | {key[1]} | " + " | ".join(f"{meds[n]:.2f}" for n in names) + " | " + " | ".join(ratios) + " |")
    print()
    print("largest |difference| against " + ref + ": " + ", ".join(f"{n} {w * 100:.2f}%" for n, w in worst.items())
          + f"; largest min-to-max spread of a cell over the passes: {spread * 100:.1f}% of its median")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
