#!/usr/bin/env python3
"""Compare the two sides of the Cryptol differential, line by line.

    compare.py RUN [--list-matches]

Reads RUN/vec/manifest.txt, RUN/vec/<name>.txt, RUN/ours/<name>.out and RUN/theirs/<name>.out.  Every line is
classified:
  match            identical canonical output
  deviation        a difference explained by a documented deviation of lean/Spec from the FIPS 204 pseudocode:
                   `erratum-alg3` (Verify with a context of more than 255 bytes is `false` here, `None` in Cryptol, which
                   has the pre-erratum `⊥`), or `fuel` (our sampler gave `none` because its
                   fuel ran out and Cryptol's unbounded loop gave a value)
  mismatch         anything else (a finding until classified by hand)
  harness-error    Cryptol printed no result for the line (`CRYPTOL-ERROR`), or the line counts differ
Writes RUN/report.txt, RUN/mismatches.txt (input line, ours, theirs; long fields cut) and prints the summary table.
Exit code 0 iff there is no mismatch and no harness error.
"""
import os
import re
import sys
from collections import defaultdict

run = sys.argv[1]
man = []
for ln in open(os.path.join(run, "vec", "manifest.txt")):
    f = ln.split()
    if f:
        man.append((f[0], int(f[1]), f[2] if len(f) > 2 else ""))


def cut(s, n=300):
    return s if len(s) <= n else s[:n] + f"...({len(s)} chars)"


stats = defaultdict(lambda: defaultdict(int))
mism, harness, devs = [], [], []
for name, _, expect in man:
    if expect == "oursonly":
        continue
    vp, op, tp = (os.path.join(run, d, name + e) for d, e in (("vec", ".txt"), ("ours", ".out"), ("theirs", ".out")))
    if not (os.path.exists(op) and os.path.exists(tp)):
        stats[name]["missing"] += 1
        harness.append((name, 0, "missing output file", "", ""))
        continue
    vec = [x for x in open(vp).read().split("\n") if x.strip()]
    ours = open(op).read().split("\n")[:-1]
    theirs = open(tp).read().split("\n")[:-1]
    if not (len(vec) == len(ours) == len(theirs)):
        stats[name]["harness"] += 1
        harness.append((name, 0, f"line counts differ: vec {len(vec)} ours {len(ours)} theirs {len(theirs)}", "", ""))
        continue
    for i, (v, a, b) in enumerate(zip(vec, ours, theirs)):
        tag = v.split(" ")[0]
        st = stats[name]
        if b.startswith("CRYPTOL-ERROR"):
            st["harness"] += 1
            harness.append((name, i, v, a, b))
        elif a == b:
            st["match"] += 1
        elif tag == "VER" and len(v.split(" ")[5]) > 510 and a == "false" and b == "none":
            st["deviation"] += 1
            devs.append((name, i, "erratum-alg3", v, a, b))
        elif a == "none" and tag in ("SIB", "RNTT", "RBP", "EXA", "EXS", "KG", "KGO", "KGT", "SGN", "SGI"):
            st["deviation"] += 1
            devs.append((name, i, "fuel", v, a, b))
        else:
            st["mismatch"] += 1
            mism.append((name, i, v, a, b))

tags = defaultdict(lambda: defaultdict(int))
for name, st in stats.items():
    key = re.sub(r"\d+$", "", name.rstrip("_0123456789")) or name
    sfx = re.search(r"(44|65|87)$", name)
    for k, v in st.items():
        tags[key][k] += v
        if sfx:
            tags[key][f"set{sfx.group(1)}"] += st.get("match", 0) + st.get("deviation", 0) + st.get("mismatch", 0)
out = []
out.append(f"{'component':<12}{'lines':>8}{'match':>8}{'deviation':>11}{'mismatch':>10}{'harness':>9}   per set (44/65/87)")
tot = defaultdict(int)
for key in sorted(tags):
    t = tags[key]
    n = t["match"] + t["deviation"] + t["mismatch"] + t["harness"]
    per = "/".join(str(t.get(f"set{s}", 0)) for s in (44, 65, 87))
    out.append(f"{key:<12}{n:>8}{t['match']:>8}{t['deviation']:>11}{t['mismatch']:>10}{t['harness']:>9}   {per}")
    for k in ("match", "deviation", "mismatch", "harness"):
        tot[k] += t[k]
out.append(f"{'TOTAL':<12}{sum(tot.values()):>8}{tot['match']:>8}{tot['deviation']:>11}{tot['mismatch']:>10}{tot['harness']:>9}")
text = "\n".join(out)
print(text)
with open(os.path.join(run, "report.txt"), "w") as fh:
    fh.write(text + "\n")
with open(os.path.join(run, "mismatches.txt"), "w") as fh:
    for m in mism:
        fh.write(f"MISMATCH {m[0]} line {m[1]}\n  in:     {cut(m[2])}\n  ours:   {cut(m[3])}\n  theirs: {cut(m[4])}\n")
    for h in harness:
        fh.write(f"HARNESS {h[0]} line {h[1]}\n  {cut(h[2])}\n  ours: {cut(h[3])}\n  theirs: {cut(h[4])}\n")
    for d in devs:
        fh.write(f"DEVIATION({d[2]}) {d[0]} line {d[1]}\n  in:     {cut(d[3])}\n  ours:   {cut(d[4])}\n  theirs: {cut(d[5])}\n")
att = []
for name, _, expect in man:
    p = os.path.join(run, "ours", name + ".out")
    if expect == "oursonly" and name.startswith("sga_") and os.path.exists(p):
        att += [int(x) for x in open(p).read().split() if x.isdigit()]
if att:
    msg = (f"signing cases: {len(att)}, attempts of Algorithm 7's loop (our side): min {min(att)}, mean {sum(att) / len(att):.2f}, "
           f"max {max(att)}; {sum(1 for x in att if x >= 2)} cases with at least 2 attempts (kappa > 0)")
    print(msg)
    with open(os.path.join(run, "report.txt"), "a") as fh:
        fh.write(msg + "\n")
print(f"mismatches: {len(mism)}, harness errors: {len(harness)}, deviations: {len(devs)} (details in {run}/mismatches.txt)")
for m in mism[:5]:
    print(f"MISMATCH {m[0]} line {m[1]}\n  in:     {cut(m[2], 200)}\n  ours:   {cut(m[3], 200)}\n  theirs: {cut(m[4], 200)}")
sys.exit(1 if (mism or harness) else 0)
