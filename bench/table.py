#!/usr/bin/env python3
"""Markdown tables from the TSV files that `bench` writes.

Usage: table.py headline FILE            one table per parameter set (microseconds; ratio to this crate in brackets)
       table.py variants FILE...         this crate, RustCrypto, libcrux and mldsa-native across build variants
       table.py repeat FILE FILE         medians of two runs of the same binary and their relative difference
       table.py spread FILE              relative spread (max - min over rounds) / median, per row
"""
import collections
import sys

ORDER = ["ours", "ours+prepared-vk", "ours+prepared-sk", "rustcrypto", "rustcrypto+cached-sk", "rustcrypto+cached-vk", "libcrux-portable", "libcrux-avx2",
         "mldsa-native-portable", "mldsa-native-avx2"]
OPS = ["keygen", "sign-det", "sign-hedged", "verify"]


def load(path):
    rows = {}
    for line in open(path):
        if not line.startswith("ROW\t") or line.startswith("ROW\tlabel"):
            continue
        f = line.rstrip("\n").split("\t")
        label, st, op, imp = f[1], int(f[2]), f[3], f[4]
        med, mean, mn, mx, p10, p50, p90, p99 = (float(x) for x in f[5:13])
        rows[(st, op, imp)] = dict(label=label, med=med, mean=mean, min=mn, max=mx, p10=p10, p50=p50, p90=p90, p99=p99)
    return rows


def us(x):
    return f"{x / 1000:.1f}" if x < 1e6 else f"{x / 1000:.0f}"


def headline(path):
    r = load(path)
    for st in (44, 65, 87):
        print(f"\nML-DSA-{st} (median per call, microseconds; in brackets: time relative to this crate)\n")
        print("| implementation | keygen | sign (deterministic) | sign (hedged) | verify |")
        print("|---|---|---|---|---|")
        for imp in ORDER:
            cells = []
            for op in OPS:
                v = r.get((st, op, imp))
                o = r.get((st, op, "ours"))
                if v is None:
                    cells.append("n/a")
                else:
                    cells.append(f"{us(v['med'])} ({v['med'] / o['med']:.2f}x)")
            if all(c == "n/a" for c in cells):
                continue
            print(f"| {imp} | " + " | ".join(cells) + " |")


def variants(paths):
    data = {p.split("/")[-1].split(".")[0]: load(p) for p in paths}
    names = list(data)
    for imp in ["ours", "rustcrypto", "libcrux-portable", "libcrux-avx2", "mldsa-native-portable", "mldsa-native-avx2"]:
        print(f"\n{imp} (median microseconds)\n")
        print("| set | op | " + " | ".join(names) + " |")
        print("|---|---|" + "---|" * len(names))
        for st in (44, 65, 87):
            for op in OPS:
                vals = [data[n].get((st, op, imp)) for n in names]
                if all(v is None for v in vals):
                    continue
                print(f"| {st} | {op} | " + " | ".join("n/a" if v is None else us(v["med"]) for v in vals) + " |")


def repeat(a, b):
    ra, rb = load(a), load(b)
    print("| set | op | impl | run A | run B | B vs A |")
    print("|---|---|---|---|---|---|")
    worst = 0
    for k in sorted(ra):
        if k in rb:
            d = rb[k]["med"] / ra[k]["med"] - 1
            worst = max(worst, abs(d))
            print(f"| {k[0]} | {k[1]} | {k[2]} | {us(ra[k]['med'])} | {us(rb[k]['med'])} | {100 * d:+.1f}% |")
    print(f"\nlargest difference: {100 * worst:.1f}%")


def spread(path):
    r = load(path)
    rel = [(100 * (v["max"] - v["min"]) / v["med"], k) for k, v in r.items()]
    rel.sort(reverse=True)
    print("largest (max-min)/median over rounds:")
    for s, k in rel[:12]:
        print(f"  {s:5.1f}%  {k}")
    print(f"median over all rows: {sorted(s for s, _ in rel)[len(rel) // 2]:.2f}%")


if __name__ == "__main__":
    cmd, args = sys.argv[1], sys.argv[2:]
    {"headline": lambda: headline(args[0]), "variants": lambda: variants(args), "repeat": lambda: repeat(*args),
     "spread": lambda: spread(args[0])}[cmd]()
