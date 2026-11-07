#!/usr/bin/env python3
"""Markdown tables from the TSV files that `bench` writes.

Usage: table.py headline FILE            one table per parameter set (microseconds; ratio to this crate in brackets)
       table.py variants FILE...         this crate, RustCrypto, libcrux and mldsa-native across build variants
       table.py repeat FILE FILE         medians of two runs of the same binary and their relative difference
       table.py spread FILE              relative spread (max - min over rounds) / median, per row
       table.py report DEF1 DEF2 AVX1 AVX2 V31 V32 [AWSLONG]
                                         the results-file tables: per parameter set, portable and AVX2 rows side by side, with
                                         ratios (this crate / fastest other). Each pair is two runs of the default build, of the
                                         `avx2`-feature build and of the x86-64-v3 build of `bench`; a cell is the mean of the
                                         two runs' medians. Competitors come from the default build, so RUSTFLAGS do not touch them.
"""
import collections
import sys

ORDER = ["ours", "ours+prepared-vk", "ours+prepared-sk", "rustcrypto", "rustcrypto+cached-sk", "rustcrypto+cached-vk", "libcrux-portable", "libcrux-avx2",
         "mldsa-native-portable", "mldsa-native-avx2", "aws-lc-rs", "aws-lc-rs+cached-sk", "aws-lc-rs+sk-export"]
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


COLS = [("keygen", "keygen", ["keygen"]), ("sign (det)", "sign-det", None), ("sign (hedged)", "sign-hedged", None),
        ("sign, prepared key (det)", "sign-det", "prep"), ("sign, prepared key (hedged)", "sign-hedged", "prep"), ("verify", "verify", None), ("verify, prepared key", "verify", "prep")]
PREP = {"ours": "ours+prepared-sk", "rustcrypto": "rustcrypto+cached-sk", "aws-lc-rs": "aws-lc-rs+cached-sk"}
PREPV = {"ours": "ours+prepared-vk", "rustcrypto": "rustcrypto+cached-vk"}


def report(args):
    runs = [load(a) for a in args[:6]]
    long_aws = load(args[6]) if len(args) > 6 else None

    def med(pair, st, op, imp):
        vals = [r[(st, op, imp)]["med"] for r in pair if (st, op, imp) in r]
        return sum(vals) / len(vals) if vals else None

    d, a, v = runs[0:2], runs[2:4], runs[4:6]

    def get(src, st, col, imp):
        _, op, kind = col
        if kind == "prep":
            imp = (PREP if op.startswith("sign") else PREPV).get(imp)
            if imp is None:
                return None
        return med(src, st, op, imp)

    # (label, source, implementation name in that source, class)
    rows = [("ours, default features", d, "ours", "portable"), ("RustCrypto ml-dsa a3690c4", d, "rustcrypto", "portable"),
            ("libcrux-ml-dsa 0.0.11 portable", d, "libcrux-portable", "portable"),
            ("mldsa-native v2.0.0 portable C", d, "mldsa-native-portable", "portable"),
            ("ours, `avx2` feature", a, "ours", "avx2"), ("ours, `-C target-cpu=x86-64-v3`", v, "ours", "avx2"),
            ("libcrux-ml-dsa 0.0.11 AVX2", d, "libcrux-avx2", "avx2"), ("mldsa-native v2.0.0 AVX2 C", d, "mldsa-native-avx2", "avx2"),
            ("aws-lc-rs 1.18.2 (runtime dispatch)", d, "aws-lc-rs", "avx2"),
            # compiled with the same `-C target-cpu=x86-64-v3` as the `ours` row above (the C libraries are not affected by RUSTFLAGS)
            ("libcrux-ml-dsa AVX2, `-C target-cpu=x86-64-v3`", v, "libcrux-avx2", "v3"),
            ("RustCrypto ml-dsa, `-C target-cpu=x86-64-v3`", v, "rustcrypto", "v3"),
            ("libcrux-ml-dsa portable, `-C target-cpu=x86-64-v3`", v, "libcrux-portable", "v3")]
    for st in (44, 65, 87):
        print(f"\n#### ML-DSA-{st} (microseconds, median of 15 rounds, mean of two runs)\n")
        print("| implementation | " + " | ".join(c[0] for c in COLS) + " |")
        print("|---|" + "---|" * len(COLS))
        vals = {}
        for label, src, imp, cls in rows:
            cells = []
            for col in COLS:
                x = get(src, st, col, imp)
                if col[0] == "keygen" and imp == "aws-lc-rs":
                    x = med(src, st, "keygen", "aws-lc-rs+sk-export")
                vals[(label, col[0])] = x
                cells.append("n/a" if x is None else us(x))
            print(f"| {label} | " + " | ".join(cells) + " |")
        print()
        port = [r[0] for r in rows if r[3] == "portable"][1:]
        avx = [r[0] for r in rows if r[3] == "avx2"][2:]
        v3 = [r[0] for r in rows if r[3] == "v3"]
        for ours_label, cls, others in (("ours, default features", "portable (default build)", port),
                                       ("ours, `avx2` feature", "AVX2 (default build)", avx),
                                       ("ours, `-C target-cpu=x86-64-v3`", "AVX2 (Rust ones built with x86-64-v3 too)", avx + v3[:1])):
            out = []
            for col in COLS:
                mine = vals[(ours_label, col[0])]
                cands = [(vals[(o, col[0])], o) for o in others if vals[(o, col[0])] is not None]
                if mine is None or not cands:
                    out.append("n/a")
                    continue
                best, who = min(cands)
                out.append(f"{mine / best:.2f}x ({who.split()[0]})")
            print(f"- {ours_label} / fastest other {cls}: " + "; ".join(f"{c[0]} {o}" for c, o in zip(COLS, out)))
    if long_aws:
        print("\naws-lc-rs hedged sign over longer rounds (1.5 s per round, same method):")
        for st in (44, 65, 87):
            print(f"- ML-DSA-{st}: sign {us(long_aws[(st, 'sign-hedged', 'aws-lc-rs')]['med'])}, "
                  f"cached key {us(long_aws[(st, 'sign-hedged', 'aws-lc-rs+cached-sk')]['med'])}")


if __name__ == "__main__":
    cmd, args = sys.argv[1], sys.argv[2:]
    {"headline": lambda: headline(args[0]), "variants": lambda: variants(args), "repeat": lambda: repeat(*args),
     "spread": lambda: spread(args[0]), "report": lambda: report(args)}[cmd]()
