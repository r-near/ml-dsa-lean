#!/usr/bin/env python3
"""Breakdown of the folded stacks written by `prof`: share of samples per category.

Usage: categorize.py FOLDED_FILE...        (one list per file)
       categorize.py --table FOLDED_FILE...  (one row per file, one column per category)
       categorize.py --table-abs PROFLOG FOLDED_FILE...  (as --table, in microseconds per call: share x the us/call that `prof`
                                           printed in PROFLOG; names must be IMPL.SET.OP.folded, with ours-default/ours-avx2 as IMPL for the
                                           two builds of this crate, which PROFLOG lists as "ours" in two sections)
       categorize.py --top N FOLDED_FILE   (also the N most frequent leaf and inclusive function names)

A sample is attributed to the first (innermost) frame whose name matches a category rule; frames that match no
rule (small arithmetic helpers, inlined field operations) are skipped, so their time goes to the caller's
category. Rules are per implementation family and are listed in RULES.
"""
import collections
import re
import sys

# Categories, in the order of the summary table.
CATS = ["Keccak-f permutation", "sponge glue and rejection parsing", "NTT and NTT^-1",
        "pointwise, add, sub", "rounding, hints, norms", "encoding", "copies", "other"]
# Sponge byte loops and the rejection parse are one category: inlining moves time between them from one build to the
# next, so the profile cannot separate them reliably.
K, SP, NT, PW, RO, EN, CP = CATS[:7]
SA = SP

# (category, regex) in priority order; the first frame, scanning from the innermost, that matches any rule decides.
# Names are demangled Rust or C symbols. Helpers that match no rule (field arithmetic, Montgomery reductions) pass
# their time to the caller's category.
COMMON = [(CP, r"memcpy|memmove|memset|__memcpy|__memmove")]
OURS = COMMON + [
    (K, r"keccak_f1600"),
    (SP, r"keccak::Shake|Shake>::"),
    (SA, r"rej_ntt_poly|rej_bounded_poly|coeff_from|sample_in_ball|expand_a|expand_s\b|expand_mask"),
    (PW, r"multiply_ntt|matrix_vector_ntt|add_poly|sub_poly|scalar_vector_ntt_inverse|mac_row_pub"),
    (NT, r"ntt_layer|ntt_inverse_layer|ntt::ntt|ntt_inverse|ntt_vec|ntt_lazy_layer|shoup_lazy|reduce_lazy|ntt_pub"),
    (RO, r"rounding::"),
    (EN, r"encode::"),
]
LIBCRUX = COMMON + [
    (SP, r"absorb|squeeze|load_block|store_block|xof::|incremental"),
    (K, r"keccakf1600|keccak_f1600|libcrux_sha3::simd|libcrux_sha3::generic_keccak"),
    (SA, r"sample|rejection|samplex4|matrix_flat"),
    (PW, r"ntt_multiply_montgomery|pointwise|compute_w_approx|add_vectors|subtract|accumulate|montgomery_multiply\b"),
    (NT, r"simd::portable::ntt|simd::portable::invntt|ntt::ntt|invert_ntt"),
    (RO, r"decompose|use_hint|infinity_norm|power2round|make_hint|rounding|shift_left"),
    (EN, r"encoding|serialize|deserialize|pack"),
]
MLD = COMMON + [
    (K, r"keccakf1600_permute|keccak_f1600|keccakf1600x4_permute"),
    (SP, r"keccak_absorb|keccak_squeeze|shake|extract_bytes|xor_bytes|mld_H|mld_keccak|fips202"),
    (SA, r"rej_uniform|poly_uniform|poly_challenge|polymat_expand|matrix_expand|uniform"),
    (PW, r"pointwise|polyvec_matrix|poly_add|poly_sub|poly_caddq|poly_reduce|poly_shiftl"),
    (NT, r"ntt|montgomery_reduce|fqmul"),
    (RO, r"decompose|power2round|use_hint|make_hint|chknorm|highbits|lowbits"),
    (EN, r"pack|unpack|encode|decode"),
]
RUSTCRYPTO = COMMON + [
    (K, r"keccak_p"),
    (SP, r"sponge_cursor|ShakeState|ShakeReader|shake::"),
    (SA, r"sampling::"),
]


def rules_for(path):
    base = path.split("/")[-1]
    if base.startswith("ours"):
        return OURS
    if base.startswith("libcrux"):
        return LIBCRUX
    if base.startswith("rustcrypto"):
        return RUSTCRYPTO
    return MLD


def classify(stack, rules):
    for name in reversed(stack):  # innermost first
        for cat, rx in rules:
            if re.search(rx, name):
                return cat
    return "other"


def shares(path):
    rules = rules_for(path)
    cats = collections.Counter()
    total = 0
    for line in open(path):
        line = line.rstrip("\n")
        if not line:
            continue
        stack_s, count_s = line.rsplit(" ", 1)
        count = int(count_s)
        total += count
        cats[classify(stack_s.split(";"), rules)] += count
    return {c: 100.0 * cats[c] / total for c in CATS}, total


def table(paths):
    """Keccak-f, sponge glue and rejection parsing are summed: inlining moves time between them (the permutation is
    inlined into the squeeze functions of some builds), so only the sum is comparable between implementations.
    The first column after it is the permutation alone, reliable for this crate only."""
    cols = ["Keccak + sponge + parsing", "of which Keccak-f", "NTT and NTT^-1", "pointwise, add, sub",
            "rounding, hints, norms", "encoding", "copies, other"]
    print("| profile | " + " | ".join(cols) + " |")
    print("|---|" + "---|" * len(cols))
    for p in paths:
        sh, _ = shares(p)
        name = p.split("/")[-1].replace(".folded", "")
        row = [sh[CATS[0]] + sh[CATS[1]], sh[CATS[0]], sh[CATS[2]], sh[CATS[3]], sh[CATS[4]], sh[CATS[5]],
               sh[CATS[6]] + sh[CATS[7]]]
        print(f"| {name} | " + " | ".join(f"{x:.0f}%" for x in row) + " |")


def table_abs(log, paths):
    """Like table(), in microseconds per call. `prof` prints one PROF line per workload; the same implementation name
    ("ours") appears in the default and the avx2 section, so the first "ours" line of a workload is ours-default."""
    per_call = {}
    seen = collections.Counter()
    for line in open(log):
        f = line.rstrip("\n").split("\t")
        if f[0] != "PROF":
            continue
        _, st, imp, op, _, _, us_call, _ = f[:8]
        if imp == "ours":
            imp = ["ours-default", "ours-avx2"][seen[(st, op)]]
            seen[(st, op)] += 1
        per_call[(imp, st, op)] = float(us_call.split()[0])
    cols = ["Keccak + sponge + parsing", "of which Keccak-f", "NTT and NTT^-1", "pointwise, add, sub",
            "rounding, hints, norms", "encoding", "copies, other", "total"]
    print("| profile (us per call) | " + " | ".join(cols) + " |")
    print("|---|" + "---|" * len(cols))
    for p in paths:
        sh, _ = shares(p)
        name = p.split("/")[-1].replace(".folded", "")
        imp, st, op = name.split(".", 2)
        t = per_call[(imp, st, op)]
        row = [sh[CATS[0]] + sh[CATS[1]], sh[CATS[0]], sh[CATS[2]], sh[CATS[3]], sh[CATS[4]], sh[CATS[5]], sh[CATS[6]] + sh[CATS[7]]]
        print(f"| {name} | " + " | ".join(f"{x * t / 100:.1f}" for x in row) + f" | {t:.1f} |")


def main():
    args = sys.argv[1:]
    if args and args[0] == "--table-abs":
        table_abs(args[1], args[2:])
        return
    if args and args[0] == "--table":
        table(args[1:])
        return
    top = 0
    if args and args[0] == "--top":
        top = int(args[1])
        args = args[2:]
    for path in args:
        rules = rules_for(path)
        cats = collections.Counter()
        leaf = collections.Counter()
        incl = collections.Counter()
        total = 0
        for line in open(path):
            line = line.rstrip("\n")
            if not line:
                continue
            stack_s, count_s = line.rsplit(" ", 1)
            count = int(count_s)
            stack = stack_s.split(";")
            total += count
            cats[classify(stack, rules)] += count
            leaf[stack[-1]] += count
            for n in set(stack):
                incl[n] += count
        print(f"== {path}: {total} samples")
        for cat, n in cats.most_common():
            print(f"  {100.0 * n / total:5.1f}%  {cat}")
        if top:
            print("  -- leaf")
            for n, c in leaf.most_common(top):
                print(f"  {100.0 * c / total:5.1f}%  {n}")
            print("  -- inclusive")
            for n, c in incl.most_common(top):
                print(f"  {100.0 * c / total:5.1f}%  {n}")


if __name__ == "__main__":
    main()
