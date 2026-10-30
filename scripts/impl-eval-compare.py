#!/usr/bin/env python3
"""Compare the outputs of the Lean (extracted) and Rust (native) evaluations; see scripts/impl-eval.sh.

Usage: python3 -I scripts/impl-eval-compare.py LEAN_DIR RS_DIR
Each directory holds inputs.txt, outputs.txt and expected.txt. Exit status 0 iff the inputs are identical, every
line agrees, and every independent expected value (NIST ACVP) matches both sides.
"""
import hashlib
import sys
from collections import OrderedDict
from pathlib import Path


def lines(p):
    return Path(p).read_text().split("\n")[:-1]


def family(line):
    return line.split(" ", 1)[0]


def short(s, n=160):
    return s if len(s) <= n else s[:n] + f"... ({len(s)} chars)"


def first_diff(a, b):
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    return min(len(a), len(b))


def main():
    ld, rd = Path(sys.argv[1]), Path(sys.argv[2])
    ok = True
    hl = hashlib.sha256((ld / "inputs.txt").read_bytes()).hexdigest()
    hr = hashlib.sha256((rd / "inputs.txt").read_bytes()).hexdigest()
    print(f"inputs sha256 lean {hl[:16]} rust {hr[:16]}: {'identical' if hl == hr else 'DIFFERENT'}")
    ok &= hl == hr
    ins, lo, ro, ex = lines(ld / "inputs.txt"), lines(ld / "outputs.txt"), lines(rd / "outputs.txt"), lines(ld / "expected.txt")
    if not (len(ins) == len(lo) == len(ro) == len(ex)):
        print(f"LINE COUNT MISMATCH inputs {len(ins)} lean {len(lo)} rust {len(ro)} expected {len(ex)}")
        sys.exit(1)
    fam = OrderedDict()
    mism = []
    for i, line in enumerate(ins):
        f = family(line)
        s = fam.setdefault(f, dict(n=0, agree=0, lean_fail=0, rs_fail=0, badin=0, none=0, exp_n=0, exp_lean=0, exp_rs=0))
        s["n"] += 1
        a, b = lo[i], ro[i]
        if a == b:
            s["agree"] += 1
        else:
            mism.append(i)
        s["lean_fail"] += a in ("FAIL", "DIV")
        s["rs_fail"] += b == "FAIL"
        s["badin"] += a == "BADIN" or b == "BADIN"
        s["none"] += a == "N"
        if ex[i] != "?":
            s["exp_n"] += 1
            s["exp_lean"] += a == ex[i]
            s["exp_rs"] += b == ex[i]
    print(f"{'op':<24}{'cases':>8}{'agree':>8}{'lean-fail':>10}{'rs-panic':>9}{'none':>7}{'badin':>6}   ACVP(lean/rust/total)")
    for f, s in fam.items():
        e = f"{s['exp_lean']}/{s['exp_rs']}/{s['exp_n']}" if s["exp_n"] else ""
        print(f"{f:<24}{s['n']:>8}{s['agree']:>8}{s['lean_fail']:>10}{s['rs_fail']:>9}{s['none']:>7}{s['badin']:>6}   {e}")
    tot = sum(s["n"] for s in fam.values())
    agree = sum(s["agree"] for s in fam.values())
    en = sum(s["exp_n"] for s in fam.values())
    el = sum(s["exp_lean"] for s in fam.values())
    er = sum(s["exp_rs"] for s in fam.values())
    print(f"\nTOTAL {tot} cases, {agree} agree, {tot - agree} differ; ACVP expected values: lean {el}/{en}, rust {er}/{en}")
    print(f"badin lines: {sum(s['badin'] for s in fam.values())}; lean fail/div: {sum(s['lean_fail'] for s in fam.values())}; rust panics: {sum(s['rs_fail'] for s in fam.values())}")
    seen = {}
    for i in mism:
        f = family(ins[i])
        seen[f] = seen.get(f, 0) + 1
        if seen[f] <= 3:
            d = first_diff(lo[i], ro[i])
            print(f"\nMISMATCH line {i + 1} op {f} (first difference at char {d})\n  input: {short(ins[i])}\n  lean:  {short(lo[i])}\n  rust:  {short(ro[i])}")
    ok &= not mism
    ok &= en == el == er
    print("\nRESULT:", "ALL AGREE" if ok else "DISAGREEMENT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
