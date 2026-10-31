#!/usr/bin/env python3
"""Static control-flow and addressing scan of the AVX2 copies of the NTT bodies (BINSEC cannot lift VEX code).

usage: scan-avx2.py DISASSEMBLY   (llvm-objdump -d --no-show-raw-insn of a driver built by checkct/select-ntt.sh)

For every function whose symbol contains "_avx2" it reports
  * the instruction count and the mnemonic histogram of the control-flow, division and gather instructions,
  * every conditional jump with the flag-setting instruction before it,
  * every memory operand that has an index register (base+index*scale), grouped by index register.
What a reviewer checks in the output: no div/idiv, no gather, no indirect jump or call, every conditional jump is a
loop back-edge on a counter compared with an immediate, and index registers are only loop counters (never loaded from
the polynomial). This is a review aid, not a proof.
"""
import re
import sys
from collections import Counter, defaultdict

text = open(sys.argv[1]).read().splitlines()
funcs = {}
cur = None
for line in text:
    m = re.match(r"^[0-9a-f]+ <(.+)>:$", line)
    if m:
        cur = m.group(1)
        funcs[cur] = []
        continue
    m = re.match(r"^\s*([0-9a-f]+):\s+(.*)$", line)
    if m and cur:
        funcs[cur].append((m.group(1), m.group(2).strip()))

FLAGSET = re.compile(r"^(cmp|test|sub|add|dec|inc|and|or|xor|neg|shl|shr|sar)")
for name, ins in funcs.items():
    if "_avx2" not in name:
        continue
    print("=" * 100)
    print(name, "-", len(ins), "instructions")
    mn = Counter(i[1].split()[0] for i in ins)
    jcc = [(k, i) for k, i in enumerate(ins) if re.match(r"^j(?!mp)\w+\b", i[1])]
    print("  jcc:", len(jcc), " jmp:", mn.get("jmp", 0), " call:", mn.get("call", 0), " ret:", mn.get("retq", 0) + mn.get("ret", 0))
    bad = [i for i in ins if re.match(r"^(div|idiv|vpgather|vgather|vpscatter)", i[1])]
    ind = [i for i in ins if re.match(r"^(jmp|call)q?\s+\*", i[1])]
    print("  div/idiv/gather/scatter:", len(bad), " indirect jmp/call:", len(ind))
    for a, b in ind:
        print(f"    indirect: {a}: {b}")
    seen = Counter()
    for k, i in jcc:
        prev = next(((a, b) for a, b in reversed(ins[max(0, k - 6):k]) if FLAGSET.match(b)), None)
        key = (i[1].split()[0], prev[1] if prev else "?")
        seen[key] += 1
    print("  conditional jumps (count, jcc, flag-setting instruction before it):")
    for (j, p), c in sorted(seen.items(), key=lambda x: -x[1]):
        print(f"    {c:4d}  {j:6s} <- {p}")
    idx = defaultdict(int)
    for _, b in ins:
        for m in re.finditer(r"\(%(\w+),%(\w+)(?:,(\d))?\)", b):
            idx[m.group(2)] += 1
    print("  index registers in base+index*scale operands (register: uses):", dict(idx))
