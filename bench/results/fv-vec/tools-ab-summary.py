#!/usr/bin/env python3
"""Summarizes ab.txt (the ab.sh output of base = fast-verify and vec = this branch) as a table of us per call."""
import re, collections, sys
d = collections.defaultdict(dict)
for l in open(sys.argv[1]):
    m = re.match(r'(base|vec)-pad(\d+)\s+ML-DSA-(\d+) (\S+)\s+(\S+)\s+median\s+([\d.]+)', l)
    if m:
        who, p, st, op, imp, v = m.groups()
        d[(p, op, imp, st)][who] = float(v)
for p in ('0', '672', '2752'):
    print('pad', p)
    for op, imp, lab in (('verify', 'ours', 'one-shot verify'), ('verifying-key', 'ours+verifying-key', 'verifying_key'), ('verify', 'ours+prepared-vk', 'prepared verify')):
        row = []
        for st in ('44', '65', '87'):
            x = d[(p, op, imp, st)]
            row.append(f"{st}: {x['base']:6.2f} -> {x['vec']:6.2f} (x{x['vec'] / x['base']:.3f})")
        print(f"  {lab:<16}" + ' | '.join(row))
