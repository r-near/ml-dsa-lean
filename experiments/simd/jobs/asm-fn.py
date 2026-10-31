#!/usr/bin/env python3
"""Print the instructions of one function from a rustc --emit asm file. Usage: asm-fn.py FILE.s SUBSTRING [maxlines]"""
import re, sys

path, pat = sys.argv[1], sys.argv[2]
maxl = int(sys.argv[3]) if len(sys.argv) > 3 else 400
on, n = False, 0
for line in open(path):
    m = re.match(r'^(_ZN[^:\s]+|_R[^:\s]+):\s*$', line)
    if m:
        on = pat in m.group(1)
        n = 0
        if on:
            print(m.group(1))
        continue
    if on and not line.startswith('\t.') or (on and re.match(r'^\.L', line)):
        if line.startswith('\t.cfi') or line.startswith('\t.p2align') or line.startswith('\t.size') or line.startswith('\t.type'):
            continue
        print(line.rstrip())
        n += 1
        if n >= maxl:
            break
