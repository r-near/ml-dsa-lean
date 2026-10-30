#!/usr/bin/env bash
# Fail unless every extracted def in lean/Impl/Funs.lean (and every theorem named in lean/headline-theorems.txt)
# depends only on propext, Classical.choice, Quot.sound. sorryAx or anything else is a failure.
# lean/headline-theorems.txt: one fully qualified name per line; `import Mod` lines add imports; `#` comments.
set -euo pipefail
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
F=.lake/axioms-check.lean
{
  echo 'import Impl.Funs'
  [ -f headline-theorems.txt ] && grep -E '^import ' headline-theorems.txt || true
  grep -oE '^(divergent )?def [A-Za-z0-9_.]+' Impl/Funs.lean | awk '{print "#print axioms Impl."$NF}'
  [ -f headline-theorems.txt ] && grep -vE '^(import |#|[[:space:]]*$)' headline-theorems.txt | awk '{print "#print axioms "$1}' || true
} > "$F"
echo "defs/theorems to check: $(grep -c '^#print' "$F")"
timeout 1800 lake env lean "$F" > .lake/axioms-check.out 2>&1 || true
python3 -I - "$F" .lake/axioms-check.out <<'PY'
import re, sys
want = [l.split()[-1] for l in open(sys.argv[1]) if l.startswith('#print')]
out = open(sys.argv[2]).read()
OK = {'propext', 'Classical.choice', 'Quot.sound'}
seen, bad = {}, []
for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out):
    seen[m.group(1)] = {a.strip() for a in (m.group(3) or '').split(',') if a.strip()}
for n in want:
    if n not in seen: bad.append(f'{n}: no axiom report')
    elif seen[n] - OK: bad.append(f'{n}: {sorted(seen[n] - OK)}')
errs = [l for l in out.splitlines() if 'error' in l.lower()]
used = sorted(set().union(*seen.values())) if seen else []
print(f'checked: {len(want)}  reported: {len(seen)}  axioms used: {used}')
if bad or errs or not want:
    print('AXIOM GATE FAIL'); [print('  ', b) for b in bad[:20]]; [print('  ', e) for e in errs[:10]]
    sys.exit(1)
print('AXIOM GATE OK')
PY
