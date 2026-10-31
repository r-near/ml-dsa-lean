#!/usr/bin/env bash
# Fail unless every theorem named in xspec/headline-theorems.txt depends only on propext, Classical.choice,
# Quot.sound (no sorryAx, no other axiom).  Also fails on any `sorry`, `admit`, `native_decide`, `axiom`,
# `opaque`, `implemented_by`, `unsafe`, `partial`, `extern`, `macro`, `elab` or `syntax` in xspec/XSpec/ (the proof files; XSpecDiff is test-only and may use
# `implemented_by`).  Run on the build box:  rx run -- bash scripts/xspec/check-axioms.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"      # cd's to xspec/
if grep -nE '\b(sorry|admit|native_decide|opaque|implemented_by|unsafe|partial|macro|elab|syntax|extern)\b|^[[:space:]]*(private[[:space:]]+)?axiom\b' XSpec/*.lean \
    | grep -vE '^\S+:[0-9]+:\s*(--|/-)' | grep -vE '`(sorry|admit|native_decide|axiom|opaque|implemented_by|unsafe|partial|macro|elab|syntax|extern)`'; then
  echo "BANNED TOKEN in xspec/XSpec"; exit 1
fi
lake build XSpec 2>&1 | tail -5
F=.lake/axioms-check.lean
{
  grep -E '^import ' headline-theorems.txt
  grep -vE '^(import |#|[[:space:]]*$)' headline-theorems.txt | awk '{print "#print axioms "$1}'
} > "$F"
echo "theorems to check: $(grep -c '^#print' "$F")"
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
for n in want:
    print('  ', n, sorted(seen.get(n, ['?'])))
if bad or errs or not want:
    print('AXIOM GATE FAIL'); [print('  ', b) for b in bad[:20]]; [print('  ', e) for e in errs[:10]]
    sys.exit(1)
print('AXIOM GATE OK')
PY
