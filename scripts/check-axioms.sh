#!/usr/bin/env bash
# Fail unless every extracted def in lean/Impl/Funs.lean (and every theorem named in lean/headline-theorems.txt)
# depends only on propext, Classical.choice, Quot.sound. sorryAx or anything else is a failure.
# lean/headline-theorems.txt: one fully qualified name per line; `import Mod` lines add imports; `#` comments.
# Usage: scripts/check-axioms.sh [--list FILE] [--no-impl]
#   --list FILE  read the names from FILE (relative to lean/) instead of headline-theorems.txt
#   --no-impl    skip the extracted defs of Impl/Funs.lean (scripts/witness-check.sh uses both flags)
set -euo pipefail
LIST=headline-theorems.txt
IMPL=1
while [ $# -gt 0 ]; do
  case "$1" in
    --list) [ $# -ge 2 ] || { echo "usage: $0 [--list FILE] [--no-impl]" >&2; exit 2; }; LIST="$2"; shift 2 ;;
    --no-impl) IMPL=0; shift ;;
    *) echo "usage: $0 [--list FILE] [--no-impl]" >&2; exit 2 ;;
  esac
done
cd "$(dirname "$0")/../lean"
if [ "$LIST" != headline-theorems.txt ] && [ ! -f "$LIST" ]; then echo "AXIOM GATE FAIL: list file $LIST not found" >&2; exit 1; fi
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
TAG=$(basename "$LIST" .txt)
F=.lake/axioms-check-$TAG.lean
OUT=.lake/axioms-check-$TAG.out
{
  [ "$IMPL" = 1 ] && echo 'import Impl.Funs' || true
  [ -f "$LIST" ] && grep -E '^import ' "$LIST" || true
  [ "$IMPL" = 1 ] && grep -oE '^(@\[[^]]*\] *)?(divergent )?def [A-Za-z0-9_.]+' Impl/Funs.lean | awk '{print "#print axioms Impl."$NF}' || true
  [ -f "$LIST" ] && grep -vE '^(import |#|[[:space:]]*$)' "$LIST" | awk '{print "#print axioms "$1}' || true
} > "$F"
echo "defs/theorems to check: $(grep -c '^#print' "$F")"
timeout 1800 lake env lean "$F" > "$OUT" 2>&1 || true
python3 -I - "$F" "$OUT" <<'PY'
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
