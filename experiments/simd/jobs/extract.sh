#!/usr/bin/env bash
# Job wrapper (runs on the box from the synced worktree root): extract one experiment crate and print the evidence.
# Usage: bash experiments/simd/jobs/extract.sh NAME CRATE_DIR ROOT...   (scratch: $HOME/rx/scratch/simd-NAME)
# Also collects the evidence files into $HOME/rx/scratch/simd-NAME/evidence/ for `rx pull`.
set -o pipefail
name=$1; crate=$2; shift 2
work="$HOME/rx/scratch/simd-$name"
bash experiments/simd/extract-mini.sh "$crate" "$work" "$@"
rc=$?
echo "=== extract-mini rc=$rc"
ev="$work/evidence"; rm -rf "$ev"; mkdir -p "$ev"
cp "$work"/lean/Impl/*.lean "$ev"/ 2>/dev/null
grep -E 'Error|Warn|error|panicked|unsupported|not supported|Unsupported' "$work/hax.log" > "$ev/charon-problems.txt" || true
grep -vE 'Applied prepasses|Translated|Post-processed|Imported|Generated' "$work/aeneas.log" > "$ev/aeneas.log" || true
# LLBC attribute record for every local item (what Charon kept of #[target_feature] etc.).
python3 - "$work/actual.llbc" > "$ev/llbc-attrs.txt" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for f in d['translated']['fun_decls']:
    if not f: continue
    m = f['item_meta']
    n = '::'.join(c['Ident'][0] if 'Ident' in c else '{impl}' if 'Impl' in c else str(list(c)[0]) for c in m['name'])
    if n.split('::')[0].startswith('core') or n.split('::')[0] == 'alloc':
        body = f.get('body')
        print('EXTERN', n, 'body=', 'None' if body in (None, 'Opaque') or (isinstance(body, dict) and 'Opaque' in body) else 'present')
        continue
    print(n, json.dumps(m.get('attr_info')), 'body=', 'None' if f.get('body') in (None, 'Opaque') else 'present')
PY
echo "=== aeneas problems"; cat "$ev/aeneas.log" | grep -vE '^\s*$|Compiler source|Source:|forward|backward' | head -60
echo "=== charon problems"; head -40 "$ev/charon-problems.txt"
echo "=== llbc attrs"; cat "$ev/llbc-attrs.txt"
echo "=== Funs.lean"; cat "$ev/Funs.lean"
echo "=== FunsExternal_Template.lean (axioms only)"; grep -E '^axiom|^def|^opaque' "$ev/FunsExternal_Template.lean"
exit $rc
