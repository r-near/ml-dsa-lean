#!/usr/bin/env bash
# One entry point (run on the Linux build box): extract -> lake build -> axiom check. Non-zero exit on any gate failure.
# Usage: scripts/extract-and-build.sh [extract.py options, e.g. --src DIR]
# Prerequisite (once per box): scripts/setup-tools.sh
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
t0=$(date +%s)
echo "== extract"
python3 scripts/extract.py "$@"
t1=$(date +%s)
echo "== lake build"
cd lean
[ -f lake-manifest.json ] || { echo "lean/lake-manifest.json missing: run 'lake update' in lean/ and commit it" >&2; exit 1; }
# Optional warm cache seed (same aeneas rev); the project stays self-contained without it.
SEED="${LEAN_PACKAGES_SEED:-$HOME/lean-survey/.lake/packages}"
if [ ! -d .lake/packages ] && [ -d "$SEED" ]; then
  echo "seeding .lake/packages from $SEED"; mkdir -p .lake && cp -a "$SEED" .lake/packages
fi
lake exe cache get 2>&1 | tail -3 || echo "warning: lake exe cache get failed (Mathlib may build from source)" >&2
timeout 3000 lake build 2>timeout 3000 lake build Impl 2>&11 | tee .lake/build.log | tail -20
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "LAKE BUILD FAILED" >&2; exit 1; }
cd ..
t2=$(date +%s)
echo "== axioms"
scripts/check-axioms.sh | tee lean/.lake/axioms-summary.txt
t3=$(date +%s)
python3 -I - <<PY
import json
p = 'lean/Impl/extract-report.json'
r = json.load(open(p))
r['lake_build'] = 'ok'
r['axiom_gate'] = 'ok'
r['axioms_summary'] = [l for l in open('lean/.lake/axioms-summary.txt').read().splitlines() if l.startswith('checked')]
json.dump(r, open(p, 'w'), indent=1); open(p, 'a').write('\n')
PY
echo "PIPELINE OK  extract=$((t1-t0))s lake=$((t2-t1))s axioms=$((t3-t2))s"
