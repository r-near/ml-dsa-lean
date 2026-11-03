#!/usr/bin/env bash
# Done-gate for the non-vacuity witnesses (run on the build box): build the TopWitness modules, which the default
# build roots (lean/Proofs.lean) do not import, fail on any build error or `sorry`, then run the axiom check on the
# names in lean/witness-theorems.txt. Exit 0 only if all three pass and the default roots stay free of the witnesses.
# Usage: scripts/witness-check.sh [Module ...]   (default: Proofs.TopWitness)
# The kernel evaluations are the cost. Measured cold (2026-11-03): Proofs.TopWitnessA (16 ExpandA entries, about 10 GB
# and 40 s each) built in about 700 s; ExpandS about 5 min and up to about 38 GB; about 12 min wall and about 19 GB
# peak per process in total. `lake` runs the independent modules in parallel.
set -euo pipefail
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
if grep -nE '^import +Proofs\.TopWitness' Proofs.lean; then
  echo "WITNESS CHECK FAIL: Proofs.lean imports a TopWitness module (it must stay out of the default build)"; exit 1
fi
mkdir -p .lake
SEED="${LEAN_PACKAGES_SEED:-$HOME/lean-survey/.lake/packages}"
if [ ! -d .lake/packages ] && [ -d "$SEED" ]; then cp -a "$SEED" .lake/packages; fi
lake exe cache get >/dev/null 2>&1 || true
[ $# -gt 0 ] || set -- Proofs.TopWitness
rc=0
timeout 3000 lake build "$@" 2>&1 | tee .lake/witness-build.log || rc=$?
if [ "$rc" -ne 0 ]; then echo "WITNESS CHECK FAIL: lake build exited $rc"; exit 1; fi
if grep -nE "(^|[^a-z])error:|declaration uses 'sorry'" .lake/witness-build.log; then
  echo "WITNESS CHECK FAIL: errors or sorry in the build log"; exit 1
fi
cd ..
scripts/check-axioms.sh --list witness-theorems.txt --no-impl
echo "WITNESS CHECK OK: $*"
