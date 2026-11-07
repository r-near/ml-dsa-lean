#!/usr/bin/env bash
# Done-gate for Lean work (run on Linux): build the given modules (default: all default targets), fail on
# any build error or `sorry` warning, then run the axiom check. Exit 0 only if all three pass.
# Usage: scripts/lean-check.sh [Module ...]   e.g. scripts/lean-check.sh Proofs.SampleA
# The full build log is printed unfiltered; read its end with `tail -30 lean/.lake/check-build.log`.
set -euo pipefail
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
# LEAN_PACKAGES_SEED: optional directory of already built lake packages (same Aeneas rev) used to seed .lake/packages.
SEED="${LEAN_PACKAGES_SEED:-}"
if [ ! -d .lake/packages ] && [ -n "$SEED" ] && [ -d "$SEED" ]; then cp -a "$SEED" .lake/packages; fi
lake exe cache get >/dev/null 2>&1 || true
rc=0
timeout 3000 lake build "$@" 2>&1 | tee .lake/check-build.log || rc=$?
if [ "$rc" -ne 0 ]; then echo "LEAN CHECK FAIL: lake build exited $rc"; exit 1; fi
if grep -nE "(^|[^a-z])error:|declaration uses 'sorry'" .lake/check-build.log; then
  echo "LEAN CHECK FAIL: errors or sorry in the build log"; exit 1
fi
cd ..
scripts/check-axioms.sh
scripts/check-axioms.sh --list keccak4-theorems.txt --no-impl
scripts/check-axioms.sh --list fast-verify-theorems.txt --no-impl
echo "LEAN CHECK OK: $*"
