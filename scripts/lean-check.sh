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
# Best effort: a failed cache download only means the libraries are built from source; it cannot turn a failing check into a pass.
lake exe cache get >/dev/null 2>&1 || true
rc=0
timeout 3000 lake build "$@" 2>&1 | tee .lake/check-build.log || rc=$?
if [ "$rc" -ne 0 ]; then echo "LEAN CHECK FAIL: lake build exited $rc"; exit 1; fi
if grep -nE "(^|[^a-z])error:|declaration uses 'sorry'" .lake/check-build.log; then
  echo "LEAN CHECK FAIL: errors or sorry in the build log"; exit 1
fi
cd ..
# The cheap gates first: the cfg inventory of src/ and the theorem counts in the README.
python3 -I scripts/cfg_inventory.py
python3 -I scripts/check-readme-counts.py
scripts/check-axioms.sh
scripts/check-axioms.sh --list keccak4-theorems.txt --no-impl
scripts/check-axioms.sh --list fast-verify-theorems.txt --no-impl
# The whole environment, not only the dependencies of the names above: no axiom, opaque, sorry, admit, native_decide,
# implemented_by or extern anywhere in lean/Impl, lean/Spec, lean/Proofs. The self-test injects each into an Impl module.
scripts/check-no-decls.sh
scripts/check-no-decls.sh --self-test
# Declarations reachable from the verify entry points, by walking the resolved constants (not text).
scripts/reachable-defs.sh
# Feature independence (needs the extraction tools): the crate extracted a second time without the verify dispatch, compared with
# lean/Impl, and lean/Proofs/NoDispatch.lean (built above) is what that extraction generates. Only for a full run (no module
# arguments). scripts/ci.sh sets ML_DSA_FEATURE_INDEPENDENCE_DONE=1 for this script only after its own feature-independence step
# passed in the same invocation; without that flag this script runs the check itself. A run with module arguments does not run
# it at all, and says so in the last line: only a full run's "LEAN CHECK OK: " (nothing after the colon) is the done-gate.
if [ $# -eq 0 ]; then
  if [ -n "${ML_DSA_FEATURE_INDEPENDENCE_DONE:-}" ]; then
    echo "feature independence: already checked by scripts/ci.sh in this invocation"
  else
    scripts/check-feature-independence.sh
  fi
  echo "LEAN CHECK OK: $*"
else
  echo "LEAN CHECK OK (PARTIAL: the named modules only; the feature-independence gate was not run, so this is not the done-gate): $*"
fi
