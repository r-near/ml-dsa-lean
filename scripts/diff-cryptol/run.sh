#!/usr/bin/env bash
# Differential check of lean/Spec against GaloisInc/cryptol-specs (ML-DSA).  Run on a Linux machine with Lean installed:
#   bash scripts/diff-cryptol/setup.sh        # once: Cryptol and cryptol-specs, pinned
#   bash scripts/diff-cryptol/run.sh all      # generate, run both sides, compare
# Steps: stage0 | stage1 | stage2 | compare | all.  `all` is stage0, then stage1 (signing cases, which need the keys our side
# generated), then stage2 (verification cases, which need our signatures), then compare.  Each stage is: generate vectors,
# run our side (`spec-diff-cryptol`), run the Cryptol side in parallel (`run_theirs.py`).
# Work directory: $DIFF_RUN (default $ML_DSA_SCRATCH/cryptol-diff/run); Cryptol tools: $CRYPTOL_TOOLS (see setup.sh).
# Knobs: DIFF_SCALE (multiplies the random-case counts, default 1), DIFF_JOBS (parallel Cryptol processes, default 40),
# DIFF_SEED, DIFF_OURS_EXE (a prebuilt spec-diff-cryptol, used instead of building one: see inject.sh).
# Outputs are bound to the vector file and program that produced them (`<name>.stamp`, see stamp.py): changing DIFF_SEED, the
# generator or a side recomputes the affected outputs, and `compare.py` refuses an output whose stamp does not match.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
root="$(cd "$(dirname "$0")/../.." && pwd)"
here="$root/scripts/diff-cryptol"
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
run="${DIFF_RUN:-$SCRATCH/cryptol-diff/run}"
step="${1:-all}"
seed="${DIFF_SEED:-204}"
# shellcheck source=lib.sh
. "$here/lib.sh"

build_ours() {
  if [ -n "${DIFF_OURS_EXE:-}" ]; then ours_exe="$DIFF_OURS_EXE"; return; fi
  (cd "$root/lean" && mkdir -p .lake && ([ -d .lake/packages ] || [ -z "${LEAN_PACKAGES_SEED:-}" ] || cp -a "$LEAN_PACKAGES_SEED" .lake/packages) \
    && (lake exe cache get >/dev/null 2>&1 || true) && lake build spec-diff-cryptol)
  ours_exe="$root/lean/.lake/build/bin/spec-diff-cryptol"
}

ours() { # our side on every vector file whose output is missing or not bound to the current vector file and build
  build_ours
  ours_run "$run/vec" "$run/ours" "$ours_exe" "$run/ours/stderr.log" || return 1
  if grep -l ERR "$run"/ours/*.out >/dev/null 2>&1; then echo "ERR lines in our output:"; grep -c ERR "$run"/ours/*.out | grep -v ':0'; return 1; fi
}

theirs() { python3 -I "$here/run_theirs.py" "$run" --jobs "${DIFF_JOBS:-40}"; }

gen() { python3 -I "$here/gen_vectors.py" --stage "$1" --out "$run" --seed "$seed"; }

stage() { gen "$1"; ours; theirs; }

mkdir -p "$run"
case "$step" in
  stage0) rm -rf "$run/vec" "$run/ours" "$run/theirs"; stage 0 ;;
  stage1) stage 1 ;;
  stage2) stage 2 ;;
  compare) python3 -I "$here/compare.py" "$run" ;;
  all)
    rm -rf "$run/vec" "$run/ours" "$run/theirs"
    start=$(date +%s)
    stage 0; stage 1; stage 2
    echo "total $(( $(date +%s) - start )) s"
    python3 -I "$here/compare.py" "$run" ;;
  *) echo "usage: run.sh stage0|stage1|stage2|compare|all"; exit 2 ;;
esac
