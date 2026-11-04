#!/usr/bin/env bash
# Differential check of lean/Spec against VCVio's MLDSA.Concrete.  Run on a Linux machine with Lean installed:
#   bash scripts/diff-vcvio/setup-vcvio.sh   # once: clone + build the VCVio side
#   bash scripts/diff-vcvio/run.sh all       # generate, run both, compare
# Steps: gen | ours | theirs | compare | reference | logic | all.  Work directory: $DIFF_RUN (default $ML_DSA_SCRATCH/vcvio-diff/run),
# VCVio clone: $VCVIO_DIR (default $ML_DSA_SCRATCH/vcvio-diff/VCVio).  Vector sizes: DIFF_N_COEFF, DIFF_N_POLY, DIFF_N_CODEC.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
root="$(cd "$(dirname "$0")/../.." && pwd)"
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
run="${DIFF_RUN:-$SCRATCH/vcvio-diff/run}"
vcv="${VCVIO_DIR:-$SCRATCH/vcvio-diff/VCVio}"
step="${1:-all}"

gen() {
  rm -rf "$run/vec"
  python3 -I "$root/scripts/diff-vcvio/gen_vectors.py" --out "$run/vec" \
    --n-coeff "${DIFF_N_COEFF:-100000}" --n-poly "${DIFF_N_POLY:-2000}" --n-codec "${DIFF_N_CODEC:-1000}"
}

eval_all() { # exe outdir
  local exe="$1" out="$2" pids=() f
  rm -rf "$out"; mkdir -p "$out"
  for f in "$run"/vec/*.txt; do
    "$exe" "$f" "$out/$(basename "${f%.txt}").out" 2>"$out/$(basename "${f%.txt}").err" &
    pids+=($!)
  done
  local rc=0
  for p in "${pids[@]}"; do wait "$p" || { echo "eval job $p failed (exit $?)"; rc=1; }; done
  cat "$out"/*.err
  [ "$rc" -eq 0 ] || return 1
  if grep -l PANIC "$out"/*.err >/dev/null 2>&1; then echo "PANIC in $out"; return 1; fi
}

ours() {
  bash "$root/scripts/diff-vcvio/check-common.sh"
  (cd "$root/lean" && mkdir -p .lake && ([ -d .lake/packages ] || [ -z "${LEAN_PACKAGES_SEED:-}" ] || cp -a "$LEAN_PACKAGES_SEED" .lake/packages) \
    && (lake exe cache get >/dev/null 2>&1 || true) && lake build spec-diff-vcvio)
  eval_all "$root/lean/.lake/build/bin/spec-diff-vcvio" "$run/ours"
}

theirs() { eval_all "$vcv/.lake/build/bin/vcv-diff" "$run/theirs"; }

logic() { # structural NTT definitions of VCVio (DiffLogic.lean) against the loop kernels
  "$vcv/.lake/build/bin/vcv-logic" "$run/vec/ntt.txt" "$run/logic.out" "${DIFF_N_LOGIC:-300}"
  python3 -I "$root/scripts/diff-vcvio/compare_logic.py" "$run" "${DIFF_N_LOGIC:-300}"
}

reference() { python3 -I "$root/scripts/diff-vcvio/reference.py" "$run"; }

compare() { python3 -I "$root/scripts/diff-vcvio/compare.py" "$run"; }

mkdir -p "$run"
case "$step" in
  gen) gen ;;
  ours) ours ;;
  theirs) theirs ;;
  compare) compare ;;
  logic) logic ;;
  reference) reference ;;
  all) gen; ours; theirs; compare; reference; logic ;;
  *) echo "usage: run.sh gen|ours|theirs|compare|reference|logic|all"; exit 2 ;;
esac
