#!/usr/bin/env bash
# Differential check of lean/Spec against VCVio's MLDSA.Concrete.  Run on the build box (never build Lean on the Mac):
#   rx submit vcv      -- 'set -o pipefail; bash scripts/diff-vcvio/setup-vcvio.sh'   # once: clone + build VCVio side
#   rx submit vcv-ours -- 'set -o pipefail; bash scripts/diff-vcvio/run.sh all'       # generate, run both, compare
# Steps: gen | ours | theirs | compare | reference | logic | all.  Work directory: $DIFF_RUN (default $HOME/rx/scratch/vcvio-diff/run),
# VCVio clone: $VCVIO_DIR (default $HOME/rx/scratch/vcvio-diff/VCVio).  Vector sizes: DIFF_N_COEFF, DIFF_N_POLY, DIFF_N_CODEC.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
root="$(cd "$(dirname "$0")/../.." && pwd)"
run="${DIFF_RUN:-$HOME/rx/scratch/vcvio-diff/run}"
vcv="${VCVIO_DIR:-$HOME/rx/scratch/vcvio-diff/VCVio}"
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
  for p in "${pids[@]}"; do wait "$p"; done
  cat "$out"/*.err
  if grep -l PANIC "$out"/*.err >/dev/null 2>&1; then echo "PANIC in $out"; return 1; fi
}

ours() {
  bash "$root/scripts/diff-vcvio/check-common.sh"
  (cd "$root/lean" && mkdir -p .lake && ([ -d .lake/packages ] || cp -a "${LEAN_PACKAGES_SEED:-$HOME/lean-survey/.lake/packages}" .lake/packages) \
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
