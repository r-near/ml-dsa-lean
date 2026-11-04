#!/usr/bin/env bash
# Compiled differential between lean/Spec (vendored as `Spec`) and ocaml-pq.  Run on Linux:
#   bash scripts/xspec/run-diff.sh all
# Steps: gen | build | ours | theirs | compare | all.  Work directory: $DIFF_RUN (default $HOME/xspec-work/run).
# Sizes: DIFF_N_COEFF, DIFF_N_POLY, DIFF_N_CODEC, DIFF_N_SAMPLER, DIFF_N_TOP, DIFF_N_SIGN.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
root="$XS_ROOT"
run="${DIFF_RUN:-$XS_WORK/run}"
step="${1:-all}"
shard="${DIFF_SHARD:-12}"   # lines per process for the slow top-level and sampler files

gen() {
  rm -rf "$run/vec"
  python3 -I "$root/scripts/xspec/gen_vectors.py" --out "$run/vec" \
    --n-coeff "${DIFF_N_COEFF:-100000}" --n-poly "${DIFF_N_POLY:-2000}" --n-codec "${DIFF_N_CODEC:-1000}" \
    --n-sampler "${DIFF_N_SAMPLER:-300}" --n-top "${DIFF_N_TOP:-100}" --n-sign "${DIFF_N_SIGN:-6}"
}

build() { lake build xspec-diff 2>&1 | tail -40; }

recat() { # concatenate the shard outputs (out.NNNNN, not out.NNNNN.err) in order
  local d
  for d in "$1"/*.parts; do
    [ -d "$d" ] || continue
    cat "$d"/out.[0-9][0-9][0-9][0-9][0-9] > "$1/$(basename "${d%.parts}").out" 2>/dev/null || true
  done
}

eval_side() { # side outdir
  local side="$1" out="$2" exe="$root/xspec/.lake/build/bin/xspec-diff" f b
  local jobs=()
  if [ -z "${DIFF_ONLY:-}" ]; then rm -rf "$out"; fi   # DIFF_ONLY="a b": re-evaluate only those files, keep the rest
  mkdir -p "$out"
  for f in "$run"/vec/*.txt; do
    b="$(basename "${f%.txt}")"
    if [ -n "${DIFF_ONLY:-}" ]; then
      case " $DIFF_ONLY " in *" $b "*) rm -rf "$out/$b.out" "$out/$b.parts" ;; *) continue ;; esac
    fi
    case "$b" in
      keygen|sign|verify|expand|samplers|ntt|bitpack|codecs)
        mkdir -p "$out/$b.parts"
        split -l "$shard" -d -a 5 "$f" "$out/$b.parts/in."
        for p in "$out/$b.parts"/in.*; do jobs+=("$p"); done ;;
      *) jobs+=("$f") ;;
    esac
  done
  printf '%s\n' "${jobs[@]}" | xargs -P "${DIFF_JOBS:-40}" -I{} bash -c '
    p="{}"; case "$p" in *.parts/in.*) o="${p/in./out.}" ;; *) o="'"$out"'/$(basename "${p%.txt}").out" ;; esac
    "'"$exe"'" '"$side"' "$p" "$o" 2>"$o.err" || echo "FAILED $p" >&2'
  recat "$out"
  cat "$out"/*.err "$out"/*.parts/*.err 2>/dev/null | sort | uniq -c | sort -rn | head -5
  if grep -lE "PANIC|panic" "$out"/*.err "$out"/*.parts/*.err >/dev/null 2>&1; then echo "PANIC in $out"; return 1; fi
}

mkdir -p "$run"
case "$step" in
  gen) gen ;;
  build) build ;;
  ours) eval_side ours "$run/ours" ;;
  theirs) eval_side theirs "$run/theirs" ;;
  recat) recat "$run/ours"; recat "$run/theirs" ;;
  compare) python3 -I "$root/scripts/xspec/compare.py" "$run" ;;
  all) gen; build; eval_side ours "$run/ours"; eval_side theirs "$run/theirs"; python3 -I "$root/scripts/xspec/compare.py" "$run" ;;
  *) echo "usage: run-diff.sh gen|build|ours|theirs|recat|compare|all"; exit 2 ;;
esac
