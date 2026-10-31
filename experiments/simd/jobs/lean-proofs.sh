#!/usr/bin/env bash
# Compile a proof file from experiments/simd/lean/ against the extraction in $HOME/rx/scratch/NAME/lean (Impl.*).
# Usage: bash experiments/simd/jobs/lean-proofs.sh NAME FILE.lean...   (Impl oleans must exist: run lean-check.sh first)
set -o pipefail
export PATH="$HOME/.elan/bin:$PATH"
pk=""
for c in /data/rx/w/*/lean/.lake/packages; do
  if [ -f "$c/mathlib/.lake/build/lib/lean/Mathlib.olean" ] && [ -f "$c/aeneas/backends/lean/.lake/build/lib/lean/Aeneas.olean" ]; then pk=$c; break; fi
done
[ -n "$pk" ] || { echo "no built package set found"; exit 2; }
LP=""
for p in "$pk"/*; do [ -d "$p/.lake/build/lib/lean" ] && LP="$LP:$p/.lake/build/lib/lean"; done
LP="$LP:$pk/aeneas/backends/lean/.lake/build/lib/lean"
LP=${LP#:}
name=$1; shift
d="$HOME/rx/scratch/$name/lean"
cd "$HOME/rx/scratch/simd-lean-proj" || exit 2
fail=0
for f in "$@"; do
  start=$(date +%s)
  cp "$OLDPWD/experiments/simd/lean/$f" "$d/$f"
  LEAN_PATH="$LP:$d" lean --root="$d" -o "$d/${f%.lean}.olean" "$d/$f" 2>&1 | head -${LEAN_LINES:-120}
  rc=${PIPESTATUS[0]}
  echo "$f: rc=$rc ($(( $(date +%s) - start )) s)"
  [ "$rc" -ne 0 ] && fail=1
done
exit $fail
