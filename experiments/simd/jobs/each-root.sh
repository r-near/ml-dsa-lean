#!/usr/bin/env bash
# Extract one crate once per root (so a failure in one variant does not hide the others) and print a compact summary.
# Usage: bash experiments/simd/jobs/each-root.sh NAME CRATE_DIR ROOT...    (scratch: $HOME/rx/scratch/simd-NAME-<root>)
# Env SIMD_RUSTFLAGS / SIMD_CHARON_ARGS are passed through to extract-mini.sh.
set -o pipefail
name=$1; crate=$2; shift 2
for root in "$@"; do
  short=${root##*::}
  work="$HOME/rx/scratch/simd-$name-$short"
  echo "################ root $root  (RUSTFLAGS='${SIMD_RUSTFLAGS---cfg miri}')"
  bash experiments/simd/extract-mini.sh "$crate" "$work" "$root" > "$work.out" 2>&1
  rc=$?
  cat "$work.out"
  ev="$work/evidence"; rm -rf "$ev"; mkdir -p "$ev"
  cp "$work"/lean/Impl/*.lean "$ev"/ 2>/dev/null
  cp "$work/hax.log" "$work/aeneas.log" "$ev"/ 2>/dev/null
  echo "--- rc=$rc"
  echo "--- charon/aeneas errors and warnings (excluding the baseline Step::* ones)"
  grep -hE '\[Error|\[Warn|^error|^warning: ' "$work/hax.log" "$work/aeneas.log" | grep -v "core::iter::range::Step" | sort | uniq -c | head -20
  echo "--- hax.log error context"
  grep -n -B2 -A12 -E '^error' "$work/hax.log" | head -60
  echo "--- FunsExternal_Template.lean declarations (minus the Step::* baseline)"
  grep -E '^(axiom|def|opaque)' "$ev/FunsExternal_Template.lean" 2>/dev/null | grep -v 'core.iter.range.Step'
  echo "--- Funs.lean (definitions after the namespace line)"
  sed -n '/^namespace Impl/,$p' "$ev/Funs.lean" 2>/dev/null
  echo "--- Types.lean (after namespace)"
  sed -n '/^namespace Impl/,$p' "$ev/Types.lean" 2>/dev/null
done
