#!/usr/bin/env bash
# Checks that the shared driver (between the BEGIN COMMON / END COMMON markers) is identical in
# common.lean.txt, lean/SpecTests/DiffVCVio.lean and scripts/diff-vcvio/DiffEval.lean.
# `check-common.sh --sync` first copies common.lean.txt into both evaluators (heads and tails are kept).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
ours="$here/../../lean/SpecTests/DiffVCVio.lean"
theirs="$here/DiffEval.lean"
common="$here/common.lean.txt"
cut() { sed -n '/^-- BEGIN COMMON/,/^-- END COMMON/p' "$1"; }
if [ "${1:-}" = "--sync" ]; then
  for f in "$ours" "$theirs"; do
    awk -v c="$common" '
      /^-- BEGIN COMMON/ { while ((getline line < c) > 0) print line; skip=1; next }
      /^-- END COMMON/ { skip=0; next }
      !skip { print }' "$f" > "$f.new"
    mv "$f.new" "$f"
  done
fi
if cut "$common" | diff -q - <(cut "$ours") >/dev/null && cut "$common" | diff -q - <(cut "$theirs") >/dev/null; then
  echo "common sections identical"
else
  echo "common sections DIFFER"; exit 1
fi
