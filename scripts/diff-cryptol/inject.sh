#!/usr/bin/env bash
# Sensitivity check of the Cryptol differential: inject bugs into a scratch copy of lean/Spec, rebuild our side, re-run it on the
# vectors of a finished run, and compare with the saved Cryptol outputs.  Never touches the committed lean/Spec.
#   bash scripts/diff-cryptol/inject.sh [NAME ...]      (default: all injections of inject.py; `inject.py list` shows them)
# Needs a finished `run.sh all` in $DIFF_RUN (the vec/ and theirs/ directories).  Scratch project: $INJECT_DIR (default
# $ML_DSA_SCRATCH/cryptol-diff/inject-lean), seeded from lean/ and $LEAN_PACKAGES_SEED (built lake packages).  One build at a time.
# Prints, per injected bug, whether the harness reports a mismatch and the first files that show it.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
root="$(cd "$(dirname "$0")/../.." && pwd)"
here="$root/scripts/diff-cryptol"
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
run="${DIFF_RUN:-$SCRATCH/cryptol-diff/run}"
proj="${INJECT_DIR:-$SCRATCH/cryptol-diff/inject-lean}"
names=("$@")
[ ${#names[@]} -gt 0 ] || mapfile -t names < <(python3 -I "$here/inject.py" list | cut -f1)

mkdir -p "$proj"
rsync -a --delete --exclude .lake "$root/lean/" "$proj/"
mkdir -p "$proj/.lake"
if [ ! -d "$proj/.lake/packages" ]; then
  [ -n "${LEAN_PACKAGES_SEED:-}" ] && [ -d "$LEAN_PACKAGES_SEED" ] || { echo "set LEAN_PACKAGES_SEED to a directory of built lake packages"; exit 1; }
  cp -a "$LEAN_PACKAGES_SEED" "$proj/.lake/packages"
fi
summary="$run/inject-summary.txt"
: > "$summary"
printf '%-24s %-9s %-9s %s\n' injection detected mismatches "first files" | tee -a "$summary"
for name in "${names[@]}"; do
  rsync -a "$root/lean/Spec/" "$proj/Spec/"          # pristine Spec
  python3 -I "$here/inject.py" apply "$name" "$proj" > "$run/inject-$name.log"
  (cd "$proj" && lake build spec-diff-cryptol >> "$run/inject-$name.log" 2>&1)
  exe="$proj/.lake/build/bin/spec-diff-cryptol"
  d="$run/inject/$name"
  rm -rf "$d"; mkdir -p "$d/ours"
  ln -s "$run/vec" "$d/vec"; ln -s "$run/theirs" "$d/theirs"
  # our side on every vector file, in parallel
  awk '{print $1}' "$run/vec/manifest.txt" | xargs -P "${DIFF_JOBS:-40}" -I{} sh -c "ulimit -s unlimited; '$exe' '$run/vec/{}.txt' '$d/ours/{}.out' 2>/dev/null"
  rc=0
  python3 -I "$here/compare.py" "$d" > "$d/compare.log" 2>&1 || rc=$?
  nm=$(grep -c '^MISMATCH' "$d/mismatches.txt" || true)
  files=$(grep '^MISMATCH' "$d/mismatches.txt" | awk '{print $2}' | sort | uniq -c | sort -rn | head -4 | awk '{printf "%s(%s) ", $2, $1}')
  det=no; [ "$nm" -gt 0 ] && det=YES
  printf '%-24s %-9s %-9s %s\n' "$name" "$det" "$nm" "$files" | tee -a "$summary"
done
