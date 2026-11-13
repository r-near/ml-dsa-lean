#!/usr/bin/env bash
# Sensitivity check of the Cryptol differential: inject bugs into a scratch copy of lean/Spec, rebuild our side, re-run it on the
# vectors of a finished run, and compare with the saved Cryptol outputs.  Never touches the committed lean/Spec.
#   bash scripts/diff-cryptol/inject.sh [NAME ...]      (default: all injections of inject.py; `inject.py list` shows them)
#   bash scripts/diff-cryptol/inject.sh --summarize     (recompute the table from the saved outputs of the last injection run)
# Needs a finished `run.sh all` in $DIFF_RUN (the vec/ and theirs/ directories).  Scratch project: $INJECT_DIR (default
# $ML_DSA_SCRATCH/cryptol-diff/inject-lean), seeded from lean/ and $LEAN_PACKAGES_SEED (built lake packages).  One build at a time.
# $INJECT_DIR is validated before anything is written (inject.py check-dest) and must be empty, absent or a directory this script
# made earlier (`.inject-scratch` marker): `rsync --delete` runs in it.
# Prints, per injected bug, whether the harness reports a mismatch and the first files that show it.  Every injection gets a row:
# detected = YES (at least one mismatching line), no (the bug survived), ERROR (the injection, build or a run failed, or the
# comparison had harness errors: nothing is concluded).  The exit status is nonzero unless every injection is detected.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
root="$(cd "$(dirname "$0")/../.." && pwd)"
here="$root/scripts/diff-cryptol"
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
run="${DIFF_RUN:-$SCRATCH/cryptol-diff/run}"
# shellcheck source=lib.sh
. "$here/lib.sh"
summarize=0
[ "${1:-}" = "--summarize" ] && summarize=1
if [ "$summarize" -eq 0 ]; then
  proj="$(python3 -I "$here/inject.py" check-dest "${INJECT_DIR-$SCRATCH/cryptol-diff/inject-lean}" "$root" "$run")" || exit 1
  names=("$@")
  if [ ${#names[@]} -eq 0 ]; then
    names=(); while IFS= read -r n; do names+=("$n"); done < <(python3 -I "$here/inject.py" list | cut -f1)
  fi
  known="$(python3 -I "$here/inject.py" list | cut -f1)"
  for n in "${names[@]}"; do
    printf '%s\n' "$known" | grep -qxF -- "$n" || { echo "inject.sh: unknown injection '$n' (see inject.py list)" >&2; exit 2; }
  done
  mkdir -p "$proj"
  touch "$proj/.inject-scratch"
  rsync -a --delete --exclude .lake --exclude .inject-scratch "$root/lean/" "$proj/"
  mkdir -p "$proj/.lake"
  if [ ! -d "$proj/.lake/packages" ]; then
    [ -n "${LEAN_PACKAGES_SEED:-}" ] && [ -d "$LEAN_PACKAGES_SEED" ] || { echo "set LEAN_PACKAGES_SEED to a directory of built lake packages"; exit 1; }
    cp -a "$LEAN_PACKAGES_SEED" "$proj/.lake/packages"
  fi
fi
summary="$run/inject-summary.txt"
: > "$summary"
printf '%-24s %-9s %-9s %s\n' injection detected mismatches "files with mismatches (lines)" | tee -a "$summary"
not_detected=0
report() { # NAME: compare the saved outputs of an injected build with the Cryptol outputs; one row, whatever happened
  local d="$run/inject/$1" nm=0 hn=0 files="" det
  rm -f "$d/mismatches.txt"
  python3 -I "$here/compare.py" "$d" > "$d/compare.log" 2>&1 || true   # exit 1 just means mismatches (or harness errors)
  if [ -f "$d/mismatches.txt" ]; then
    nm=$(grep -c '^MISMATCH' "$d/mismatches.txt" || true)
    hn=$(grep -c '^HARNESS' "$d/mismatches.txt" || true)
    files=$({ grep '^MISMATCH' "$d/mismatches.txt" || true; } | awk '{print $2}' | sort | uniq -c | sort -rn | awk '{printf "%s(%s) ", $2, $1}')
  else
    hn=1; files="(no comparison output: see $d/compare.log)"
  fi
  if [ "$hn" -gt 0 ]; then det=ERROR; elif [ "$nm" -gt 0 ]; then det=YES; else det=no; fi
  [ "$det" = YES ] || not_detected=$((not_detected + 1))
  [ "$hn" -eq 0 ] || files="harness errors: $hn; $files"
  printf '%-24s %-9s %-9s %s\n' "$1" "$det" "$nm" "$files" | tee -a "$summary"
}
error_row() { # NAME REASON
  not_detected=$((not_detected + 1))
  printf '%-24s %-9s %-9s %s\n' "$1" ERROR - "$2" | tee -a "$summary"
}
build_and_run() { # NAME: inject, rebuild, run our side on the compared vector files; returns nonzero (with a reason in $why) on failure
  local name=$1 exe sha
  local log="$run/inject-$name.log" d="$run/inject/$name"
  why=""
  rsync -a --delete "$root/lean/Spec/" "$proj/Spec/" || { why="rsync of the pristine Spec failed"; return 1; }
  python3 -I "$here/inject.py" apply "$name" "$proj" > "$log" 2>&1 || { why="inject.py apply failed (see $log)"; return 1; }
  (cd "$proj" && lake build spec-diff-cryptol >> "$log" 2>&1) || { why="lake build failed (see $log)"; return 1; }
  exe="$proj/.lake/build/bin/spec-diff-cryptol"
  [ -x "$exe" ] || { why="no executable after the build"; return 1; }
  sha="$(sha256sum "$exe" | cut -d' ' -f1)"
  echo "executable sha256 $sha (pristine $pristine_sha)" >> "$log"
  [ "$sha" != "$pristine_sha" ] || { why="the injected build is byte-identical to the pristine build"; return 1; }
  rm -rf "$d"; mkdir -p "$d/ours"
  ln -s "$run/vec" "$d/vec"; ln -s "$run/theirs" "$d/theirs"
  # our side on every compared vector file, in parallel (the `oursonly` files only feed the generator)
  ours_run "$run/vec" "$d/ours" "$exe" "$log" compared || { why="our side failed on a vector file (see $log)"; return 1; }
}
if [ "$summarize" -eq 1 ]; then   # recompute the table from the saved outputs of the last injection run
  for d in "$run"/inject/*/; do report "$(basename "$d")"; done
else
  mkdir -p "$run/inject"
  # the pristine build, to check that every injected build really differs
  rsync -a --delete "$root/lean/Spec/" "$proj/Spec/"
  (cd "$proj" && lake build spec-diff-cryptol > "$run/inject-pristine.log" 2>&1) || { echo "inject.sh: the pristine build failed (see $run/inject-pristine.log)" >&2; exit 1; }
  pristine_sha="$(sha256sum "$proj/.lake/build/bin/spec-diff-cryptol" | cut -d' ' -f1)"
  why=""
  for name in "${names[@]}"; do
    if build_and_run "$name"; then report "$name"; else error_row "$name" "$why"; fi
  done
fi
if [ "$not_detected" -gt 0 ]; then
  echo "$not_detected injection(s) not detected or failed (rows marked no or ERROR above)" | tee -a "$summary" >&2
  exit 1
fi
echo "all injections detected" | tee -a "$summary"
