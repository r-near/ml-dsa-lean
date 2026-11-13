# shellcheck shell=bash disable=SC2154
# Shared by run.sh and inject.sh (source it; needs $here, the directory of these scripts).

# ours_run VECDIR OUTDIR EXE LOG [compared]
# Run EXE (spec-diff-cryptol) on every vector file of VECDIR/manifest.txt (only the compared ones when the fifth argument is
# `compared`: the `oursonly` files feed the generator, not the comparison) whose output in OUTDIR is missing or not bound to the
# current vector file and EXE (see stamp.py), one process per file, DIFF_JOBS in parallel.  An output is written under a
# temporary name and renamed, with its stamp, only when EXE exits 0.  Returns nonzero if any file failed.
ours_run() {
  local vdir=$1 odir=$2 exe=$3 log=$4 which=${5:-all} tool name rest todo=() failed=0
  mkdir -p "$odir"
  tool="$(python3 -I "$here/stamp.py" tool "$exe")" || return 1
  while read -r name _ rest; do
    [ -n "$name" ] || continue
    [ "$which" = compared ] && [ "$rest" = oursonly ] && continue
    python3 -I "$here/stamp.py" check "$odir/$name.out" "$vdir/$name.txt" "$tool" || {
      rm -f "$odir/$name.out" "$odir/$name.stamp"; todo+=("$name"); }
  done < "$vdir/manifest.txt"
  [ ${#todo[@]} -eq 0 ] && return 0
  # shellcheck disable=SC2016  # the worker script is single-quoted on purpose; its variables are the positional arguments
  printf '%s\n' "${todo[@]}" | xargs -P "${DIFF_JOBS:-40}" -I{} bash -c '
    ulimit -s unlimited
    exe=$1; vdir=$2; odir=$3; log=$4; tool=$5; here=$6; name=$7
    "$exe" "$vdir/$name.txt" "$odir/$name.out.tmp" 2>>"$log" || { rm -f "$odir/$name.out.tmp"; exit 1; }
    mv "$odir/$name.out.tmp" "$odir/$name.out"
    python3 -I "$here/stamp.py" write "$odir/$name.out" "$vdir/$name.txt" "$tool"' _ "$exe" "$vdir" "$odir" "$log" "$tool" "$here" {} \
    || failed=1
  for name in "${todo[@]}"; do
    python3 -I "$here/stamp.py" check "$odir/$name.out" "$vdir/$name.txt" "$tool" || { echo "our side failed on $name" >&2; failed=1; }
  done
  return $failed
}
