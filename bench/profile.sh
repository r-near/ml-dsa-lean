#!/usr/bin/env bash
# Category profile (bench/categorize.py) of this crate's default and `avx2` builds and of the AVX2 competitors, for
# ML-DSA-65 and 87, sign (deterministic) and verify. Builds the sampling profiler (`prof`) twice with the nearcore profile
# (fat LTO, one codegen unit, panic = abort) plus line tables and frame pointers, so the profile is of the code that the
# timings measure (PROFILE=profiling selects the plain release profile instead, which is 20-40% slower for the portable
# build and shifts the shares), runs it pinned to one CPU, and prints one table.
# Run from the repository root on an otherwise idle machine:
#   bash bench/profile.sh LABEL [CPU] [SECS] 2>&1 | tee profile-LABEL.log
# CPU defaults to 1 (pass the CPU compare.sh printed); SECS (default 20) is the length of each workload.
# Output: $ML_DSA_SCRATCH/profile-LABEL/{default,avx2}/*.folded and flat/ (renamed for the table).
set -o pipefail
L=${1:?usage: profile.sh LABEL [CPU] [SECS]}
CPU=${2:-1}
SECS=${3:-20}
PROFILE=${PROFILE:-nearcore}
OUT=${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}/profile-$L
mkdir -p "$OUT/flat"
root=$PWD
cd bench || exit 1
for v in default avx2; do
  FEAT="--features prof"
  [ "$v" = avx2 ] && FEAT="--features prof,avx2"
  CARGO_PROFILE_NEARCORE_DEBUG=1 RUSTFLAGS="-C force-frame-pointers=yes" cargo build --profile "$PROFILE" --bin prof $FEAT --message-format=json-render-diagnostics >"$OUT/$v.json" || exit 1
  python3 - "$OUT/$v.json" "$OUT/prof-$v" <<'PY' || exit 1
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "prof":
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
PY
done
cd "$root" || exit 1
uptime
for v in default avx2; do
  # default build: this crate only; avx2 build: this crate with the dispatch, plus the AVX2 competitors
  IMPS=ours
  [ "$v" = avx2 ] && IMPS=ours,mldsa-native-avx2,libcrux-avx2
  echo "== prof $v ($IMPS) $(date -u +%H:%M:%S) load $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "$CPU" "$OUT/prof-$v" "$OUT/$v" --secs "$SECS" --impl "$IMPS" --sets 65,87 --ops sign-det,verify | tee -a "$OUT/profile.log" || exit 1
done
for f in "$OUT"/default/ours.*.folded; do cp "$f" "$OUT/flat/ours-default.${f##*/ours.}"; done
for f in "$OUT"/avx2/ours.*.folded; do cp "$f" "$OUT/flat/ours-avx2.${f##*/ours.}"; done
for f in "$OUT"/avx2/mldsa-native-avx2.*.folded "$OUT"/avx2/libcrux-avx2.*.folded; do cp "$f" "$OUT/flat/"; done
for op in sign-det verify; do
  for set in 65 87; do
    echo; echo "ML-DSA-$set $op (share of samples)"
    python3 bench/categorize.py --table "$OUT"/flat/*."$set.$op.folded"
    echo; echo "ML-DSA-$set $op (microseconds per call under the profiler)"
    python3 bench/categorize.py --table-abs "$OUT/profile.log" "$OUT"/flat/*."$set.$op.folded"
  done
done
