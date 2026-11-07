#!/usr/bin/env bash
# One implementation per process. A fresh process runs this crate's portable code (and RustCrypto's) up to 1.5x slower than a
# process that has already executed mldsa-native's AVX2 code (see bench/results/2026-11-06.md, "Process state"), and the
# full `bench` run measures every implementation in one process, so the numbers depend on the order of the cells. This script
# runs the binaries built by compare.sh once per implementation, each in a new process pinned to CPU, and writes one TSV per
# build and repetition (concatenated, same format as `bench`; table.py reads them).
# Usage: bench/isolated.sh BINDIR CPU OUTDIR [REPS]   (BINDIR holds bench-default, bench-avx2, bench-v3 as compare.sh writes them)
set -o pipefail
BIN=${1:?usage: isolated.sh BINDIR CPU OUTDIR [REPS]}
CPU=${2:?cpu}
OUT=${3:?outdir}
REPS=${4:-1}
mkdir -p "$OUT"
# implementation names as `bench` prints them; --only matches substrings of "IMPL GROUP", so "ours" covers the prepared-key cells
declare -A IMPLS=(
  [default]="ours rustcrypto libcrux-portable libcrux-avx2 mldsa-native-portable mldsa-native-avx2 aws-lc-rs"
  [avx2]="ours"
  [v3]="ours rustcrypto libcrux-portable libcrux-avx2"
)
uptime
for r in $(seq 1 "$REPS"); do
  for v in default avx2 v3; do
    f="$OUT/$v.fresh$r.tsv"
    : > "$f"
    for i in ${IMPLS[$v]}; do
      echo "== $v rep $r: $i $(date -u +%H:%M:%S) load $(cut -d' ' -f1-3 /proc/loadavg)"
      taskset -c "$CPU" "$BIN/bench-$v" --label "$v-fresh$r-$i-cpu$CPU" --only "$i" 2>/dev/null >> "$f" || exit 1
    done
  done
done
