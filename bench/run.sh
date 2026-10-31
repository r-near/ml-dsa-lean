#!/usr/bin/env bash
# Runs the binaries built by build.sh, one after the other, each pinned to one CPU.
# Usage: bench/run.sh BINDIR CPU OUTDIR [variant ...] [-- bench args]
#   variants default to: release-default nearcore-default release-native nearcore-native nearcore-v3
set -euo pipefail
bindir=${1:?usage: run.sh BINDIR CPU OUTDIR [variant ...] [-- bench args]}
cpu=${2:?cpu}
outdir=${3:?outdir}
shift 3
variants=()
while [ $# -gt 0 ] && [ "$1" != "--" ]; do variants+=("$1"); shift; done
[ $# -gt 0 ] && shift
[ ${#variants[@]} -eq 0 ] && variants=(release-default nearcore-default release-native nearcore-native nearcore-v3)
mkdir -p "$outdir"
for v in "${variants[@]}"; do
  echo "== $v on cpu $cpu: $(date -u +%H:%M:%S) $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "$cpu" "$bindir/bench-$v" --label "$v-cpu$cpu" "$@" | tee "$outdir/$v.cpu$cpu.tsv"
done
