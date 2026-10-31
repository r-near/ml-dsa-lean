#!/usr/bin/env bash
# Build the x4_bench at the default target and at x86-64-v3, then run both pinned to one quiet physical core.
# Usage: bash experiments/simd/jobs/x4-bench.sh [CPU]    (default: the first CPU whose SMT sibling is also idle)
set -o pipefail
out="$HOME/rx/scratch/simd-bench-out"; rm -rf "$out"; mkdir -p "$out"
cpu=${1:-$(python3 experiments/simd/jobs/pick-cpu.py)}
cd experiments/simd/x4_bench || exit 1
unset RUSTFLAGS
cargo build --release 2>&1 | tail -3
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "BUILD FAILED (default)"; exit 1; }
cp target/release/x4_bench "$out/bench-default"
RUSTFLAGS="-C target-cpu=x86-64-v3" cargo build --release 2>&1 | tail -3
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "BUILD FAILED (v3)"; exit 1; }
cp target/release/x4_bench "$out/bench-v3"
echo "load: $(cut -d' ' -f1-3 /proc/loadavg); pinned to cpu $cpu (siblings: $(cat /sys/devices/system/cpu/cpu$cpu/topology/thread_siblings_list)): $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2)"
for rep in 1 2; do
  for v in default v3; do
    echo "== $v rep $rep"
    if [ "$rep" = 1 ]; then
      taskset -c "$cpu" "$out/bench-$v" "$v-r$rep" | tee "$out/$v.r$rep.txt"
    else
      SIMD_SKIP_CHECK=1 taskset -c "$cpu" "$out/bench-$v" "$v-r$rep" | tee "$out/$v.r$rep.txt"
    fi
    [ "${PIPESTATUS[0]}" -eq 0 ] || { echo "BENCH FAILED ($v rep $rep)"; exit 1; }
  done
done
echo BENCH-DONE
