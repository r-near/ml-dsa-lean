#!/usr/bin/env bash
# Phase 0 cross-check: the same sources at x86-64-v3 with LLVM's SLP threshold lowered (non-default flag, so only a
# diagnostic), plus the intrinsics reference. Prints scalar4, the best plain-loop variants and the intrinsics.
set -o pipefail
cd experiments/keccak4 || exit 1
cpu=$(python3 ../simd/jobs/pick-cpu.py)
echo "load: $(cut -d' ' -f1-3 /proc/loadavg); cpu $cpu"
for thr in 0 -2; do
  export RUSTFLAGS="-C target-cpu=x86-64-v3 -C llvm-args=-slp-threshold=$thr"
  cargo build --release 2>&1 | tail -1
  for rep in 1 2; do
    echo "== slp-threshold $thr rep $rep"
    taskset -c "$cpu" target/release/keccak4 "thr$thr-r$rep" 2>&1 | grep -E "ROW.*(scalar4|x4_v2|x4_v4|x4_v5|x4_v6|x4_v7|x4_intrinsics)\s"
  done
done
