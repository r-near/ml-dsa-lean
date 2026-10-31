#!/usr/bin/env bash
# Build x5_bench (differential tests of the AVX2 shims + hand-written kernel benchmark) at the default target and run it
# pinned to one quiet core. Usage: bash experiments/simd/jobs/x5-bench.sh [CPU]
set -o pipefail
out="$HOME/rx/scratch/simd-bench5-out"; rm -rf "$out"; mkdir -p "$out"
cpu=${1:-$(python3 experiments/simd/jobs/pick-cpu.py)}
cd experiments/simd/x5_bench || exit 1
unset RUSTFLAGS
cargo build --release 2>&1 | tail -30
[ "${PIPESTATUS[0]}" -eq 0 ] || { echo "BUILD FAILED"; exit 1; }
cp target/release/x5_bench "$out/bench5"
echo "load: $(cut -d' ' -f1-3 /proc/loadavg); pinned to cpu $cpu"
for rep in 1 2; do
  echo "== rep $rep"
  if [ "$rep" = 1 ]; then
    taskset -c "$cpu" "$out/bench5" "x5-r$rep" | tee "$out/r$rep.txt"
  else
    SIMD_SKIP_CHECK=1 taskset -c "$cpu" "$out/bench5" "x5-r$rep" | tee "$out/r$rep.txt"
  fi
  [ "${PIPESTATUS[0]}" -eq 0 ] || { echo "BENCH FAILED (rep $rep)"; exit 1; }
done
echo BENCH5-DONE
