#!/usr/bin/env bash
# Runs the split probes (checkct/driver/src/split.rs) on the targets where the probe they split gave no verdict:
# the AArch64 scalar build (compute_t_44, prepare_sk_*, signing_key_*) and riscv32imac (vec_power2round_87, and
# prepare_sk_44/87 on the older tree). Two containers at the same time, each with JOBS parallel BINSEC instances.
# From the repository root:
#   bash checkct/split-run.sh 2>&1 | tee split.log
# Environment: TIMEOUT (default 3600 s per probe), JOBS (default 2 per container), AONLY / RONLY (probe regexes for the
# AArch64 and riscv32imac containers; an empty RONLY skips the riscv32imac container).
# Exits nonzero if either container run fails (each runs in its own subshell with pipefail, so the `sed` prefix
# does not hide the run script's exit code).
# Argument "round2": only the probes added after the first run (finer pieces of prepare_sk_87 on AArch64, windows and
# K = 3..5 of vec_power2round on riscv32imac); the first round is every other probe of split.rs.
set -o pipefail
if [ "${1-}" = round2 ]; then
  AONLY='split_prepare_sk_87_[0-9]x1|split_ntt_vec_into'
  RONLY='split_vec_power2round_[3458]'
fi
TIMEOUT="${TIMEOUT:-3600}"
JOBS="${JOBS:-2}"
pids=()
(
  set -o pipefail
  NAME=sp-ct-a64 NONEON=1 ONLY="${AONLY:-^split_}" JOBS="$JOBS" TIMEOUT="$TIMEOUT" bash checkct/aarch64.sh 2>&1 | sed 's/^/a64: /'
) &
pids+=($!)
if [ -n "${RONLY-split_(vec_power2round|prepare_sk)}" ]; then
  (
    set -o pipefail
    NAME=sp-ct-rv TARGETS=riscv32imac-unknown-none-elf ONLY="${RONLY-split_(vec_power2round|prepare_sk)}" JOBS="$JOBS" TIMEOUT="$TIMEOUT" \
      bash checkct/run-select.sh 2>&1 | sed 's/^/rv: /'
  ) &
  pids+=($!)
fi
rc=0
for p in "${pids[@]}"; do
  wait "$p" || rc=1
done
exit $rc
