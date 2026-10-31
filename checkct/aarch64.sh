#!/usr/bin/env bash
# Experiment: can BINSEC analyze AArch64 binaries? cargo-checkct does not support the target, so this builds the
# driver for aarch64-unknown-linux-gnu inside the ct-binsec container and writes the BINSEC scripts by hand, with the
# same template as cargo-checkct's (lr = x30). From the repository root:
#   rx submit ct4 -- 'set -o pipefail; NAME=ct4-a64 ONLY="ct_select|field_mul" bash checkct/aarch64.sh 2>&1 | tee a64.log'
# Environment: ONLY (extended regex over probe names, default all), TIMEOUT (default 900), JOBS (default 16), NAME, OUT,
# NONEON=1 (build with -C target-feature=-neon,-fp-armv8: BINSEC cannot lift most NEON instructions, and LLVM
# auto-vectorizes the loops, so those probes end "unknown" at the first vector instruction without it).
# CT_MEMORY / CT_CPUS: docker --memory / --cpus caps (default 64g / 24); uncapped BINSEC runs have pushed the box
# out of memory and killed unrelated Lean builds.
set -o pipefail
MOUNT=""
if [ -n "$OUT" ]; then mkdir -p "$OUT" && chmod 777 "$OUT" && MOUNT="-v $OUT:/out"; fi
docker run --rm --memory "${CT_MEMORY:-64g}" --memory-swap "${CT_MEMORY:-64g}" --cpus "${CT_CPUS:-24}" --name "${NAME:-ct-a64}" $MOUNT -e ONLY="${ONLY:-.}" -e TIMEOUT="${TIMEOUT:-900}" -e JOBS="${JOBS:-16}" -e NONEON="${NONEON:-}" \
  -v "$PWD":/src:ro ct-binsec bash /src/checkct/aarch64-inner.sh
