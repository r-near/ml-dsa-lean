#!/usr/bin/env bash
# Extract the cfg(target_feature) dispatch variants with avx2 enabled at compile time (the other cfg branch).
set -o pipefail
export SIMD_RUSTFLAGS="--cfg miri -C target-feature=+avx2"
exec bash experiments/simd/jobs/each-root.sh x2avx experiments/simd/x2_dispatch x2_dispatch::dispatch_cfg x2_dispatch::dispatch_cfg_bang
