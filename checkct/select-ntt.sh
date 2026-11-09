#!/usr/bin/env bash
# The probes that run the NTT, the pointwise product or the Shoup/Montgomery field products: the leaf probes, the
# KeyGen and Sign pieces built on them (compute_t, matrix_vector_ntt, response, hint_step) and the whole-Sign census.
# Usage (from the repository root):
#   bash checkct/select-ntt.sh 2>&1 | tee ntt-ct.log
#   bash checkct/select-ntt.sh avx2      # x86_64 only, built with -C target-feature=+avx2 (static AVX2 arm)
# The default mode builds the crate default. There are no dispatch modes (round 12).
# A second argument replaces the probe regex (matched against driver__module__probe), a third the target list.
# The container name is unique per invocation unless NAME is set.
# Environment overrides for run-select.sh (NAME, JOBS, TIMEOUT, OUT, TARGETS, PROFILE) are honored.
set -o pipefail
export NAME="${NAME:-ct-ntt-$$}"
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
[ -n "$3" ] && export TARGETS="$3"
mode="${1:-default}"
case "$mode" in
  avx2)
    export TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}" PROFILE="${PROFILE:-avx2}"
    export OUT="${OUT:-$SCRATCH/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-4}" ;;
  nearcore-avx2)
    export TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}" PROFILE=nearcore-avx2
    export OUT="${OUT:-$SCRATCH/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-4}" ;;
  *)
    export OUT="${OUT:-$SCRATCH/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-24}" ;;
esac
export TIMEOUT="${TIMEOUT:-3600}"
export ONLY="${2:-__(ntt|ntt_inverse|multiply_ntt|field_mul|field_mul_shoup|field_mul_mont|field_mont_reduce|ntt_vec_44|matrix_vector_ntt_.*|scalar_vector_ntt_inverse_1|compute_t_.*|response_.*|hint_step_.*|census_sign_internal_44)$}"
echo "drivers copied to $OUT"
exec bash "$(dirname "$0")/run-select.sh"
