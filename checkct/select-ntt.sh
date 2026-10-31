#!/usr/bin/env bash
# The probes that run the NTT, the pointwise product or the Shoup/Montgomery field products: the leaf probes, the
# KeyGen and Sign pieces built on them (compute_t, matrix_vector_ntt, response, hint_step) and the whole-Sign census.
# Usage (from the repository root, on the build box):
#   rx submit ntt-ct -- 'set -o pipefail; bash checkct/select-ntt.sh 2>&1 | tee ntt-ct.log'
#   bash checkct/select-ntt.sh avx2      # x86_64 only, built with -C target-feature=+avx2 (static AVX2 arm)
#   bash checkct/select-ntt.sh dispatch  # x86_64 only, PROFILE=dispatch: the driver is built with its `avx2` feature, so
#                                        # the runtime AVX2 dispatch is compiled in; the cache is pre-set to "no AVX2"
#                                        # (the portable arm), see run-select.sh. Other targets build the same as default.
#   bash checkct/select-ntt.sh nearcore-dispatch   # the same with the nearcore settings
# The default mode builds without the dispatch (the crate default; `avx2` is opt-in) and says so in the log.
# A second argument replaces the probe regex (matched against driver__module__probe), a third the target list.
# The container name is unique per invocation unless NAME is set.
# Environment overrides for run-select.sh (NAME, JOBS, TIMEOUT, OUT, TARGETS, PROFILE) are honored.
set -o pipefail
export NAME="${NAME:-ct-ntt-$$}"
[ -n "$3" ] && export TARGETS="$3"
mode="${1:-default}"
case "$mode" in
  avx2)
    export TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}" PROFILE="${PROFILE:-avx2}"
    export OUT="${OUT:-$HOME/rx/scratch/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-16}" ;;
  nearcore-avx2)
    export TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}" PROFILE=nearcore-avx2
    export OUT="${OUT:-$HOME/rx/scratch/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-16}" ;;
  dispatch|nearcore-dispatch)
    export TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}" PROFILE="$mode"
    export OUT="${OUT:-$HOME/rx/scratch/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-16}" ;;
  *)
    export OUT="${OUT:-$HOME/rx/scratch/ntt-ct-out-$mode-$$}" JOBS="${JOBS:-24}" ;;
esac
export TIMEOUT="${TIMEOUT:-3600}"
export ONLY="${2:-__(ntt|ntt_inverse|multiply_ntt|field_mul|field_mul_shoup|field_mul_mont|field_mont_reduce|ntt_vec_44|matrix_vector_ntt_.*|scalar_vector_ntt_inverse_1|compute_t_.*|response_.*|hint_step_.*|census_sign_internal_44)$}"
echo "drivers copied to $OUT"
exec bash "$(dirname "$0")/run-select.sh"
