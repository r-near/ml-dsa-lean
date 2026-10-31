#!/usr/bin/env bash
# The probes that run the NTT, the pointwise product or the Shoup/Montgomery field products: the leaf probes, the
# KeyGen and Sign pieces built on them (compute_t, matrix_vector_ntt, response, hint_step) and the whole-Sign census.
# Extra arguments are environment overrides for run-select.sh, for example:
#   rx submit ntt-ct -- 'set -o pipefail; bash checkct/select-ntt.sh 2>&1 | tee ntt-ct.log'
#   TARGETS=x86_64-unknown-linux-gnu PROFILE=nearcore bash checkct/select-ntt.sh
set -o pipefail
export NAME="${NAME:-ct-ntt}" JOBS="${JOBS:-24}" TIMEOUT="${TIMEOUT:-3600}"
export OUT="${OUT:-$HOME/rx/scratch/ntt-ct-out}"
export ONLY="__(ntt|ntt_inverse|multiply_ntt|field_mul|field_mul_shoup|field_mul_mont|field_mont_reduce|ntt_vec_44|matrix_vector_ntt_.*|scalar_vector_ntt_inverse_1|compute_t_.*|response_.*|hint_step_.*|census_sign_internal_44)$"
exec bash "$(dirname "$0")/run-select.sh"
