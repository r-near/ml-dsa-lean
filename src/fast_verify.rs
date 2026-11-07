//! Run-time dispatch of verify to the 4-way AVX2 body. Opt-in (feature `avx2`), x86_64 only, never under Miri.
//! NOT part of the Lean proof; read this before relying on the theorems for a shipped binary.
//!
//! What is proved and what is not:
//!
//! * `verify::verify_internal` and `verify::prepare_vk` are the proved scalar functions. Every `api` function equals the
//!   FIPS 204 transcription in Lean.
//! * The 4-way versions (`verify::verify_internal_x4::<K, L, X>` and `verify::prepare_vk_x4::<K, L, X>`, with
//!   `X: keccak4::Lanes4`) are extracted and proved equal to the scalar functions on every input for `X = Shim4`
//!   (`Proofs/FastVerify.lean`; theorem names in `lean/fast-verify-theorems.txt`).
//! * This module instantiates them with `keccak4::avx2::Avx2` inside a `#[target_feature(enable = "avx2")]` wrapper and
//!   chooses between them and the scalar functions with a cached CPU check. The `Avx2` lane operations are tested equal
//!   to the proved `Shim4` operations (`tests/keccak4_avx2.rs`: every operation, every rotation immediate the kernel
//!   uses, and whole permutations), not proved. The wrapper, the dispatch and the CPU check are outside the proof.
//!
//! `api.rs` imports `verify_internal` and `prepare_vk` from this module (one line, so that the source line numbers the
//! extracted Lean quotes do not move). Without the `avx2` feature, on other targets and under Miri (which includes the
//! extraction, `--cfg miri`) the module only re-exports the scalar functions of `verify.rs`: the extracted `api`
//! functions are exactly the scalar ones and nothing of the dispatch exists. With the feature on x86_64 the same two
//! names are the dispatchers below, with the same signatures.
//!
//! `verify_prepared_internal` is not dispatched: it does not run ExpandA (the matrix is in the prepared key), and the
//! rest of verify is the NTT, which has its own dispatch (`ntt.rs`).

// The scalar functions themselves.
#[cfg(not(all(feature = "avx2", not(miri), target_arch = "x86_64")))]
pub(crate) use crate::verify::{prepare_vk, verify_internal};

// The dispatch (src/fast_verify/dispatch.rs).
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
#[allow(unsafe_code)]
mod dispatch;
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
pub use dispatch::*;
