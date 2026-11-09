//! Proof-first ML-DSA (FIPS 204).
//!
//! Every function named `alg_NN_*` or documented "Algorithm NN" follows the numbered algorithm of
//! FIPS 204 step for step. The core uses plain `u32` coefficient arrays, `while` loops (no `for`/ranges) and
//! free functions only: no iterator adapters, closures, operator-trait impls, `hybrid-array` or
//! `module-lattice`. Parameter sets are a `Params` value plus `K`/`L` const generics.
#![no_std]
// The only `unsafe` is the optional AVX2 code (feature `avx2`, x86_64): the NTT dispatch (`mod dispatch` in src/ntt.rs), the CPU
// check (src/cpu.rs), and the verify dispatch (src/fast_verify/dispatch.rs, three blocks); each carries its own `allow`. There are no
// intrinsics: the AVX2 code is the proved plain-Rust code, compiled inside `#[target_feature(enable = "avx2")]` functions. Without the
// feature the crate forbids `unsafe` outright, and the three verify `_with` functions (src/fast_verify.rs) are the same text as in the
// extraction: the dispatch exists in every build, with an uninhabited `cpu::Avx2` token where it cannot run.
#![cfg_attr(not(feature = "avx2"), forbid(unsafe_code))]
#![cfg_attr(feature = "avx2", deny(unsafe_code))]
#![allow(clippy::many_single_char_names, clippy::needless_range_loop)]

// Only `api` is public. The other modules hold panicking internals (`sign::sign_internal` and
// `keygen::keygen_internal` index slices of the wrong length, `verify::verify_internal` indexes by K/L), so
// they are crate-private unless the `internals` feature (tests, fuzzing) is on.
pub mod api;

#[cfg(feature = "internals")]
pub mod encode;
#[cfg(not(feature = "internals"))]
mod encode;
// The CPU check and the `Avx2` token (see `cpu.rs`). It exists in every build: without the dispatch it is the stub
// `avx2() -> None`.
#[cfg(feature = "internals")]
#[cfg_attr(feature = "avx2", allow(unsafe_code))]
pub mod cpu;
#[cfg(not(feature = "internals"))]
#[cfg_attr(feature = "avx2", allow(unsafe_code))]
mod cpu;
// `fast_verify` always exists: `api.rs` calls its `_with` functions, which choose between the scalar function and the
// AVX2 wrapper by an `Option<cpu::Avx2>` argument. Without the dispatch they are the scalar functions.
#[cfg(feature = "internals")]
pub mod fast_verify;
#[cfg(not(feature = "internals"))]
mod fast_verify;
#[cfg(feature = "internals")]
pub mod field;
#[cfg(not(feature = "internals"))]
mod field;
#[cfg(feature = "internals")]
pub mod keccak;
#[cfg(not(feature = "internals"))]
mod keccak;
#[cfg(feature = "internals")]
pub mod keccak4;
#[cfg(not(feature = "internals"))]
mod keccak4;
#[cfg(feature = "internals")]
pub mod keygen;
#[cfg(not(feature = "internals"))]
mod keygen;
#[cfg(feature = "internals")]
pub mod ntt;
#[cfg(not(feature = "internals"))]
mod ntt;
#[cfg(feature = "internals")]
pub mod params;
// `params::sk_len` is used only by tests and fuzzing; no other dead code is silenced.
#[cfg_attr(not(feature = "internals"), allow(dead_code))]
#[cfg(not(feature = "internals"))]
mod params;
#[cfg(feature = "internals")]
pub mod rounding;
#[cfg(not(feature = "internals"))]
mod rounding;
#[cfg(feature = "internals")]
pub mod sampling;
#[cfg(not(feature = "internals"))]
mod sampling;
#[cfg(feature = "internals")]
pub mod sign;
#[cfg(not(feature = "internals"))]
mod sign;
#[cfg(feature = "internals")]
pub mod verify;
#[cfg(feature = "internals")]
pub mod verify_arith;
#[cfg(not(feature = "internals"))]
mod verify_arith;
#[cfg(not(feature = "internals"))]
mod verify;
