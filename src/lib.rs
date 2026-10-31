//! Proof-first ML-DSA (FIPS 204).
//!
//! Every function named `alg_NN_*` or documented "Algorithm NN" follows the numbered algorithm of
//! FIPS 204 step for step. The core uses plain `u32` coefficient arrays, `while` loops (no `for`/ranges) and
//! free functions only: no iterator adapters, closures, operator-trait impls, `hybrid-array` or
//! `module-lattice`. Parameter sets are a `Params` value plus `K`/`L` const generics.
#![no_std]
// The only `unsafe` is the optional AVX2 dispatch shim (feature `avx2`, src/ntt.rs).
#![cfg_attr(not(feature = "avx2"), forbid(unsafe_code))]
#![allow(clippy::many_single_char_names, clippy::needless_range_loop)]

// Only `api` is public. The other modules hold panicking internals (`sign::sign_internal` and
// `keygen::keygen_internal` index slices of the wrong length, `verify::verify_internal` indexes by K/L), so
// they are crate-private unless the `internals` feature (tests, fuzzing) is on.
pub mod api;

#[cfg(feature = "internals")]
pub mod encode;
#[cfg(not(feature = "internals"))]
mod encode;
#[cfg(feature = "internals")]
pub mod field;
#[cfg(not(feature = "internals"))]
mod field;
#[cfg(feature = "internals")]
pub mod keccak;
#[cfg(not(feature = "internals"))]
mod keccak;
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
#[cfg(not(feature = "internals"))]
mod verify;
