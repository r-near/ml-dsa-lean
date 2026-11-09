//! Proof-first ML-DSA (FIPS 204).
//!
//! Every function named `alg_NN_*` or documented "Algorithm NN" follows the numbered algorithm of
//! FIPS 204 step for step. The core uses plain `u32` coefficient arrays, `while` loops (no `for`/ranges) and
//! free functions only: no iterator adapters, closures, operator-trait impls, `hybrid-array` or
//! `module-lattice`. Parameter sets are a `Params` value plus `K`/`L` const generics.
#![no_std]
// The only `unsafe` is the NTT dispatch of the opt-in `avx2` feature (x86_64): the `#[target_feature(enable = "avx2")]` copies of the
// NTT bodies in src/ntt.rs and the CPU check in src/cpu.rs, each with its own `allow`. Verify, `verifying_key` and the prepared
// verify have no dispatch and no `unsafe` (round 12): they call the 4-way functions directly, and the build's target features
// decide what LLVM emits. Without the feature the crate forbids `unsafe` outright.
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
// The CPU check of the NTT dispatch (`cpu.rs`); it exists only with the `avx2` feature on x86_64.
#[cfg(feature = "internals")]
#[cfg_attr(feature = "avx2", allow(unsafe_code))]
pub mod cpu;
#[cfg(not(feature = "internals"))]
#[cfg_attr(feature = "avx2", allow(unsafe_code))]
mod cpu;
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
