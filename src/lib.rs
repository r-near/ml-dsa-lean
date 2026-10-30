//! Proof-first ML-DSA (FIPS 204).
//!
//! Every function named `alg_NN_*` or documented "Algorithm NN" follows the numbered algorithm of
//! FIPS 204 step for step. The core uses plain `u32` coefficient arrays, `while` loops (no `for`/ranges) and
//! free functions only: no iterator adapters, closures, operator-trait impls, `hybrid-array` or
//! `module-lattice`. Parameter sets are a `Params` value plus `K`/`L` const generics.
#![no_std]
#![allow(clippy::many_single_char_names, clippy::needless_range_loop)]

pub mod api;
pub mod encode;
pub mod field;
pub mod keccak;
pub mod keygen;
pub mod ntt;
pub mod params;
pub mod rounding;
pub mod sampling;
pub mod sign;
pub mod verify;
