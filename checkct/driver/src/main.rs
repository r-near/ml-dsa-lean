// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright (c) 2024-2026 RustCrypto Developers
// Adapted from the constant-time harness in RustCrypto's ml-dsa crate (github.com/RustCrypto/signatures, ml-dsa/checkct,
// rev a3690c4, licensed Apache-2.0 OR MIT): the driver crate layout and the `#[path]` inclusion of the production
// modules, with this crate's modules and probes in place of upstream's.

#![no_std]
#![no_main]

// Compile the production modules directly (no public testing API needed). Same approach as the
// RustCrypto ml-dsa checkct driver.
#[allow(dead_code)]
#[path = "../../../src/params.rs"]
mod params;
#[allow(dead_code)]
#[path = "../../../src/field.rs"]
mod field;
#[allow(dead_code)]
#[path = "../../../src/rounding.rs"]
mod rounding;
#[allow(dead_code)]
#[path = "../../../src/ntt.rs"]
mod ntt;
#[allow(dead_code)]
#[path = "../../../src/keccak.rs"]
mod keccak;
// The 4-way Keccak of the fast verify (`Lanes4`, `Shim4`, and with the `avx2` feature on x86_64 the AVX2 lane operations).
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/keccak4.rs"]
mod keccak4;
// The CPU check of the `avx2` feature, with the cfg of the crate's `lib.rs` (the driver never sets `miri`).
#[cfg(all(feature = "avx2", target_arch = "x86_64"))]
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/cpu.rs"]
mod cpu;
#[allow(dead_code)]
#[path = "../../../src/encode.rs"]
mod encode;
#[allow(dead_code)]
#[path = "../../../src/sampling.rs"]
mod sampling;
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/sign.rs"]
mod sign;
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/keygen.rs"]
mod keygen;
// The verify-only arithmetic that `verify.rs` calls (public data only; the probes never reach it).
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/verify_arith.rs"]
mod verify_arith;
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/verify.rs"]
mod verify;
// The verify dispatch of src/fast_verify.rs. That file cannot be included by `#[path]` itself: its `mod dispatch;` would
// be looked up next to it as src/dispatch.rs, not in src/fast_verify/. So this module repeats its two items, each with
// the cfg of the original, and includes the real dispatch file (src/fast_verify/dispatch.rs) by `#[path]`; the
// attribute on the module sets the directory. Without the `avx2` feature (or off x86_64) it only re-exports the scalar
// functions of `verify`, as in the crate.
#[path = "../../../src/fast_verify"]
mod fast_verify {
    #[cfg(not(all(feature = "avx2", target_arch = "x86_64")))]
    pub(crate) use crate::verify::{prepare_vk, verify_internal};

    #[cfg(all(feature = "avx2", target_arch = "x86_64"))]
    #[allow(dead_code, unexpected_cfgs)]
    #[path = "dispatch.rs"]
    mod dispatch;
    #[cfg(all(feature = "avx2", target_arch = "x86_64"))]
    pub use dispatch::*;
}
// The public API, so that the probes enter through the same functions callers use.
#[allow(dead_code)]
#[path = "../../../src/api.rs"]
mod api;

mod extra;
#[cfg(feature = "experiments")]
mod experiments;
mod prepared;
mod probes;
mod rng;
mod signing;
mod split;

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    panic!()
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    __checkct_panic()
}

/// The analysis of a path stops when it reaches this function.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn __checkct_panic() -> ! {
    loop {}
}
