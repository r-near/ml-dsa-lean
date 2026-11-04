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
#[allow(dead_code, unexpected_cfgs)]
#[path = "../../../src/verify.rs"]
mod verify;
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
