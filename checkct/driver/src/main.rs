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

mod probes;
mod rng;
mod signing;

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
