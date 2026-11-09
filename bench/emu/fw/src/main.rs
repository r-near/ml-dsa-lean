//! Bare-metal firmware for the instruction-count runs (bench/emu/run.sh). `run(sel)` verifies one signature and returns 1 if it
//! verified. `sel` = set * 10 + path: set 44, 65 or 87; path 0 = scalar (`verify_internal`), 1 = 4-way (`verify_internal_x4`),
//! 2 = one-shot API (`api::verify_NN`), 3 = prepare the key (4-way, `verifying_key_NN`), 4 = prepared verify. The key for path 4
//! is built by the host side once per run (path 3 stores it in `VK`).
#![no_std]
#![no_main]
#![allow(static_mut_refs)]

use core::arch::global_asm;
use core::hint::black_box;
use ml_dsa_lean::api;
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87};
use ml_dsa_lean::verify::{verify_internal, verify_internal_x4};

include!("../../data.rs");

/// M′ = 0x00 || len(ctx) || M for an empty context (Algorithm 3, pure ML-DSA).
static PFX: [u8; 2] = [0, 0];

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// Vector table (SP, reset) for thumbv7em; RISC-V gets its own entry below.
#[cfg(target_arch = "arm")]
global_asm!(
    ".section .vectors,\"a\"",
    ".word _stack_top",
    ".word _reset + 1",
    ".section .text._reset,\"ax\"",
    ".thumb_func",
    ".global _reset",
    "_reset:",
    "ldr r0, =_stack_top",
    "mov sp, r0",
    "bl main_loop",
    "bkpt #0",
);
#[cfg(target_arch = "riscv32")]
global_asm!(
    ".section .text._reset,\"ax\"",
    ".global _reset",
    "_reset:",
    "la sp, _stack_top",
    "call main_loop",
    "ebreak",
);

static mut VK44: Option<api::VerifyingKey44> = None;
static mut VK65: Option<api::VerifyingKey65> = None;
static mut VK87: Option<api::VerifyingKey87> = None;
#[unsafe(no_mangle)]
pub static mut SEL: u32 = 0;
#[unsafe(no_mangle)]
pub static mut RESULT: u32 = 0;

#[unsafe(no_mangle)]
pub extern "C" fn main_loop() {
    unsafe {
        RESULT = run(black_box(SEL)) as u32;
    }
}

#[inline(never)]
fn run(sel: u32) -> bool {
    let msg = black_box(&MSG[..]);
    unsafe {
        match sel {
            440 => verify_internal::<4, 4>(&ML_DSA_44, &PK44, &PFX, msg, &SIG44),
            441 => verify_internal_x4::<4, 4>(&ML_DSA_44, &PK44, &PFX, msg, &SIG44),
            442 => api::verify_44(&PK44, msg, &[], &SIG44),
            443 => {
                VK44 = Some(api::verifying_key_44(&PK44));
                true
            }
            444 => api::verify_prepared_44(VK44.as_ref().unwrap(), msg, &[], &SIG44),
            650 => verify_internal::<6, 5>(&ML_DSA_65, &PK65, &PFX, msg, &SIG65),
            651 => verify_internal_x4::<6, 5>(&ML_DSA_65, &PK65, &PFX, msg, &SIG65),
            652 => api::verify_65(&PK65, msg, &[], &SIG65),
            653 => {
                VK65 = Some(api::verifying_key_65(&PK65));
                true
            }
            654 => api::verify_prepared_65(VK65.as_ref().unwrap(), msg, &[], &SIG65),
            870 => verify_internal::<8, 7>(&ML_DSA_87, &PK87, &PFX, msg, &SIG87),
            871 => verify_internal_x4::<8, 7>(&ML_DSA_87, &PK87, &PFX, msg, &SIG87),
            872 => api::verify_87(&PK87, msg, &[], &SIG87),
            873 => {
                VK87 = Some(api::verifying_key_87(&PK87));
                true
            }
            874 => api::verify_prepared_87(VK87.as_ref().unwrap(), msg, &[], &SIG87),
            _ => false,
        }
    }
}
