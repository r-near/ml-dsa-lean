//! Arithmetic in Z_q, q = 8380417, on canonical representatives `0 <= x < q`.
//! `small_reduce`/`barrett_reduce` keep the module-lattice 0.2.3 expressions (ARITH-02/03) with the
//! macro parameters substituted.

pub const Q: u32 = 8_380_417;
const BARRETT_SHIFT: u32 = 46; // 2 * (ilog2(Q) + 1)
const BARRETT_MULTIPLIER: u128 = (1u128 << BARRETT_SHIFT) / (Q as u128);

/// x - q if x >= q, else x. Requires x < 2q.
pub fn small_reduce(x: u32) -> u32 {
    let mask = 0u32.wrapping_sub((x >= Q) as u32);
    x - (Q & mask)
}

/// x mod q for x < q^2.
pub fn barrett_reduce(x: u64) -> u32 {
    let x = x as u128;
    let product = x * BARRETT_MULTIPLIER;
    let quotient = product >> BARRETT_SHIFT;
    let remainder = x - quotient * (Q as u128);
    small_reduce(remainder as u32)
}

pub fn add(a: u32, b: u32) -> u32 {
    small_reduce(a + b)
}
pub fn sub(a: u32, b: u32) -> u32 {
    small_reduce(a + Q - b)
}
pub fn neg(a: u32) -> u32 {
    small_reduce(Q - a)
}
pub fn mul(a: u32, b: u32) -> u32 {
    barrett_reduce((a as u64) * (b as u64))
}

/// Optimization barrier: the identity, but opaque to LLVM, so that the mask idioms below are not turned back
/// into branches on targets without a conditional move (checkct found this on riscv32imac; ISSUES.md CT-1).
/// Only RISC-V gets the barrier: x86_64 and thumbv7em check clean without it, and `black_box` costs about 25%
/// in signing there. Extraction runs with `--cfg miri`, so the extracted (proved) code is the plain identity;
/// the compiled code differs from it only by `core::hint::black_box`, which is the identity on values.
#[cfg(all(not(miri), any(target_arch = "riscv32", target_arch = "riscv64")))]
fn barrier_u64(x: u64) -> u64 {
    core::hint::black_box(x)
}
#[cfg(any(miri, not(any(target_arch = "riscv32", target_arch = "riscv64"))))]
fn barrier_u64(x: u64) -> u64 {
    x
}
#[cfg(all(not(miri), any(target_arch = "riscv32", target_arch = "riscv64")))]
fn barrier_u32(x: u32) -> u32 {
    core::hint::black_box(x)
}
#[cfg(any(miri, not(any(target_arch = "riscv32", target_arch = "riscv64"))))]
fn barrier_u32(x: u32) -> u32 {
    x
}

/// All-ones if `a < b`, else zero. Requires a, b < 2^63.
pub fn ct_lt_mask(a: u64, b: u64) -> u64 {
    0u64.wrapping_sub(barrier_u64(a.wrapping_sub(b) >> 63))
}
/// `if_true` where `mask` is all-ones, `if_false` where it is zero.
pub fn ct_select(if_false: u32, if_true: u32, mask: u32) -> u32 {
    if_false ^ ((if_false ^ if_true) & barrier_u32(mask))
}
