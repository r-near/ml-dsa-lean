//! Arithmetic in Z_q, q = 8380417, on canonical representatives `0 <= x < q`.
//! `small_reduce`/`barrett_reduce` keep the module-lattice 0.2.3 expressions (ARITH-02/03) with the
//! macro parameters substituted. The NTT hot paths use `mul_shoup` (fixed twiddle) and `mul_mont` (two variable
//! operands), which need only 32 x 32 -> 64 bit multiplies and so vectorize; `mul` (Barrett, one u64 x u128
//! multiply) is the reference they are tested against.

pub const Q: u32 = 8_380_417;
const BARRETT_SHIFT: u32 = 46; // 2 * (ilog2(Q) + 1)
const BARRETT_MULTIPLIER: u128 = (1u128 << BARRETT_SHIFT) / (Q as u128);

// The functions the NTT bodies call are `#[inline(always)]` on x86_64 builds that have the runtime AVX2 dispatch (see
// `ntt.rs`, `dispatch`), so that the AVX2 compilation of a body contains them: LLVM only inlines a callee into a
// `#[target_feature]` function when it is allowed to, and an out-of-line copy would be compiled without AVX2. Other
// targets keep ordinary inlining: forcing it crate-wide changed the code shape enough that BINSEC no longer finished the
// riscv32imac `response`/`hint_step` probes within an hour (they were `secure` before).

// Overflow checks (nearcore builds with `overflow-checks = true`): every `+ - *` on a possibly secret value is a
// branch to a panic, and BINSEC cannot decide those guards on secret data (checkct/README.md). The operations below are
// `wrapping_*` wherever the proofs (lean/Proofs/Field.lean, FieldFast.lean) already show that the exact result fits,
// so the wrapping result is the exact one and the compiled code has no guard.

/// x - q if x >= q, else x. Requires x < 2q.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn small_reduce(x: u32) -> u32 {
    let mask = 0u32.wrapping_sub((x >= Q) as u32);
    x.wrapping_sub(Q & mask)
}

/// x mod q for x < q^2.
pub fn barrett_reduce(x: u64) -> u32 {
    let x = x as u128;
    let product = x.wrapping_mul(BARRETT_MULTIPLIER);
    let quotient = product >> BARRETT_SHIFT;
    let remainder = x.wrapping_sub(quotient.wrapping_mul(Q as u128));
    small_reduce(remainder as u32)
}

#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn add(a: u32, b: u32) -> u32 {
    small_reduce(a.wrapping_add(b))
}
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn sub(a: u32, b: u32) -> u32 {
    small_reduce(a.wrapping_add(Q).wrapping_sub(b))
}
pub fn neg(a: u32) -> u32 {
    small_reduce(Q.wrapping_sub(a))
}
/// Reference product. The NTT code uses `mul_shoup` and `mul_mont`; this one has no vector instruction (the u128
/// multiply), so it is kept as the specification the fast products are tested against.
#[allow(dead_code)]
pub fn mul(a: u32, b: u32) -> u32 {
    barrett_reduce((a as u64) * (b as u64))
}

/// Shoup multiplication: `z * x mod q` for a fixed `z < q`, its companion `zp = floor(z * 2^32 / q)` and any `x`.
/// With `hi = floor(x * zp / 2^32)` the exact quotient satisfies `hi <= floor(z * x / q) <= hi + 1`, so
/// `z * x - hi * q` lies in `[0, 2q)` and fits in a u32; the wrapping u32 arithmetic below computes it exactly. One
/// `small_reduce` (a mask in the source; that the compiled code has no branch is a per-target BINSEC result,
/// see checkct/README.md and ISSUES.md CT-1) finishes. Only 32 x 32 -> 64 multiplies.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn mul_shoup(z: u32, zp: u32, x: u32) -> u32 {
    let hi = (((x as u64) * (zp as u64)) >> 32) as u32;
    small_reduce(z.wrapping_mul(x).wrapping_sub(hi.wrapping_mul(Q)))
}

/// -q^-1 mod 2^32.
const QNEG: u32 = 4_236_238_847;
/// 2^64 mod q.
const R2: u64 = 2_365_951;

/// Montgomery reduction with R = 2^32: `a * 2^-32 mod q`, in `[0, 2q)`, for `a < 2^32 * q`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn mont_reduce(a: u64) -> u32 {
    let m = (a as u32).wrapping_mul(QNEG);
    (a.wrapping_add((m as u64).wrapping_mul(Q as u64)) >> 32) as u32
}

/// `a * b mod q` for canonical `a`, `b`, with two Montgomery reductions: the first leaves `a * b * 2^-32`, the second
/// multiplies by `2^64 mod q` to cancel it. Only 32 x 32 -> 64 multiplies.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64", not(target_feature = "avx2")), inline(always))]
pub fn mul_mont(a: u32, b: u32) -> u32 {
    let p = mont_reduce((a as u64) * (b as u64));
    small_reduce(mont_reduce((p as u64) * R2))
}

/// Optimization barrier: the identity, but opaque to LLVM, so that the mask idioms below are not turned back
/// into branches on targets without a conditional move (checkct found this on riscv32imac; ISSUES.md CT-1).
/// Only RISC-V gets it on every mask: the mask idioms check clean on x86_64 and thumbv7em without it (the one
/// exception, `decompose`'s edge mask, uses `opaque_u32` below), and `black_box` on every mask costs about 25% in
/// signing there. Extraction runs with `--cfg miri`, so the extracted (proved) code is the plain identity;
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

/// Optimization barrier on every target (unlike `barrier_u32`, which is RISC-V only). Used where LLVM turns a mask
/// select into a branch on x86_64 because one arm is a multiply (`decompose`'s edge case, checkct hint_step probes;
/// ISSUES.md CT-1). Like `barrier_u32` it is the identity under `cfg(miri)`, so the extracted (proved) code is the
/// plain identity.
#[cfg(not(miri))]
pub fn opaque_u32(x: u32) -> u32 {
    core::hint::black_box(x)
}
#[cfg(miri)]
pub fn opaque_u32(x: u32) -> u32 {
    x
}
