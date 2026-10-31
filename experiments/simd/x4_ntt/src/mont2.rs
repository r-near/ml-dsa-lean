//! Variant M: canonical pointwise product of two variable operands with two unsigned Montgomery reductions
//! (R = 2^32): `p = a*b/R in [0, 2q)`, then `p*R2/R = a*b` (R2 = 2^64 mod q), then one conditional subtract.
//! For a, b < q: exactly `a*b mod q`. Only 32 x 32 -> 64 multiplies.

use crate::fold::{small_reduce, Q};
use crate::tables::R2;

const QNEG: u32 = 4_236_238_847; // -q^-1 mod 2^32 = 2^32 - 58_728_449

/// a * 2^-32 mod q, in [0, 2q), for a < 2^32 * q.
#[inline(always)]
pub fn mont_u(a: u64) -> u32 {
    let m = (a as u32).wrapping_mul(QNEG);
    ((a + (m as u64) * (Q as u64)) >> 32) as u32
}

/// a*b mod q for a, b < q.
#[inline(always)]
pub fn mul(a: u32, b: u32) -> u32 {
    let p = mont_u((a as u64) * (b as u64)); // a*b/R in [0, 2q)
    small_reduce(mont_u((p as u64) * R2)) // a*b
}

#[inline(always)]
pub fn multiply_ntt_body(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    let mut c = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        c[i] = mul(a[i], b[i]);
        i += 1;
    }
    c
}
pub fn multiply_ntt(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    multiply_ntt_body(a, b)
}
#[target_feature(enable = "avx2")]
pub fn multiply_ntt_avx2(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    multiply_ntt_body(a, b)
}
