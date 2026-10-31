//! Variant L: lazy signed i32. Coefficients are signed and are NOT reduced after add/sub (|w| grows by less than
//! q/2 + q/64 per layer); the butterfly multiplies by the centered Montgomery form zeta*2^32 mod q with a signed
//! Montgomery reduction (no u128, one 32x32->64 multiply per product). `normalize` maps back to [0, q).
//! Contract change versus the crate: the intermediate state is "bounded and congruent", not canonical.

use crate::tables::{QINV, ZETAS_MONT};

pub const Q: i32 = 8_380_417;

/// Signed Montgomery reduction: a * 2^-32 mod q, in [-(|a|/2^32 + q/2), +(|a|/2^32 + q/2)], for |a| < 2^31 * q.
#[inline(always)]
pub fn mont(a: i64) -> i32 {
    let t = (a as i32).wrapping_mul(QINV);
    ((a - (t as i64) * (Q as i64)) >> 32) as i32
}

#[inline(always)]
pub fn ntt_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [i32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let z = ZETAS_MONT[*m] as i64;
        let mut j = start;
        while j < (start + LEN) {
            let t = mont(z * (w[j + LEN] as i64));
            w[j + LEN] = w[j] - t;
            w[j] = w[j] + t;
            j += 1;
        }
        i += 1;
    }
}

/// [0, q) representative of x, for |x| <= 2^30.
#[inline(always)]
pub fn normalize_one(x: i32) -> u32 {
    let t = (x + (1 << 22)) >> 23;
    let r = x - t * Q;
    (r + ((r >> 31) & Q)) as u32
}

#[inline(always)]
pub fn ntt_body(w: &[u32; 256]) -> [u32; 256] {
    let mut a = [0i32; 256];
    let mut j = 0;
    while j < 256 {
        a[j] = w[j] as i32; // canonical: 0 <= w < q
        j += 1;
    }
    let mut m = 0;
    ntt_layer::<128, 1>(&mut a, &mut m);
    ntt_layer::<64, 2>(&mut a, &mut m);
    ntt_layer::<32, 4>(&mut a, &mut m);
    ntt_layer::<16, 8>(&mut a, &mut m);
    ntt_layer::<8, 16>(&mut a, &mut m);
    ntt_layer::<4, 32>(&mut a, &mut m);
    ntt_layer::<2, 64>(&mut a, &mut m);
    ntt_layer::<1, 128>(&mut a, &mut m);
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = normalize_one(a[j]);
        j += 1;
    }
    out
}
/// The lazy transform alone (no normalize), for timing the layers.
#[inline(always)]
pub fn ntt_lazy_body(a: &mut [i32; 256]) {
    let mut m = 0;
    ntt_layer::<128, 1>(a, &mut m);
    ntt_layer::<64, 2>(a, &mut m);
    ntt_layer::<32, 4>(a, &mut m);
    ntt_layer::<16, 8>(a, &mut m);
    ntt_layer::<8, 16>(a, &mut m);
    ntt_layer::<4, 32>(a, &mut m);
    ntt_layer::<2, 64>(a, &mut m);
    ntt_layer::<1, 128>(a, &mut m);
}
pub fn ntt(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
pub fn ntt_lazy(a: &mut [i32; 256]) {
    ntt_lazy_body(a)
}
pub fn layer128(w: &mut [i32; 256]) {
    let mut m = 0;
    ntt_layer::<128, 1>(w, &mut m);
}
pub fn layer16(w: &mut [i32; 256]) {
    let mut m = 7;
    ntt_layer::<16, 8>(w, &mut m);
}
pub fn layer4(w: &mut [i32; 256]) {
    let mut m = 31;
    ntt_layer::<4, 32>(w, &mut m);
}
#[target_feature(enable = "avx2")]
pub fn ntt_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
#[target_feature(enable = "avx2")]
pub fn ntt_lazy_avx2(a: &mut [i32; 256]) {
    ntt_lazy_body(a)
}

/// Single layer for the micro-benchmark; `M0` is the value of `m` before the layer.
#[inline(always)]
pub fn layer<const LEN: usize, const ITERATIONS: usize, const M0: usize>(w: &mut [i32; 256]) {
    let mut m = M0;
    ntt_layer::<LEN, ITERATIONS>(w, &mut m);
}
