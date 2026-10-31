//! Variant F: canonical in, canonical out, exactly the crate's `ntt.rs` structure; only the modular multiply changes.
//! `barrett_reduce` (u64 -> u128 multiply) is replaced by folding with 2^23 = q + (2^13 - 1), i.e. 2^23 == 2^13 - 1
//! (mod q). Everything is u64 shifts, masks, adds and one multiply by the constant 8191 (LLVM emits shift and
//! subtract). The statement is unchanged: for x < q^2, `fold_reduce x == x % q`.
//! All helpers are `#[inline(always)]` so the body can be compiled twice (portable and `target_feature = "avx2"`).

pub const Q: u32 = 8_380_417;

#[inline(always)]
pub fn small_reduce(x: u32) -> u32 {
    let mask = 0u32.wrapping_sub((x >= Q) as u32);
    x - (Q & mask)
}

/// x mod q for x < q^2 (< 2^46).
#[inline(always)]
pub fn fold_reduce(x: u64) -> u32 {
    let y = (x & 0x7F_FFFF) + (x >> 23) * 8191; // x < 2^46 -> y < 2^36
    let y = (y & 0x7F_FFFF) + (y >> 23) * 8191; // y >> 23 <= 8191 -> y < 75_481_088
    let y = (y & 0x7F_FFFF) + (y >> 23) * 8191; // y >> 23 <= 8 -> y <= 8_454_135 < 2q
    small_reduce(y as u32)
}

#[inline(always)]
pub fn add(a: u32, b: u32) -> u32 {
    small_reduce(a + b)
}
#[inline(always)]
pub fn sub(a: u32, b: u32) -> u32 {
    small_reduce(a + Q - b)
}
#[inline(always)]
pub fn mul(a: u32, b: u32) -> u32 {
    fold_reduce((a as u64) * (b as u64))
}

use crate::ntt::ZETAS;

#[inline(always)]
pub fn ntt_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let z = ZETAS[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = mul(z, w[j + LEN]);
            w[j + LEN] = sub(w[j], t);
            w[j] = add(w[j], t);
            j += 1;
        }
        i += 1;
    }
}

#[inline(always)]
pub fn ntt_inverse_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m -= 1;
        let z = sub(0, ZETAS[*m]);
        let mut j = start;
        while j < (start + LEN) {
            let t = w[j];
            w[j] = add(t, w[j + LEN]);
            w[j + LEN] = mul(z, sub(t, w[j + LEN]));
            j += 1;
        }
        i += 1;
    }
}

#[inline(always)]
pub fn ntt_body(w: &[u32; 256]) -> [u32; 256] {
    let mut w = *w;
    let mut m = 0;
    ntt_layer::<128, 1>(&mut w, &mut m);
    ntt_layer::<64, 2>(&mut w, &mut m);
    ntt_layer::<32, 4>(&mut w, &mut m);
    ntt_layer::<16, 8>(&mut w, &mut m);
    ntt_layer::<8, 16>(&mut w, &mut m);
    ntt_layer::<4, 32>(&mut w, &mut m);
    ntt_layer::<2, 64>(&mut w, &mut m);
    ntt_layer::<1, 128>(&mut w, &mut m);
    w
}

#[inline(always)]
pub fn ntt_inverse_body(w_hat: &[u32; 256]) -> [u32; 256] {
    let mut w = *w_hat;
    let mut m = 256;
    ntt_inverse_layer::<1, 128>(&mut w, &mut m);
    ntt_inverse_layer::<2, 64>(&mut w, &mut m);
    ntt_inverse_layer::<4, 32>(&mut w, &mut m);
    ntt_inverse_layer::<8, 16>(&mut w, &mut m);
    ntt_inverse_layer::<16, 8>(&mut w, &mut m);
    ntt_inverse_layer::<32, 4>(&mut w, &mut m);
    ntt_inverse_layer::<64, 2>(&mut w, &mut m);
    ntt_inverse_layer::<128, 1>(&mut w, &mut m);
    let f = 8_347_681; // 256^-1 mod q
    let mut j = 0;
    while j < 256 {
        w[j] = mul(f, w[j]);
        j += 1;
    }
    w
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

pub fn ntt(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
pub fn ntt_inverse(w: &[u32; 256]) -> [u32; 256] {
    ntt_inverse_body(w)
}
pub fn multiply_ntt(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    multiply_ntt_body(a, b)
}

/// Single layers for the micro-benchmark (LEN = 128: one block of 128 butterflies; LEN = 16; LEN = 4).
pub fn layer128(w: &mut [u32; 256]) {
    let mut m = 0;
    ntt_layer::<128, 1>(w, &mut m);
}
pub fn layer16(w: &mut [u32; 256]) {
    let mut m = 7;
    ntt_layer::<16, 8>(w, &mut m);
}
pub fn layer4(w: &mut [u32; 256]) {
    let mut m = 31;
    ntt_layer::<4, 32>(w, &mut m);
}

#[target_feature(enable = "avx2")]
pub fn ntt_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
#[target_feature(enable = "avx2")]
pub fn ntt_inverse_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_inverse_body(w)
}
#[target_feature(enable = "avx2")]
pub fn multiply_ntt_avx2(a: &[u32; 256], b: &[u32; 256]) -> [u32; 256] {
    multiply_ntt_body(a, b)
}

/// Single layer for the micro-benchmark; `M0` is the value of `m` before the layer.
#[inline(always)]
pub fn layer<const LEN: usize, const ITERATIONS: usize, const M0: usize>(w: &mut [u32; 256]) {
    let mut m = M0;
    ntt_layer::<LEN, ITERATIONS>(w, &mut m);
}
