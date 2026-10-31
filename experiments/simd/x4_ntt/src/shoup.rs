//! Variant S: canonical in, canonical out. The butterfly multiplies by a fixed zeta with Shoup's trick:
//! with zp = floor(z * 2^32 / q) precomputed, `hi = (x * zp) >> 32` and `r = x*z - hi*q` (mod 2^32) is exactly
//! x*z mod q up to one extra q, for any x < 2^32 and z < q. Needs a second table (`ZETAS_SHOUP`); only 32 x 32 -> 64
//! multiplies, no u128. The statement of each butterfly is unchanged.

use crate::fold::{add, small_reduce, sub, Q};
use crate::ntt::ZETAS;
use crate::tables::{F_SHOUP, ZETAS_NEG_SHOUP, ZETAS_SHOUP};

/// x*z mod q for x < 2^32, z < q, zp = floor(z*2^32/q).
#[inline(always)]
pub fn mul_shoup(z: u32, zp: u32, x: u32) -> u32 {
    let hi = (((x as u64) * (zp as u64)) >> 32) as u32;
    let r = z.wrapping_mul(x).wrapping_sub(hi.wrapping_mul(Q)); // in [0, 2q)
    small_reduce(r)
}

#[inline(always)]
pub fn ntt_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let z = ZETAS[*m];
        let zp = ZETAS_SHOUP[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = mul_shoup(z, zp, w[j + LEN]);
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
        let zp = ZETAS_NEG_SHOUP[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = w[j];
            w[j] = add(t, w[j + LEN]);
            w[j + LEN] = mul_shoup(z, zp, sub(t, w[j + LEN]));
            j += 1;
        }
        i += 1;
    }
}

// ---- Loop-shape rewrites of the three narrow layers (LEN = 4, 2, 1), same butterflies in the same order of zetas.
// In the crate's shape the inner loop has only LEN iterations, below the vector width; indexing by the *block* makes
// the zeta index the loop counter and gives LLVM contiguous / interleaved accesses to vectorize.

#[inline(always)]
pub fn layer1_blocks(w: &mut [u32; 256]) {
    let mut k = 0;
    while k < 128 {
        let z = ZETAS[128 + k];
        let zp = ZETAS_SHOUP[128 + k];
        let t = mul_shoup(z, zp, w[2 * k + 1]);
        w[2 * k + 1] = sub(w[2 * k], t);
        w[2 * k] = add(w[2 * k], t);
        k += 1;
    }
}

#[inline(always)]
pub fn layer2_blocks(w: &mut [u32; 256]) {
    let mut g = 0;
    while g < 64 {
        let z = ZETAS[64 + g];
        let zp = ZETAS_SHOUP[64 + g];
        let b = 4 * g;
        let t0 = mul_shoup(z, zp, w[b + 2]);
        let t1 = mul_shoup(z, zp, w[b + 3]);
        w[b + 2] = sub(w[b], t0);
        w[b + 3] = sub(w[b + 1], t1);
        w[b] = add(w[b], t0);
        w[b + 1] = add(w[b + 1], t1);
        g += 1;
    }
}

#[inline(always)]
pub fn layer4_blocks(w: &mut [u32; 256]) {
    let mut g = 0;
    while g < 32 {
        let z = ZETAS[32 + g];
        let zp = ZETAS_SHOUP[32 + g];
        let b = 8 * g;
        let t0 = mul_shoup(z, zp, w[b + 4]);
        let t1 = mul_shoup(z, zp, w[b + 5]);
        let t2 = mul_shoup(z, zp, w[b + 6]);
        let t3 = mul_shoup(z, zp, w[b + 7]);
        w[b + 4] = sub(w[b], t0);
        w[b + 5] = sub(w[b + 1], t1);
        w[b + 6] = sub(w[b + 2], t2);
        w[b + 7] = sub(w[b + 3], t3);
        w[b] = add(w[b], t0);
        w[b + 1] = add(w[b + 1], t1);
        w[b + 2] = add(w[b + 2], t2);
        w[b + 3] = add(w[b + 3], t3);
        g += 1;
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

/// Same transform with the three narrow layers in block-indexed shape.
#[inline(always)]
pub fn ntt_blocks_body(w: &[u32; 256]) -> [u32; 256] {
    let mut w = *w;
    let mut m = 0;
    ntt_layer::<128, 1>(&mut w, &mut m);
    ntt_layer::<64, 2>(&mut w, &mut m);
    ntt_layer::<32, 4>(&mut w, &mut m);
    ntt_layer::<16, 8>(&mut w, &mut m);
    ntt_layer::<8, 16>(&mut w, &mut m);
    layer4_blocks(&mut w);
    layer2_blocks(&mut w);
    layer1_blocks(&mut w);
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
        w[j] = mul_shoup(f, F_SHOUP, w[j]);
        j += 1;
    }
    w
}

pub fn ntt(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
pub fn ntt_blocks(w: &[u32; 256]) -> [u32; 256] {
    ntt_blocks_body(w)
}
pub fn ntt_inverse(w: &[u32; 256]) -> [u32; 256] {
    ntt_inverse_body(w)
}
#[target_feature(enable = "avx2")]
pub fn ntt_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_body(w)
}
#[target_feature(enable = "avx2")]
pub fn ntt_blocks_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_blocks_body(w)
}
#[target_feature(enable = "avx2")]
pub fn ntt_inverse_avx2(w: &[u32; 256]) -> [u32; 256] {
    ntt_inverse_body(w)
}

/// Single layers (forward, crate shape) for the micro-benchmark; `M0` is the value of `m` before the layer.
#[inline(always)]
pub fn layer<const LEN: usize, const ITERATIONS: usize, const M0: usize>(w: &mut [u32; 256]) {
    let mut m = M0;
    ntt_layer::<LEN, ITERATIONS>(w, &mut m);
}
