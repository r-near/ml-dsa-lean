// Included (via `include!`) into `kernel_shim` and `kernel_real` (see lib.rs): the SAME source is compiled against the
// shims and against the real intrinsics, which is SymCrypt's "single-body cfg-swap redirect". The including module
// brings `M256` and the operations below into scope.
//
// Lazy forward NTT on signed Montgomery arithmetic (the `lazy` variant of x4_ntt), 8 coefficients per register.
// Coefficients are i32 bit patterns held in u32 lanes.

use crate::tables::{QINV, ZETAS_MONT};

const Q: u32 = 8_380_417;

/// Lane-wise `lazy::mont(z * b)` for a broadcast zeta `z` and `zq = z * QINV mod 2^32` (also broadcast): signed
/// Montgomery product z*b*2^-32 in (-(q/2 + |zb|/2^32), +...). Only even-lane 32 x 32 -> 64 multiplies exist, so the odd
/// lanes are moved down with `shuffle_epi32` and the results merged with `blend_epi32`.
#[inline(always)]
pub fn montmul(b: M256, z: M256, zq: M256, q: M256) -> M256 {
    let b_odd = shuffle_epi32::<0xF5>(b);
    let pe = mul_epi32(z, b);
    let po = mul_epi32(z, b_odd);
    let me = mul_epi32(zq, b); // low dword = (z*QINV*b) mod 2^32, the Montgomery quotient
    let mo = mul_epi32(zq, b_odd);
    let qe = mul_epi32(me, q);
    let qo = mul_epi32(mo, q);
    let re = srli_epi64::<32>(sub_epi32(pe, qe)); // low dwords cancel, so the dword subtract is exact
    let ro = sub_epi32(po, qo);
    blend_epi32::<0xAA>(re, ro)
}

#[inline(always)]
fn zeta_vecs(zc: i32) -> (M256, M256) {
    (set1_epi32(zc as u32), set1_epi32(zc.wrapping_mul(QINV) as u32))
}

/// Layers with LEN >= 8: whole registers, butterfly between register j and register j + LEN.
#[inline(always)]
pub fn layer_wide<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let q = set1_epi32(Q);
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let (z, zq) = zeta_vecs(ZETAS_MONT[*m]);
        let mut j = start;
        while j < start + LEN {
            let a = loadu_si256(w, j);
            let b = loadu_si256(w, j + LEN);
            let t = montmul(b, z, zq, q);
            storeu_si256(w, j + LEN, sub_epi32(a, t));
            storeu_si256(w, j, add_epi32(a, t));
            j += 8;
        }
        i += 1;
    }
}

/// LEN = 4: one block per register; partner halves are brought together with `permute2x128`.
#[inline(always)]
pub fn layer4(w: &mut [u32; 256], m: &mut usize) {
    let q = set1_epi32(Q);
    let mut g = 0;
    while g < 32 {
        *m += 1;
        let (z, zq) = zeta_vecs(ZETAS_MONT[*m]);
        let v = loadu_si256(w, 8 * g);
        let ae = permute2x128_si256::<0x00>(v, v);
        let bo = permute2x128_si256::<0x11>(v, v);
        let t = montmul(bo, z, zq, q);
        storeu_si256(w, 8 * g, blend_epi32::<0xF0>(add_epi32(ae, t), sub_epi32(ae, t)));
        g += 1;
    }
}

/// LEN = 2: two blocks per register (one per 128-bit half, each with its own zeta).
#[inline(always)]
pub fn layer2(w: &mut [u32; 256], m: &mut usize) {
    let q = set1_epi32(Q);
    let mut h = 0;
    while h < 32 {
        let z0 = ZETAS_MONT[*m + 1];
        let z1 = ZETAS_MONT[*m + 2];
        *m += 2;
        let (za, zqa) = zeta_vecs(z0);
        let (zb, zqb) = zeta_vecs(z1);
        let z = blend_epi32::<0xF0>(za, zb);
        let zq = blend_epi32::<0xF0>(zqa, zqb);
        let v = loadu_si256(w, 8 * h);
        let ae = shuffle_epi32::<0x44>(v);
        let bo = shuffle_epi32::<0xEE>(v);
        let t = montmul(bo, z, zq, q);
        storeu_si256(w, 8 * h, blend_epi32::<0xCC>(add_epi32(ae, t), sub_epi32(ae, t)));
        h += 1;
    }
}

/// LEN = 1: four blocks per register, one zeta per pair of lanes.
#[inline(always)]
pub fn layer1(w: &mut [u32; 256], m: &mut usize) {
    let q = set1_epi32(Q);
    let mut h = 0;
    while h < 32 {
        let z0 = ZETAS_MONT[*m + 1];
        let z1 = ZETAS_MONT[*m + 2];
        let z2 = ZETAS_MONT[*m + 3];
        let z3 = ZETAS_MONT[*m + 4];
        *m += 4;
        let z = setr_epi32(z0 as u32, z0 as u32, z1 as u32, z1 as u32, z2 as u32, z2 as u32, z3 as u32, z3 as u32);
        let zq = setr_epi32(
            z0.wrapping_mul(QINV) as u32,
            z0.wrapping_mul(QINV) as u32,
            z1.wrapping_mul(QINV) as u32,
            z1.wrapping_mul(QINV) as u32,
            z2.wrapping_mul(QINV) as u32,
            z2.wrapping_mul(QINV) as u32,
            z3.wrapping_mul(QINV) as u32,
            z3.wrapping_mul(QINV) as u32,
        );
        let v = loadu_si256(w, 8 * h);
        let ae = shuffle_epi32::<0xA0>(v);
        let bo = shuffle_epi32::<0xF5>(v);
        let t = montmul(bo, z, zq, q);
        storeu_si256(w, 8 * h, blend_epi32::<0xAA>(add_epi32(ae, t), sub_epi32(ae, t)));
        h += 1;
    }
}

/// The whole lazy forward transform (no normalization): all eight layers.
#[inline(always)]
pub fn ntt_lazy_vec(w: &mut [u32; 256]) {
    let mut m = 0;
    layer_wide::<128, 1>(w, &mut m);
    layer_wide::<64, 2>(w, &mut m);
    layer_wide::<32, 4>(w, &mut m);
    layer_wide::<16, 8>(w, &mut m);
    layer_wide::<8, 16>(w, &mut m);
    layer4(w, &mut m);
    layer2(w, &mut m);
    layer1(w, &mut m);
}

/// [0, q) representative of the lazy value x, for |x| <= 2^30 (copy of `lazy::normalize_one` in x4_ntt).
#[inline(always)]
pub fn normalize_one(x: i32) -> u32 {
    let t = (x + (1 << 22)) >> 23;
    let r = x - t * (Q as i32);
    (r + ((r >> 31) & (Q as i32))) as u32
}

/// Canonical in, canonical out: transform, then normalize with the scalar routine (LLVM vectorizes that loop).
#[inline(always)]
pub fn ntt_vec(w: &[u32; 256]) -> [u32; 256] {
    let mut a = *w;
    ntt_lazy_vec(&mut a);
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = normalize_one(a[j] as i32);
        j += 1;
    }
    out
}
