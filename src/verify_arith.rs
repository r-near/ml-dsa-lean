//! Verify-only arithmetic on public data: the fused multiply-accumulate row for `Â ∘ NTT(z) − NTT(c) ∘ NTT(t1 · 2^d)`
//! and the lazy-reduction NTT. Each is proved to compute exactly what the shared constant-time functions of `ntt.rs`
//! compute (`Proofs/VerifyArith.lean`) and is called only on verify's path; signing and key generation keep the shared
//! functions. They are plain integer code: no intrinsics, no `unsafe`. LLVM vectorizes them with
//! the target features of the build (SSE2 by default, 256-bit code with `-C target-feature=+avx2`); nothing at run time
//! chooses, and the compiled code computes the proved source either way.

use crate::field::{mont_reduce, mul_shoup, small_reduce, Q};
use crate::ntt::{F_SHOUP, ZETAS, ZETAS_NEG_SHOUP, ZETAS_SHOUP};

/// 2^64 mod q.
const R2: u64 = 2_365_951;
/// q².
const QQ: u64 = (Q as u64) * (Q as u64);

/// `Σ_l a_l ∘ z_l − c ∘ t` for one row, coefficient by coefficient (`a_l` and `z_l` are the row of Â and the entries of
/// NTT(z)), with the products summed before the Montgomery reduction: `q² − c·t` stands for `−c·t`, and the sum of
/// `L + 1` products below `q²` is below `2^32·q`, so two reductions finish it as in `field::mul_mont`.
pub fn mac_row_pub<const L: usize>(a: &[[u32; 256]; L], z: &[[u32; 256]; L], c: &[u32; 256], t: &[u32; 256]) -> [u32; 256] {
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        let mut s = QQ.wrapping_sub((c[j] as u64).wrapping_mul(t[j] as u64));
        let mut l = 0;
        while l < L {
            s = s.wrapping_add((a[l][j] as u64).wrapping_mul(z[l][j] as u64));
            l += 1;
        }
        let p = mont_reduce(s);
        out[j] = small_reduce(mont_reduce((p as u64).wrapping_mul(R2)));
        j += 1;
    }
    out
}

/// `z · x − floor(x · zp / 2^32) · q` for `zp = floor(z · 2^32 / q)`, `z < q` and any `x`: congruent to `z · x` mod q and
/// in `[0, 2q)` (the value `mul_shoup` reduces once more).
fn shoup_lazy(z: u32, zp: u32, x: u32) -> u32 {
    let hi = (((x as u64) * (zp as u64)) >> 32) as u32;
    z.wrapping_mul(x).wrapping_sub(hi.wrapping_mul(Q))
}

/// One NTT layer without reduction: entries grow by at most 2q per layer.
fn ntt_lazy_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let z = ZETAS[*m];
        let zp = ZETAS_SHOUP[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = shoup_lazy(z, zp, w[j + LEN]);
            let a = w[j];
            w[j + LEN] = a.wrapping_add(2 * Q).wrapping_sub(t);
            w[j] = a.wrapping_add(t);
            j += 1;
        }
        i += 1;
    }
}

/// `x mod q` for `x < 2^28`: `x − (x >> 23) · q` is in `[0, 2q)`.
fn reduce_lazy(x: u32) -> u32 {
    small_reduce(x.wrapping_sub((x >> 23).wrapping_mul(Q)))
}

/// Algorithm 41 NTT(w) for canonical `w`, in place, with one reduction at the end instead of one per butterfly.
pub fn ntt_pub_in_place(w: &mut [u32; 256]) {
    let mut m = 0;
    ntt_lazy_layer::<128, 1>(w, &mut m);
    ntt_lazy_layer::<64, 2>(w, &mut m);
    ntt_lazy_layer::<32, 4>(w, &mut m);
    ntt_lazy_layer::<16, 8>(w, &mut m);
    ntt_lazy_layer::<8, 16>(w, &mut m);
    ntt_lazy_layer::<4, 32>(w, &mut m);
    ntt_lazy_layer::<2, 64>(w, &mut m);
    ntt_lazy_layer::<1, 128>(w, &mut m);
    let mut j = 0;
    while j < 256 {
        w[j] = reduce_lazy(w[j]);
        j += 1;
    }
}

/// Algorithm 41 NTT(w) for canonical `w`.
pub fn ntt_pub(w: &[u32; 256]) -> [u32; 256] {
    let mut o = *w;
    ntt_pub_in_place(&mut o);
    o
}

/// `ntt_pub` on every entry of a vector.
pub fn ntt_vec_pub<const N: usize>(v: &[[u32; 256]; N]) -> [[u32; 256]; N] {
    let mut out = [[0u32; 256]; N];
    let mut i = 0;
    while i < N {
        out[i] = ntt_pub(&v[i]);
        i += 1;
    }
    out
}

/// One NTT⁻¹ layer without reduction; `b` bounds every entry of `w` on entry (`b ≥ q`), so `t + b − u` does not
/// underflow, and the entries on exit are below `2b`.
fn ntt_inverse_lazy_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize, b: u32) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m -= 1;
        let z = Q.wrapping_sub(ZETAS[*m]);
        let zp = ZETAS_NEG_SHOUP[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = w[j];
            let u = w[j + LEN];
            w[j] = t.wrapping_add(u);
            w[j + LEN] = shoup_lazy(z, zp, t.wrapping_add(b).wrapping_sub(u));
            j += 1;
        }
        i += 1;
    }
}

/// Algorithm 42 NTT⁻¹(ŵ) for canonical `ŵ`, in place: lazy layers and the 256⁻¹ scaling as the only reduction.
pub fn ntt_inverse_pub_in_place(w: &mut [u32; 256]) {
    let mut m = 256;
    ntt_inverse_lazy_layer::<1, 128>(w, &mut m, Q);
    ntt_inverse_lazy_layer::<2, 64>(w, &mut m, 2 * Q);
    ntt_inverse_lazy_layer::<4, 32>(w, &mut m, 4 * Q);
    ntt_inverse_lazy_layer::<8, 16>(w, &mut m, 8 * Q);
    ntt_inverse_lazy_layer::<16, 8>(w, &mut m, 16 * Q);
    ntt_inverse_lazy_layer::<32, 4>(w, &mut m, 32 * Q);
    ntt_inverse_lazy_layer::<64, 2>(w, &mut m, 64 * Q);
    ntt_inverse_lazy_layer::<128, 1>(w, &mut m, 128 * Q);
    let f = 8_347_681; // 256⁻¹ mod q
    let mut j = 0;
    while j < 256 {
        w[j] = mul_shoup(f, F_SHOUP, w[j]);
        j += 1;
    }
}

/// Algorithm 42 NTT⁻¹(ŵ) for canonical `ŵ`.
pub fn ntt_inverse_pub(w_hat: &[u32; 256]) -> [u32; 256] {
    let mut o = *w_hat;
    ntt_inverse_pub_in_place(&mut o);
    o
}
