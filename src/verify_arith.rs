//! Verify-only arithmetic on public data: the fused multiply-accumulate row for `Â ∘ NTT(z) − NTT(c) ∘ NTT(t1 · 2^d)`
//! and the lazy-reduction NTT. Each is proved to compute exactly what the shared constant-time functions of `ntt.rs`
//! compute (`Proofs/VerifyArith.lean`) and is called only on verify's path; signing and key generation keep the shared
//! functions. They are plain integer code: no intrinsics, no `unsafe`. Where the build has the AVX2 dispatch they are
//! `#[inline(always)]` so that they are compiled inside the `#[target_feature(enable = "avx2")]` verify wrapper
//! (`fast_verify/dispatch.rs`), where LLVM vectorizes them.

use crate::field::{mont_reduce, small_reduce, Q};

/// 2^64 mod q.
const R2: u64 = 2_365_951;
/// q².
const QQ: u64 = (Q as u64) * (Q as u64);

/// `Σ_l a_l ∘ z_l − c ∘ t` for one row, coefficient by coefficient (`a_l` and `z_l` are the row of Â and the entries of
/// NTT(z)), with the products summed before the Montgomery reduction: `q² − c·t` stands for `−c·t`, and the sum of
/// `L + 1` products below `q²` is below `2^32·q`, so two reductions finish it as in `field::mul_mont`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
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
