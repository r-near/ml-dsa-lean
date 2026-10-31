//! Algorithm 8 ML-DSA.Verify_internal(pk, M′, σ). Step numbers refer to FIPS 204.

use crate::encode::{pk_decode, sig_decode, w1_encode};
use crate::keccak::Shake;
use crate::ntt::{matrix_vector_ntt, multiply_ntt, ntt, ntt_inverse, ntt_vec, sub_poly};
use crate::params::{pk_len, sig_len, Params};
use crate::rounding::{poly_use_hint, vec_infinity_norm};
use crate::sampling::{expand_a, sample_in_ball};

/// t1 · 2^d with d = 13, coefficient-wise. Every t1 coefficient is a 10-bit value (pkDecode), so
/// t1 ≤ 2^10 − 1 and t1 · 2^13 ≤ 8380416 = q − 1: no u32 overflow and the result is canonical.
fn scale_by_2d(t1: &[u32; 256]) -> [u32; 256] {
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = t1[j] << 13;
        j += 1;
    }
    out
}

/// scale_by_2d applied to every entry of a vector.
fn scale_vec_by_2d<const N: usize>(t1: &[[u32; 256]; N]) -> [[u32; 256]; N] {
    let mut out = [[0u32; 256]; N];
    let mut i = 0;
    while i < N {
        out[i] = scale_by_2d(&t1[i]);
        i += 1;
    }
    out
}

/// Constant-shape equality of the first `len` bytes of two 64-byte buffers (`len` ≤ 64).
pub(crate) fn prefix_eq(a: &[u8; 64], b: &[u8; 64], len: usize) -> bool {
    let mut diff = 0u8;
    let mut i = 0;
    while i < len {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff == 0
}

/// The part of Algorithm 8 that depends on the public key alone: Â (step 6), tr (step 7) and
/// NTT(t1 · 2^d) (the key-dependent half of step 10). Verifying many signatures against one key computes it
/// once. The fields are private to the crate; the `api` module wraps this type per parameter set.
///
/// Size: (K·L + K) KiB + 64 bytes (20,544 / 36,928 / 65,600 bytes for ML-DSA-44 / 65 / 87).
#[derive(Clone)]
pub struct PreparedVk<const K: usize, const L: usize> {
    /// Â ← ExpandA(ρ), NTT domain.
    pub(crate) a_hat: [[[u32; 256]; L]; K],
    /// NTT(t1 · 2^d), one polynomial per row.
    pub(crate) t1_2d_hat: [[u32; 256]; K],
    /// tr ← H(pk, 64).
    pub(crate) tr: [u8; 64],
}

/// Steps 1, 6, 7 and the key-dependent half of step 10 of Algorithm 8: (ρ, t1) ← pkDecode(pk);
/// Â ← ExpandA(ρ); tr ← H(pk, 64); NTT(t1 · 2^d).
///
/// Precondition: `pk.len() == 32 + 320 * K` (the decoder indexes by `K`). Diverges exactly where ExpandA does
/// (FIPS 204's rejection sampler has no bound).
pub(crate) fn prepare_vk<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    // 1: (ρ, t1) ← pkDecode(pk)
    let (rho, t1) = pk_decode::<K>(pk);
    // 6: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&rho);
    // 7: tr ← H(pk, 64)
    let mut tr = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(pk);
    hash.finalize();
    hash.squeeze(&mut tr);
    // 10 (key half): NTT(t1 · 2^d)
    let t1_2d_hat = ntt_vec(&scale_vec_by_2d(&t1));
    PreparedVk { a_hat, t1_2d_hat, tr }
}

/// Steps 8–13 of Algorithm 8 for a decoded signature (c̃, z, h) against a prepared key. Nothing here depends on
/// the key beyond `vk`.
///
/// Precondition: `p` is the parameter set matching `K` and `L`, and `c_tilde[..p.c_tilde_len]` is the
/// signature's c̃ (as returned by `sig_decode`).
fn verify_decoded<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    c_tilde: &[u8; 64],
    z: &[[u32; 256]; L],
    h: &[[bool; 256]; K],
) -> bool {
    // 8: μ ← H(BytesToBits(tr) ‖ M′, 64)
    let mut mu = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(&vk.tr);
    hash.absorb(m_prefix);
    hash.absorb(m);
    hash.finalize();
    hash.squeeze(&mut mu);
    // 9: c ← SampleInBall(c̃)
    let c = sample_in_ball(p, &c_tilde[..p.c_tilde_len]);
    // 10: w′_Approx ← NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t1 · 2^d))
    let az_hat = matrix_vector_ntt::<K, L>(&vk.a_hat, &ntt_vec(z));
    let c_hat = ntt(&c);
    let mut w_approx = [[0u32; 256]; K];
    let mut w1 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        let ct1_hat = multiply_ntt(&c_hat, &vk.t1_2d_hat[i]);
        w_approx[i] = ntt_inverse(&sub_poly(&az_hat[i], &ct1_hat));
        // 11: w′1 ← UseHint(h, w′_Approx)
        w1[i] = poly_use_hint(p, &h[i], &w_approx[i]);
        i += 1;
    }
    // 12: c̃′ ← H(μ ‖ w1Encode(w′1), λ/4)
    let mut w1_enc = [0u8; 8 * 192];
    w1_encode(p, &w1, &mut w1_enc);
    let mut c_tilde_prime = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(&mu);
    hash.absorb(&w1_enc[..K * 32 * p.w1_bits]);
    hash.finalize();
    hash.squeeze(&mut c_tilde_prime[..p.c_tilde_len]);
    // 13: return ‖z‖∞ < γ1 − β and c̃ = c̃′
    let norm_ok = vec_infinity_norm(z) < p.gamma1 - p.beta;
    let hash_ok = prefix_eq(c_tilde, &c_tilde_prime, p.c_tilde_len);
    norm_ok && hash_ok
}

/// Algorithm 8 ML-DSA.Verify_internal(pk, M′, σ) with M′ = `m_prefix` ‖ `m`. A `pk` whose length is not
/// `pk_len(p)` or a `sig` whose length is not `sig_len(p)` returns false. This is input validation consistent
/// with FIPS 204 (its pk and σ are byte strings of those lengths), not a numbered step.
///
/// Order: the signature is decoded (steps 2–5) before the per-key work (`prepare_vk`: steps 1, 6, 7), so a
/// malformed signature is rejected without running ExpandA, as in the algorithm. The result is the same as
/// `prepare_vk` followed by `verify_prepared_internal`.
///
/// Precondition: `p` is the parameter set matching `K` and `L` (`p.k == K`, `p.l == L`). The decoders index by
/// `K`/`L`, so an inconsistent `p` can panic. The `api` functions always pass a consistent `p`.
pub fn verify_internal<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    // Length guard: wrong-length pk/sig return false before any decoding.
    if pk.len() != pk_len(p) || sig.len() != sig_len(p) {
        return false;
    }
    // 2: (c̃, z, h) ← sigDecode(σ)
    // 3–5: if h = ⊥ then return false
    let (c_tilde, z, h) = match sig_decode::<K, L>(p, sig) {
        Some(parts) => parts,
        None => return false,
    };
    // 1, 6, 7, 10 (key half)
    let vk = prepare_vk::<K, L>(pk);
    // 8–13
    verify_decoded::<K, L>(p, &vk, m_prefix, m, &c_tilde, &z, &h)
}

/// Algorithm 8 against a prepared key: `verify_internal(p, pk, m_prefix, m, sig)` where `vk = prepare_vk(pk)`.
/// A `sig` whose length is not `sig_len(p)` returns false.
///
/// Precondition: `p` matches `K` and `L`, as for `verify_internal`.
pub fn verify_prepared_internal<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    if sig.len() != sig_len(p) {
        return false;
    }
    // 2–5
    let (c_tilde, z, h) = match sig_decode::<K, L>(p, sig) {
        Some(parts) => parts,
        None => return false,
    };
    // 8–13
    verify_decoded::<K, L>(p, vk, m_prefix, m, &c_tilde, &z, &h)
}

#[cfg(test)]
mod tests {
    use super::prefix_eq;

    #[test]
    fn prefix_eq_compares_exactly_len_bytes() {
        let mut a = [0u8; 64];
        for (i, b) in a.iter_mut().enumerate() {
            *b = i as u8 ^ 0x5a;
        }
        // Identical buffers are equal for every len.
        for len in [0, 32, 48, 64] {
            assert!(prefix_eq(&a, &a, len));
        }
        // λ/4 = 32, 48, 64 for ML-DSA-44/65/87.
        for len in [32usize, 48, 64] {
            // Differing only at index len - 1: unequal.
            let mut b = a;
            b[len - 1] ^= 1;
            assert!(!prefix_eq(&a, &b, len), "len {len}: last compared byte ignored");
            // Differing at the first byte: unequal.
            let mut c = a;
            c[0] ^= 0x80;
            assert!(!prefix_eq(&a, &c, len));
            // Differing only at indices >= len: equal.
            let mut d = a;
            for x in &mut d[len..] {
                *x ^= 0xff;
            }
            assert!(prefix_eq(&a, &d, len), "len {len}: bytes past len were compared");
        }
    }
}
