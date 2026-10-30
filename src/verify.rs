//! Algorithm 8 ML-DSA.Verify_internal(pk, M′, σ). Step numbers refer to FIPS 204.

use crate::encode::{pk_decode, sig_decode, w1_encode};
use crate::keccak::Shake;
use crate::ntt::{matrix_vector_ntt, multiply_ntt, ntt, ntt_inverse, ntt_vec, sub_poly};
use crate::params::Params;
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
fn prefix_eq(a: &[u8; 64], b: &[u8; 64], len: usize) -> bool {
    let mut diff = 0u8;
    let mut i = 0;
    while i < len {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff == 0
}

/// Algorithm 8 ML-DSA.Verify_internal(pk, M′, σ) with M′ = `m_prefix` ‖ `m`. `pk` has 32 + 320·K bytes and
/// `sig` has `sig_len(p)` bytes.
pub fn verify_internal<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    // 1: (ρ, t1) ← pkDecode(pk)
    let (rho, t1) = pk_decode::<K>(pk);
    // 2: (c̃, z, h) ← sigDecode(σ)
    // 3–5: if h = ⊥ then return false
    let (c_tilde, z, h) = match sig_decode::<K, L>(p, sig) {
        Some(parts) => parts,
        None => return false,
    };
    // 6: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&rho);
    // 7: tr ← H(pk, 64)
    let mut tr = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(pk);
    hash.finalize();
    hash.squeeze(&mut tr);
    // 8: μ ← H(BytesToBits(tr) ‖ M′, 64)
    let mut mu = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(&tr);
    hash.absorb(m_prefix);
    hash.absorb(m);
    hash.finalize();
    hash.squeeze(&mut mu);
    // 9: c ← SampleInBall(c̃)
    let c = sample_in_ball(p, &c_tilde[..p.c_tilde_len]);
    // 10: w′_Approx ← NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t1 · 2^d))
    let az_hat = matrix_vector_ntt::<K, L>(&a_hat, &ntt_vec(&z));
    let c_hat = ntt(&c);
    let t1_2d_hat = ntt_vec(&scale_vec_by_2d(&t1));
    let mut w_approx = [[0u32; 256]; K];
    let mut w1 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        let ct1_hat = multiply_ntt(&c_hat, &t1_2d_hat[i]);
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
    let norm_ok = vec_infinity_norm(&z) < p.gamma1 - p.beta;
    let hash_ok = prefix_eq(&c_tilde, &c_tilde_prime, p.c_tilde_len);
    norm_ok && hash_ok
}
