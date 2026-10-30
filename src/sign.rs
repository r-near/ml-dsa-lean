//! Algorithm 7 ML-DSA.Sign_internal(sk, M′, rnd). Step numbers refer to FIPS 204.

use crate::encode::{sig_encode, sk_decode, w1_encode};
use crate::field::{add, neg};
use crate::keccak::Shake;
use crate::ntt::{matrix_vector_ntt, ntt, ntt_inverse, scalar_vector_ntt_inverse, sub_poly};
use crate::params::Params;
use crate::rounding::{make_hint, poly_high_bits, poly_low_bits, vec_infinity_norm};
use crate::sampling::{expand_a, expand_mask, sample_in_ball};

fn ntt_vec<const N: usize>(v: &[[u32; 256]; N]) -> [[u32; 256]; N] {
    let mut out = [[0u32; 256]; N];
    let mut i = 0;
    while i < N {
        out[i] = ntt(&v[i]);
        i += 1;
    }
    out
}

/// One iteration of the loop body, steps 11–29. `None` is the ⊥ outcome.
#[allow(clippy::type_complexity)]
fn attempt<const K: usize, const L: usize>(
    p: &Params,
    a_hat: &[[[u32; 256]; L]; K],
    s1_hat: &[[u32; 256]; L],
    s2_hat: &[[u32; 256]; K],
    t0_hat: &[[u32; 256]; K],
    mu: &[u8; 64],
    rho_pp: &[u8; 64],
    kappa: u16,
) -> Option<([u8; 64], [[u32; 256]; L], [[bool; 256]; K])> {
    // 11: y ← ExpandMask(ρ″, κ)
    let y = expand_mask::<L>(p, rho_pp, kappa);
    // 12: w ← NTT⁻¹(Â ∘ NTT(y))
    let w_hat = matrix_vector_ntt::<K, L>(a_hat, &ntt_vec(&y));
    let mut w = [[0u32; 256]; K];
    let mut w1 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        w[i] = ntt_inverse(&w_hat[i]);
        // 13: w1 ← HighBits(w)
        w1[i] = poly_high_bits(p, &w[i]);
        i += 1;
    }
    // 15: c̃ ← H(μ || w1Encode(w1), λ/4)
    let mut w1_enc = [0u8; 8 * 192];
    w1_encode(p, &w1, &mut w1_enc);
    let mut c_tilde = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(mu);
    h.absorb(&w1_enc[..K * 32 * p.w1_bits]);
    h.finalize();
    h.squeeze(&mut c_tilde[..p.c_tilde_len]);
    // 16–17: c ← SampleInBall(c̃); ĉ ← NTT(c)
    let c_hat = ntt(&sample_in_ball(p, &c_tilde[..p.c_tilde_len]));
    // 18–19: ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩
    let cs1 = scalar_vector_ntt_inverse::<L>(&c_hat, s1_hat);
    let cs2 = scalar_vector_ntt_inverse::<K>(&c_hat, s2_hat);
    // 20: z ← y + ⟨⟨cs1⟩⟩
    let mut z = [[0u32; 256]; L];
    let mut i = 0;
    while i < L {
        let mut j = 0;
        while j < 256 {
            z[i][j] = add(y[i][j], cs1[i][j]);
            j += 1;
        }
        i += 1;
    }
    // 21: r0 ← LowBits(w − ⟨⟨cs2⟩⟩)
    let mut w_cs2 = [[0u32; 256]; K];
    let mut r0 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        w_cs2[i] = sub_poly(&w[i], &cs2[i]);
        r0[i] = poly_low_bits(p, &w_cs2[i]);
        i += 1;
    }
    // 23: reject on ‖z‖∞ ≥ γ1 − β or ‖r0‖∞ ≥ γ2 − β
    if vec_infinity_norm(&z) >= p.gamma1 - p.beta || vec_infinity_norm(&r0) >= p.gamma2 - p.beta {
        return None;
    }
    // 25: ⟨⟨ct0⟩⟩ ← NTT⁻¹(ĉ ∘ t̂0)
    let ct0 = scalar_vector_ntt_inverse::<K>(&c_hat, t0_hat);
    // 26: h ← MakeHint(−⟨⟨ct0⟩⟩, w − ⟨⟨cs2⟩⟩ + ⟨⟨ct0⟩⟩)
    let mut hint = [[false; 256]; K];
    let mut ones = 0;
    let mut i = 0;
    while i < K {
        let mut j = 0;
        while j < 256 {
            hint[i][j] = make_hint(p, neg(ct0[i][j]), add(w_cs2[i][j], ct0[i][j]));
            ones += hint[i][j] as usize;
            j += 1;
        }
        i += 1;
    }
    // 28: reject on ‖ct0‖∞ ≥ γ2 or more than ω ones in h
    if vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega {
        return None;
    }
    Some((c_tilde, z, hint))
}

/// Algorithm 7 ML-DSA.Sign_internal(sk, M′, rnd) with M′ = `m_prefix` ‖ `m` (the external API passes
/// 0 ‖ |ctx| ‖ ctx as the prefix; the internal interface passes an empty prefix). Writes σ to `sig` and
/// returns true, or returns false when the κ budget (all complete ExpandMask batches below 2^16) is exhausted.
pub fn sign_internal<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    rnd: &[u8; 32],
    sig: &mut [u8],
) -> bool {
    // 1: (ρ, K, tr, s1, s2, t0) ← skDecode(sk)
    let key = sk_decode::<K, L>(p, sk);
    // 2–4: ŝ1, ŝ2, t̂0
    let s1_hat = ntt_vec(&key.s1);
    let s2_hat = ntt_vec(&key.s2);
    let t0_hat = ntt_vec(&key.t0);
    // 5: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&key.rho);
    // 6: μ ← H(tr || M′, 64)
    let mut mu = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&key.tr);
    h.absorb(m_prefix);
    h.absorb(m);
    h.finalize();
    h.squeeze(&mut mu);
    // 7: ρ″ ← H(K || rnd || μ, 64)
    let mut rho_pp = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&key.key);
    h.absorb(rnd);
    h.absorb(&mu);
    h.finalize();
    h.squeeze(&mut rho_pp);
    // 8–32: rejection loop, κ ← κ + ℓ
    let mut kappa: u32 = 0;
    while kappa + (L as u32) - 1 <= 0xFFFF {
        if let Some((c_tilde, z, hint)) =
            attempt::<K, L>(p, &a_hat, &s1_hat, &s2_hat, &t0_hat, &mu, &rho_pp, kappa as u16)
        {
            // 33: σ ← sigEncode(c̃, z mod± q, h); z is already the canonical Z_q representative
            sig_encode::<K, L>(p, &c_tilde, &z, &hint, sig);
            return true;
        }
        kappa += L as u32;
    }
    false
}
