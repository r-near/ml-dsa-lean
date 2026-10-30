//! Algorithm 7 ML-DSA.Sign_internal(sk, M′, rnd). Step numbers refer to FIPS 204.

#[cfg(feature = "zeroize")]
use crate::encode::SecretKey;
use crate::encode::{sig_encode, sk_decode, w1_encode};
use crate::field::{add, neg};
use crate::keccak::Shake;
use crate::ntt::{matrix_vector_ntt, ntt, ntt_inverse, ntt_vec, scalar_vector_ntt_inverse, sub_poly};
use crate::params::Params;
use crate::rounding::{make_hint, poly_high_bits, poly_low_bits, vec_infinity_norm};
use crate::sampling::{expand_a, expand_mask, sample_in_ball};

/// Steps 18–21: ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, z, w − ⟨⟨cs2⟩⟩ and r0. Returns (z, w − ⟨⟨cs2⟩⟩, r0).
#[allow(clippy::type_complexity)]
pub(crate) fn response<const K: usize, const L: usize>(
    p: &Params,
    y: &[[u32; 256]; L],
    c_hat: &[u32; 256],
    s1_hat: &[[u32; 256]; L],
    s2_hat: &[[u32; 256]; K],
    w: &[[u32; 256]; K],
) -> ([[u32; 256]; L], [[u32; 256]; K], [[u32; 256]; K]) {
    // 18–19: ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩
    let cs1 = scalar_vector_ntt_inverse::<L>(c_hat, s1_hat);
    let cs2 = scalar_vector_ntt_inverse::<K>(c_hat, s2_hat);
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
    (z, w_cs2, r0)
}

/// Steps 25–26: ⟨⟨ct0⟩⟩, h = MakeHint(−⟨⟨ct0⟩⟩, w − ⟨⟨cs2⟩⟩ + ⟨⟨ct0⟩⟩) and the number of ones in h.
/// Returns (h, ⟨⟨ct0⟩⟩, ones).
#[allow(clippy::type_complexity)]
pub(crate) fn hint_step<const K: usize>(
    p: &Params,
    c_hat: &[u32; 256],
    t0_hat: &[[u32; 256]; K],
    w_cs2: &[[u32; 256]; K],
) -> ([[bool; 256]; K], [[u32; 256]; K], usize) {
    // 25: ⟨⟨ct0⟩⟩ ← NTT⁻¹(ĉ ∘ t̂0)
    let ct0 = scalar_vector_ntt_inverse::<K>(c_hat, t0_hat);
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
    (hint, ct0, ones)
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
    // 18–21: z, w − ⟨⟨cs2⟩⟩, r0
    let (z, w_cs2, r0) = response::<K, L>(p, &y, &c_hat, s1_hat, s2_hat, &w);
    // 23: reject on ‖z‖∞ ≥ γ1 − β or ‖r0‖∞ ≥ γ2 − β
    if vec_infinity_norm(&z) >= p.gamma1 - p.beta || vec_infinity_norm(&r0) >= p.gamma2 - p.beta {
        return None;
    }
    // 25–26: ct0, h, number of ones
    let (hint, ct0, ones) = hint_step::<K>(p, &c_hat, t0_hat, &w_cs2);
    // 28: reject on ‖ct0‖∞ ≥ γ2 or more than ω ones in h
    if vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega {
        return None;
    }
    Some((c_tilde, z, hint))
}

/// Zeroizes the secret temporaries of `sign_internal`: ρ″, the decoded key's K/s1/s2/t0 and the NTT
/// forms ŝ1, ŝ2, t̂0. Only compiled with the `zeroize` feature. This is outside the Lean proof (Aeneas
/// models neither `Drop` nor volatile writes); the feature-on build differs from the proved code only by
/// the calls to this function, which run after σ is written. Not wiped: the per-attempt vectors y, cs1,
/// cs2, ct0 (locals of `attempt`), and any copies the compiler makes of the above.
#[cfg(feature = "zeroize")]
fn wipe_sign<const K: usize, const L: usize>(
    key: &mut SecretKey<K, L>,
    s1_hat: &mut [[u32; 256]; L],
    s2_hat: &mut [[u32; 256]; K],
    t0_hat: &mut [[u32; 256]; K],
    rho_pp: &mut [u8; 64],
) {
    use zeroize::Zeroize;
    key.key.zeroize();
    key.s1.zeroize();
    key.s2.zeroize();
    key.t0.zeroize();
    s1_hat.zeroize();
    s2_hat.zeroize();
    t0_hat.zeroize();
    rho_pp.zeroize();
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
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut key = sk_decode::<K, L>(p, sk);
    // 2–4: ŝ1, ŝ2, t̂0
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut s1_hat = ntt_vec(&key.s1);
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut s2_hat = ntt_vec(&key.s2);
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut t0_hat = ntt_vec(&key.t0);
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
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
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
            #[cfg(feature = "zeroize")]
            wipe_sign::<K, L>(&mut key, &mut s1_hat, &mut s2_hat, &mut t0_hat, &mut rho_pp);
            return true;
        }
        kappa += L as u32;
    }
    #[cfg(feature = "zeroize")]
    wipe_sign::<K, L>(&mut key, &mut s1_hat, &mut s2_hat, &mut t0_hat, &mut rho_pp);
    false
}
