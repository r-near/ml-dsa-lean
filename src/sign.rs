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

/// The part of Algorithm 7 that depends on the secret key alone: ŝ1, ŝ2, t̂0 (steps 2-4), Â (step 5), and the
/// key's K and tr (used by steps 6-7). Signing many messages with one key computes it once. The fields are
/// private to the crate; the `api` module wraps this type per parameter set.
///
/// Secret material: ŝ1, ŝ2, t̂0 and K. With the `zeroize` feature, dropping it wipes them (the `Drop` impl is
/// `cfg`-gated, so it is outside the Lean model, which has no `Drop`).
///
/// Size: (K·L + L + 2K) KiB + 96 bytes (28,768 / 48,224 / 80,992 bytes for ML-DSA-44 / 65 / 87).
pub struct PreparedSk<const K: usize, const L: usize> {
    /// Â ← ExpandA(ρ), NTT domain. Public. (ρ itself is not kept: ExpandA is its only use.)
    pub(crate) a_hat: [[[u32; 256]; L]; K],
    /// ŝ1 ← NTT(s1).
    pub(crate) s1_hat: [[u32; 256]; L],
    /// ŝ2 ← NTT(s2).
    pub(crate) s2_hat: [[u32; 256]; K],
    /// t̂0 ← NTT(t0).
    pub(crate) t0_hat: [[u32; 256]; K],
    /// K, the secret seed of step 7.
    pub(crate) key: [u8; 32],
    /// tr, the hash of the public key (step 6).
    pub(crate) tr: [u8; 64],
}

#[cfg(feature = "zeroize")]
impl<const K: usize, const L: usize> Drop for PreparedSk<K, L> {
    /// Wipes ŝ1, ŝ2, t̂0 and K (Â and tr are public). Outside the Lean proof: Aeneas models neither `Drop` nor
    /// volatile writes. Copies the compiler makes of the struct (moves) are not wiped.
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.s1_hat.zeroize();
        self.s2_hat.zeroize();
        self.t0_hat.zeroize();
        self.key.zeroize();
    }
}

/// Steps 1-5 of Algorithm 7: skDecode, the three NTTs and ExpandA. Everything that depends on `sk` alone.
/// With the `zeroize` feature the decoded s1, s2, t0 and K are wiped before returning.
pub fn prepare_sk<const K: usize, const L: usize>(p: &Params, sk: &[u8]) -> PreparedSk<K, L> {
    // 1: (ρ, K, tr, s1, s2, t0) ← skDecode(sk)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut key = sk_decode::<K, L>(p, sk);
    // 2–4: ŝ1, ŝ2, t̂0
    let s1_hat = ntt_vec(&key.s1);
    let s2_hat = ntt_vec(&key.s2);
    let t0_hat = ntt_vec(&key.t0);
    // 5: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&key.rho);
    let out = PreparedSk { a_hat, s1_hat, s2_hat, t0_hat, key: key.key, tr: key.tr };
    #[cfg(feature = "zeroize")]
    wipe_decoded::<K, L>(&mut key);
    out
}

/// Zeroizes the decoded secret key of `prepare_sk` (K, s1, s2, t0). Only compiled with the `zeroize` feature.
/// Outside the Lean proof (see `PreparedSk`'s `Drop`).
#[cfg(feature = "zeroize")]
fn wipe_decoded<const K: usize, const L: usize>(key: &mut SecretKey<K, L>) {
    use zeroize::Zeroize;
    key.key.zeroize();
    key.s1.zeroize();
    key.s2.zeroize();
    key.t0.zeroize();
}

/// Steps 6-33 of Algorithm 7 on a prepared key: μ, ρ″, the rejection loop and sigEncode. Same contract as
/// `sign_internal` for the key `ps` was built from (`sign_internal` is `prepare_sk` followed by this function).
/// The operations and their order on secret data are those of `sign_internal`; there is no branch on a secret
/// beyond the algorithm's own rejection tests. With the `zeroize` feature ρ″ is wiped before returning.
pub fn sign_prepared_internal<const K: usize, const L: usize>(
    p: &Params,
    ps: &PreparedSk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    rnd: &[u8; 32],
    sig: &mut [u8],
) -> bool {
    // 6: μ ← H(tr || M′, 64)
    let mut mu = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&ps.tr);
    h.absorb(m_prefix);
    h.absorb(m);
    h.finalize();
    h.squeeze(&mut mu);
    // 7: ρ″ ← H(K || rnd || μ, 64)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut rho_pp = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&ps.key);
    h.absorb(rnd);
    h.absorb(&mu);
    h.finalize();
    h.squeeze(&mut rho_pp);
    // 8–32: rejection loop, κ ← κ + ℓ
    let mut kappa: u32 = 0;
    while kappa + (L as u32) - 1 <= 0xFFFF {
        if let Some((c_tilde, z, hint)) =
            attempt::<K, L>(p, &ps.a_hat, &ps.s1_hat, &ps.s2_hat, &ps.t0_hat, &mu, &rho_pp, kappa as u16)
        {
            // 33: σ ← sigEncode(c̃, z mod± q, h); z is already the canonical Z_q representative
            sig_encode::<K, L>(p, &c_tilde, &z, &hint, sig);
            #[cfg(feature = "zeroize")]
            wipe_rho_pp(&mut rho_pp);
            return true;
        }
        kappa += L as u32;
    }
    #[cfg(feature = "zeroize")]
    wipe_rho_pp(&mut rho_pp);
    false
}

/// Zeroizes ρ″ (Algorithm 7 step 7). Only compiled with the `zeroize` feature; outside the Lean proof.
/// Not wiped: the per-attempt vectors y, cs1, cs2, ct0 (locals of `attempt`), and any copies the compiler makes.
#[cfg(feature = "zeroize")]
fn wipe_rho_pp(rho_pp: &mut [u8; 64]) {
    use zeroize::Zeroize;
    rho_pp.zeroize();
}

/// Algorithm 7 ML-DSA.Sign_internal(sk, M′, rnd) with M′ = `m_prefix` ‖ `m` (the external API passes
/// 0 ‖ |ctx| ‖ ctx as the prefix; the internal interface passes an empty prefix). Writes σ to `sig` and
/// returns true, or returns false when the κ budget (all complete ExpandMask batches below 2^16) is exhausted.
/// It is `prepare_sk` followed by `sign_prepared_internal`; with the `zeroize` feature the prepared key is
/// wiped when it goes out of scope.
pub fn sign_internal<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    rnd: &[u8; 32],
    sig: &mut [u8],
) -> bool {
    let ps = prepare_sk::<K, L>(p, sk);
    sign_prepared_internal::<K, L>(p, &ps, m_prefix, m, rnd, sig)
}
