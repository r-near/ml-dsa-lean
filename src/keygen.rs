//! Algorithm 6 ML-DSA.KeyGen_internal(ξ). Step numbers refer to FIPS 204.

use crate::encode::{pk_encode, sk_encode};
use crate::keccak::Shake;
use crate::ntt::{add_poly, matrix_vector_ntt, ntt_inverse, ntt_vec};
use crate::params::Params;
use crate::rounding::poly_power2round;
use crate::sampling::{expand_a, expand_s};

/// Power2Round applied to every entry of t: returns (t1, t0).
#[allow(clippy::type_complexity)]
fn vec_power2round<const K: usize>(t: &[[u32; 256]; K]) -> ([[u32; 256]; K], [[u32; 256]; K]) {
    let mut t1 = [[0u32; 256]; K];
    let mut t0 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        let (a, b) = poly_power2round(&t[i]);
        t1[i] = a;
        t0[i] = b;
        i += 1;
    }
    (t1, t0)
}

/// t ← NTT⁻¹(Â ∘ ŝ1) + s2, entry-wise.
fn compute_t<const K: usize, const L: usize>(
    a_hat: &[[[u32; 256]; L]; K],
    s1_hat: &[[u32; 256]; L],
    s2: &[[u32; 256]; K],
) -> [[u32; 256]; K] {
    let prod = matrix_vector_ntt::<K, L>(a_hat, s1_hat);
    let mut t = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        t[i] = add_poly(&ntt_inverse(&prod[i]), &s2[i]);
        i += 1;
    }
    t
}

/// Zeroizes the secret temporaries of `keygen_internal`: the SHAKE output holding ρ′ and K, ρ′, K, s1, s2
/// and t0. Only compiled with the `zeroize` feature. This is outside the Lean proof (Aeneas models
/// neither `Drop` nor volatile writes); the feature-on build differs from the proved code only by the call
/// to this function, which runs after pk and sk are written. Copies the compiler makes are not wiped.
#[cfg(feature = "zeroize")]
fn wipe_keygen<const K: usize, const L: usize>(
    expanded: &mut [u8; 128],
    rho_prime: &mut [u8; 64],
    key: &mut [u8; 32],
    s1: &mut [[u32; 256]; L],
    s2: &mut [[u32; 256]; K],
    t0: &mut [[u32; 256]; K],
) {
    use zeroize::Zeroize;
    expanded.zeroize();
    rho_prime.zeroize();
    key.zeroize();
    s1.zeroize();
    s2.zeroize();
    t0.zeroize();
}

/// Algorithm 6 ML-DSA.KeyGen_internal(ξ). Writes pk (32 + 320·K bytes) and sk (`sk_len(p)` bytes).
pub fn keygen_internal<const K: usize, const L: usize>(p: &Params, xi: &[u8; 32], pk: &mut [u8], sk: &mut [u8]) {
    // 1: (ρ, ρ′, K) ← H(ξ ‖ IntegerToBytes(k, 1) ‖ IntegerToBytes(ℓ, 1), 128)
    let kl = [K as u8, L as u8];
    let mut h = Shake::shake256();
    h.absorb(xi);
    h.absorb(&kl);
    h.finalize();
    let mut expanded = [0u8; 128];
    h.squeeze(&mut expanded);
    let mut rho = [0u8; 32];
    let mut rho_prime = [0u8; 64];
    let mut key = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        rho[i] = expanded[i];
        key[i] = expanded[96 + i];
        i += 1;
    }
    let mut i = 0;
    while i < 64 {
        rho_prime[i] = expanded[32 + i];
        i += 1;
    }
    // 3: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&rho);
    // 4: (s1, s2) ← ExpandS(ρ′)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let (mut s1, mut s2) = expand_s::<K, L>(p, &rho_prime);
    // 5: t ← NTT⁻¹(Â ∘ NTT(s1)) + s2
    let t = compute_t::<K, L>(&a_hat, &ntt_vec::<L>(&s1), &s2);
    // 6: (t1, t0) ← Power2Round(t)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let (t1, mut t0) = vec_power2round::<K>(&t);
    // 8: pk ← pkEncode(ρ, t1)
    pk_encode::<K>(&rho, &t1, pk);
    // 9: tr ← H(pk, 64)
    let mut tr = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&pk[..32 + 320 * K]);
    h.finalize();
    h.squeeze(&mut tr);
    // 10: sk ← skEncode(ρ, K, tr, s1, s2, t0)
    sk_encode::<K, L>(p, &rho, &key, &tr, &s1, &s2, &t0, sk);
    #[cfg(feature = "zeroize")]
    wipe_keygen::<K, L>(&mut expanded, &mut rho_prime, &mut key, &mut s1, &mut s2, &mut t0);
}
