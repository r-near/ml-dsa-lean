//! Algorithm 6 ML-DSA.KeyGen_internal(ξ). Step numbers refer to FIPS 204.

use crate::encode::{SecretKey, pk_encode, sk_decode, sk_encode, sk_is_well_formed};
use crate::keccak::Shake;
use crate::ntt::{add_poly, matrix_vector_ntt, ntt_inverse, ntt_vec};
use crate::params::Params;
use crate::rounding::poly_power2round;
use crate::sampling::{expand_a, expand_s};
use crate::verify::prefix_eq;

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
/// to this function, which runs after pk and sk are written, plus `Shake::wipe` on the sponge that absorbed ξ and the
/// wipes inside `expand_s`. Not wiped: t0 in the tuple `vec_power2round` returns by value, one copy of K, and other
/// copies the compiler makes (`tests/zeroize.rs` finds both; the secret-key array returned by `api::keygen_*` is the
/// caller's).
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
    // The sponge absorbed ξ and holds (ρ, ρ′, K).
    #[cfg(feature = "zeroize")]
    h.wipe();
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

/// OR of `a[i] ^ b[i]` over the 256 coefficients: zero iff the polynomials are equal. No data-dependent branch.
fn poly_diff(a: &[u32; 256], b: &[u32; 256]) -> u32 {
    let mut diff = 0u32;
    let mut i = 0;
    while i < 256 {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff
}

/// OR of `poly_diff` over the K entries: zero iff the vectors are equal. No data-dependent branch.
fn vec_diff<const K: usize>(a: &[[u32; 256]; K], b: &[[u32; 256]; K]) -> u32 {
    let mut diff = 0u32;
    let mut i = 0;
    while i < K {
        diff |= poly_diff(&a[i], &b[i]);
        i += 1;
    }
    diff
}

/// Zeroizes the secret temporaries of `pk_from_sk`: the decoded K, s1, s2 and t0. Only compiled with the
/// `zeroize` feature; outside the Lean proof, like `wipe_keygen`.
#[cfg(feature = "zeroize")]
fn wipe_decoded<const K: usize, const L: usize>(dec: &mut SecretKey<K, L>) {
    use zeroize::Zeroize;
    dec.key.zeroize();
    dec.s1.zeroize();
    dec.s2.zeroize();
    dec.t0.zeroize();
}

/// Steps 5–9 of KeyGen_internal from the decoded key `dec` and Â = ExpandA(ρ), then the comparison with the stored
/// t0 and tr. Writes the recomputed pk into `pk` (32 + 320·K bytes) and returns true iff the recomputed t0 equals
/// `dec.t0` and the recomputed tr equals `dec.tr`. Both comparisons run to the end (no early exit).
/// The caller has checked (`sk_is_well_formed`) that s1 and s2 lie within [−η, η], which keeps the NTT inputs small.
fn pk_check<const K: usize, const L: usize>(
    a_hat: &[[[u32; 256]; L]; K],
    dec: &SecretKey<K, L>,
    pk: &mut [u8],
) -> bool {
    // 5: t ← NTT⁻¹(Â ∘ NTT(s1)) + s2
    let t = compute_t::<K, L>(a_hat, &ntt_vec::<L>(&dec.s1), &dec.s2);
    // 6: (t1, t0) ← Power2Round(t)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let (t1, mut t0_new) = vec_power2round::<K>(&t);
    // 8: pk ← pkEncode(ρ, t1)
    pk_encode::<K>(&dec.rho, &t1, pk);
    // 9: tr ← H(pk, 64)
    let mut tr = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&pk[..32 + 320 * K]);
    h.finalize();
    h.squeeze(&mut tr);
    // Compare with the stored t0 and tr.
    let t0_same = vec_diff::<K>(&t0_new, &dec.t0) == 0;
    let tr_same = prefix_eq(&tr, &dec.tr, 64);
    #[cfg(feature = "zeroize")]
    {
        use zeroize::Zeroize;
        t0_new.zeroize();
    }
    t0_same && tr_same
}

/// Key-consistency check (not a FIPS 204 step): recomputes the public key from the secret key and compares.
/// `sk` has `sk_len(p)` bytes and `pk` has `pk_len(p)` bytes (panics otherwise, like `keygen_internal`).
///
/// Returns false if any coefficient of s1 or s2 lies outside [−η, η] (`sk_is_well_formed`). Otherwise it decodes
/// sk (Algorithm 25) and redoes KeyGen_internal steps 5–9 from (ρ, s1, s2):
/// t ← NTT⁻¹(Â ∘ NTT(s1)) + s2 with Â ← ExpandA(ρ); (t1, t0) ← Power2Round(t); pk ← pkEncode(ρ, t1);
/// tr ← H(pk, 64). It returns true iff the recomputed t0 equals the stored t0 and the recomputed tr equals the
/// stored tr, and then `pk` holds the public key. When it returns false, `pk` holds the recomputed (unconfirmed)
/// bytes, or is untouched if the range check failed. The key K is not checked: it is a free seed.
///
/// The t0 and tr comparisons OR the differences together (no early exit, as in `prefix_eq`).
pub fn pk_from_sk<const K: usize, const L: usize>(p: &Params, sk: &[u8], pk: &mut [u8]) -> bool {
    // Range check on s1 and s2 (what sk_is_well_formed decides).
    if !sk_is_well_formed::<K, L>(p, sk) {
        return false;
    }
    // 1: (ρ, K, tr, s1, s2, t0) ← skDecode(sk)
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut dec = sk_decode::<K, L>(p, sk);
    // 3: Â ← ExpandA(ρ)
    let a_hat = expand_a::<K, L>(&dec.rho);
    let ok = pk_check::<K, L>(&a_hat, &dec, pk);
    #[cfg(feature = "zeroize")]
    wipe_decoded::<K, L>(&mut dec);
    ok
}
