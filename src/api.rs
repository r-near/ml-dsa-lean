//! Public API: FIPS 204 Algorithms 1, 2 and 3, one set of functions per parameter set.
//!
//! Stateless and allocation free: keys and signatures are fixed-size arrays, and each function is
//! the literal algorithm. In every function below K = `p.k` and L = `p.l` of the named parameter set
//! (44: 4, 4; 65: 6, 5; 87: 8, 7).
//!
//! The RNG stays above this API:
//!
//! - `keygen_*` is Algorithm 1 from step 4 on. Steps 1–3 (draw ξ from an approved RNG, return ⊥ if the
//!   RNG fails) are the caller's job; the caller passes the 32-byte ξ in.
//! - `sign_*` takes `rnd` explicitly. Pass 32 fresh random bytes for the default hedged variant, or 32
//!   zero bytes for the deterministic variant of Algorithm 2.
//!
//! `sign_internal_*` and `verify_internal_*` expose Algorithms 7 and 8 (M′ supplied by the caller).
//! `sk_is_well_formed_*` is an optional range check on a stored secret key (s₁, s₂ within [−η, η]); `sign_*` does
//! not call it. `pk_from_sk_*` is a stronger optional check (not a FIPS step): it recomputes the public key from
//! a stored secret key and rejects keys that are inconsistent. HashML-DSA (Algorithms 4 and 5) and external μ are out of scope.

use crate::encode::sk_is_well_formed;
use crate::keygen::{keygen_internal, pk_from_sk};
use crate::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87};
use crate::sign::sign_internal;
use crate::verify::verify_internal;

/// Builds the prefix 0 ‖ |ctx| ‖ ctx of M′ = IntegerToBytes(0, 1) ‖ IntegerToBytes(|ctx|, 1) ‖ ctx ‖ M.
/// Returns the buffer (bytes `..2 + ctx.len()` are the prefix), or `None` if |ctx| > 255
/// (Algorithm 2 steps 1–3, Algorithm 3 steps 1–3).
fn ctx_prefix(ctx: &[u8]) -> Option<[u8; 257]> {
    if ctx.len() > 255 {
        return None;
    }
    let mut prefix = [0u8; 257];
    prefix[0] = 0;
    prefix[1] = ctx.len() as u8;
    let mut i = 0;
    while i < ctx.len() {
        prefix[2 + i] = ctx[i];
        i += 1;
    }
    Some(prefix)
}

// ---------------------------------------------------------------------------------------------
// ML-DSA-44 (K = 4, L = 4)
// ---------------------------------------------------------------------------------------------

/// Algorithm 1 ML-DSA.KeyGen for ML-DSA-44, with the RNG output ξ passed in (steps 1–3 are the caller's).
/// Returns (pk, sk).
pub fn keygen_44(xi: &[u8; 32]) -> ([u8; 1312], [u8; 2560]) {
    let mut pk = [0u8; 1312];
    let mut sk = [0u8; 2560];
    keygen_internal::<4, 4>(&ML_DSA_44, xi, &mut pk, &mut sk);
    (pk, sk)
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-44. `None` if |ctx| > 255 or the κ budget is exhausted.
/// `rnd`: 32 random bytes (hedged) or 32 zero bytes (deterministic variant).
pub fn sign_44(sk: &[u8; 2560], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 2420]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 2420];
    if sign_internal::<4, 4>(&ML_DSA_44, sk, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-44. False if |ctx| > 255.
pub fn verify_44(pk: &[u8; 1312], m: &[u8], ctx: &[u8], sig: &[u8; 2420]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_internal::<4, 4>(&ML_DSA_44, pk, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-44: M′ is supplied by the caller.
pub fn sign_internal_44(sk: &[u8; 2560], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 2420]> {
    let mut sig = [0u8; 2420];
    if sign_internal::<4, 4>(&ML_DSA_44, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-44: M′ is supplied by the caller.
pub fn verify_internal_44(pk: &[u8; 1312], m_prime: &[u8], sig: &[u8; 2420]) -> bool {
    verify_internal::<4, 4>(&ML_DSA_44, pk, &[], m_prime, sig)
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-44). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_44` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_44` pass.
///
/// Not covered by the constant-time checks: the source branches on whether each coefficient is negative. Run
/// it where timing is not observable, e.g. once at key load.
pub fn sk_is_well_formed_44(sk: &[u8; 2560]) -> bool {
    sk_is_well_formed::<4, 4>(&ML_DSA_44, sk)
}

/// Derives the public key from a stored secret key and checks that the key is internally consistent
/// (ML-DSA-44). Returns `Some(pk)` iff every coefficient of s₁ and s₂ lies in [−η, η] and recomputing from
/// (ρ, s₁, s₂) as in KeyGen_internal steps 5–9 (Â ← ExpandA(ρ); t ← NTT⁻¹(Â ∘ NTT(s₁)) + s₂;
/// (t₁, t₀) ← Power2Round(t); pk ← pkEncode(ρ, t₁); tr ← H(pk, 64)) gives the stored t₀ and tr. Keys from
/// `keygen_44` pass and give back their pk. A flipped bit in ρ, tr, t₀, s₁ or s₂ is rejected. The key K
/// (bytes 32..64) is a free seed and is not checked.
///
/// This is not a FIPS 204 step. FIPS 204 Algorithm 25 and Section 7.2 say skDecode should only run on trusted
/// input, and `sign_44` follows it literally (it never calls this). Use this to validate secret keys loaded from
/// untrusted storage and to derive the public key of a stored key. It matches the intent of mldsa-native's
/// `pk_from_sk`.
///
/// Constant time: the t₀ and tr comparisons accumulate differences with no early exit, and the range check is
/// `sk_is_well_formed`. The function returns early when that check fails, which only reveals the (public) result.
/// The recomputation is the data-independent KeyGen arithmetic; BINSEC covers the individual steps, not this
/// function as a whole.
pub fn pk_from_sk_44(sk: &[u8; 2560]) -> Option<[u8; 1312]> {
    let mut pk = [0u8; 1312];
    if pk_from_sk::<4, 4>(&ML_DSA_44, sk, &mut pk) {
        Some(pk)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------------------------
// ML-DSA-65 (K = 6, L = 5)
// ---------------------------------------------------------------------------------------------

/// Algorithm 1 ML-DSA.KeyGen for ML-DSA-65, with the RNG output ξ passed in (steps 1–3 are the caller's).
/// Returns (pk, sk).
pub fn keygen_65(xi: &[u8; 32]) -> ([u8; 1952], [u8; 4032]) {
    let mut pk = [0u8; 1952];
    let mut sk = [0u8; 4032];
    keygen_internal::<6, 5>(&ML_DSA_65, xi, &mut pk, &mut sk);
    (pk, sk)
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-65. `None` if |ctx| > 255 or the κ budget is exhausted.
/// `rnd`: 32 random bytes (hedged) or 32 zero bytes (deterministic variant).
pub fn sign_65(sk: &[u8; 4032], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 3309]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 3309];
    if sign_internal::<6, 5>(&ML_DSA_65, sk, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-65. False if |ctx| > 255.
pub fn verify_65(pk: &[u8; 1952], m: &[u8], ctx: &[u8], sig: &[u8; 3309]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_internal::<6, 5>(&ML_DSA_65, pk, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-65: M′ is supplied by the caller.
pub fn sign_internal_65(sk: &[u8; 4032], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 3309]> {
    let mut sig = [0u8; 3309];
    if sign_internal::<6, 5>(&ML_DSA_65, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-65: M′ is supplied by the caller.
pub fn verify_internal_65(pk: &[u8; 1952], m_prime: &[u8], sig: &[u8; 3309]) -> bool {
    verify_internal::<6, 5>(&ML_DSA_65, pk, &[], m_prime, sig)
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-65). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_65` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_65` pass.
///
/// Not covered by the constant-time checks: the source branches on whether each coefficient is negative. Run
/// it where timing is not observable, e.g. once at key load.
pub fn sk_is_well_formed_65(sk: &[u8; 4032]) -> bool {
    sk_is_well_formed::<6, 5>(&ML_DSA_65, sk)
}

/// Derives the public key from a stored secret key and checks that the key is internally consistent
/// (ML-DSA-65). Returns `Some(pk)` iff every coefficient of s₁ and s₂ lies in [−η, η] and recomputing from
/// (ρ, s₁, s₂) as in KeyGen_internal steps 5–9 (Â ← ExpandA(ρ); t ← NTT⁻¹(Â ∘ NTT(s₁)) + s₂;
/// (t₁, t₀) ← Power2Round(t); pk ← pkEncode(ρ, t₁); tr ← H(pk, 64)) gives the stored t₀ and tr. Keys from
/// `keygen_65` pass and give back their pk. A flipped bit in ρ, tr, t₀, s₁ or s₂ is rejected. The key K
/// (bytes 32..64) is a free seed and is not checked.
///
/// This is not a FIPS 204 step. FIPS 204 Algorithm 25 and Section 7.2 say skDecode should only run on trusted
/// input, and `sign_65` follows it literally (it never calls this). Use this to validate secret keys loaded from
/// untrusted storage and to derive the public key of a stored key. It matches the intent of mldsa-native's
/// `pk_from_sk`.
///
/// Constant time: the t₀ and tr comparisons accumulate differences with no early exit, and the range check is
/// `sk_is_well_formed`. The function returns early when that check fails, which only reveals the (public) result.
/// The recomputation is the data-independent KeyGen arithmetic; BINSEC covers the individual steps, not this
/// function as a whole.
pub fn pk_from_sk_65(sk: &[u8; 4032]) -> Option<[u8; 1952]> {
    let mut pk = [0u8; 1952];
    if pk_from_sk::<6, 5>(&ML_DSA_65, sk, &mut pk) {
        Some(pk)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------------------------
// ML-DSA-87 (K = 8, L = 7)
// ---------------------------------------------------------------------------------------------

/// Algorithm 1 ML-DSA.KeyGen for ML-DSA-87, with the RNG output ξ passed in (steps 1–3 are the caller's).
/// Returns (pk, sk).
pub fn keygen_87(xi: &[u8; 32]) -> ([u8; 2592], [u8; 4896]) {
    let mut pk = [0u8; 2592];
    let mut sk = [0u8; 4896];
    keygen_internal::<8, 7>(&ML_DSA_87, xi, &mut pk, &mut sk);
    (pk, sk)
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-87. `None` if |ctx| > 255 or the κ budget is exhausted.
/// `rnd`: 32 random bytes (hedged) or 32 zero bytes (deterministic variant).
pub fn sign_87(sk: &[u8; 4896], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 4627]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 4627];
    if sign_internal::<8, 7>(&ML_DSA_87, sk, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-87. False if |ctx| > 255.
pub fn verify_87(pk: &[u8; 2592], m: &[u8], ctx: &[u8], sig: &[u8; 4627]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_internal::<8, 7>(&ML_DSA_87, pk, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-87: M′ is supplied by the caller.
pub fn sign_internal_87(sk: &[u8; 4896], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 4627]> {
    let mut sig = [0u8; 4627];
    if sign_internal::<8, 7>(&ML_DSA_87, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-87: M′ is supplied by the caller.
pub fn verify_internal_87(pk: &[u8; 2592], m_prime: &[u8], sig: &[u8; 4627]) -> bool {
    verify_internal::<8, 7>(&ML_DSA_87, pk, &[], m_prime, sig)
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-87). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_87` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_87` pass.
///
/// Not covered by the constant-time checks: the source branches on whether each coefficient is negative. Run
/// it where timing is not observable, e.g. once at key load.
pub fn sk_is_well_formed_87(sk: &[u8; 4896]) -> bool {
    sk_is_well_formed::<8, 7>(&ML_DSA_87, sk)
}

/// Derives the public key from a stored secret key and checks that the key is internally consistent
/// (ML-DSA-87). Returns `Some(pk)` iff every coefficient of s₁ and s₂ lies in [−η, η] and recomputing from
/// (ρ, s₁, s₂) as in KeyGen_internal steps 5–9 (Â ← ExpandA(ρ); t ← NTT⁻¹(Â ∘ NTT(s₁)) + s₂;
/// (t₁, t₀) ← Power2Round(t); pk ← pkEncode(ρ, t₁); tr ← H(pk, 64)) gives the stored t₀ and tr. Keys from
/// `keygen_87` pass and give back their pk. A flipped bit in ρ, tr, t₀, s₁ or s₂ is rejected. The key K
/// (bytes 32..64) is a free seed and is not checked.
///
/// This is not a FIPS 204 step. FIPS 204 Algorithm 25 and Section 7.2 say skDecode should only run on trusted
/// input, and `sign_87` follows it literally (it never calls this). Use this to validate secret keys loaded from
/// untrusted storage and to derive the public key of a stored key. It matches the intent of mldsa-native's
/// `pk_from_sk`.
///
/// Constant time: the t₀ and tr comparisons accumulate differences with no early exit, and the range check is
/// `sk_is_well_formed`. The function returns early when that check fails, which only reveals the (public) result.
/// The recomputation is the data-independent KeyGen arithmetic; BINSEC covers the individual steps, not this
/// function as a whole.
pub fn pk_from_sk_87(sk: &[u8; 4896]) -> Option<[u8; 2592]> {
    let mut pk = [0u8; 2592];
    if pk_from_sk::<8, 7>(&ML_DSA_87, sk, &mut pk) {
        Some(pk)
    } else {
        None
    }
}
