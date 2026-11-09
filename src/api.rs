//! Public API: FIPS 204 Algorithms 1, 2 and 3, one set of functions per parameter set.
//!
//! Allocation free. The one-shot functions are stateless: keys and signatures are fixed-size arrays, and each
//! function is the literal algorithm. The prepared-key objects (`VerifyingKey*`, `SigningKey*`, below) are fixed-size
//! structs built by one constructor each and then only read; the crate holds no other state and detects nothing at run time.
//! In every function below K = `p.k` and L = `p.l` of the named parameter set
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
//!
//! Prepared verifying keys: `verifying_key_*` computes the part of Verify that depends on the public key alone
//! (Â, NTT(t1 · 2^d), tr) once; `verify_prepared_*` and `verify_internal_prepared_*` then check signatures
//! against it without recomputing. They return exactly what `verify_*` and `verify_internal_*` return for the
//! key the `VerifyingKey*` was built from (proved in Lean, `Proofs/PreparedVerify.lean`). The key objects are
//! 20,544 / 36,928 / 65,600 bytes (ML-DSA-44 / 65 / 87): too large to copy freely, so keep them in a `Box`
//! (this crate is `no_std` without `alloc`, so it cannot do that for you).
//!
//! Prepared signing keys: `signing_key_*` computes the part of Sign that depends on the secret key alone (ŝ1, ŝ2, t̂0,
//! Â, K, tr) once; `sign_prepared_*` and `sign_internal_prepared_*` then sign without recomputing, returning exactly
//! what `sign_*` and `sign_internal_*` return for the same key (proved in Lean, `Proofs/PreparedSign.lean`). The
//! operations on secret data are those of `sign_*`, reorganized; no new secret-dependent branch. The key objects
//! are 28,768 / 48,224 / 80,992 bytes and contain secrets: keep them in a `Box`, do not copy them. With the
//! `zeroize` feature, dropping one wipes ŝ1, ŝ2, t̂0 and K (the `Drop` impl is not part of the Lean model).
//!
//! Stack, worst case below the caller's frame in a release build (`tools/stack/`, painted stack and static walk, x86_64,
//! thumbv7em and riscv32imac agree within 4%; ML-DSA-44 / 65 / 87, in KB): the one-shot `verify_*` take 56 / 80 / 118
//! (the key is built in place, `verify::prepare_vk_into_x4`, and verify always runs the 4-way ExpandA) and `verifying_key_*`
//! 50 / 73 / 108, plus the returned key in the caller's frame (20.5 / 36.9 / 65.6); the 87 figure of `verifying_key_*` is
//! the compiler keeping an extra copy of the key (the build-in-place figure is about 26 KB, which an older toolchain reached).
//! `signing_key_*` 60 / 99 / 164, plus the returned key (28.8 / 48.2 / 81.0); `verify_prepared_*` and
//! `verify_internal_prepared_*` 34 / 45 / 59; `sign_prepared_*` and `sign_internal_prepared_*` 73 / 101 / 134; `sign_*`
//! 116 / 168 / 240. Results vary by about 5% with the toolchain and inlining, and by more for `verifying_key_*` and
//! `verify_*` under LTO; `tools/stack/README.md` and `bench/results/2026-11-09-p12.md` have the full tables.
//!
//! Zeroize coverage (feature `zeroize`; outside the Lean model, which has no `Drop` and no volatile writes, so the
//! theorems are about the code without it). What it wipes: dropping a `SigningKey*`; in `keygen_*`, `sign_*`,
//! `sign_prepared_*`, `signing_key_*` and `pk_from_sk_*`, the decoded or derived secrets held in locals (the decoded
//! key, ρ′, K, ρ″, the raw bit fields behind y, s1 and s2) and the SHAKE states that absorbed a secret (ξ, ρ′, ρ″,
//! K ‖ rnd ‖ μ, w1; `Shake::wipe`). `signing_key_*` and `sign_*` build ŝ1, ŝ2, t̂0 and K directly in the key object
//! (`sign::prepare_sk_into`, `encode::sk_decode_into`, `ntt::ntt_vec_into`: the secret vectors are decoded and
//! transformed where they lie) and `signing_key_*` returns the object through `mem::replace`, so that no copy is left
//! in the dead stack frames below the call. Each Sign attempt (`sign::attempt`) wipes, on every exit (accepted,
//! rejected before or after the hint step), the mask y and everything derived from it: ŷ, Â ∘ ŷ, w, w1, ĉ, ⟨⟨cs1⟩⟩,
//! ⟨⟨cs2⟩⟩, w − ⟨⟨cs2⟩⟩, r0, ⟨⟨ct0⟩⟩ and, for a rejected attempt, z, h and c̃ (which an accepted attempt publishes). It
//! does so by having the secrets live in buffers `attempt` owns (`response_into`, `hint_step_into`,
//! `ntt::scalar_vector_ntt_inverse_into`, `ntt::matrix_vector_ntt_into`, `ntt::ntt_in_place`,
//! `ntt::ntt_inverse_in_place`) rather than in values returned from callees, whose dead frames keep a copy.
//! `tests/zeroize.rs` checks this: it scans the stack below each call for K, s1, s2, t0, their NTT forms and ρ″, and,
//! for every attempt of a `sign_*` / `sign_prepared_*` call (accepted and rejected) and for one call of `attempt` that
//! ends in each of the three ways, for y, ŷ, Â ∘ ŷ, w, ĉ ∘ ŝ1, ĉ ∘ ŝ2, ĉ ∘ t̂0, ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, w − ⟨⟨cs2⟩⟩, r0, ⟨⟨ct0⟩⟩ and,
//! for a rejected attempt, z and c̃. It also reads a dropped key back. A needle is the first 16 coefficients of a vector
//! (the whole value for a seed), so a copy that is partly overwritten is still found. The stack-residue results hold for optimized builds on the measured toolchain (release;
//! also under nearcore's release profile, `scripts/ci.sh` step `nearcore-test-zeroize`). At opt-level 0 most of them
//! fail: 21 of the 24 stack-residue scan tests find copies in dead frames (everything except `signing_key_*`, which
//! passes for all three sets). The exact counts are for one Linux x86_64 machine and one aarch64 macOS machine. At dev
//! opt-level 1 (the whole crate and test built at opt-level 1, not the per-package override of a downstream workspace)
//! 28 of 28 tests of `tests/zeroize.rs` passed on macOS and 26 of 28 on Linux (`keygen_44`, `keygen_65` fail). The drop wipe and the explicit wipes are not affected: their
//! tests (`signing_key_drop_wipes`, `shake_wipe_zeroes_the_sponge`) pass at opt-level 0 and in release. What remains:
//!
//! - Copies the compiler makes when it moves a returned value are in the caller's frame and are the caller's concern:
//!   a `SigningKey*` (keep it in a `Box`, build it there, and do not move it), and the secret-key array `keygen_*`
//!   returns. The key bytes passed in (`sk`) are the caller's too.
//! - `sign_*`: z, c̃ and h of the accepted attempt are the signature and are not wiped; the intermediate values the
//!   scan does not look for (a needle is a prefix of a vector, so a copy of a vector shorter than 16 coefficients, or
//!   one the compiler stores in pieces, would be missed); registers and unnamed spills.
//! - `keygen_*` and `pk_from_sk_*`: t0 survives in the tuple `vec_power2round` returns by value, and `keygen_*` leaves
//!   one copy of K (the scan finds both, `tests/zeroize.rs`, `KEYGEN_KNOWN`). s1, s2, ξ, ρ′ and the expanded seed are
//!   wiped.
//! - A panic or `mem::forget` skips the wipes. Registers, spills the compiler placed in unnamed temporaries, and
//!   anything the operating system copied (swap, core dumps) are out of reach.
//!
//! `sk_is_well_formed_*` is an optional range check on a stored secret key (s₁, s₂ within [−η, η]); `sign_*` does
//! not call it. `pk_from_sk_*` is a stronger optional check (not a FIPS step): it recomputes the public key from
//! a stored secret key and rejects keys that are inconsistent. HashML-DSA (Algorithms 4 and 5) and external μ are out of scope.

use crate::encode::sk_is_well_formed;
use crate::keygen::{keygen_internal, pk_from_sk};
use crate::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87};
use crate::sign::{prepare_sk_into, sign_internal, sign_prepared_internal, PreparedSk};
use crate::verify::{prepare_vk_into_x4, verify_internal_x4, verify_prepared_internal, PreparedVk};

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
    verify_internal_x4::<4, 4>(&ML_DSA_44, pk, &prefix[..2 + ctx.len()], m, sig)
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
    verify_internal_x4::<4, 4>(&ML_DSA_44, pk, &[], m_prime, sig)
}

/// A public key prepared for repeated verification (ML-DSA-44): Â = ExpandA(ρ) and NTT(t1 · 2^d) in the NTT
/// domain, and tr = H(pk, 64), everything Algorithm 8 recomputes from the public key on every call.
///
/// Build it with [`verifying_key_44`], use it with [`verify_prepared_44`] and [`verify_internal_prepared_44`]. It holds
/// no secret. Size: 20,544 bytes (4·4 + 4 polynomials of 1 KiB, plus 64 bytes), so keep it in a `Box` or
/// a long-lived structure rather than on a small stack. The fields are private: the only way to obtain one is
/// `verifying_key_44`, which fixes the relation to the key bytes.
#[derive(Clone)]
pub struct VerifyingKey44 {
    inner: PreparedVk<4, 4>,
}

/// Prepares a public key for ML-DSA-44 verification: computes Â, NTT(t1 · 2^d) and tr once
/// (Algorithm 8 steps 1, 6, 7 and the key half of step 10). Cost: about one `verify_44` call minus the
/// per-signature work (dominated by ExpandA).
///
/// Never fails: every byte string of 1312 bytes decodes. Like `verify_44` it diverges only if the SHAKE output never
/// completes ExpandA (Proofs/Divergence.lean). Returns by value (20,544 bytes); with a
/// `Box`, write `Box::new(verifying_key_44(&pk))`.
pub fn verifying_key_44(pk: &[u8; 1312]) -> VerifyingKey44 {
    let mut vk = PreparedVk::<4, 4>::zeroed();
    prepare_vk_into_x4::<4, 4>(pk, &mut vk);
    VerifyingKey44 { inner: vk }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-44 against a prepared key. For `vk = verifying_key_44(pk)` it returns
/// exactly `verify_44(pk, m, ctx, sig)`. False if |ctx| > 255.
pub fn verify_prepared_44(vk: &VerifyingKey44, m: &[u8], ctx: &[u8], sig: &[u8; 2420]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_prepared_internal::<4, 4>(&ML_DSA_44, &vk.inner, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-44 against a prepared key: M′ is supplied by the caller. For
/// `vk = verifying_key_44(pk)` it returns exactly `verify_internal_44(pk, m_prime, sig)`.
pub fn verify_internal_prepared_44(vk: &VerifyingKey44, m_prime: &[u8], sig: &[u8; 2420]) -> bool {
    verify_prepared_internal::<4, 4>(&ML_DSA_44, &vk.inner, &[], m_prime, sig)
}

/// A secret key prepared for repeated signing (ML-DSA-44): ŝ1, ŝ2 and t̂0 in the NTT domain, Â = ExpandA(ρ), K and
/// tr, everything Algorithm 7 recomputes from the secret key on every call (steps 1-5, plus the key inputs of 6-7).
///
/// Build it with [`signing_key_44`], use it with [`sign_prepared_44`] and [`sign_internal_prepared_44`]. It holds
/// secret material (ŝ1, ŝ2, t̂0, K). With the `zeroize` feature, dropping it wipes those fields (a `cfg`-gated `Drop`
/// impl; outside the Lean model, which has no `Drop`). Not `Clone`: do not make extra copies of a secret.
/// Size: 28,768 bytes (4·4 + 4 + 2·4 = 28 polynomials of 1 KiB, plus 96 bytes), so keep it in a `Box` or a
/// long-lived structure rather than on a small stack; moving it copies it (the copy is not wiped). The fields are
/// private: the only way to obtain one is `signing_key_44`, which fixes the relation to the key bytes.
pub struct SigningKey44 {
    pub(crate) inner: PreparedSk<4, 4>,
}

/// Prepares a secret key for ML-DSA-44 signing: skDecode, the three NTTs and ExpandA (Algorithm 7 steps 1-5) once.
/// Cost: about the key-dependent share of one `sign_44` call, dominated by ExpandA.
///
/// Like `sign_44` it does not validate the key (see `sk_is_well_formed_44`) and diverges only if the SHAKE output
/// never completes ExpandA (Proofs/Divergence.lean). Returns by value (28,768 bytes); with a `Box`, write
/// `Box::new(signing_key_44(&sk))`.
pub fn signing_key_44(sk: &[u8; 2560]) -> SigningKey44 {
    let mut out = SigningKey44 { inner: PreparedSk::<4, 4>::zeroed() };
    prepare_sk_into::<4, 4>(&ML_DSA_44, sk, &mut out.inner);
    core::mem::replace(&mut out, SigningKey44 { inner: PreparedSk::<4, 4>::zeroed() })
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-44 with a prepared key. For `ssk = signing_key_44(sk)` it returns exactly
/// `sign_44(sk, m, ctx, rnd)`. `None` if |ctx| > 255 or the κ budget is exhausted. Same operations on secret data
/// as `sign_44` (only reorganized: no new branch depends on a secret).
pub fn sign_prepared_44(ssk: &SigningKey44, m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 2420]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 2420];
    if sign_prepared_internal::<4, 4>(&ML_DSA_44, &ssk.inner, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-44 with a prepared key: M′ is supplied by the caller. For
/// `ssk = signing_key_44(sk)` it returns exactly `sign_internal_44(sk, m_prime, rnd)`.
pub fn sign_internal_prepared_44(ssk: &SigningKey44, m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 2420]> {
    let mut sig = [0u8; 2420];
    if sign_prepared_internal::<4, 4>(&ML_DSA_44, &ssk.inner, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-44). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_44` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_44` pass.
///
/// Constant time: no branch depends on a coefficient. Each one contributes a mask bit, the bits are OR-ed, and
/// the result is compared with zero once (`encode::sk_is_well_formed`), with wrapping arithmetic, so the same holds
/// in builds with overflow checks. BINSEC reports it secure on x86_64 in every profile measured (including nearcore's
/// release settings: overflow checks, its target features, Rust 1.95.0), on thumbv7em, on riscv32imac and on AArch64
/// without NEON (`checkct/README.md`, sweep at 1a72d9e).
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
    verify_internal_x4::<6, 5>(&ML_DSA_65, pk, &prefix[..2 + ctx.len()], m, sig)
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
    verify_internal_x4::<6, 5>(&ML_DSA_65, pk, &[], m_prime, sig)
}

/// A public key prepared for repeated verification (ML-DSA-65): Â = ExpandA(ρ) and NTT(t1 · 2^d) in the NTT
/// domain, and tr = H(pk, 64), everything Algorithm 8 recomputes from the public key on every call.
///
/// Build it with [`verifying_key_65`], use it with [`verify_prepared_65`] and [`verify_internal_prepared_65`]. It holds
/// no secret. Size: 36,928 bytes (6·5 + 6 polynomials of 1 KiB, plus 64 bytes), so keep it in a `Box` or
/// a long-lived structure rather than on a small stack. The fields are private: the only way to obtain one is
/// `verifying_key_65`, which fixes the relation to the key bytes.
#[derive(Clone)]
pub struct VerifyingKey65 {
    inner: PreparedVk<6, 5>,
}

/// Prepares a public key for ML-DSA-65 verification: computes Â, NTT(t1 · 2^d) and tr once
/// (Algorithm 8 steps 1, 6, 7 and the key half of step 10). Cost: about one `verify_65` call minus the
/// per-signature work (dominated by ExpandA).
///
/// Never fails: every byte string of 1952 bytes decodes. Like `verify_65` it diverges only if the SHAKE output never
/// completes ExpandA (Proofs/Divergence.lean). Returns by value (36,928 bytes); with a
/// `Box`, write `Box::new(verifying_key_65(&pk))`.
pub fn verifying_key_65(pk: &[u8; 1952]) -> VerifyingKey65 {
    let mut vk = PreparedVk::<6, 5>::zeroed();
    prepare_vk_into_x4::<6, 5>(pk, &mut vk);
    VerifyingKey65 { inner: vk }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-65 against a prepared key. For `vk = verifying_key_65(pk)` it returns
/// exactly `verify_65(pk, m, ctx, sig)`. False if |ctx| > 255.
pub fn verify_prepared_65(vk: &VerifyingKey65, m: &[u8], ctx: &[u8], sig: &[u8; 3309]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_prepared_internal::<6, 5>(&ML_DSA_65, &vk.inner, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-65 against a prepared key: M′ is supplied by the caller. For
/// `vk = verifying_key_65(pk)` it returns exactly `verify_internal_65(pk, m_prime, sig)`.
pub fn verify_internal_prepared_65(vk: &VerifyingKey65, m_prime: &[u8], sig: &[u8; 3309]) -> bool {
    verify_prepared_internal::<6, 5>(&ML_DSA_65, &vk.inner, &[], m_prime, sig)
}

/// A secret key prepared for repeated signing (ML-DSA-65): ŝ1, ŝ2 and t̂0 in the NTT domain, Â = ExpandA(ρ), K and
/// tr, everything Algorithm 7 recomputes from the secret key on every call (steps 1-5, plus the key inputs of 6-7).
///
/// Build it with [`signing_key_65`], use it with [`sign_prepared_65`] and [`sign_internal_prepared_65`]. It holds
/// secret material (ŝ1, ŝ2, t̂0, K). With the `zeroize` feature, dropping it wipes those fields (a `cfg`-gated `Drop`
/// impl; outside the Lean model, which has no `Drop`). Not `Clone`: do not make extra copies of a secret.
/// Size: 48,224 bytes (6·5 + 5 + 2·6 = 47 polynomials of 1 KiB, plus 96 bytes), so keep it in a `Box` or a
/// long-lived structure rather than on a small stack; moving it copies it (the copy is not wiped). The fields are
/// private: the only way to obtain one is `signing_key_65`, which fixes the relation to the key bytes.
pub struct SigningKey65 {
    pub(crate) inner: PreparedSk<6, 5>,
}

/// Prepares a secret key for ML-DSA-65 signing: skDecode, the three NTTs and ExpandA (Algorithm 7 steps 1-5) once.
/// Cost: about the key-dependent share of one `sign_65` call, dominated by ExpandA.
///
/// Like `sign_65` it does not validate the key (see `sk_is_well_formed_65`) and diverges only if the SHAKE output
/// never completes ExpandA (Proofs/Divergence.lean). Returns by value (48,224 bytes); with a `Box`, write
/// `Box::new(signing_key_65(&sk))`.
pub fn signing_key_65(sk: &[u8; 4032]) -> SigningKey65 {
    let mut out = SigningKey65 { inner: PreparedSk::<6, 5>::zeroed() };
    prepare_sk_into::<6, 5>(&ML_DSA_65, sk, &mut out.inner);
    core::mem::replace(&mut out, SigningKey65 { inner: PreparedSk::<6, 5>::zeroed() })
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-65 with a prepared key. For `ssk = signing_key_65(sk)` it returns exactly
/// `sign_65(sk, m, ctx, rnd)`. `None` if |ctx| > 255 or the κ budget is exhausted. Same operations on secret data
/// as `sign_65` (only reorganized: no new branch depends on a secret).
pub fn sign_prepared_65(ssk: &SigningKey65, m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 3309]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 3309];
    if sign_prepared_internal::<6, 5>(&ML_DSA_65, &ssk.inner, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-65 with a prepared key: M′ is supplied by the caller. For
/// `ssk = signing_key_65(sk)` it returns exactly `sign_internal_65(sk, m_prime, rnd)`.
pub fn sign_internal_prepared_65(ssk: &SigningKey65, m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 3309]> {
    let mut sig = [0u8; 3309];
    if sign_prepared_internal::<6, 5>(&ML_DSA_65, &ssk.inner, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-65). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_65` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_65` pass.
///
/// Constant time: no branch depends on a coefficient. Each one contributes a mask bit, the bits are OR-ed, and
/// the result is compared with zero once (`encode::sk_is_well_formed`), with wrapping arithmetic, so the same holds
/// in builds with overflow checks. BINSEC reports it secure on x86_64 in every profile measured (including nearcore's
/// release settings: overflow checks, its target features, Rust 1.95.0), on thumbv7em, on riscv32imac and on AArch64
/// without NEON (`checkct/README.md`, sweep at 1a72d9e).
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
    verify_internal_x4::<8, 7>(&ML_DSA_87, pk, &prefix[..2 + ctx.len()], m, sig)
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
    verify_internal_x4::<8, 7>(&ML_DSA_87, pk, &[], m_prime, sig)
}

/// A public key prepared for repeated verification (ML-DSA-87): Â = ExpandA(ρ) and NTT(t1 · 2^d) in the NTT
/// domain, and tr = H(pk, 64), everything Algorithm 8 recomputes from the public key on every call.
///
/// Build it with [`verifying_key_87`], use it with [`verify_prepared_87`] and [`verify_internal_prepared_87`]. It holds
/// no secret. Size: 65,600 bytes (8·7 + 8 polynomials of 1 KiB, plus 64 bytes), so keep it in a `Box` or
/// a long-lived structure rather than on a small stack. The fields are private: the only way to obtain one is
/// `verifying_key_87`, which fixes the relation to the key bytes.
#[derive(Clone)]
pub struct VerifyingKey87 {
    inner: PreparedVk<8, 7>,
}

/// Prepares a public key for ML-DSA-87 verification: computes Â, NTT(t1 · 2^d) and tr once
/// (Algorithm 8 steps 1, 6, 7 and the key half of step 10). Cost: about one `verify_87` call minus the
/// per-signature work (dominated by ExpandA).
///
/// Never fails: every byte string of 2592 bytes decodes. Like `verify_87` it diverges only if the SHAKE output never
/// completes ExpandA (Proofs/Divergence.lean). Returns by value (65,600 bytes); with a
/// `Box`, write `Box::new(verifying_key_87(&pk))`.
pub fn verifying_key_87(pk: &[u8; 2592]) -> VerifyingKey87 {
    let mut vk = PreparedVk::<8, 7>::zeroed();
    prepare_vk_into_x4::<8, 7>(pk, &mut vk);
    VerifyingKey87 { inner: vk }
}

/// Algorithm 3 ML-DSA.Verify for ML-DSA-87 against a prepared key. For `vk = verifying_key_87(pk)` it returns
/// exactly `verify_87(pk, m, ctx, sig)`. False if |ctx| > 255.
pub fn verify_prepared_87(vk: &VerifyingKey87, m: &[u8], ctx: &[u8], sig: &[u8; 4627]) -> bool {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return false,
    };
    verify_prepared_internal::<8, 7>(&ML_DSA_87, &vk.inner, &prefix[..2 + ctx.len()], m, sig)
}

/// Algorithm 8 ML-DSA.Verify_internal for ML-DSA-87 against a prepared key: M′ is supplied by the caller. For
/// `vk = verifying_key_87(pk)` it returns exactly `verify_internal_87(pk, m_prime, sig)`.
pub fn verify_internal_prepared_87(vk: &VerifyingKey87, m_prime: &[u8], sig: &[u8; 4627]) -> bool {
    verify_prepared_internal::<8, 7>(&ML_DSA_87, &vk.inner, &[], m_prime, sig)
}

/// A secret key prepared for repeated signing (ML-DSA-87): ŝ1, ŝ2 and t̂0 in the NTT domain, Â = ExpandA(ρ), K and
/// tr, everything Algorithm 7 recomputes from the secret key on every call (steps 1-5, plus the key inputs of 6-7).
///
/// Build it with [`signing_key_87`], use it with [`sign_prepared_87`] and [`sign_internal_prepared_87`]. It holds
/// secret material (ŝ1, ŝ2, t̂0, K). With the `zeroize` feature, dropping it wipes those fields (a `cfg`-gated `Drop`
/// impl; outside the Lean model, which has no `Drop`). Not `Clone`: do not make extra copies of a secret.
/// Size: 80,992 bytes (8·7 + 7 + 2·8 = 79 polynomials of 1 KiB, plus 96 bytes), so keep it in a `Box` or a
/// long-lived structure rather than on a small stack; moving it copies it (the copy is not wiped). The fields are
/// private: the only way to obtain one is `signing_key_87`, which fixes the relation to the key bytes.
pub struct SigningKey87 {
    pub(crate) inner: PreparedSk<8, 7>,
}

/// Prepares a secret key for ML-DSA-87 signing: skDecode, the three NTTs and ExpandA (Algorithm 7 steps 1-5) once.
/// Cost: about the key-dependent share of one `sign_87` call, dominated by ExpandA.
///
/// Like `sign_87` it does not validate the key (see `sk_is_well_formed_87`) and diverges only if the SHAKE output
/// never completes ExpandA (Proofs/Divergence.lean). Returns by value (80,992 bytes); with a `Box`, write
/// `Box::new(signing_key_87(&sk))`.
pub fn signing_key_87(sk: &[u8; 4896]) -> SigningKey87 {
    let mut out = SigningKey87 { inner: PreparedSk::<8, 7>::zeroed() };
    prepare_sk_into::<8, 7>(&ML_DSA_87, sk, &mut out.inner);
    core::mem::replace(&mut out, SigningKey87 { inner: PreparedSk::<8, 7>::zeroed() })
}

/// Algorithm 2 ML-DSA.Sign for ML-DSA-87 with a prepared key. For `ssk = signing_key_87(sk)` it returns exactly
/// `sign_87(sk, m, ctx, rnd)`. `None` if |ctx| > 255 or the κ budget is exhausted. Same operations on secret data
/// as `sign_87` (only reorganized: no new branch depends on a secret).
pub fn sign_prepared_87(ssk: &SigningKey87, m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<[u8; 4627]> {
    let prefix = match ctx_prefix(ctx) {
        Some(b) => b,
        None => return None,
    };
    let mut sig = [0u8; 4627];
    if sign_prepared_internal::<8, 7>(&ML_DSA_87, &ssk.inner, &prefix[..2 + ctx.len()], m, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Algorithm 7 ML-DSA.Sign_internal for ML-DSA-87 with a prepared key: M′ is supplied by the caller. For
/// `ssk = signing_key_87(sk)` it returns exactly `sign_internal_87(sk, m_prime, rnd)`.
pub fn sign_internal_prepared_87(ssk: &SigningKey87, m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 4627]> {
    let mut sig = [0u8; 4627];
    if sign_prepared_internal::<8, 7>(&ML_DSA_87, &ssk.inner, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}

/// Optional check for secret keys loaded from untrusted storage (ML-DSA-87). True iff every coefficient of s₁
/// and s₂, as decoded by skDecode (FIPS 204 Algorithm 25: BitUnpack with a = b = η), lies in [−η, η]. t₀ needs no
/// check: its 13-bit field decodes to 4096 − z with z < 2¹³, always within [−4095, 4096].
///
/// FIPS 204 Algorithm 25 notes that s₁ and s₂ "may lie outside [−η, η] if input is malformed" and leaves
/// Sign's behavior there undefined. `sign_87` does not call this and follows the algorithm literally (it signs
/// with such a key); callers that load untrusted keys can call this first. Keys from `keygen_87` pass.
///
/// Constant time: no branch depends on a coefficient. Each one contributes a mask bit, the bits are OR-ed, and
/// the result is compared with zero once (`encode::sk_is_well_formed`), with wrapping arithmetic, so the same holds
/// in builds with overflow checks. BINSEC reports it secure on x86_64 in every profile measured (including nearcore's
/// release settings: overflow checks, its target features, Rust 1.95.0), on thumbv7em, on riscv32imac and on AArch64
/// without NEON (`checkct/README.md`, sweep at 1a72d9e).
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
