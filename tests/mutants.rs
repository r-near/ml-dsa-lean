//! Regression tests for planted-bug (mutation) survivors: boundary conditions that the differential suites
//! never hit.
//!
//! * `infinity_norm` at the (q - 1)/2 boundary (mutant: threshold `(q >> 1) + 1`).
//! * HintBitUnpack rejects a row count byte greater than omega (mutant: that check dropped).
//! * Verify rejects a signature whose z has ||z||_inf exactly gamma1 - beta (mutant: `<` became `<=`). Every
//!   other check of that signature passes, so only the norm comparison can reject it.
//! * Sign's loop guard allows the attempt at the largest κ whose nonces κ, …, κ + ℓ − 1 fit in 16 bits (mutant: the guard
//!   `kappa + ℓ - 1 <= 0xFFFF` became `<`, which skips ML-DSA-44's last attempt at κ = 65532). That attempt is reached
//!   only after thousands of rejections, so the test pins the guard itself, `sign::more_attempts`, which the loop calls.
//! * Verify rejects a flipped last byte of c-tilde. NOTE: this does NOT kill the `prefix_eq` off-by-one mutant
//!   (see the comment on that test); it is kept as a plain regression test.
use ml_dsa_lean::encode::{hint_bit_unpack, sig_decode, sk_decode};
use ml_dsa_lean::field::{Q, add, neg};
use ml_dsa_lean::keccak::Shake;
use ml_dsa_lean::keygen::keygen_internal;
use ml_dsa_lean::ntt::{matrix_vector_ntt, ntt, ntt_inverse, ntt_vec};
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params, pk_len, sig_len, sk_len};
use ml_dsa_lean::rounding::{infinity_norm, make_hint, poly_high_bits, poly_low_bits, vec_infinity_norm};
use ml_dsa_lean::sampling::{expand_a, expand_mask, sample_in_ball};
use ml_dsa_lean::sign::{more_attempts, sign_internal};
use ml_dsa_lean::verify::verify_internal;

/// Dispatch a generic-over-(K, L) function on the parameter set.
macro_rules! with_kl {
    ($p:expr, $f:ident($($arg:expr),*)) => {
        match $p.k {
            4 => $f::<4, 4>($($arg),*),
            6 => $f::<6, 5>($($arg),*),
            8 => $f::<8, 7>($($arg),*),
            _ => unreachable!(),
        }
    };
}

const SETS: [(&str, Params); 3] = [("ML-DSA-44", ML_DSA_44), ("ML-DSA-65", ML_DSA_65), ("ML-DSA-87", ML_DSA_87)];

fn keypair_kl<const K: usize, const L: usize>(p: &Params, xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
    let mut pk = vec![0u8; pk_len(p)];
    let mut sk = vec![0u8; sk_len(p)];
    keygen_internal::<K, L>(p, xi, &mut pk, &mut sk);
    (pk, sk)
}

fn keypair(p: &Params) -> (Vec<u8>, Vec<u8>) {
    let xi: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(p.k as u8));
    with_kl!(p, keypair_kl(p, &xi))
}

fn sign_kl<const K: usize, const L: usize>(p: &Params, sk: &[u8], m: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    let mut sig = vec![0u8; sig_len(p)];
    assert!(sign_internal::<K, L>(p, sk, &[], m, rnd, &mut sig), "sign exhausted");
    sig
}

fn sign(p: &Params, sk: &[u8], m: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    with_kl!(p, sign_kl(p, sk, m, rnd))
}

fn verify_kl<const K: usize, const L: usize>(p: &Params, pk: &[u8], m: &[u8], sig: &[u8]) -> bool {
    verify_internal::<K, L>(p, pk, &[], m, sig)
}

fn verify(p: &Params, pk: &[u8], m: &[u8], sig: &[u8]) -> bool {
    with_kl!(p, verify_kl(p, pk, m, sig))
}

// ---------------------------------------------------------------------------------------------------------
// M12: rounding::infinity_norm threshold.
// ---------------------------------------------------------------------------------------------------------

/// FIPS 204 definition: |r mod± q|, where r mod± q is the representative of r mod q in [-(q-1)/2, (q-1)/2].
fn infinity_norm_reference(r: u32) -> u32 {
    let q = Q as i64;
    let mut s = (r as i64).rem_euclid(q);
    if s > (q - 1) / 2 {
        s -= q;
    }
    s.unsigned_abs() as u32
}

#[test]
fn infinity_norm_boundary() {
    assert_eq!(Q, 8_380_417);
    let half = (Q - 1) / 2;
    assert_eq!(half, 4_190_208);
    // Pinned values: the boundary itself, and its neighbor, which must wrap around to q - r.
    assert_eq!(infinity_norm(half), 4_190_208);
    assert_eq!(infinity_norm(half + 1), 4_190_208, "r = (q+1)/2 has |r mod± q| = (q-1)/2");
    assert_eq!(infinity_norm(0), 0);
    assert_eq!(infinity_norm(1), 1);
    assert_eq!(infinity_norm(Q - 1), 1);
    assert_eq!(infinity_norm(Q - 2), 2);
    // Every value near the boundary and near both ends, against the definition.
    for r in (0..64).chain(half - 64..half + 64).chain(Q - 64..Q) {
        assert_eq!(infinity_norm(r), infinity_norm_reference(r), "r = {r}");
    }
    // Coarse sweep of the whole range.
    let mut r = 0;
    while r < Q {
        assert_eq!(infinity_norm(r), infinity_norm_reference(r), "r = {r}");
        r += 4_093;
    }
}

// ---------------------------------------------------------------------------------------------------------
// M13: HintBitUnpack rejects a row count byte greater than omega.
// ---------------------------------------------------------------------------------------------------------

/// A hint block y (omega + K bytes) whose first omega bytes are strictly increasing positions 0..omega-1 and
/// whose count bytes are `counts`.
fn hint_block(p: &Params, counts: &[u8]) -> Vec<u8> {
    let mut y = vec![0u8; p.omega + p.k];
    for j in 0..p.omega {
        y[j] = j as u8;
    }
    y[p.omega..].copy_from_slice(counts);
    y
}

fn hint_unpack_is_none(p: &Params, y: &[u8]) -> bool {
    fn go<const K: usize, const L: usize>(p: &Params, y: &[u8]) -> bool {
        hint_bit_unpack::<K>(p, y).is_none()
    }
    with_kl!(p, go(p, y))
}

fn sig_decode_is_none(p: &Params, sig: &[u8]) -> bool {
    fn go<const K: usize, const L: usize>(p: &Params, sig: &[u8]) -> bool {
        sig_decode::<K, L>(p, sig).is_none()
    }
    with_kl!(p, go(p, sig))
}

#[test]
fn hint_bit_unpack_rejects_count_above_omega() {
    for (name, p) in SETS {
        let (pk, sk) = keypair(&p);
        let msg = b"hint count above omega";
        let sig = sign(&p, &sk, msg, &[0u8; 32]);
        assert!(verify(&p, &pk, msg, &sig), "{name}: control signature must verify");
        let hint_off = sig.len() - (p.omega + p.k);
        // Control: the genuine hint block decodes.
        assert!(!hint_unpack_is_none(&p, &sig[hint_off..]), "{name}: control hint block must decode");

        let w = p.omega as u8;
        // A: every count byte is omega + 1 (non-decreasing, every position byte strictly increasing).
        let all_over = vec![w + 1; p.k];
        // B: all counts omega except the last, which is omega + 1 (non-decreasing).
        let mut last_over = vec![w; p.k];
        last_over[p.k - 1] = w + 1;
        // C: a larger overshoot in the last row only.
        let mut last_far_over = vec![w; p.k];
        last_far_over[p.k - 1] = w + 40;
        // D: valid until the last row, which jumps to 255.
        let mut last_max = vec![0u8; p.k];
        last_max[p.k - 1] = 255;
        // A control with the same shape that is legal: all counts exactly omega.
        let at_omega = vec![w; p.k];
        assert!(!hint_unpack_is_none(&p, &hint_block(&p, &at_omega)), "{name}: count = omega is legal");

        for (label, counts) in [("A", all_over), ("B", last_over), ("C", last_far_over), ("D", last_max)] {
            let y = hint_block(&p, &counts);
            assert!(hint_unpack_is_none(&p, &y), "{name}/{label}: hint_bit_unpack accepted counts {counts:?}");
            // Same through sigDecode and Verify, on a signature whose hint block is replaced.
            let mut bad = sig.clone();
            bad[hint_off..].copy_from_slice(&y);
            assert!(sig_decode_is_none(&p, &bad), "{name}/{label}: sig_decode accepted counts {counts:?}");
            assert!(!verify(&p, &pk, msg, &bad), "{name}/{label}: verify accepted counts {counts:?}");
        }
    }
}

// ---------------------------------------------------------------------------------------------------------
// M5: c-tilde comparison covers all lambda/4 bytes.
// ---------------------------------------------------------------------------------------------------------

/// Flipping the LAST byte of c-tilde must be rejected, for every parameter set.
///
/// Honest limitation: this test does not distinguish the `prefix_eq` off-by-one mutant (compare lambda/4 - 1
/// bytes). c-tilde seeds SampleInBall, so flipping any of its bytes changes c, hence w1' and the recomputed
/// c-tilde', which then differs from the signature's c-tilde in the early bytes too (probability 1 - 2^-248).
/// A discriminating input would need c-tilde' == c-tilde on the first lambda/4 - 1 bytes but not the last,
/// which is a 2^248 search. `prefix_eq` is a private function, so it cannot be called from an integration
/// test either.
#[test]
fn verify_rejects_flipped_last_byte_of_c_tilde() {
    for (name, p) in SETS {
        let (pk, sk) = keypair(&p);
        let msg = b"flip the last c-tilde byte";
        let sig = sign(&p, &sk, msg, &[0u8; 32]);
        assert!(verify(&p, &pk, msg, &sig), "{name}: control signature must verify");
        assert_eq!(p.c_tilde_len, [32, 48, 64][[4, 6, 8].iter().position(|&k| k == p.k).unwrap()]);
        for bit in 0..8 {
            let mut bad = sig.clone();
            bad[p.c_tilde_len - 1] ^= 1 << bit;
            assert!(!verify(&p, &pk, msg, &bad), "{name}: accepted c-tilde with last-byte bit {bit} flipped");
        }
        // The first byte too, for symmetry.
        let mut bad = sig.clone();
        bad[0] ^= 1;
        assert!(!verify(&p, &pk, msg, &bad), "{name}: accepted c-tilde with first byte flipped");
    }
}

// ---------------------------------------------------------------------------------------------------------
// M15: Verify's ||z||_inf < gamma1 - beta.
// ---------------------------------------------------------------------------------------------------------

/// Sign_internal's rejection-loop body (Algorithm 7 steps 11-29, empty M' prefix) with a switch for the
/// ||z||_inf test. `strict` is the real signer (reject when ||z||_inf >= gamma1 - beta). With `strict` false,
/// ||z||_inf == gamma1 - beta is accepted, so a signature with exactly that norm can be produced; every other
/// check is unchanged. Returns (c-tilde, z, h) or None for a rejected attempt.
#[allow(clippy::type_complexity)]
fn attempt_kl<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    m: &[u8],
    rnd: &[u8; 32],
    kappa: u16,
    strict: bool,
) -> Option<(Vec<u8>, [[u32; 256]; L], [[bool; 256]; K])> {
    let key = sk_decode::<K, L>(p, sk);
    let s1_hat = ntt_vec(&key.s1);
    let s2_hat = ntt_vec(&key.s2);
    let t0_hat = ntt_vec(&key.t0);
    let a_hat = expand_a::<K, L>(&key.rho);
    let mut mu = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&key.tr);
    h.absorb(m);
    h.finalize();
    h.squeeze(&mut mu);
    let mut rho_pp = [0u8; 64];
    let mut h = Shake::shake256();
    h.absorb(&key.key);
    h.absorb(rnd);
    h.absorb(&mu);
    h.finalize();
    h.squeeze(&mut rho_pp);

    let y = expand_mask::<L>(p, &rho_pp, kappa);
    let w_hat = matrix_vector_ntt::<K, L>(&a_hat, &ntt_vec(&y));
    let mut w = [[0u32; 256]; K];
    let mut w1 = [[0u32; 256]; K];
    for i in 0..K {
        w[i] = ntt_inverse(&w_hat[i]);
        w1[i] = poly_high_bits(p, &w[i]);
    }
    let mut w1_enc = vec![0u8; K * 32 * p.w1_bits];
    ml_dsa_lean::encode::w1_encode(p, &w1, &mut w1_enc);
    let mut c_tilde = vec![0u8; p.c_tilde_len];
    let mut h = Shake::shake256();
    h.absorb(&mu);
    h.absorb(&w1_enc);
    h.finalize();
    h.squeeze(&mut c_tilde);
    let c_hat = ntt(&sample_in_ball(p, &c_tilde));

    let cs1 = ntt_vec_scalar::<L>(&c_hat, &s1_hat);
    let cs2 = ntt_vec_scalar::<K>(&c_hat, &s2_hat);
    let mut z = [[0u32; 256]; L];
    for i in 0..L {
        for j in 0..256 {
            z[i][j] = add(y[i][j], cs1[i][j]);
        }
    }
    let mut w_cs2 = [[0u32; 256]; K];
    let mut r0 = [[0u32; 256]; K];
    for i in 0..K {
        for j in 0..256 {
            w_cs2[i][j] = ml_dsa_lean::field::sub(w[i][j], cs2[i][j]);
        }
        r0[i] = poly_low_bits(p, &w_cs2[i]);
    }
    let bound = p.gamma1 - p.beta;
    let z_norm = vec_infinity_norm(&z);
    let z_bad = if strict { z_norm >= bound } else { z_norm > bound };
    if z_bad || vec_infinity_norm(&r0) >= p.gamma2 - p.beta {
        return None;
    }
    let ct0 = ntt_vec_scalar::<K>(&c_hat, &t0_hat);
    let mut hint = [[false; 256]; K];
    let mut ones = 0;
    for i in 0..K {
        for j in 0..256 {
            hint[i][j] = make_hint(p, neg(ct0[i][j]), add(w_cs2[i][j], ct0[i][j]));
            ones += hint[i][j] as usize;
        }
    }
    if vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega {
        return None;
    }
    Some((c_tilde, z, hint))
}

fn ntt_vec_scalar<const N: usize>(c_hat: &[u32; 256], v_hat: &[[u32; 256]; N]) -> [[u32; 256]; N] {
    ml_dsa_lean::ntt::scalar_vector_ntt_inverse::<N>(c_hat, v_hat)
}

/// `attempt_kl` with the strict (real) norm check, as a full signing loop: must equal `sign_internal`.
fn strict_sign_kl<const K: usize, const L: usize>(p: &Params, sk: &[u8], m: &[u8], rnd: &[u8; 32]) -> Vec<u8> {
    let mut kappa = 0u32;
    while kappa + L as u32 - 1 <= 0xFFFF {
        if let Some((c_tilde, z, h)) = attempt_kl::<K, L>(p, sk, m, rnd, kappa as u16, true) {
            let mut sig = vec![0u8; sig_len(p)];
            ml_dsa_lean::encode::sig_encode::<K, L>(p, &c_tilde, &z, &h, &mut sig);
            return sig;
        }
        kappa += L as u32;
    }
    panic!("kappa budget exhausted");
}

/// Search rnd = 0, 1, 2, ... (kappa = 0) for an attempt that passes every signer check with the relaxed norm
/// test and has ||z||_inf exactly gamma1 - beta. Returns the encoded signature and the number of tries.
fn boundary_sig_kl<const K: usize, const L: usize>(p: &Params, sk: &[u8], m: &[u8]) -> (Vec<u8>, usize) {
    let bound = p.gamma1 - p.beta;
    for n in 0..400_000usize {
        let mut rnd = [0u8; 32];
        rnd[..8].copy_from_slice(&(n as u64).to_le_bytes());
        if let Some((c_tilde, z, h)) = attempt_kl::<K, L>(p, sk, m, &rnd, 0, false) {
            if vec_infinity_norm(&z) == bound {
                let mut sig = vec![0u8; sig_len(p)];
                ml_dsa_lean::encode::sig_encode::<K, L>(p, &c_tilde, &z, &h, &mut sig);
                return (sig, n + 1);
            }
        }
    }
    panic!("no boundary signature found");
}

#[test]
fn verify_rejects_z_norm_exactly_gamma1_minus_beta() {
    let msg = b"z at exactly gamma1 - beta";
    for (name, p) in SETS {
        let (pk, sk) = keypair(&p);

        // The reimplemented signing loop (strict check) reproduces the real signer, so the relaxed variant
        // differs from it in the norm comparison only.
        for n in 0..2u8 {
            let rnd = [n; 32];
            let real = sign(&p, &sk, msg, &rnd);
            let mine = with_kl!(p, strict_sign_kl(&p, &sk, msg, &rnd));
            assert_eq!(real, mine, "{name}: reimplemented signer differs from sign_internal");
            assert!(verify(&p, &pk, msg, &real), "{name}: control signature must verify");
        }

        let (sig, tries) = with_kl!(p, boundary_sig_kl(&p, &sk, msg));
        eprintln!("{name}: boundary signature found after {tries} attempts");
        // The signature is well formed and its z has exactly the boundary norm.
        let norm = with_kl!(p, z_norm_of_sig(&p, &sig));
        assert_eq!(norm, p.gamma1 - p.beta, "{name}: construction error");
        // Everything but the norm test passes (c-tilde matches, hints decode), yet FIPS 204 Verify requires
        // ||z||_inf < gamma1 - beta strictly.
        assert!(!verify(&p, &pk, msg, &sig), "{name}: Verify accepted ||z||_inf == gamma1 - beta");
    }
}

fn z_norm_of_sig<const K: usize, const L: usize>(p: &Params, sig: &[u8]) -> u32 {
    let (_, z, _) = sig_decode::<K, L>(p, sig).expect("decodes");
    vec_infinity_norm(&z)
}

/// The κ values the signing loop visits, by running the loop on its guard alone, for L = `L`: the count is
/// ⌊(2¹⁶ − ℓ)/ℓ⌋ + 1 (`kappaBudget` in the Lean spec), and the last one is the largest multiple of ℓ whose ExpandMask
/// nonces κ, …, κ + ℓ − 1 are all below 2¹⁶. A guard that is one too strict (`<` for `<=`) stops one attempt early; one
/// too lax would visit κ = 2¹⁶ − ℓ + 1 or more and ExpandMask's 16-bit nonce would wrap.
fn guard_boundary<const L: usize>() {
    let l = L as u32;
    let mut kappa = 0u32;
    let mut visited = 0u32;
    let mut last = 0u32;
    while more_attempts::<L>(kappa) {
        last = kappa;
        visited += 1;
        kappa += l;
    }
    assert_eq!(visited, (65536 - l) / l + 1, "L = {L}: number of attempts the guard allows");
    // The last allowed attempt uses nonces up to 0xFFFF at most, and the next one would not fit.
    assert!(last + l - 1 <= 0xFFFF, "L = {L}: the last attempt at {last} overflows the 16-bit nonce");
    assert!(last + 2 * l - 1 > 0xFFFF, "L = {L}: the guard stopped early, the attempt at {} was skipped", last + l);
    // Exact boundary, from both sides.
    assert!(more_attempts::<L>(65536 - l), "L = {L}: kappa = 65536 - L must be allowed");
    assert!(!more_attempts::<L>(65536 - l + 1), "L = {L}: kappa = 65536 - L + 1 must not be allowed");
}

#[test]
fn sign_loop_guard_allows_the_last_attempt() {
    guard_boundary::<4>(); // ML-DSA-44: the last attempt is at κ = 65532, nonces 65532 … 65535
    guard_boundary::<5>(); // ML-DSA-65: κ = 65530
    guard_boundary::<7>(); // ML-DSA-87: κ = 65527
    assert!(more_attempts::<4>(65532));
    assert!(!more_attempts::<4>(65536));
}
