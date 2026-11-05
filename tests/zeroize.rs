//! What the `zeroize` feature wipes, tested from the outside.
//!
//! 1. `signing_key_drop_wipes_*`: drop a `SigningKeyNN` in place (`ManuallyDrop` + `drop_in_place`), then read its
//!    secret fields (ŝ1, ŝ2, t̂0, K) back with volatile reads: all zero; and the struct's bytes hold no copy of K.
//! 2. `stack_residue_*`: paint the stack below the test frame, run one library call from a frame that holds the
//!    result, then read the painted region back (the library's own dead frames) and search it for copies of the
//!    secrets: K, the decoded s1/s2/t0, their NTT forms, and the derived seeds ρ′ and ρ″. A copy in the caller's own
//!    frame (the returned struct, which is moved around by the compiler) is outside the scanned region and is the
//!    caller's concern, as `PreparedSk`'s documentation says.
//! 3. `shake_wipe_zeroes_the_sponge`: `Shake::wipe` zeroes the sponge.
//!
//! What the stack scan still finds is listed in `KEYGEN_KNOWN` and `PK_FROM_SK_KNOWN` and in the documentation of
//! `keygen_internal` and `pk_from_sk`: t0 survives in a by-value temporary (`vec_power2round`'s tuple), and in KeyGen
//! one copy of K. The scan asserts everything else, including all of Sign and `signing_key_*`.
//!
//! Needs `--features zeroize` (and `internals`, which the crate's self dev-dependency turns on). The stack scan
//! reads memory the abstract machine considers uninitialized, with volatile loads; it is a test of what the machine
//! code leaves behind, not of anything the language specifies.
#![cfg(all(feature = "zeroize", feature = "internals"))]
#![allow(clippy::needless_range_loop)]

use ml_dsa_lean::api::*;
use ml_dsa_lean::encode::{sk_decode, w1_encode};
use ml_dsa_lean::field::{add, neg};
use ml_dsa_lean::keccak::Shake;
use ml_dsa_lean::ntt::{matrix_vector_ntt, multiply_ntt, ntt, ntt_inverse, ntt_vec, scalar_vector_ntt_inverse, sub_poly};
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use ml_dsa_lean::rounding::{make_hint, poly_high_bits, poly_low_bits, vec_infinity_norm};
use ml_dsa_lean::sampling::{expand_a, expand_mask, sample_in_ball};
use ml_dsa_lean::sign::{PreparedSk, prepare_sk};
use std::hint::black_box;
use std::mem::{size_of, ManuallyDrop, MaybeUninit};
use std::ptr;

/// Labels the KeyGen stack scan is known to find (not wiped, see the module comment).
const KEYGEN_KNOWN: &[&str] = &["K", "t0[0]", "t0[1]", "t0[2]", "t0[3]", "t0[4]", "t0[5]", "t0[6]", "t0[7]"];
/// The same for `pk_from_sk`: only the recomputed t0 (the tuple `vec_power2round` returns by value).
const PK_FROM_SK_KNOWN: &[&str] = &["t0[0]", "t0[1]", "t0[2]", "t0[3]", "t0[4]", "t0[5]", "t0[6]", "t0[7]"];

fn read_bytes(ptr: *const u8, len: usize) -> Vec<u8> {
    // SAFETY: callers pass a pointer into a live (possibly already dropped, but not freed) object of `len` bytes.
    (0..len).map(|i| unsafe { ptr::read_volatile(ptr.add(i)) }).collect()
}

fn contains(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

/// Stack bytes painted and scanned. More than the deepest call chain of any function tested (Sign for ML-DSA-87
/// uses about 239 KB, `tools/stack/README.md`).
const SCAN: usize = 512 * 1024;

fn pattern(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

/// A secret to look for: a label and a byte pattern that identifies it (the first 16 coefficients of a
/// polynomial, 64 bytes, or a whole seed).
struct Needle {
    label: String,
    bytes: Vec<u8>,
}

fn poly_needles(label: &str, v: &[[u32; 256]], out: &mut Vec<Needle>) {
    for (i, p) in v.iter().enumerate() {
        out.push(Needle { label: format!("{label}[{i}]"), bytes: pattern(&p[..16]) });
    }
}

#[inline(never)]
fn paint() {
    let mut buf = [0xA5u8; SCAN];
    black_box(&mut buf);
}

/// Reads back the region `paint` covered (the same depth), copies it to the heap, returns the hits per needle.
#[inline(never)]
fn scan(needles: &[Needle]) -> Vec<(String, usize)> {
    let buf = MaybeUninit::<[u8; SCAN]>::uninit();
    let p = buf.as_ptr() as *const u8;
    let mut snap = Vec::with_capacity(SCAN);
    for i in 0..SCAN {
        // SAFETY: in bounds of `buf`; the byte may be uninitialized, which a volatile load of a u8 tolerates in practice.
        snap.push(unsafe { std::ptr::read_volatile(p.add(i)) });
    }
    black_box(&buf);
    needles
        .iter()
        .map(|n| {
            let hits = snap.windows(n.bytes.len()).filter(|w| *w == n.bytes.as_slice()).count();
            (n.label.clone(), hits)
        })
        .collect()
}

fn xi(seed: u8) -> [u8; 32] {
    let mut x = [0u8; 32];
    for (i, b) in x.iter_mut().enumerate() {
        *b = seed.wrapping_mul(31).wrapping_add(i as u8 * 7 + 1);
    }
    x
}

/// Needles for a stored secret key: K, decoded s1/s2/t0 and their NTT forms.
fn sk_needles<const K: usize, const L: usize>(p: &Params, sk: &[u8]) -> Vec<Needle> {
    let d = sk_decode::<K, L>(p, sk);
    let mut v = vec![Needle { label: "K".into(), bytes: d.key.to_vec() }];
    poly_needles("s1", &d.s1, &mut v);
    poly_needles("s2", &d.s2, &mut v);
    poly_needles("t0", &d.t0, &mut v);
    poly_needles("s1_hat", &ntt_vec(&d.s1), &mut v);
    poly_needles("s2_hat", &ntt_vec(&d.s2), &mut v);
    poly_needles("t0_hat", &ntt_vec(&d.t0), &mut v);
    v
}

fn shake256(parts: &[&[u8]], n: usize) -> Vec<u8> {
    let mut h = Shake::shake256();
    for p in parts {
        h.absorb(p);
    }
    h.finalize();
    let mut out = vec![0u8; n];
    h.squeeze(&mut out);
    out
}

/// How a Sign attempt ends (Algorithm 7 steps 23 and 28).
#[derive(Clone, Copy, PartialEq, Debug)]
enum Outcome {
    /// Rejected on ‖z‖∞ ≥ γ1 − β or ‖r0‖∞ ≥ γ2 − β: the attempt returns before computing ct0 and h.
    RejectedEarly,
    /// Rejected on ‖ct0‖∞ ≥ γ2 or more than ω ones in h.
    RejectedLate,
    Accepted,
}

/// The secrets of Sign attempt number `att` (κ = att·ℓ), Algorithm 7 steps 11-26 rebuilt from the library's own pieces:
/// y, ŷ, w, ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, w − ⟨⟨cs2⟩⟩, r0 and ⟨⟨ct0⟩⟩ (an attempt that is rejected early never computes `ct0`, so
/// that needle is never found there, which is not an error). For a rejected attempt also z = y + ⟨⟨cs1⟩⟩ and c̃, which
/// are not published (an accepted attempt's are the signature). Returns c̃ and the outcome of the attempt.
fn attempt_secrets<const K: usize, const L: usize>(
    p: &Params,
    d: &ml_dsa_lean::encode::SecretKey<K, L>,
    mu: &[u8],
    rho_pp: &[u8; 64],
    att: usize,
    out: &mut Vec<Needle>,
) -> (Vec<u8>, Outcome) {
    let a_hat = expand_a::<K, L>(&d.rho);
    let (s1_hat, s2_hat, t0_hat) = (ntt_vec(&d.s1), ntt_vec(&d.s2), ntt_vec(&d.t0));
    let y = expand_mask::<L>(p, rho_pp, (att * L) as u16);
    let w_hat = matrix_vector_ntt::<K, L>(&a_hat, &ntt_vec(&y));
    let mut w = [[0u32; 256]; K];
    let mut w1 = [[0u32; 256]; K];
    for i in 0..K {
        w[i] = ntt_inverse(&w_hat[i]);
        w1[i] = poly_high_bits(p, &w[i]);
    }
    let mut enc = vec![0u8; 8 * 192];
    w1_encode::<K>(p, &w1, &mut enc);
    let ct = shake256(&[mu, &enc[..K * 32 * p.w1_bits]], p.c_tilde_len);
    let c_hat = ntt(&sample_in_ball(p, &ct));
    let cs1 = scalar_vector_ntt_inverse::<L>(&c_hat, &s1_hat);
    let cs2 = scalar_vector_ntt_inverse::<K>(&c_hat, &s2_hat);
    let ct0 = scalar_vector_ntt_inverse::<K>(&c_hat, &t0_hat);
    let mut z = [[0u32; 256]; L];
    for i in 0..L {
        for j in 0..256 {
            z[i][j] = add(y[i][j], cs1[i][j]);
        }
    }
    let mut w_cs2 = [[0u32; 256]; K];
    let mut r0 = [[0u32; 256]; K];
    let mut ones = 0;
    for i in 0..K {
        w_cs2[i] = sub_poly(&w[i], &cs2[i]);
        r0[i] = poly_low_bits(p, &w_cs2[i]);
        for j in 0..256 {
            ones += make_hint(p, neg(ct0[i][j]), add(w_cs2[i][j], ct0[i][j])) as usize;
        }
    }
    let outcome = if vec_infinity_norm(&z) >= p.gamma1 - p.beta || vec_infinity_norm(&r0) >= p.gamma2 - p.beta {
        Outcome::RejectedEarly
    } else if vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega {
        Outcome::RejectedLate
    } else {
        Outcome::Accepted
    };
    let tag = format!("att{att}({outcome:?})");
    poly_needles(&format!("{tag} y"), &y, out);
    let y_hat = ntt_vec(&y);
    poly_needles(&format!("{tag} y_hat"), &y_hat, out);
    // Â ∘ ŷ in the NTT domain (the transform of w) and its K·ℓ terms Â[i][j] ∘ ŷ[j].
    poly_needles(&format!("{tag} w_hat"), &w_hat, out);
    for i in 0..K {
        let terms: Vec<[u32; 256]> = (0..L).map(|j| multiply_ntt(&a_hat[i][j], &y_hat[j])).collect();
        poly_needles(&format!("{tag} a_y[{i}]"), &terms, out);
    }
    // ĉ ∘ ŝ1, ĉ ∘ ŝ2 and ĉ ∘ t̂0: the NTT forms of ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩ and ⟨⟨ct0⟩⟩.
    let cs_hat = |v: &[[u32; 256]]| -> Vec<[u32; 256]> { v.iter().map(|x| multiply_ntt(&c_hat, x)).collect() };
    poly_needles(&format!("{tag} c_s1_hat"), &cs_hat(&s1_hat), out);
    poly_needles(&format!("{tag} c_s2_hat"), &cs_hat(&s2_hat), out);
    if outcome != Outcome::RejectedEarly {
        poly_needles(&format!("{tag} c_t0_hat"), &cs_hat(&t0_hat), out);
    }
    poly_needles(&format!("{tag} c_hat"), &[c_hat], out);
    poly_needles(&format!("{tag} w"), &w, out);
    poly_needles(&format!("{tag} cs1"), &cs1, out);
    poly_needles(&format!("{tag} cs2"), &cs2, out);
    poly_needles(&format!("{tag} w_cs2"), &w_cs2, out);
    poly_needles(&format!("{tag} r0"), &r0, out);
    if outcome != Outcome::RejectedEarly {
        poly_needles(&format!("{tag} ct0"), &ct0, out);
    }
    if outcome != Outcome::Accepted {
        poly_needles(&format!("{tag} z"), &z, out);
        out.push(Needle { label: format!("{tag} c_tilde"), bytes: ct.clone() });
    }
    (ct, outcome)
}

/// `attempt_secrets` for every attempt up to and including the accepted one, the one whose c̃ is `c_tilde`. Returns
/// the number of rejected attempts before the accepted one.
fn attempt_needles<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    mu: &[u8],
    rho_pp: &[u8; 64],
    c_tilde: &[u8],
    out: &mut Vec<Needle>,
) -> usize {
    let d = sk_decode::<K, L>(p, sk);
    for att in 0..200usize {
        let (ct, outcome) = attempt_secrets::<K, L>(p, &d, mu, rho_pp, att, out);
        // The rebuilt attempt agrees with the library's: it is the accepted one iff its c̃ is the signature's.
        assert_eq!(outcome == Outcome::Accepted, ct == c_tilde, "the rebuilt attempt {att} disagrees with Sign");
        if outcome == Outcome::Accepted {
            return att;
        }
    }
    panic!("no attempt reproduces the signature's c-tilde");
}

/// The first attempt (κ = att·ℓ) of the key and (μ, ρ″) that ends as `want`, and the needles of its secrets.
fn find_attempt<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    mu: &[u8],
    rho_pp: &[u8; 64],
    want: Outcome,
) -> (usize, Vec<Needle>) {
    let d = sk_decode::<K, L>(p, sk);
    for att in 0..5000usize {
        let mut v = Vec::new();
        if attempt_secrets::<K, L>(p, &d, mu, rho_pp, att, &mut v).1 == want {
            return (att, v);
        }
    }
    panic!("no attempt ends as {want:?} within 5000 attempts");
}

/// All needles for a Sign call on message `m` with context "ctx" and rnd = 7…7: the stored key's secrets, ρ″ and the
/// attempts (`attempt_needles`). `sign_fn` is the call under test (it returns the signature, whose first c̃ bytes
/// identify the accepted attempt). Returns the needles and the number of rejected attempts before the accepted one.
fn sign_needles_for<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    m: &[u8],
    sign_fn: &dyn Fn(&[u8]) -> Vec<u8>,
) -> (Vec<Needle>, usize) {
    let mut needles = sk_needles::<K, L>(p, sk);
    // ρ″ = H(K ‖ rnd ‖ μ, 64), μ = H(tr ‖ M′, 64), M′ = 0 ‖ |ctx| ‖ ctx ‖ M.
    let d = sk_decode::<K, L>(p, sk);
    let mut mp = vec![0u8, 3];
    mp.extend_from_slice(b"ctx");
    mp.extend_from_slice(m);
    let mu = shake256(&[&d.tr, &mp], 64);
    let rho_pp = shake256(&[&d.key, &[7u8; 32], &mu], 64);
    needles.push(Needle { label: "rho_pp".into(), bytes: rho_pp.clone() });
    let sig = sign_fn(m);
    let rejected = attempt_needles::<K, L>(p, sk, &mu, rho_pp.as_slice().try_into().unwrap(), &sig[..p.c_tilde_len], &mut needles);
    (needles, rejected)
}

/// A message for which Sign rejects at least one attempt before it accepts (about three in four messages for
/// ML-DSA-44, more for the others), so the scan sees the secrets of a rejected attempt as well as of the accepted one.
fn message_with_rejection<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    sign_fn: &dyn Fn(&[u8]) -> Vec<u8>,
) -> (Vec<u8>, Vec<Needle>) {
    for t in 0..64u8 {
        let mut m = b"stack residue message".to_vec();
        m.push(t);
        let (needles, rejected) = sign_needles_for::<K, L>(p, sk, &m, sign_fn);
        if rejected > 0 {
            return (m, needles);
        }
    }
    panic!("no test message with a rejected attempt");
}

/// Prints the hits and returns the labels with a nonzero count.
fn report(name: &str, hits: &[(String, usize)]) -> Vec<String> {
    let found: Vec<&(String, usize)> = hits.iter().filter(|(_, c)| *c > 0).collect();
    let bad: Vec<String> = found.iter().map(|(l, c)| format!("{l} x{c}")).collect();
    eprintln!("{name}: {} secret patterns searched, residue: {}", hits.len(), if bad.is_empty() { "none".into() } else { bad.join(", ") });
    found.into_iter().map(|(l, _)| l.clone()).collect()
}

macro_rules! residue_tests {
    ($set:ident, $p:expr, $k:literal, $l:literal, $keygen:ident, $signing_key:ident, $sign:ident, $sign_prepared:ident,
     $SK:literal, $SKT:ty, $pk_from_sk:ident) => {
        mod $set {
            use super::*;

            #[inline(never)]
            fn exp_keygen(x: &[u8; 32], needles: &[Needle]) -> Vec<(String, usize)> {
                paint();
                let r = black_box($keygen(x));
                let hits = scan(needles);
                black_box(&r);
                hits
            }

            #[inline(never)]
            fn exp_signing_key(sk: &[u8; $SK], needles: &[Needle]) -> Vec<(String, usize)> {
                paint();
                let b = Box::new($signing_key(sk));
                drop(black_box(b));
                scan(needles)
            }

            #[inline(never)]
            fn exp_sign(sk: &[u8; $SK], m: &[u8], needles: &[Needle]) -> Vec<(String, usize)> {
                paint();
                let r = black_box($sign(sk, m, b"ctx", &[7u8; 32]));
                let hits = scan(needles);
                black_box(&r);
                hits
            }

            #[inline(never)]
            fn exp_sign_prepared(ssk: &$SKT, m: &[u8], needles: &[Needle]) -> Vec<(String, usize)> {
                paint();
                let r = black_box($sign_prepared(ssk, m, b"ctx", &[7u8; 32]));
                let hits = scan(needles);
                black_box(&r);
                hits
            }

            #[inline(never)]
            fn exp_pk_from_sk(sk: &[u8; $SK], needles: &[Needle]) -> Vec<(String, usize)> {
                paint();
                let r = black_box($pk_from_sk(sk));
                let hits = scan(needles);
                black_box(&r);
                hits
            }

            #[test]
            fn stack_residue_pk_from_sk() {
                let (_pk, sk) = $keygen(&xi(5));
                let needles = sk_needles::<$k, $l>(&$p, &sk);
                let hits = exp_pk_from_sk(&sk, &needles);
                let bad = report(concat!(stringify!($set), " pk_from_sk"), &hits);
                let unexpected: Vec<_> = bad.iter().filter(|l| !PK_FROM_SK_KNOWN.contains(&l.as_str())).collect();
                assert!(unexpected.is_empty(), "secret residue on the stack after pk_from_sk: {unexpected:?}");
            }

            #[test]
            fn signing_key_drop_wipes() {
                let (_pk, sk) = $keygen(&xi(9));
                let mut slot = ManuallyDrop::new($signing_key(&sk));
                let regions = slot.secret_regions();
                let whole = (&*slot as *const $SKT as *const u8, size_of::<$SKT>());
                // Before: every secret field is nonzero, and K (sk[32..64]) is in the struct.
                for (i, r) in regions.iter().enumerate() {
                    assert!(read_bytes(r.0, r.1).iter().any(|&b| b != 0), "field {i} is already zero");
                }
                let k = read_bytes(regions[3].0, regions[3].1);
                assert_eq!(k, &sk[32..64]);
                assert!(contains(&read_bytes(whole.0, whole.1), &k));
                // Drop in place, then read the memory back.
                // SAFETY: `slot` is not used as a value afterwards; its storage is still live.
                unsafe { ManuallyDrop::drop(&mut slot) };
                for (i, r) in regions.iter().enumerate() {
                    let after = read_bytes(r.0, r.1);
                    assert!(after.iter().all(|&b| b == 0), "secret field {i} not wiped by Drop");
                }
                assert!(!contains(&read_bytes(whole.0, whole.1), &k), "a copy of K is left in the struct");
                // Â and tr are public and are not wiped (documented).
            }

            #[test]
            fn stack_residue_keygen() {
                let x = xi(1);
                let (_pk, sk) = $keygen(&x);
                let mut needles = sk_needles::<$k, $l>(&$p, &sk);
                // ρ′ and K come from H(ξ ‖ k ‖ ℓ, 128).
                let expanded = shake256(&[&x, &[$k as u8, $l as u8]], 128);
                needles.push(Needle { label: "expanded".into(), bytes: expanded.clone() });
                needles.push(Needle { label: "rho_prime".into(), bytes: expanded[32..96].to_vec() });
                needles.push(Needle { label: "xi".into(), bytes: x.to_vec() });
                let hits = exp_keygen(&x, &needles);
                let bad = report(concat!(stringify!($set), " keygen"), &hits);
                let unexpected: Vec<_> = bad.iter().filter(|l| !KEYGEN_KNOWN.contains(&l.as_str())).collect();
                assert!(unexpected.is_empty(), "secret residue on the stack after keygen: {unexpected:?}");
            }

            #[test]
            fn stack_residue_signing_key() {
                let (_pk, sk) = $keygen(&xi(2));
                let needles = sk_needles::<$k, $l>(&$p, &sk);
                let hits = exp_signing_key(&sk, &needles);
                let bad = report(concat!(stringify!($set), " signing_key"), &hits);
                assert!(bad.is_empty(), "secret residue on the stack after signing_key: {bad:?}");
            }

            /// The message and the needles for a Sign call under `sign_fn` (see `message_with_rejection`).
            fn sign_case(sk: &[u8; $SK], sign_fn: &dyn Fn(&[u8]) -> Vec<u8>) -> (Vec<u8>, Vec<Needle>) {
                message_with_rejection::<$k, $l>(&$p, sk, sign_fn)
            }

            #[inline(never)]
            fn exp_attempt(
                ps: &PreparedSk<$k, $l>,
                mu: &[u8; 64],
                rho_pp: &[u8; 64],
                kappa: u16,
                needles: &[Needle],
            ) -> (bool, Vec<(String, usize)>) {
                paint();
                let r = black_box(ps.attempt_at(&$p, mu, rho_pp, kappa));
                let hits = scan(needles);
                let accepted = r.is_some();
                black_box(&r);
                (accepted, hits)
            }

            /// One call of Sign's loop body (`attempt`, via the `internals` hook) that ends as `want`, then a scan for
            /// the secrets of that attempt. `sign_*` cannot show a rejected attempt: the next attempt overwrites it.
            fn attempt_residue(want: Outcome) {
                let (_pk, sk) = $keygen(&xi(6));
                let mu: [u8; 64] = shake256(&[b"stack residue mu"], 64).try_into().unwrap();
                let rho_pp: [u8; 64] = shake256(&[b"stack residue rho''"], 64).try_into().unwrap();
                let (att, found) = find_attempt::<$k, $l>(&$p, &sk, &mu, &rho_pp, want);
                let mut needles = sk_needles::<$k, $l>(&$p, &sk);
                needles.extend(found);
                needles.push(Needle { label: "rho_pp".into(), bytes: rho_pp.to_vec() });
                let ps = Box::new(prepare_sk::<$k, $l>(&$p, &sk));
                let (accepted, hits) = exp_attempt(&ps, &mu, &rho_pp, (att * $l) as u16, &needles);
                assert_eq!(accepted, want == Outcome::Accepted, "the library's attempt {att} disagrees with the rebuilt one");
                let bad = report(&format!("{} attempt {want:?} (att {att})", stringify!($set)), &hits);
                assert!(bad.is_empty(), "secret residue on the stack after an attempt that ends as {want:?}: {bad:?}");
            }

            #[test]
            fn stack_residue_attempt_rejected_early() {
                attempt_residue(Outcome::RejectedEarly);
            }

            #[test]
            fn stack_residue_attempt_rejected_late() {
                attempt_residue(Outcome::RejectedLate);
            }

            #[test]
            fn stack_residue_attempt_accepted() {
                attempt_residue(Outcome::Accepted);
            }

            #[test]
            fn stack_residue_sign() {
                let (_pk, sk) = $keygen(&xi(3));
                let (m, needles) = sign_case(&sk, &|m| $sign(&sk, m, b"ctx", &[7u8; 32]).unwrap().to_vec());
                let hits = exp_sign(&sk, &m, &needles);
                let bad = report(concat!(stringify!($set), " sign"), &hits);
                assert!(bad.is_empty(), "secret residue on the stack after sign: {bad:?}");
            }

            #[test]
            fn stack_residue_sign_prepared() {
                let (_pk, sk) = $keygen(&xi(4));
                let ssk = Box::new($signing_key(&sk));
                let (m, needles) =
                    sign_case(&sk, &|m| $sign_prepared(&ssk, m, b"ctx", &[7u8; 32]).unwrap().to_vec());
                let hits = exp_sign_prepared(&ssk, &m, &needles);
                let bad = report(concat!(stringify!($set), " sign_prepared"), &hits);
                assert!(bad.is_empty(), "secret residue on the stack after sign_prepared: {bad:?}");
            }
        }
    };
}

residue_tests!(ml_dsa_44, ML_DSA_44, 4, 4, keygen_44, signing_key_44, sign_44, sign_prepared_44, 2560, SigningKey44, pk_from_sk_44);
residue_tests!(ml_dsa_65, ML_DSA_65, 6, 5, keygen_65, signing_key_65, sign_65, sign_prepared_65, 4032, SigningKey65, pk_from_sk_65);
residue_tests!(ml_dsa_87, ML_DSA_87, 8, 7, keygen_87, signing_key_87, sign_87, sign_prepared_87, 4896, SigningKey87, pk_from_sk_87);

#[test]
fn shake_wipe_zeroes_the_sponge() {
    let secret: Vec<u8> = (1..=200u8).collect();
    for fresh in [Shake::shake128, Shake::shake256] {
        let mut h = fresh();
        h.absorb(&secret);
        h.finalize();
        let mut out = [0u8; 64];
        h.squeeze(&mut out);
        let bytes = |h: &Shake| read_bytes(h as *const Shake as *const u8, size_of::<Shake>());
        let nonzero_before = bytes(&h).iter().filter(|&&b| b != 0).count();
        h.wipe();
        let after = bytes(&h);
        // What is left is the rate (168 or 136), one nonzero byte.
        let nonzero_after = after.iter().filter(|&&b| b != 0).count();
        assert!(nonzero_before > 100, "state looked empty before the wipe ({nonzero_before} nonzero bytes)");
        assert!(nonzero_after <= 1, "{nonzero_after} nonzero bytes left after wipe");
        // A wiped sponge behaves as a fresh one.
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        h.finalize();
        h.squeeze(&mut a);
        let mut f = fresh();
        f.finalize();
        f.squeeze(&mut b);
        assert_eq!(a, b);
    }
}
