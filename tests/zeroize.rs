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

use ml_dsa_verified::api::*;
use ml_dsa_verified::encode::sk_decode;
use ml_dsa_verified::keccak::Shake;
use ml_dsa_verified::ntt::ntt_vec;
use ml_dsa_verified::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
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

/// Prints the hits and returns the labels with a nonzero count.
fn report(name: &str, hits: &[(String, usize)]) -> Vec<String> {
    let bad: Vec<String> = hits.iter().filter(|(_, c)| *c > 0).map(|(l, c)| format!("{l} x{c}")).collect();
    eprintln!("{name}: {} secret patterns searched, residue: {}", hits.len(), if bad.is_empty() { "none".into() } else { bad.join(", ") });
    bad.into_iter().map(|s| s.split_whitespace().next().unwrap().to_string()).collect()
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

            fn sign_needles(sk: &[u8; $SK], m: &[u8]) -> Vec<Needle> {
                let mut needles = sk_needles::<$k, $l>(&$p, sk);
                // ρ″ = H(K ‖ rnd ‖ μ, 64), μ = H(tr ‖ M′, 64), M′ = 0 ‖ |ctx| ‖ ctx ‖ M.
                let d = sk_decode::<$k, $l>(&$p, sk);
                let mut mp = vec![0u8, 3];
                mp.extend_from_slice(b"ctx");
                mp.extend_from_slice(m);
                let mu = shake256(&[&d.tr, &mp], 64);
                let rho_pp = shake256(&[&d.key, &[7u8; 32], &mu], 64);
                needles.push(Needle { label: "rho_pp".into(), bytes: rho_pp });
                needles
            }

            #[test]
            fn stack_residue_sign() {
                let (_pk, sk) = $keygen(&xi(3));
                let m = b"stack residue message";
                let needles = sign_needles(&sk, m);
                let hits = exp_sign(&sk, m, &needles);
                let bad = report(concat!(stringify!($set), " sign"), &hits);
                assert!(bad.is_empty(), "secret residue on the stack after sign: {bad:?}");
            }

            #[test]
            fn stack_residue_sign_prepared() {
                let (_pk, sk) = $keygen(&xi(4));
                let m = b"stack residue message";
                let needles = sign_needles(&sk, m);
                let ssk = Box::new($signing_key(&sk));
                let hits = exp_sign_prepared(&ssk, m, &needles);
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
