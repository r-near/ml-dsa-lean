//! Larger randomized differential of the internal interface against upstream RustCrypto `ml-dsa` (a3690c4):
//! KeyGen_internal, Sign_internal and Verify_internal for all three parameter sets.
//!
//! Counts per parameter set (release; debug uses `SCALE` = 10x fewer of the bulk cases to stay fast):
//! - `keygen_matches_upstream`: 200 random ξ, pk and sk bytes compared.
//! - `sign_verify_matches_upstream`: 200 random (sk, M′, rnd) with M′ of length 0, short, up to 10 kB, split at a
//!   random point between `m_prefix` and `m` (split must not change the result); sign bytes compared with
//!   upstream's expanded-key `sign_internal`; Verify_internal on each signature and on a mutated copy, verdicts
//!   compared with upstream (also on the split M′ and on a wrong-message copy).
//! - `sign_many_matches_upstream`: 2000 signing cases (20 keys x 100 random rnd/message), byte-for-byte.
//!   The κ loop is not observable through the public API. Each attempt succeeds with a probability of roughly
//!   1/4 to 1/5 (FIPS 204 Table 1 expected repetitions: 4.25, 5.1, 3.85), so among 2000 cases per set many needed
//!   two or more attempts and some five or more; all agree with upstream byte for byte, which pins the κ schedule
//!   (κ += ℓ) and the per-attempt masking. The exact iteration count per case is not derived.
#![allow(deprecated)]
use ml_dsa::{
    EncodedVerifyingKey, ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed, Signature, VerifyingKey,
};
use ml_dsa_lean::keygen::keygen_internal;
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params, pk_len, sig_len, sk_len};
use ml_dsa_lean::sign::sign_internal;
use ml_dsa_lean::verify::verify_internal;

/// Bulk-case divisor: unoptimized builds (overflow checks on) run a tenth of the cases.
const SCALE: usize = if cfg!(debug_assertions) { 10 } else { 1 };

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn arr32(&mut self) -> [u8; 32] {
        let mut a = [0u8; 32];
        for b in a.iter_mut() {
            *b = self.next() as u8;
        }
        a
    }
}

fn upstream_verify<P: MlDsaParams>(pk: &[u8], mp: &[u8], sig: &[u8]) -> bool {
    let Ok(enc) = EncodedVerifyingKey::<P>::try_from(pk) else { return false };
    let vk = VerifyingKey::<P>::decode(&enc);
    match Signature::<P>::try_from(sig) {
        Ok(s) => vk.verify_internal(mp, &s),
        Err(_) => false,
    }
}

fn ours_sign<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    prefix: &[u8],
    m: &[u8],
    rnd: &[u8; 32],
) -> Vec<u8> {
    let mut sig = vec![0u8; sig_len(p)];
    assert!(sign_internal::<K, L>(p, sk, prefix, m, rnd, &mut sig), "kappa budget exhausted");
    sig
}

/// Message length: empty, short, medium, or up to 10 kB (many SHAKE-256 blocks of 136 bytes).
fn msg_len(rng: &mut Rng, case: usize) -> usize {
    match case {
        0 => 0,
        1 => 10_000,
        2 => 135,
        3 => 136,
        4 => 137,
        _ => match rng.below(4) {
            0 => 0,
            1 => rng.below(200),
            2 => rng.below(1500),
            _ => rng.below(10_001),
        },
    }
}

fn keygen_case<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, rng: &mut Rng) -> (Vec<u8>, Vec<u8>) {
    let xi = rng.arr32();
    let mut seed = Seed::default();
    seed.copy_from_slice(&xi);
    let esk = ExpandedSigningKey::<P>::from_seed(&seed);
    let up_pk = esk.verifying_key().encode();
    let up_sk = esk.to_expanded();
    let mut pk = vec![0u8; pk_len(p)];
    let mut sk = vec![0u8; sk_len(p)];
    keygen_internal::<K, L>(p, &xi, &mut pk, &mut sk);
    assert_eq!(up_pk.as_slice(), pk.as_slice(), "pk mismatch xi={xi:02x?}");
    assert_eq!(up_sk.as_slice(), sk.as_slice(), "sk mismatch xi={xi:02x?}");
    (pk, sk)
}

fn keygen_check<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, tag: u64) {
    let mut rng = Rng(0xA076_1D64_78BD_642F ^ tag);
    for _ in 0..200 {
        keygen_case::<P, K, L>(p, &mut rng);
    }
}

#[test]
fn keygen_matches_upstream() {
    keygen_check::<MlDsa44, 4, 4>(&ML_DSA_44, 44);
    keygen_check::<MlDsa65, 6, 5>(&ML_DSA_65, 65);
    keygen_check::<MlDsa87, 8, 7>(&ML_DSA_87, 87);
}

fn sign_verify_check<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, tag: u64) {
    let mut rng = Rng(0xE703_7ED1_A0B4_28DB ^ tag);
    let n_cases = 200 / SCALE;
    let (mut acc, mut rej) = (0, 0);
    let mut key_pool: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    for case in 0..n_cases {
        // fresh random key every 4th case, otherwise a random earlier one
        if key_pool.is_empty() || case % 4 == 0 {
            key_pool.push(keygen_case::<P, K, L>(p, &mut rng));
        }
        let (pk, sk) = key_pool[rng.below(key_pool.len())].clone();
        let n = msg_len(&mut rng, case);
        let mp = rng.bytes(n);
        let rnd = rng.arr32();
        let split = if n == 0 { 0 } else { rng.below(n + 1) };
        let (pre, rest) = mp.split_at(split);

        // upstream: expanded-key sign_internal on the decoded sk
        let esk_bytes = ml_dsa::ExpandedSigningKeyBytes::<P>::try_from(sk.as_slice()).unwrap();
        let esk = ExpandedSigningKey::<P>::from_expanded(&esk_bytes);
        let up_sig = esk.sign_internal(&[&mp], &ml_dsa::B32::from(rnd)).encode();
        let up_sig = up_sig.as_slice();

        // ours, whole M′ in `m`, and split at a random point (and at both extremes)
        let a = ours_sign::<K, L>(p, &sk, &[], &mp, &rnd);
        let b = ours_sign::<K, L>(p, &sk, pre, rest, &rnd);
        let c = ours_sign::<K, L>(p, &sk, &mp, &[], &rnd);
        assert_eq!(up_sig, a.as_slice(), "sign mismatch case {case} len {n}");
        assert_eq!(a, b, "split at {split} of {n} changed the signature");
        assert_eq!(a, c, "prefix-only M′ changed the signature");

        // verify: valid signature, then a mutated copy and a wrong-message copy
        let mut mutated = a.clone();
        let flips = 1 + rng.below(3);
        for _ in 0..flips {
            let pos = rng.below(mutated.len());
            mutated[pos] ^= 1 << rng.below(8);
        }
        let mut wrong = mp.clone();
        if wrong.is_empty() {
            wrong.push(7);
        } else {
            let pos = rng.below(wrong.len());
            wrong[pos] ^= 0x80;
        }
        let ver = |m_all: &[u8], s: &[u8], cut: usize| -> bool {
            let (x, y) = m_all.split_at(cut.min(m_all.len()));
            let mine = verify_internal::<K, L>(p, &pk, x, y, s);
            let theirs = upstream_verify::<P>(&pk, m_all, s);
            assert_eq!(mine, theirs, "verify verdict mismatch (case {case}, len {n}, cut {cut})");
            mine
        };
        assert!(ver(&mp, &a, split), "valid signature rejected");
        assert!(ver(&mp, &a, 0));
        assert!(ver(&mp, &a, n));
        for (m_all, s) in [(&mp, &mutated), (&wrong, &a)] {
            if ver(m_all, s, split) {
                acc += 1
            } else {
                rej += 1
            }
        }
    }
    assert!(rej > 0);
    eprintln!("K={K}: {n_cases} sign cases, mutated/wrong verdicts: {acc} accepted, {rej} rejected");
}

#[test]
fn sign_verify_matches_upstream() {
    sign_verify_check::<MlDsa44, 4, 4>(&ML_DSA_44, 44);
    sign_verify_check::<MlDsa65, 6, 5>(&ML_DSA_65, 65);
    sign_verify_check::<MlDsa87, 8, 7>(&ML_DSA_87, 87);
}

fn sign_many_check<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, tag: u64) {
    let mut rng = Rng(0x8EBC_6AF0_9C88_C6E3 ^ tag);
    let keys = 20;
    let per_key = 100 / SCALE;
    let mut cases = 0;
    for _ in 0..keys {
        let (_pk, sk) = keygen_case::<P, K, L>(p, &mut rng);
        let esk_bytes = ml_dsa::ExpandedSigningKeyBytes::<P>::try_from(sk.as_slice()).unwrap();
        let esk = ExpandedSigningKey::<P>::from_expanded(&esk_bytes);
        for _ in 0..per_key {
            let n = rng.below(64);
            let mp = rng.bytes(n);
            let rnd = rng.arr32();
            let up = esk.sign_internal(&[&mp], &ml_dsa::B32::from(rnd)).encode();
            let mine = ours_sign::<K, L>(p, &sk, &[], &mp, &rnd);
            assert_eq!(up.as_slice(), mine.as_slice(), "sign mismatch, rnd={rnd:02x?} M′={mp:02x?}");
            cases += 1;
        }
    }
    eprintln!("K={K}: {cases} sign cases agree byte for byte");
}

#[test]
fn sign_many_matches_upstream() {
    sign_many_check::<MlDsa44, 4, 4>(&ML_DSA_44, 44);
    sign_many_check::<MlDsa65, 6, 5>(&ML_DSA_65, 65);
    sign_many_check::<MlDsa87, 8, 7>(&ML_DSA_87, 87);
}
