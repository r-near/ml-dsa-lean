//! Verify_internal against upstream RustCrypto ml-dsa (a3690c4): valid signatures, mutated signatures,
//! wrong message, wrong pk. Plus a no-panic test on random byte strings (run in debug for overflow checks).
#![allow(deprecated)]
use ml_dsa::{
    EncodedVerifyingKey, ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed, Signature, VerifyingKey,
};
use ml_dsa_verified::params::{self, ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use ml_dsa_verified::verify::verify_internal;

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
}

fn ours(p: &Params, pk: &[u8], prefix: &[u8], m: &[u8], sig: &[u8]) -> bool {
    match p.k {
        4 => verify_internal::<4, 4>(p, pk, prefix, m, sig),
        6 => verify_internal::<6, 5>(p, pk, prefix, m, sig),
        8 => verify_internal::<8, 7>(p, pk, prefix, m, sig),
        _ => unreachable!(),
    }
}

fn upstream<P: MlDsaParams>(pk: &[u8], m: &[u8], sig: &[u8]) -> bool {
    let Ok(enc) = EncodedVerifyingKey::<P>::try_from(pk) else { return false };
    let vk = VerifyingKey::<P>::decode(&enc);
    match Signature::<P>::try_from(sig) {
        Ok(s) => vk.verify_internal(m, &s),
        Err(_) => false,
    }
}

fn seed(rng: &mut Rng) -> Seed {
    let mut s = Seed::default();
    for b in s.iter_mut() {
        *b = rng.next() as u8;
    }
    s
}

fn check<P: MlDsaParams>(p: &Params, tag: u64) {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15 ^ tag);
    let mut esks = Vec::new();
    let mut pks: Vec<Vec<u8>> = Vec::new();
    let (mut accepted, mut rejected, mut agree) = (0, 0, 0);
    for _ in 0..20 {
        let esk = ExpandedSigningKey::<P>::from_seed(&seed(&mut rng));
        pks.push(esk.verifying_key().encode().as_slice().to_vec());
        esks.push(esk);
    }
    for key in 0..20 {
        let esk = &esks[key];
        let pk = pks[key].clone();
        let n = rng.below(300);
        let m = rng.bytes(n);
        let mut rnd = [0u8; 32];
        rnd.copy_from_slice(&rng.bytes(32));
        let sig = esk.sign_internal(&[&m], &ml_dsa::B32::from(rnd)).encode().as_slice().to_vec();
        assert_eq!(sig.len(), params::sig_len(p));
        let mut cmp = |pk: &[u8], m: &[u8], sig: &[u8], what: &str| -> bool {
            let a = ours(p, pk, &[], m, sig);
            let b = upstream::<P>(pk, m, sig);
            assert_eq!(a, b, "{what}: key {key} ours={a} upstream={b}");
            agree += 1;
            if a { accepted += 1 } else { rejected += 1 }
            a
        };
        // valid
        assert!(cmp(&pk, &m, &sig, "valid"), "valid signature rejected (key {key})");
        // split of M' between prefix and message must not matter
        let cut = rng.below(m.len() + 1);
        assert!(ours(p, &pk, &m[..cut], &m[cut..], &sig), "prefix split changed result");
        // single bit flips: c~ area, z area, hint area
        let ct = p.c_tilde_len;
        let hint_start = sig.len() - p.omega - p.k;
        for t in 0..60 {
            let (lo, hi) = match t % 3 {
                0 => (0, ct),
                1 => (ct, hint_start),
                _ => (hint_start, sig.len()),
            };
            let pos = lo + rng.below(hi - lo);
            let mut bad = sig.clone();
            bad[pos] ^= 1 << rng.below(8);
            cmp(&pk, &m, &bad, "bitflip");
        }
        // wrong message
        let mut m2 = m.clone();
        if m2.is_empty() { m2.push(1) } else { m2[0] ^= 0x80 }
        assert!(!cmp(&pk, &m2, &sig, "wrong message"));
        // wrong pk
        let other = &pks[(key + 1) % 20];
        assert!(!cmp(other, &m, &sig, "wrong pk"));
    }
    println!("{}: {agree} comparisons agree ({accepted} accepted, {rejected} rejected)", p.k);
    assert!(accepted >= 20 && rejected > 0);
}

#[test]
fn agrees_with_upstream_44() {
    check::<MlDsa44>(&ML_DSA_44, 44);
}
#[test]
fn agrees_with_upstream_65() {
    check::<MlDsa65>(&ML_DSA_65, 65);
}
#[test]
fn agrees_with_upstream_87() {
    check::<MlDsa87>(&ML_DSA_87, 87);
}

fn no_panic(p: &Params, tag: u64) {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03 ^ tag);
    let pk = rng.bytes(params::pk_len(p));
    let mut accepted = 0;
    for _ in 0..2000 {
        let sig = rng.bytes(params::sig_len(p));
        accepted += ours(p, &pk, &[], b"msg", &sig) as usize;
    }
    // structured: valid-looking hint section (all counts zero) so decoding proceeds further
    let hint_start = params::sig_len(p) - p.omega - p.k;
    for _ in 0..200 {
        let mut sig = rng.bytes(params::sig_len(p));
        for b in sig[hint_start..].iter_mut() {
            *b = 0;
        }
        accepted += ours(p, &pk, &[], b"msg", &sig) as usize;
    }
    for _ in 0..200 {
        let pk = rng.bytes(params::pk_len(p));
        let sig = rng.bytes(params::sig_len(p));
        let n = rng.below(400);
        let (pre, msg) = (rng.bytes(5), rng.bytes(n));
        accepted += ours(p, &pk, &pre, &msg, &sig) as usize;
    }
    // extremes
    for fill in [0x00u8, 0xFF] {
        let pk = vec![fill; params::pk_len(p)];
        let sig = vec![fill; params::sig_len(p)];
        accepted += ours(p, &pk, &[], &[], &sig) as usize;
        let mut sig0 = vec![fill; params::sig_len(p)];
        for b in sig0[hint_start..].iter_mut() {
            *b = 0;
        }
        accepted += ours(p, &pk, &[], &[], &sig0) as usize;
    }
    assert_eq!(accepted, 0, "random input accepted");
}

#[test]
fn no_panic_random_bytes() {
    no_panic(&ML_DSA_44, 1);
    no_panic(&ML_DSA_65, 2);
    no_panic(&ML_DSA_87, 3);
}

/// Wrong-length pk or σ (one byte shorter or longer) must return false without panicking, even when the
/// extra byte is appended to an otherwise valid input.
fn wrong_length<P: MlDsaParams>(p: &Params, tag: u64) {
    let mut rng = Rng(0x2545_F491_4F6C_DD1D ^ tag);
    let esk = ExpandedSigningKey::<P>::from_seed(&seed(&mut rng));
    let pk = esk.verifying_key().encode().as_slice().to_vec();
    let m = rng.bytes(40);
    let mut rnd = [0u8; 32];
    rnd.copy_from_slice(&rng.bytes(32));
    let sig = esk.sign_internal(&[&m], &ml_dsa::B32::from(rnd)).encode().as_slice().to_vec();
    assert!(ours(p, &pk, &[], &m, &sig), "valid signature rejected");
    let variants = |v: &[u8]| -> Vec<Vec<u8>> {
        let mut out = vec![v[..v.len() - 1].to_vec(), Vec::new()];
        for extra in [0u8, 0xFF] {
            let mut longer = v.to_vec();
            longer.push(extra);
            out.push(longer);
        }
        out
    };
    for bad_pk in variants(&pk) {
        assert!(!ours(p, &bad_pk, &[], &m, &sig), "wrong-length pk ({}) accepted", bad_pk.len());
    }
    for bad_sig in variants(&sig) {
        assert!(!ours(p, &pk, &[], &m, &bad_sig), "wrong-length sig ({}) accepted", bad_sig.len());
    }
}

#[test]
fn wrong_length_pk_and_sig_return_false() {
    wrong_length::<MlDsa44>(&ML_DSA_44, 1);
    wrong_length::<MlDsa65>(&ML_DSA_65, 2);
    wrong_length::<MlDsa87>(&ML_DSA_87, 3);
}
