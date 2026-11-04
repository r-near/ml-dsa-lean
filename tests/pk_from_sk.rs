//! `api::pk_from_sk_NN`: returns `Some(pk)` iff the secret key is internally consistent, i.e. s1/s2 are within
//! [-eta, eta] and recomputing (t1, t0) and tr from (rho, s1, s2) gives the stored t0 and tr. Honest keys give back
//! KeyGen's pk; a flipped bit in rho, tr, t0, s1 or s2 is rejected; K is a free seed and is not checked. Sign does
//! not call it.
use ml_dsa_lean::api;
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};

struct Set {
    name: &'static str,
    p: &'static Params,
    keygen: fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    pk_from_sk: fn(&[u8]) -> Option<Vec<u8>>,
}

fn sets() -> [Set; 3] {
    [
        Set {
            name: "ML-DSA-44",
            p: &ML_DSA_44,
            keygen: |xi| {
                let (pk, sk) = api::keygen_44(xi);
                (pk.to_vec(), sk.to_vec())
            },
            pk_from_sk: |sk| api::pk_from_sk_44(sk.try_into().unwrap()).map(|p| p.to_vec()),
        },
        Set {
            name: "ML-DSA-65",
            p: &ML_DSA_65,
            keygen: |xi| {
                let (pk, sk) = api::keygen_65(xi);
                (pk.to_vec(), sk.to_vec())
            },
            pk_from_sk: |sk| api::pk_from_sk_65(sk.try_into().unwrap()).map(|p| p.to_vec()),
        },
        Set {
            name: "ML-DSA-87",
            p: &ML_DSA_87,
            keygen: |xi| {
                let (pk, sk) = api::keygen_87(xi);
                (pk.to_vec(), sk.to_vec())
            },
            pk_from_sk: |sk| api::pk_from_sk_87(sk.try_into().unwrap()).map(|p| p.to_vec()),
        },
    ]
}

const ETA_START: usize = 128;

fn block_len(p: &Params) -> usize {
    32 * p.eta_bits
}

/// Byte ranges of the sk regions: rho, K, tr, s1, s2, t0.
struct Layout {
    rho: std::ops::Range<usize>,
    key: std::ops::Range<usize>,
    tr: std::ops::Range<usize>,
    s1: std::ops::Range<usize>,
    s2: std::ops::Range<usize>,
    t0: std::ops::Range<usize>,
}

fn layout(p: &Params, sk_len: usize) -> Layout {
    let n = block_len(p);
    let s1_end = ETA_START + p.l * n;
    let s2_end = s1_end + p.k * n;
    assert_eq!(s2_end + p.k * 416, sk_len);
    Layout { rho: 0..32, key: 32..64, tr: 64..128, s1: ETA_START..s1_end, s2: s1_end..s2_end, t0: s2_end..sk_len }
}

fn honest(set: &Set, tag: u8) -> (Vec<u8>, Vec<u8>) {
    let mut xi = [0u8; 32];
    for (i, b) in xi.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(11) ^ tag;
    }
    (set.keygen)(&xi)
}

fn flip(sk: &[u8], bit: usize) -> Vec<u8> {
    let mut v = sk.to_vec();
    v[bit / 8] ^= 1 << (bit % 8);
    v
}

/// A spread of bit positions inside `r` (byte range): first, last, and every `step`-th bit.
fn bits_in(r: &std::ops::Range<usize>, step: usize) -> Vec<usize> {
    let mut v: Vec<usize> = (r.start * 8..r.end * 8).step_by(step).collect();
    v.push(r.start * 8);
    v.push(r.end * 8 - 1);
    v
}

#[test]
fn honest_keys_give_back_keygens_pk() {
    for set in sets() {
        for tag in 0..8u8 {
            let (pk, sk) = honest(&set, tag);
            assert_eq!((set.pk_from_sk)(&sk), Some(pk), "{} honest key {tag}", set.name);
        }
    }
}

#[test]
fn every_single_bit_flip_of_rho_tr_t0_is_rejected() {
    for set in sets() {
        let (_, sk) = honest(&set, 21);
        let l = layout(set.p, sk.len());
        for (name, r) in [("rho", &l.rho), ("tr", &l.tr), ("t0", &l.t0)] {
            // Every bit of rho and tr; a stride through t0 (13-bit fields: a stride coprime to 13 hits all offsets).
            let step = if name == "t0" { 7 } else { 1 };
            for bit in bits_in(r, step) {
                assert_eq!((set.pk_from_sk)(&flip(&sk, bit)), None, "{} {name} bit {bit} accepted", set.name);
            }
        }
    }
}

#[test]
fn bit_flips_in_s1_or_s2_are_rejected() {
    for set in sets() {
        let (_, sk) = honest(&set, 22);
        let l = layout(set.p, sk.len());
        for (name, r) in [("s1", &l.s1), ("s2", &l.s2)] {
            for bit in bits_in(r, 5) {
                assert_eq!((set.pk_from_sk)(&flip(&sk, bit)), None, "{} {name} bit {bit} accepted", set.name);
            }
        }
    }
}

#[test]
fn key_k_is_a_free_seed_and_is_accepted() {
    for set in sets() {
        let (pk, sk) = honest(&set, 23);
        let l = layout(set.p, sk.len());
        for bit in bits_in(&l.key, 1) {
            assert_eq!((set.pk_from_sk)(&flip(&sk, bit)), Some(pk.clone()), "{} K bit {bit} rejected", set.name);
        }
        let mut sk0 = sk.clone();
        sk0[l.key.clone()].fill(0xff);
        assert_eq!((set.pk_from_sk)(&sk0), Some(pk.clone()));
        sk0[l.key].fill(0);
        assert_eq!((set.pk_from_sk)(&sk0), Some(pk));
    }
}

/// Writes the raw `eta_bits`-bit field `idx` of eta-block `block` (blocks 0..l are s1, l..l+k are s2).
fn set_z(sk: &mut [u8], p: &Params, block: usize, idx: usize, z: u32) {
    let c = p.eta_bits;
    let bit0 = (ETA_START + block * block_len(p)) * 8 + idx * c;
    for b in 0..c {
        let bit = bit0 + b;
        let v = ((z >> b) & 1) as u8;
        sk[bit / 8] = (sk[bit / 8] & !(1 << (bit % 8))) | (v << (bit % 8));
    }
}

#[test]
fn out_of_range_s1_or_s2_is_rejected_and_agrees_with_the_range_check() {
    for set in sets() {
        let p = set.p;
        let (_, sk0) = honest(&set, 24);
        let bad: Vec<u32> = (2 * p.eta + 1..1 << p.eta_bits).collect();
        for block in [0, p.l - 1, p.l, p.l + p.k - 1] {
            for idx in [0usize, 100, 255] {
                for &z in &bad {
                    let mut sk = sk0.clone();
                    set_z(&mut sk, p, block, idx, z);
                    assert_eq!((set.pk_from_sk)(&sk), None, "{} block {block} idx {idx} z {z} accepted", set.name);
                }
            }
        }
    }
}

#[test]
fn degenerate_keys_are_rejected() {
    for set in sets() {
        let len = honest(&set, 0).1.len();
        assert_eq!((set.pk_from_sk)(&vec![0u8; len]), None, "{} all-zero key", set.name);
        assert_eq!((set.pk_from_sk)(&vec![0xffu8; len]), None, "{} all-0xff key", set.name);
    }
}

/// The derived pk is the real one: a signature from the stored key verifies under it.
#[test]
fn derived_pk_verifies_signatures() {
    let (pk, sk) = {
        let set = &sets()[0];
        honest(set, 25)
    };
    let sk: [u8; 2560] = sk.try_into().unwrap();
    let derived = api::pk_from_sk_44(&sk).unwrap();
    assert_eq!(derived.as_slice(), pk.as_slice());
    let sig = api::sign_44(&sk, b"hello", b"ctx", &[0u8; 32]).unwrap();
    assert!(api::verify_44(&derived, b"hello", b"ctx", &sig));
}

/// Sign does not consult the check: an inconsistent key (flipped t0 bit) is still signed with.
#[test]
fn sign_does_not_call_it() {
    let set = &sets()[0];
    let (_, sk) = honest(set, 26);
    let l = layout(set.p, sk.len());
    let bad: [u8; 2560] = flip(&sk, l.t0.start * 8 + 3).try_into().unwrap();
    assert!(api::pk_from_sk_44(&bad).is_none());
    assert!(api::sign_44(&bad, b"m", b"", &[0u8; 32]).is_some());
}
