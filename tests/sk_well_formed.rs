//! `api::sk_is_well_formed_NN`: true iff every s1 and s2 coefficient that skDecode (FIPS 204 Algorithm 25) produces
//! lies in [-eta, eta]. Honest keys pass; a field value outside [-eta, eta] in any s1 or s2 block fails; the
//! boundary values +-eta pass. The last test compares against upstream `ml-dsa`, whose decoder panics on exactly
//! those out-of-range keys.
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, ExpandedSigningKeyBytes, MlDsa44, MlDsa65, MlDsa87, MlDsaParams};
use ml_dsa_lean::api;
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};

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
}

/// One parameter set through slice-based adapters.
struct Set {
    name: &'static str,
    p: &'static Params,
    keygen: fn(&[u8; 32]) -> Vec<u8>,
    well_formed: fn(&[u8]) -> bool,
}

fn sets() -> [Set; 3] {
    [
        Set {
            name: "ML-DSA-44",
            p: &ML_DSA_44,
            keygen: |xi| api::keygen_44(xi).1.to_vec(),
            well_formed: |sk| api::sk_is_well_formed_44(sk.try_into().unwrap()),
        },
        Set {
            name: "ML-DSA-65",
            p: &ML_DSA_65,
            keygen: |xi| api::keygen_65(xi).1.to_vec(),
            well_formed: |sk| api::sk_is_well_formed_65(sk.try_into().unwrap()),
        },
        Set {
            name: "ML-DSA-87",
            p: &ML_DSA_87,
            keygen: |xi| api::keygen_87(xi).1.to_vec(),
            well_formed: |sk| api::sk_is_well_formed_87(sk.try_into().unwrap()),
        },
    ]
}

/// Byte offset of the first eta-block (after rho, K, tr).
const ETA_START: usize = 128;

fn block_len(p: &Params) -> usize {
    32 * p.eta_bits
}

/// Reads the raw `eta_bits`-bit field `idx` of eta-block `block` (blocks 0..l are s1, l..l+k are s2).
/// BitUnpack decodes it to the coefficient eta - z.
fn get_z(sk: &[u8], p: &Params, block: usize, idx: usize) -> u32 {
    let c = p.eta_bits;
    let bit0 = (ETA_START + block * block_len(p)) * 8 + idx * c;
    let mut z = 0u32;
    for b in 0..c {
        let bit = bit0 + b;
        z |= (((sk[bit / 8] >> (bit % 8)) & 1) as u32) << b;
    }
    z
}

fn set_z(sk: &mut [u8], p: &Params, block: usize, idx: usize, z: u32) {
    let c = p.eta_bits;
    assert!(z < (1 << c));
    let bit0 = (ETA_START + block * block_len(p)) * 8 + idx * c;
    for b in 0..c {
        let bit = bit0 + b;
        let v = ((z >> b) & 1) as u8;
        sk[bit / 8] = (sk[bit / 8] & !(1 << (bit % 8))) | (v << (bit % 8));
    }
}

fn honest(set: &Set, tag: u8) -> Vec<u8> {
    let mut xi = [0u8; 32];
    for (i, b) in xi.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(7) ^ tag;
    }
    (set.keygen)(&xi)
}

#[test]
fn honest_keys_are_well_formed() {
    for set in sets() {
        for tag in 0..8u8 {
            let sk = honest(&set, tag);
            assert!((set.well_formed)(&sk), "{} honest key {tag} rejected", set.name);
            // The accepted range really is the one the helpers read: every raw field is <= 2*eta.
            for block in 0..set.p.l + set.p.k {
                for idx in 0..256 {
                    assert!(get_z(&sk, set.p, block, idx) <= 2 * set.p.eta, "{} block {block}", set.name);
                }
            }
        }
    }
}

#[test]
fn out_of_range_s1_or_s2_field_is_rejected() {
    for set in sets() {
        let p = set.p;
        let sk0 = honest(&set, 1);
        // Out-of-range raw values: 2*eta + 1 ..= 2^eta_bits - 1 (5..=7 for eta = 2, 9..=15 for eta = 4).
        let bad: Vec<u32> = (2 * p.eta + 1..1 << p.eta_bits).collect();
        assert_eq!(bad.first().copied(), Some(if p.eta == 2 { 5 } else { 9 }));
        // First, last and middle block of s1 and of s2; first, last and a middle coefficient.
        let blocks = [0, p.l / 2, p.l - 1, p.l, p.l + p.k / 2, p.l + p.k - 1];
        for &block in &blocks {
            for &idx in &[0usize, 100, 255] {
                for &z in &bad {
                    let mut sk = sk0.clone();
                    set_z(&mut sk, p, block, idx, z);
                    assert!(!(set.well_formed)(&sk), "{} block {block} idx {idx} z {z} accepted", set.name);
                }
            }
        }
        // Every single s1 and s2 block, one bad field each.
        for block in 0..p.l + p.k {
            let mut sk = sk0.clone();
            set_z(&mut sk, p, block, 17, *bad.last().unwrap());
            assert!(!(set.well_formed)(&sk), "{} block {block} accepted", set.name);
        }
    }
}

#[test]
fn boundary_values_are_accepted() {
    for set in sets() {
        let p = set.p;
        let sk0 = honest(&set, 2);
        // z = 0 decodes to +eta, z = 2*eta decodes to -eta; set every coefficient of every block to each extreme.
        for &z in &[0, p.eta, 2 * p.eta] {
            let mut sk = sk0.clone();
            for block in 0..p.l + p.k {
                for idx in 0..256 {
                    set_z(&mut sk, p, block, idx, z);
                }
            }
            assert!((set.well_formed)(&sk), "{} all fields z = {z} rejected", set.name);
        }
        // One extreme next to an out-of-range field in a different block: still rejected.
        let mut sk = sk0.clone();
        set_z(&mut sk, p, 0, 0, 2 * p.eta);
        set_z(&mut sk, p, p.l, 255, 2 * p.eta);
        assert!((set.well_formed)(&sk));
        set_z(&mut sk, p, p.l + p.k - 1, 255, 2 * p.eta + 1);
        assert!(!(set.well_formed)(&sk));
    }
}

#[test]
fn t0_and_header_bytes_do_not_matter() {
    for set in sets() {
        let p = set.p;
        let mut sk = honest(&set, 3);
        // rho, K, tr (first 128 bytes) and the t0 region (after s1, s2) take any bytes.
        for b in &mut sk[..ETA_START] {
            *b = 0xff;
        }
        let t0_start = ETA_START + (p.l + p.k) * block_len(p);
        for b in &mut sk[t0_start..] {
            *b = 0xff;
        }
        assert!((set.well_formed)(&sk), "{} t0/header bytes affected the verdict", set.name);
        for b in &mut sk[t0_start..] {
            *b = 0;
        }
        assert!((set.well_formed)(&sk));
    }
}

/// Signing is unchanged: `sign_NN` does not consult the check and still signs with an out-of-range key
/// (E-4 in `docs/assurance.md`; FIPS 204 Algorithm 25 leaves that case undefined).
#[test]
fn sign_does_not_call_the_check() {
    let set = &sets()[0];
    let mut sk = honest(set, 4);
    set_z(&mut sk, set.p, 0, 0, 7);
    assert!(!(set.well_formed)(&sk));
    let sk: [u8; 2560] = sk.try_into().unwrap();
    assert!(api::sign_44(&sk, b"msg", b"", &[0u8; 32]).is_some());
}

fn upstream_panics<P: MlDsaParams>(sk: &[u8]) -> bool {
    let Ok(enc) = ExpandedSigningKeyBytes::<P>::try_from(sk) else { panic!("wrong sk length") };
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = ExpandedSigningKey::<P>::from_expanded(&enc);
    }))
    .is_err()
}

/// Random mutations of honest keys (one to three fields set to random raw values, some in range and some not):
/// `sk_is_well_formed == !upstream_panics`, and at least one case of each outcome occurs.
#[test]
fn agrees_with_upstream_decoder() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut rng = Rng(0x2545_F491_4F6C_DD1D);
    let mut seen = [[0usize; 2]; 3];
    for (si, set) in sets().iter().enumerate() {
        let p = set.p;
        let sk0 = honest(set, 5);
        for case in 0..200 {
            let mut sk = sk0.clone();
            for _ in 0..1 + rng.next() % 3 {
                let block = (rng.next() % (p.l + p.k) as u64) as usize;
                let idx = (rng.next() % 256) as usize;
                let z = (rng.next() % (1 << p.eta_bits)) as u32;
                set_z(&mut sk, p, block, idx, z);
            }
            let ours = (set.well_formed)(&sk);
            let up_ok = !match si {
                0 => upstream_panics::<MlDsa44>(&sk),
                1 => upstream_panics::<MlDsa65>(&sk),
                _ => upstream_panics::<MlDsa87>(&sk),
            };
            assert_eq!(ours, up_ok, "{} case {case}: ours {ours}, upstream accepts {up_ok}", set.name);
            seen[si][ours as usize] += 1;
        }
    }
    std::panic::set_hook(prev);
    for (si, s) in seen.iter().enumerate() {
        assert!(s[0] > 0 && s[1] > 0, "set {si}: outcomes {s:?} do not cover both verdicts");
    }
}
