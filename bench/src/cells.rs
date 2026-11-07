//! Inputs and per-implementation closures shared by the `bench` and `prof` binaries.
//!
//! Every implementation gets the same inputs. The crosscheck harness has shown that all of them produce
//! byte-identical keys and signatures, so the rejection loop runs the same number of attempts everywhere and
//! signing differences are implementation speed.
#![allow(deprecated)]

use crate::*;
use ml_dsa_lean::api;

pub const NMSG: usize = 256;
pub const NSEED: usize = 64;
pub const MSG_LEN: usize = 64;
pub const CTX: &[u8] = b"";
pub const ZERO: [u8; 32] = [0u8; 32];

pub struct Cell<'a> {
    pub imp: String,
    pub group: &'static str,
    pub n: usize,
    pub f: Box<dyn FnMut(usize) -> u64 + 'a>,
}

fn cell<'a>(cells: &mut Vec<Cell<'a>>, imp: &str, group: &'static str, n: usize, f: impl FnMut(usize) -> u64 + 'a) {
    cells.push(Cell { imp: imp.to_string(), group, n, f: Box::new(f) });
}

/// Inputs for one parameter set.
pub struct SetData {
    pub seeds: Vec<[u8; 32]>,
    pub msgs: Vec<Vec<u8>>,
    pub rnd_h: Vec<[u8; 32]>,
    pub pk: Vec<u8>,
    pub sk: Vec<u8>,
    pub sig_det: Vec<Vec<u8>>,
}

impl SetData {
    fn build(
        lvl: u64,
        keygen: impl Fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
        sign: impl Fn(&[u8], &[u8], &[u8; 32]) -> Vec<u8>,
    ) -> SetData {
        let mut r = Rng::new("inputs", lvl);
        let seeds: Vec<[u8; 32]> = (0..NSEED).map(|_| r.bytes()).collect();
        let key_seed: [u8; 32] = r.bytes();
        let msgs: Vec<Vec<u8>> = (0..NMSG).map(|_| r.bytes::<MSG_LEN>().to_vec()).collect();
        let rnd_h: Vec<[u8; 32]> = (0..NMSG).map(|_| r.bytes()).collect();
        let (pk, sk) = keygen(&key_seed);
        let sig_det = msgs.iter().map(|m| sign(&sk, m, &ZERO)).collect();
        SetData { seeds, msgs, rnd_h, pk, sk, sig_det }
    }
}

#[cfg(target_arch = "x86_64")]
fn have_avx2() -> bool {
    avx2()
}

macro_rules! lc_cells {
    ($cells:ident, $d:ident, $label:literal, $m:ident, $be:ident, $LSK:ident, $LVK:ident, $LSIG:ident, $pk:literal, $sk:literal) => {{
        use libcrux_ml_dsa::$m::{$LSIG, $LSK, $LVK, $be};
        let lsk = $LSK::new($d.sk.as_slice().try_into().unwrap());
        let lvk = $LVK::new($d.pk.as_slice().try_into().unwrap());
        let sigs: Vec<$LSIG> = $d.sig_det.iter().map(|s| $LSIG::new(s.as_slice().try_into().unwrap())).collect();
        cell($cells, $label, "keygen", NSEED, move |i| {
            let kp = $be::generate_key_pair($d.seeds[i]);
            tag(kp.verification_key.as_slice()) ^ tag(kp.signing_key.as_slice())
        });
        cell($cells, $label, "sign-det", NMSG, {
            let lsk = $LSK::new($d.sk.as_slice().try_into().unwrap());
            move |i| tag($be::sign(&lsk, &$d.msgs[i], CTX, ZERO).unwrap().as_slice())
        });
        cell($cells, $label, "sign-hedged", NMSG, move |i| {
            tag($be::sign(&lsk, &$d.msgs[i], CTX, $d.rnd_h[i]).unwrap().as_slice())
        });
        cell($cells, $label, "verify", NMSG, move |i| $be::verify(&lvk, &$d.msgs[i], CTX, &sigs[i]).is_ok() as u64);
    }};
}

macro_rules! mld_cells {
    ($cells:ident, $d:ident, $label:literal, $kp:path, $sg:path, $vf:path, $lvl:literal, $pk:literal, $sk:literal, $sig:literal) => {{
        cell($cells, $label, "keygen", NSEED, move |i| {
            let mut pk = [0u8; $pk];
            let mut sk = [0u8; $sk];
            let rc = unsafe { $kp($lvl, pk.as_mut_ptr(), sk.as_mut_ptr(), $d.seeds[i].as_ptr()) };
            assert_eq!(rc, 0);
            tag(&pk) ^ tag(&sk)
        });
        cell($cells, $label, "sign-det", NMSG, move |i| {
            let mut sig = [0u8; $sig];
            let m = &$d.msgs[i];
            let rc = unsafe { $sg($lvl, sig.as_mut_ptr(), m.as_ptr(), m.len(), CTX.as_ptr(), CTX.len(), ZERO.as_ptr(), $d.sk.as_ptr()) };
            assert_eq!(rc, 0);
            tag(&sig)
        });
        cell($cells, $label, "sign-hedged", NMSG, move |i| {
            let mut sig = [0u8; $sig];
            let m = &$d.msgs[i];
            let rc = unsafe { $sg($lvl, sig.as_mut_ptr(), m.as_ptr(), m.len(), CTX.as_ptr(), CTX.len(), $d.rnd_h[i].as_ptr(), $d.sk.as_ptr()) };
            assert_eq!(rc, 0);
            tag(&sig)
        });
        cell($cells, $label, "verify", NMSG, move |i| {
            let m = &$d.msgs[i];
            let rc = unsafe { $vf($lvl, $d.sig_det[i].as_ptr(), m.as_ptr(), m.len(), CTX.as_ptr(), CTX.len(), $d.pk.as_ptr()) };
            (rc == 0) as u64
        });
    }};
}

/// aws-lc-rs 1.18.2, called the way nearcore calls it: verify through `UnparsedPublicKey`, sign through
/// `PqdsaKeyPair::from_raw_private_key` + `sign`, keygen through `PqdsaKeyPair::from_seed`. There is no context
/// parameter (the empty context is implied) and signing is hedged with fresh randomness, so there is no
/// deterministic sign and the sign outputs differ from run to run (`is_random_output`).
macro_rules! aws_cells {
    ($cells:ident, $d:ident, $kg:ident, $alg_v:path, $alg_s:path, $sig:literal) => {{
        use aws_lc_rs::encoding::AsRawBytes;
        use aws_lc_rs::signature::{KeyPair, PqdsaKeyPair, UnparsedPublicKey};
        // Untimed sanity: the aws-lc key from the seed matches ours, and the signatures it produces verify under ours.
        {
            let kp = PqdsaKeyPair::from_seed(&$alg_s, &$d.seeds[0]).unwrap();
            assert_eq!(kp.public_key().as_ref(), api::$kg(&$d.seeds[0]).0.as_slice());
            let mut sig = [0u8; $sig];
            let kp = PqdsaKeyPair::from_raw_private_key(&$alg_s, &$d.sk).unwrap();
            assert_eq!(kp.sign(&$d.msgs[0], &mut sig).unwrap(), $sig);
            assert!(UnparsedPublicKey::new(&$alg_v, &$d.pk).verify(&$d.msgs[0], &sig).is_ok());
            assert!(UnparsedPublicKey::new(&$alg_v, &$d.pk).verify(&$d.msgs[0], &$d.sig_det[0]).is_ok());
        }
        cell($cells, "aws-lc-rs", "keygen", NSEED, move |i| {
            let kp = PqdsaKeyPair::from_seed(&$alg_s, &$d.seeds[i]).unwrap();
            tag(kp.public_key().as_ref())
        });
        // plus exporting the expanded secret key, which is part of the output of every other implementation's keygen
        cell($cells, "aws-lc-rs+sk-export", "keygen", NSEED, move |i| {
            let kp = PqdsaKeyPair::from_seed(&$alg_s, &$d.seeds[i]).unwrap();
            let sk = kp.private_key().as_raw_bytes().unwrap();
            tag(kp.public_key().as_ref()) ^ tag(sk.as_ref())
        });
        cell($cells, "aws-lc-rs", "sign-hedged", NMSG, move |i| {
            let kp = PqdsaKeyPair::from_raw_private_key(&$alg_s, &$d.sk).unwrap();
            let mut sig = [0u8; $sig];
            assert_eq!(kp.sign(&$d.msgs[i], &mut sig).unwrap(), $sig);
            tag(&sig)
        });
        {
            let kp = PqdsaKeyPair::from_raw_private_key(&$alg_s, &$d.sk).unwrap();
            cell($cells, "aws-lc-rs+cached-sk", "sign-hedged", NMSG, move |i| {
                let mut sig = [0u8; $sig];
                assert_eq!(kp.sign(&$d.msgs[i], &mut sig).unwrap(), $sig);
                tag(&sig)
            });
        }
        cell($cells, "aws-lc-rs", "verify", NMSG, move |i| {
            UnparsedPublicKey::new(&$alg_v, &$d.pk).verify(&$d.msgs[i], &$d.sig_det[i]).is_ok() as u64
        });
    }};
}

/// Cells whose output cannot be compared with the other implementations' bytes: aws-lc-rs signs with fresh
/// randomness, and its plain keygen cell returns only the public key's tag (the `+sk-export` cell is compared).
pub fn skips_agreement_check(imp: &str, group: &str) -> bool {
    (imp.starts_with("aws-lc-rs") && group.starts_with("sign")) || (imp == "aws-lc-rs" && group == "keygen")
}

macro_rules! define_set {
    ($build:ident, $cellsfn:ident, $lvl:literal, $P:ty, $kg:ident, $sg:ident, $vf:ident, $vkf:ident, $vpf:ident, $skf:ident, $spf:ident,
     $pk:literal, $sk:literal, $sig:literal, $m:ident, $LSK:ident, $LVK:ident, $LSIG:ident, $AV:path, $AS:path) => {
        pub fn $build() -> SetData {
            SetData::build(
                $lvl,
                |xi| {
                    let (pk, sk) = api::$kg(xi);
                    (pk.to_vec(), sk.to_vec())
                },
                |sk, m, rnd| api::$sg(sk.try_into().unwrap(), m, CTX, rnd).unwrap().to_vec(),
            )
        }

        pub fn $cellsfn<'a>(d: &'a SetData, cells: &mut Vec<Cell<'a>>) {
            let pk_a: &'a [u8; $pk] = d.pk.as_slice().try_into().unwrap();
            let sk_a: &'a [u8; $sk] = d.sk.as_slice().try_into().unwrap();

            // ---- this crate -------------------------------------------------------------------
            cell(cells, "ours", "keygen", NSEED, move |i| {
                let (pk, sk) = api::$kg(&d.seeds[i]);
                tag(&pk) ^ tag(&sk)
            });
            cell(cells, "ours", "sign-det", NMSG, move |i| tag(&api::$sg(sk_a, &d.msgs[i], CTX, &ZERO).unwrap()));
            cell(cells, "ours", "sign-hedged", NMSG, move |i| tag(&api::$sg(sk_a, &d.msgs[i], CTX, &d.rnd_h[i]).unwrap()));
            cell(cells, "ours", "verify", NMSG, move |i| {
                let s: &[u8; $sig] = d.sig_det[i].as_slice().try_into().unwrap();
                api::$vf(pk_a, &d.msgs[i], CTX, s) as u64
            });

            // building the prepared verifying key (`verifying_key_NN`: ExpandA, NTT(t1 * 2^d), tr); dispatched like verify
            cell(cells, "ours+verifying-key", "verifying-key", NMSG, move |_| {
                std::hint::black_box(api::$vkf(std::hint::black_box(pk_a)));
                1
            });

            // prepared verifying key (Â, NTT(t1 * 2^d), tr computed once; boxed like a caller would)
            {
                let vk = Box::new(api::$vkf(pk_a));
                cell(cells, "ours+prepared-vk", "verify", NMSG, move |i| {
                    let s: &[u8; $sig] = d.sig_det[i].as_slice().try_into().unwrap();
                    api::$vpf(&vk, &d.msgs[i], CTX, s) as u64
                });
            }

            // prepared signing key (skDecode, NTTs, Â, K, tr computed once; boxed like a caller would)
            {
                let ssk = Box::new(api::$skf(sk_a));
                cell(cells, "ours+prepared-sk", "sign-det", NMSG, move |i| {
                    tag(&api::$spf(&ssk, &d.msgs[i], CTX, &ZERO).unwrap())
                });
            }
            {
                let ssk = Box::new(api::$skf(sk_a));
                cell(cells, "ours+prepared-sk", "sign-hedged", NMSG, move |i| {
                    tag(&api::$spf(&ssk, &d.msgs[i], CTX, &d.rnd_h[i]).unwrap())
                });
            }

            // ---- RustCrypto ml-dsa a3690c4 ---------------------------------------------------
            {
                use ml_dsa::{EncodedVerifyingKey, ExpandedSigningKey, ExpandedSigningKeyBytes, Seed, Signature, VerifyingKey};
                type P = $P;
                let enc_sk = ExpandedSigningKeyBytes::<P>::try_from(d.sk.as_slice()).unwrap();
                let esk = ExpandedSigningKey::<P>::from_expanded(&enc_sk);
                let vk = VerifyingKey::<P>::decode(&EncodedVerifyingKey::<P>::try_from(d.pk.as_slice()).unwrap());
                // M' = 0 || |ctx| || ctx || m, built outside the timed call
                let mps: Vec<Vec<u8>> = d.msgs.iter().map(|m| [&[0u8, CTX.len() as u8][..], CTX, m].concat()).collect();
                let mps2 = mps.clone();
                let mps3 = mps.clone();
                let mps4 = mps.clone();
                cell(cells, "rustcrypto", "keygen", NSEED, move |i| {
                    let e = ExpandedSigningKey::<P>::from_seed(&Seed::from(d.seeds[i]));
                    let pk = e.verifying_key().encode();
                    let sk = e.to_expanded();
                    tag(pk.as_slice()) ^ tag(sk.as_slice())
                });
                // from the encoded key every call, like every other implementation here
                cell(cells, "rustcrypto", "sign-det", NMSG, move |i| {
                    let e = ExpandedSigningKey::<P>::from_expanded(&enc_sk);
                    tag(e.sign_internal(&[&mps[i]], &ml_dsa::B32::from(ZERO)).encode().as_slice())
                });
                let enc_sk2 = ExpandedSigningKeyBytes::<P>::try_from(d.sk.as_slice()).unwrap();
                cell(cells, "rustcrypto", "sign-hedged", NMSG, move |i| {
                    let e = ExpandedSigningKey::<P>::from_expanded(&enc_sk2);
                    tag(e.sign_internal(&[&mps2[i]], &ml_dsa::B32::from(d.rnd_h[i])).encode().as_slice())
                });
                // key expanded once (Â, ŝ1, ŝ2, t̂0 cached)
                let esk2 = ExpandedSigningKey::<P>::from_expanded(&ExpandedSigningKeyBytes::<P>::try_from(d.sk.as_slice()).unwrap());
                cell(cells, "rustcrypto+cached-sk", "sign-det", NMSG, move |i| {
                    tag(esk.sign_internal(&[&mps3[i]], &ml_dsa::B32::from(ZERO)).encode().as_slice())
                });
                cell(cells, "rustcrypto+cached-sk", "sign-hedged", NMSG, move |i| {
                    tag(esk2.sign_internal(&[&mps4[i]], &ml_dsa::B32::from(d.rnd_h[i])).encode().as_slice())
                });
                // decode the key (this expands Â) on every call
                cell(cells, "rustcrypto", "verify", NMSG, move |i| {
                    let vk = VerifyingKey::<P>::decode(&EncodedVerifyingKey::<P>::try_from(d.pk.as_slice()).unwrap());
                    let s = Signature::<P>::try_from(d.sig_det[i].as_slice()).unwrap();
                    vk.verify_with_context(&d.msgs[i], CTX, &s) as u64
                });
                // key decoded once; Â cached inside the VerifyingKey
                cell(cells, "rustcrypto+cached-vk", "verify", NMSG, move |i| {
                    let s = Signature::<P>::try_from(d.sig_det[i].as_slice()).unwrap();
                    vk.verify_with_context(&d.msgs[i], CTX, &s) as u64
                });
            }

            // ---- libcrux-ml-dsa 0.0.11 --------------------------------------------------------
            lc_cells!(cells, d, "libcrux-portable", $m, portable, $LSK, $LVK, $LSIG, $pk, $sk);
            #[cfg(target_arch = "x86_64")]
            if have_avx2() {
                lc_cells!(cells, d, "libcrux-avx2", $m, avx2, $LSK, $LVK, $LSIG, $pk, $sk);
            }

            // ---- aws-lc-rs 1.18.2 (C, runtime CPU dispatch) -----------------------------------
            aws_cells!(cells, d, $kg, $AV, $AS, $sig);

            // ---- mldsa-native v2.0.0 (C) ------------------------------------------------------
            mld_cells!(
                cells, d, "mldsa-native-portable",
                mld::portable::xc_p_keypair_internal, mld::portable::xc_p_signature, mld::portable::xc_p_verify,
                $lvl, $pk, $sk, $sig
            );
            #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
            if have_avx2() {
                mld_cells!(
                    cells, d, "mldsa-native-avx2",
                    mld::avx2::xc_a_keypair_internal, mld::avx2::xc_a_signature, mld::avx2::xc_a_verify,
                    $lvl, $pk, $sk, $sig
                );
            }
        }
    };
}

define_set!(build_44, cells_44, 44, ml_dsa::MlDsa44, keygen_44, sign_44, verify_44, verifying_key_44, verify_prepared_44, signing_key_44, sign_prepared_44, 1312, 2560, 2420,
    ml_dsa_44, MLDSA44SigningKey, MLDSA44VerificationKey, MLDSA44Signature,
    aws_lc_rs::signature::ML_DSA_44, aws_lc_rs::signature::ML_DSA_44_SIGNING);
define_set!(build_65, cells_65, 65, ml_dsa::MlDsa65, keygen_65, sign_65, verify_65, verifying_key_65, verify_prepared_65, signing_key_65, sign_prepared_65, 1952, 4032, 3309,
    ml_dsa_65, MLDSA65SigningKey, MLDSA65VerificationKey, MLDSA65Signature,
    aws_lc_rs::signature::ML_DSA_65, aws_lc_rs::signature::ML_DSA_65_SIGNING);
define_set!(build_87, cells_87, 87, ml_dsa::MlDsa87, keygen_87, sign_87, verify_87, verifying_key_87, verify_prepared_87, signing_key_87, sign_prepared_87, 2592, 4896, 4627,
    ml_dsa_87, MLDSA87SigningKey, MLDSA87VerificationKey, MLDSA87Signature,
    aws_lc_rs::signature::ML_DSA_87, aws_lc_rs::signature::ML_DSA_87_SIGNING);


/// Inputs for ML-DSA-`set`.
pub fn build_set(set: u32) -> SetData {
    match set {
        44 => build_44(),
        65 => build_65(),
        87 => build_87(),
        _ => panic!("set must be 44, 65 or 87"),
    }
}

/// All implementations' closures for ML-DSA-`set`, ordered by operation (keygen, sign-det, sign-hedged, verify, verifying-key).
pub fn cells_for<'a>(set: u32, d: &'a SetData) -> Vec<Cell<'a>> {
    let mut cells: Vec<Cell> = vec![];
    match set {
        44 => cells_44(d, &mut cells),
        65 => cells_65(d, &mut cells),
        _ => cells_87(d, &mut cells),
    }
    let order = ["keygen", "sign-det", "sign-hedged", "verify", "verifying-key"];
    cells.sort_by_key(|c| order.iter().position(|g| *g == c.group).unwrap());
    cells
}
