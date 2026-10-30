//! Uniform access to every implementation: ours (public `api` only), RustCrypto `ml-dsa`, libcrux-ml-dsa
//! (portable, AVX2) and mldsa-native (portable C, AVX2).
//!
//! All inputs are exact-length byte slices (the arrays and pointers of three of the four APIs cannot express
//! anything else). Panics inside an oracle are caught by `guard` and reported, never propagated.
#![allow(deprecated)]

use crate::Set;
use crate::mldsa_native;
use ml_dsa::{
    EncodedVerifyingKey, ExpandedSigningKey, ExpandedSigningKeyBytes, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Signature,
    VerifyingKey,
};
use ml_dsa_verified::api;
use std::cell::Cell;

// ---------------------------------------------------------------------------------------------
// Implementations
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Imp {
    Ours,
    RustCrypto,
    LibcruxPortable,
    LibcruxAvx2,
    MldsaPortable,
    MldsaAvx2,
}

impl Imp {
    pub fn name(self) -> &'static str {
        match self {
            Imp::Ours => "ours",
            Imp::RustCrypto => "rustcrypto",
            Imp::LibcruxPortable => "libcrux-portable",
            Imp::LibcruxAvx2 => "libcrux-avx2",
            Imp::MldsaPortable => "mldsa-native-portable",
            Imp::MldsaAvx2 => "mldsa-native-avx2",
        }
    }
}

/// Whether the AVX2 backends can run here: compiled in and supported by this CPU.
pub fn avx2_usable() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        is_x86_feature_detected!("avx2") && is_x86_feature_detected!("bmi2")
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        false
    }
}

/// Every implementation usable on this machine, `Ours` first. `XC_NO_AVX2=1` (run time) drops the AVX2 backends.
pub fn available() -> Vec<Imp> {
    let mut v = vec![Imp::Ours, Imp::RustCrypto, Imp::LibcruxPortable, Imp::MldsaPortable];
    let avx2 = avx2_usable() && std::env::var_os("XC_NO_AVX2").is_none();
    if avx2 {
        v.push(Imp::LibcruxAvx2);
        #[cfg(xc_avx2)]
        v.push(Imp::MldsaAvx2);
    }
    v
}

// ---------------------------------------------------------------------------------------------
// Results
// ---------------------------------------------------------------------------------------------

/// Outcome of a signing attempt. Two outcomes are equal when both are the same signature bytes, both are a
/// refusal (whatever the error text), or both panicked.
#[derive(Clone, Debug)]
pub enum SignRes {
    Sig(Vec<u8>),
    NoSig(String),
    Panic(String),
}

impl SignRes {
    pub fn kind(&self) -> &'static str {
        match self {
            SignRes::Sig(_) => "sig",
            SignRes::NoSig(_) => "error",
            SignRes::Panic(_) => "panic",
        }
    }
    pub fn same(&self, other: &SignRes) -> bool {
        match (self, other) {
            (SignRes::Sig(a), SignRes::Sig(b)) => a == b,
            (SignRes::NoSig(_), SignRes::NoSig(_)) | (SignRes::Panic(_), SignRes::Panic(_)) => true,
            _ => false,
        }
    }
    pub fn sig(&self) -> Option<&Vec<u8>> {
        match self {
            SignRes::Sig(s) => Some(s),
            _ => None,
        }
    }
}

/// Verify outcome: the verdict plus the oracle's reason when it gives one (for reports only).
#[derive(Clone, Copy, Debug)]
pub struct Verdict {
    pub ok: bool,
    pub why: &'static str,
}

impl Verdict {
    fn yes() -> Verdict {
        Verdict { ok: true, why: "" }
    }
    fn no(why: &'static str) -> Verdict {
        Verdict { ok: false, why }
    }
}

// ---------------------------------------------------------------------------------------------
// Panic containment
// ---------------------------------------------------------------------------------------------

thread_local! {
    static GUARDED: Cell<u32> = const { Cell::new(0) };
}

/// Installs a panic hook that stays quiet inside `guard` and otherwise prints and, if `abort` is set, aborts
/// (so libFuzzer records a crash).
pub fn install_panic_hook(abort: bool) {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if GUARDED.with(|g| g.get()) > 0 {
            return;
        }
        prev(info);
        if abort {
            std::process::abort();
        }
    }));
}

/// Runs `f`; a panic comes back as `Err(message)`.
pub fn guard<R>(f: impl FnOnce() -> R) -> Result<R, String> {
    GUARDED.with(|g| g.set(g.get() + 1));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    GUARDED.with(|g| g.set(g.get() - 1));
    r.map_err(|p| {
        if let Some(s) = p.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = p.downcast_ref::<String>() {
            s.clone()
        } else {
            "panic".to_string()
        }
    })
}

// ---------------------------------------------------------------------------------------------
// ours
// ---------------------------------------------------------------------------------------------

fn ours_keygen(set: Set, xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
    match set {
        Set::S44 => {
            let (pk, sk) = api::keygen_44(xi);
            (pk.to_vec(), sk.to_vec())
        }
        Set::S65 => {
            let (pk, sk) = api::keygen_65(xi);
            (pk.to_vec(), sk.to_vec())
        }
        Set::S87 => {
            let (pk, sk) = api::keygen_87(xi);
            (pk.to_vec(), sk.to_vec())
        }
    }
}

fn opt(r: Option<Vec<u8>>, why: &str) -> SignRes {
    match r {
        Some(s) => SignRes::Sig(s),
        None => SignRes::NoSig(why.to_string()),
    }
}

fn ours_sign(set: Set, sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> SignRes {
    let r = match set {
        Set::S44 => api::sign_44(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
        Set::S65 => api::sign_65(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
        Set::S87 => api::sign_87(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
    };
    opt(r, "None (|ctx| > 255 or kappa budget)")
}

fn ours_sign_internal(set: Set, sk: &[u8], mp: &[u8], rnd: &[u8; 32]) -> SignRes {
    let r = match set {
        Set::S44 => api::sign_internal_44(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
        Set::S65 => api::sign_internal_65(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
        Set::S87 => api::sign_internal_87(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
    };
    opt(r, "None (kappa budget)")
}

fn ours_verify(set: Set, pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> bool {
    match set {
        Set::S44 => api::verify_44(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
        Set::S65 => api::verify_65(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
        Set::S87 => api::verify_87(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
    }
}

fn ours_verify_internal(set: Set, pk: &[u8], mp: &[u8], sig: &[u8]) -> bool {
    match set {
        Set::S44 => api::verify_internal_44(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
        Set::S65 => api::verify_internal_65(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
        Set::S87 => api::verify_internal_87(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
    }
}

/// `sk_is_well_formed_NN` of our crate.
pub fn ours_sk_is_well_formed(set: Set, sk: &[u8]) -> bool {
    match set {
        Set::S44 => api::sk_is_well_formed_44(sk.try_into().unwrap()),
        Set::S65 => api::sk_is_well_formed_65(sk.try_into().unwrap()),
        Set::S87 => api::sk_is_well_formed_87(sk.try_into().unwrap()),
    }
}

// ---------------------------------------------------------------------------------------------
// RustCrypto ml-dsa
// ---------------------------------------------------------------------------------------------

fn rc_keygen_p<P: MlDsaParams>(xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
    let esk = ExpandedSigningKey::<P>::from_seed(&ml_dsa::B32::from(*xi));
    (esk.verifying_key().encode().as_slice().to_vec(), esk.to_expanded().as_slice().to_vec())
}

fn rc_sign_internal_p<P: MlDsaParams>(sk: &[u8], mp: &[u8], rnd: &[u8; 32]) -> SignRes {
    let Ok(enc) = ExpandedSigningKeyBytes::<P>::try_from(sk) else { return SignRes::NoSig("bad sk length".into()) };
    let esk = ExpandedSigningKey::<P>::from_expanded(&enc);
    SignRes::Sig(esk.sign_internal(&[mp], &ml_dsa::B32::from(*rnd)).encode().as_slice().to_vec())
}

/// Algorithm 2 for |ctx| <= 255 goes through Sign_internal on M′; a longer context is handed to upstream's own
/// `sign_deterministic` so that upstream's length check is what refuses it.
fn rc_sign_p<P: MlDsaParams>(sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> SignRes {
    if ctx.len() <= 255 {
        let mp = [&[0u8, ctx.len() as u8][..], ctx, m].concat();
        return rc_sign_internal_p::<P>(sk, &mp, rnd);
    }
    let Ok(enc) = ExpandedSigningKeyBytes::<P>::try_from(sk) else { return SignRes::NoSig("bad sk length".into()) };
    let esk = ExpandedSigningKey::<P>::from_expanded(&enc);
    match esk.sign_deterministic(m, ctx) {
        Ok(s) => SignRes::Sig(s.encode().as_slice().to_vec()),
        Err(e) => SignRes::NoSig(format!("{e:?}")),
    }
}

fn rc_verify_p<P: MlDsaParams>(pk: &[u8], sig: &[u8], internal_mp: Option<&[u8]>, m: &[u8], ctx: &[u8]) -> Verdict {
    let Ok(enc) = EncodedVerifyingKey::<P>::try_from(pk) else { return Verdict::no("bad pk length") };
    let vk = VerifyingKey::<P>::decode(&enc);
    let Ok(s) = Signature::<P>::try_from(sig) else { return Verdict::no("signature decode") };
    let ok = match internal_mp {
        Some(mp) => vk.verify_internal(mp, &s),
        None => vk.verify_with_context(m, ctx, &s),
    };
    if ok { Verdict::yes() } else { Verdict::no("reject") }
}

macro_rules! by_set {
    ($set:expr, $f:ident($($a:expr),*)) => {
        match $set {
            Set::S44 => $f::<MlDsa44>($($a),*),
            Set::S65 => $f::<MlDsa65>($($a),*),
            Set::S87 => $f::<MlDsa87>($($a),*),
        }
    };
}

/// RustCrypto is the only oracle whose API takes slices: Verify on inputs of any length (wrong lengths must be
/// rejected, never panic). The other APIs take fixed-size arrays or pointers whose size is the contract.
pub fn rc_verify_any_len(set: Set, pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> Result<bool, String> {
    guard(|| by_set!(set, rc_verify_p(pk, sig, None, m, ctx)).ok)
}


// ---------------------------------------------------------------------------------------------
// libcrux-ml-dsa
// ---------------------------------------------------------------------------------------------

macro_rules! lc_module {
    ($modname:ident, $lvl:ident, $be:ident, $SK:ident, $VK:ident, $SIG:ident) => {
        pub mod $modname {
            use libcrux_ml_dsa::$lvl::{$SIG, $SK, $VK, $be};

            pub fn keygen(xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
                let kp = $be::generate_key_pair(*xi);
                (kp.verification_key.as_slice().to_vec(), kp.signing_key.as_slice().to_vec())
            }
            pub fn sign(sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> crate::oracle::SignRes {
                let sk = $SK::new(sk.try_into().unwrap());
                match $be::sign(&sk, m, ctx, *rnd) {
                    Ok(s) => crate::oracle::SignRes::Sig(s.as_slice().to_vec()),
                    Err(e) => crate::oracle::SignRes::NoSig(format!("{e:?}")),
                }
            }
            pub fn sign_internal(sk: &[u8], mp: &[u8], rnd: &[u8; 32]) -> crate::oracle::SignRes {
                let sk = $SK::new(sk.try_into().unwrap());
                match $be::sign_internal(&sk, mp, *rnd) {
                    Ok(s) => crate::oracle::SignRes::Sig(s.as_slice().to_vec()),
                    Err(e) => crate::oracle::SignRes::NoSig(format!("{e:?}")),
                }
            }
            fn why(e: libcrux_ml_dsa::VerificationError) -> &'static str {
                use libcrux_ml_dsa::VerificationError::*;
                match e {
                    MalformedHintError => "MalformedHint",
                    SignerResponseExceedsBoundError => "ResponseExceedsBound",
                    CommitmentHashesDontMatchError => "CommitmentHashMismatch",
                    VerificationContextTooLongError => "ContextTooLong",
                }
            }
            pub fn verify(pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> crate::oracle::Verdict {
                let pk = $VK::new(pk.try_into().unwrap());
                let sig = $SIG::new(sig.try_into().unwrap());
                match $be::verify(&pk, m, ctx, &sig) {
                    Ok(()) => crate::oracle::Verdict { ok: true, why: "" },
                    Err(e) => crate::oracle::Verdict { ok: false, why: why(e) },
                }
            }
            pub fn verify_internal(pk: &[u8], mp: &[u8], sig: &[u8]) -> crate::oracle::Verdict {
                let pk = $VK::new(pk.try_into().unwrap());
                let sig = $SIG::new(sig.try_into().unwrap());
                match $be::verify_internal(&pk, mp, &sig) {
                    Ok(()) => crate::oracle::Verdict { ok: true, why: "" },
                    Err(e) => crate::oracle::Verdict { ok: false, why: why(e) },
                }
            }
        }
    };
}

pub mod lc {
    lc_module!(p44, ml_dsa_44, portable, MLDSA44SigningKey, MLDSA44VerificationKey, MLDSA44Signature);
    lc_module!(p65, ml_dsa_65, portable, MLDSA65SigningKey, MLDSA65VerificationKey, MLDSA65Signature);
    lc_module!(p87, ml_dsa_87, portable, MLDSA87SigningKey, MLDSA87VerificationKey, MLDSA87Signature);
    #[cfg(target_arch = "x86_64")]
    lc_module!(a44, ml_dsa_44, avx2, MLDSA44SigningKey, MLDSA44VerificationKey, MLDSA44Signature);
    #[cfg(target_arch = "x86_64")]
    lc_module!(a65, ml_dsa_65, avx2, MLDSA65SigningKey, MLDSA65VerificationKey, MLDSA65Signature);
    #[cfg(target_arch = "x86_64")]
    lc_module!(a87, ml_dsa_87, avx2, MLDSA87SigningKey, MLDSA87VerificationKey, MLDSA87Signature);
}

macro_rules! lc_dispatch {
    ($avx2:expr, $set:expr, $f:ident($($a:expr),*)) => {{
        #[cfg(target_arch = "x86_64")]
        {
            if $avx2 {
                match $set { Set::S44 => lc::a44::$f($($a),*), Set::S65 => lc::a65::$f($($a),*), Set::S87 => lc::a87::$f($($a),*) }
            } else {
                match $set { Set::S44 => lc::p44::$f($($a),*), Set::S65 => lc::p65::$f($($a),*), Set::S87 => lc::p87::$f($($a),*) }
            }
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            let _ = $avx2;
            match $set { Set::S44 => lc::p44::$f($($a),*), Set::S65 => lc::p65::$f($($a),*), Set::S87 => lc::p87::$f($($a),*) }
        }
    }};
}

// ---------------------------------------------------------------------------------------------
// mldsa-native
// ---------------------------------------------------------------------------------------------

fn mldsa_backend(imp: Imp) -> mldsa_native::Backend {
    match imp {
        Imp::MldsaPortable => mldsa_native::PORTABLE,
        #[cfg(xc_avx2)]
        Imp::MldsaAvx2 => mldsa_native::AVX2,
        _ => unreachable!("not an mldsa-native implementation"),
    }
}

fn mld_sign_res(r: Result<Vec<u8>, i32>) -> SignRes {
    match r {
        Ok(s) => SignRes::Sig(s),
        Err(rc) => SignRes::NoSig(mldsa_native::err_name(rc)),
    }
}

fn mld_verdict(rc: i32) -> Verdict {
    match rc {
        0 => Verdict::yes(),
        -6 => Verdict::no("INVALID_SIGNATURE"),
        -9 => Verdict::no("INVALID_ARG"),
        _ => Verdict::no("other error"),
    }
}

// ---------------------------------------------------------------------------------------------
// Dispatch
// ---------------------------------------------------------------------------------------------

impl Imp {
    /// KeyGen from ξ: (pk, sk). mldsa-native is asked through `keypair_internal`; `keygen_alt` goes through the
    /// randomized `keypair` entry point with ξ supplied as its random bytes.
    pub fn keygen(self, set: Set, xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
        match self {
            Imp::Ours => ours_keygen(set, xi),
            Imp::RustCrypto => by_set!(set, rc_keygen_p(xi)),
            Imp::LibcruxPortable => lc_dispatch!(false, set, keygen(xi)),
            Imp::LibcruxAvx2 => lc_dispatch!(true, set, keygen(xi)),
            Imp::MldsaPortable | Imp::MldsaAvx2 => mldsa_backend(self).keypair_internal(set, xi),
        }
    }

    /// Second KeyGen entry point where one exists (mldsa-native `keypair`).
    pub fn keygen_alt(self, set: Set, xi: &[u8; 32]) -> Option<(Vec<u8>, Vec<u8>)> {
        match self {
            Imp::MldsaPortable | Imp::MldsaAvx2 => Some(mldsa_backend(self).keypair(set, xi)),
            _ => None,
        }
    }

    /// Algorithm 2: Sign(sk, m, ctx) with the given 32 bytes of randomness (zeros = deterministic variant).
    pub fn sign(self, set: Set, sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> SignRes {
        let r = guard(|| match self {
            Imp::Ours => ours_sign(set, sk, m, ctx, rnd),
            Imp::RustCrypto => by_set!(set, rc_sign_p(sk, m, ctx, rnd)),
            Imp::LibcruxPortable => lc_dispatch!(false, set, sign(sk, m, ctx, rnd)),
            Imp::LibcruxAvx2 => lc_dispatch!(true, set, sign(sk, m, ctx, rnd)),
            Imp::MldsaPortable | Imp::MldsaAvx2 => mld_sign_res(mldsa_backend(self).signature(set, sk, m, ctx, rnd)),
        });
        r.unwrap_or_else(SignRes::Panic)
    }

    /// Algorithm 7: Sign_internal on M′. mldsa-native receives M′ split as `mp[..split]` (prefix) and `mp[split..]`.
    pub fn sign_internal(self, set: Set, sk: &[u8], mp: &[u8], split: usize, rnd: &[u8; 32]) -> SignRes {
        let r = guard(|| match self {
            Imp::Ours => ours_sign_internal(set, sk, mp, rnd),
            Imp::RustCrypto => by_set!(set, rc_sign_internal_p(sk, mp, rnd)),
            Imp::LibcruxPortable => lc_dispatch!(false, set, sign_internal(sk, mp, rnd)),
            Imp::LibcruxAvx2 => lc_dispatch!(true, set, sign_internal(sk, mp, rnd)),
            Imp::MldsaPortable | Imp::MldsaAvx2 => {
                let s = split.min(mp.len());
                mld_sign_res(mldsa_backend(self).signature_internal(set, sk, &mp[..s], &mp[s..], rnd))
            }
        });
        r.unwrap_or_else(SignRes::Panic)
    }

    /// Algorithm 3: Verify(pk, m, ctx, sig).
    pub fn verify(self, set: Set, pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> Verdict {
        let r = guard(|| match self {
            Imp::Ours => {
                if ours_verify(set, pk, m, ctx, sig) {
                    Verdict::yes()
                } else {
                    Verdict::no("reject")
                }
            }
            Imp::RustCrypto => by_set!(set, rc_verify_p(pk, sig, None, m, ctx)),
            Imp::LibcruxPortable => lc_dispatch!(false, set, verify(pk, m, ctx, sig)),
            Imp::LibcruxAvx2 => lc_dispatch!(true, set, verify(pk, m, ctx, sig)),
            Imp::MldsaPortable | Imp::MldsaAvx2 => mld_verdict(mldsa_backend(self).verify(set, pk, m, ctx, sig)),
        });
        r.unwrap_or(Verdict { ok: false, why: "PANIC" })
    }

    /// Algorithm 8: Verify_internal on M′ (`split` as for `sign_internal`).
    pub fn verify_internal(self, set: Set, pk: &[u8], mp: &[u8], split: usize, sig: &[u8]) -> Verdict {
        let r = guard(|| match self {
            Imp::Ours => {
                if ours_verify_internal(set, pk, mp, sig) {
                    Verdict::yes()
                } else {
                    Verdict::no("reject")
                }
            }
            Imp::RustCrypto => by_set!(set, rc_verify_p(pk, sig, Some(mp), &[], &[])),
            Imp::LibcruxPortable => lc_dispatch!(false, set, verify_internal(pk, mp, sig)),
            Imp::LibcruxAvx2 => lc_dispatch!(true, set, verify_internal(pk, mp, sig)),
            Imp::MldsaPortable | Imp::MldsaAvx2 => {
                let s = split.min(mp.len());
                mld_verdict(mldsa_backend(self).verify_internal(set, pk, &mp[..s], &mp[s..], sig))
            }
        });
        r.unwrap_or(Verdict { ok: false, why: "PANIC" })
    }

    /// mldsa-native only: `pk_from_sk` (validates s1/s2 range, t0 and tr). Other implementations: `None`.
    pub fn validate_sk(self, set: Set, sk: &[u8]) -> Option<Result<Vec<u8>, i32>> {
        match self {
            Imp::MldsaPortable | Imp::MldsaAvx2 => Some(mldsa_backend(self).pk_from_sk(set, sk)),
            _ => None,
        }
    }
}

/// M′ = 0 ‖ |ctx| ‖ ctx ‖ m for |ctx| <= 255 (Algorithm 2 step 10), else `None`.
pub fn build_mp(ctx: &[u8], m: &[u8]) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let mut v = Vec::with_capacity(2 + ctx.len() + m.len());
    v.push(0);
    v.push(ctx.len() as u8);
    v.extend_from_slice(ctx);
    v.extend_from_slice(m);
    Some(v)
}
