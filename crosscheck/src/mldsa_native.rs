//! FFI to mldsa-native (vendored, built by build.rs). Two builds with distinct namespaces: portable C and, on
//! x86_64 Linux, AVX2 (native arithmetic and Keccak). Every call takes the level (44, 65 or 87).
//!
//! The randomized entry points (`keypair`, `signature`) draw their random bytes from a thread-local buffer that
//! the C wrapper fills from the `rnd`/`seed` argument, so they are deterministic here.
use crate::Set;
use std::os::raw::c_int;

type KeypairInternal = unsafe extern "C" fn(c_int, *mut u8, *mut u8, *const u8) -> c_int;
type SignatureInternal =
    unsafe extern "C" fn(c_int, *mut u8, *const u8, usize, *const u8, usize, *const u8, *const u8) -> c_int;
type Signature = unsafe extern "C" fn(c_int, *mut u8, *const u8, usize, *const u8, usize, *const u8, *const u8) -> c_int;
type VerifyInternal = unsafe extern "C" fn(c_int, *const u8, *const u8, usize, *const u8, usize, *const u8) -> c_int;
type Verify = unsafe extern "C" fn(c_int, *const u8, *const u8, usize, *const u8, usize, *const u8) -> c_int;
type PkFromSk = unsafe extern "C" fn(c_int, *mut u8, *const u8) -> c_int;

macro_rules! backend_externs {
    ($m:ident, $kpi:ident, $kp:ident, $si:ident, $s:ident, $vi:ident, $v:ident, $pfs:ident) => {
        mod $m {
            use super::*;
            unsafe extern "C" {
                pub fn $kpi(lvl: c_int, pk: *mut u8, sk: *mut u8, seed: *const u8) -> c_int;
                pub fn $kp(lvl: c_int, pk: *mut u8, sk: *mut u8, seed: *const u8) -> c_int;
                pub fn $si(lvl: c_int, sig: *mut u8, m: *const u8, mlen: usize, pre: *const u8, prelen: usize, rnd: *const u8, sk: *const u8) -> c_int;
                pub fn $s(lvl: c_int, sig: *mut u8, m: *const u8, mlen: usize, ctx: *const u8, ctxlen: usize, rnd: *const u8, sk: *const u8) -> c_int;
                pub fn $vi(lvl: c_int, sig: *const u8, m: *const u8, mlen: usize, pre: *const u8, prelen: usize, pk: *const u8) -> c_int;
                pub fn $v(lvl: c_int, sig: *const u8, m: *const u8, mlen: usize, ctx: *const u8, ctxlen: usize, pk: *const u8) -> c_int;
                pub fn $pfs(lvl: c_int, pk: *mut u8, sk: *const u8) -> c_int;
            }
        }
    };
}

backend_externs!(p, xc_p_keypair_internal, xc_p_keypair, xc_p_signature_internal, xc_p_signature, xc_p_verify_internal, xc_p_verify, xc_p_pk_from_sk);
#[cfg(xc_avx2)]
backend_externs!(a, xc_a_keypair_internal, xc_a_keypair, xc_a_signature_internal, xc_a_signature, xc_a_verify_internal, xc_a_verify, xc_a_pk_from_sk);

/// One mldsa-native build.
#[derive(Clone, Copy)]
pub struct Backend {
    pub name: &'static str,
    keypair_internal: KeypairInternal,
    keypair: KeypairInternal,
    signature_internal: SignatureInternal,
    signature: Signature,
    verify_internal: VerifyInternal,
    verify: Verify,
    pk_from_sk: PkFromSk,
}

pub const PORTABLE: Backend = Backend {
    name: "mldsa-native-portable",
    keypair_internal: p::xc_p_keypair_internal,
    keypair: p::xc_p_keypair,
    signature_internal: p::xc_p_signature_internal,
    signature: p::xc_p_signature,
    verify_internal: p::xc_p_verify_internal,
    verify: p::xc_p_verify,
    pk_from_sk: p::xc_p_pk_from_sk,
};

#[cfg(xc_avx2)]
pub const AVX2: Backend = Backend {
    name: "mldsa-native-avx2",
    keypair_internal: a::xc_a_keypair_internal,
    keypair: a::xc_a_keypair,
    signature_internal: a::xc_a_signature_internal,
    signature: a::xc_a_signature,
    verify_internal: a::xc_a_verify_internal,
    verify: a::xc_a_verify,
    pk_from_sk: a::xc_a_pk_from_sk,
};

/// mldsa-native status codes (mldsa_native.h).
pub fn err_name(rc: i32) -> String {
    match rc {
        0 => "ok".into(),
        -1 => "FAIL".into(),
        -2 => "OUT_OF_MEMORY".into(),
        -3 => "RNG_FAIL".into(),
        -4 => "SIGN_ATTEMPTS_EXHAUSTED".into(),
        -5 => "SIGNING_PAUSED".into(),
        -6 => "INVALID_SIGNATURE".into(),
        -7 => "INVALID_KEY".into(),
        -8 => "PCT_FAIL".into(),
        -9 => "INVALID_ARG".into(),
        n => format!("code {n}"),
    }
}

impl Backend {
    fn lvl(set: Set) -> c_int {
        set.level()
    }

    /// Algorithm 6 from the seed (`keypair_internal`).
    pub fn keypair_internal(&self, set: Set, seed: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
        let (mut pk, mut sk) = (vec![0u8; set.pk_len()], vec![0u8; set.sk_len()]);
        let rc = unsafe { (self.keypair_internal)(Self::lvl(set), pk.as_mut_ptr(), sk.as_mut_ptr(), seed.as_ptr()) };
        assert_eq!(rc, 0, "{}: keypair_internal returned {}", self.name, err_name(rc));
        (pk, sk)
    }

    /// Algorithm 1 (`keypair`) with the seed supplied through the randombytes hook.
    pub fn keypair(&self, set: Set, seed: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
        let (mut pk, mut sk) = (vec![0u8; set.pk_len()], vec![0u8; set.sk_len()]);
        let rc = unsafe { (self.keypair)(Self::lvl(set), pk.as_mut_ptr(), sk.as_mut_ptr(), seed.as_ptr()) };
        assert_eq!(rc, 0, "{}: keypair returned {}", self.name, err_name(rc));
        (pk, sk)
    }

    /// Algorithm 7: M′ = `pre` ‖ `m`, explicit rnd.
    pub fn signature_internal(&self, set: Set, sk: &[u8], pre: &[u8], m: &[u8], rnd: &[u8; 32]) -> Result<Vec<u8>, i32> {
        assert_eq!(sk.len(), set.sk_len());
        let mut sig = vec![0u8; set.sig_len()];
        let rc = unsafe {
            (self.signature_internal)(Self::lvl(set), sig.as_mut_ptr(), m.as_ptr(), m.len(), pre.as_ptr(), pre.len(), rnd.as_ptr(), sk.as_ptr())
        };
        if rc == 0 { Ok(sig) } else { Err(rc) }
    }

    /// Algorithm 2 (`signature`), rnd through the randombytes hook.
    pub fn signature(&self, set: Set, sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Result<Vec<u8>, i32> {
        assert_eq!(sk.len(), set.sk_len());
        let mut sig = vec![0u8; set.sig_len()];
        let rc = unsafe {
            (self.signature)(Self::lvl(set), sig.as_mut_ptr(), m.as_ptr(), m.len(), ctx.as_ptr(), ctx.len(), rnd.as_ptr(), sk.as_ptr())
        };
        if rc == 0 { Ok(sig) } else { Err(rc) }
    }

    /// Algorithm 8: M′ = `pre` ‖ `m`.
    pub fn verify_internal(&self, set: Set, pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8]) -> i32 {
        assert_eq!(pk.len(), set.pk_len());
        assert_eq!(sig.len(), set.sig_len());
        unsafe { (self.verify_internal)(Self::lvl(set), sig.as_ptr(), m.as_ptr(), m.len(), pre.as_ptr(), pre.len(), pk.as_ptr()) }
    }

    /// Algorithm 3.
    pub fn verify(&self, set: Set, pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> i32 {
        assert_eq!(pk.len(), set.pk_len());
        assert_eq!(sig.len(), set.sig_len());
        unsafe { (self.verify)(Self::lvl(set), sig.as_ptr(), m.as_ptr(), m.len(), ctx.as_ptr(), ctx.len(), pk.as_ptr()) }
    }

    /// Secret-key validation: s1 and s2 in [−η, η], and t0 and tr consistent. Returns the recomputed pk on success.
    pub fn pk_from_sk(&self, set: Set, sk: &[u8]) -> Result<Vec<u8>, i32> {
        assert_eq!(sk.len(), set.sk_len());
        let mut pk = vec![0u8; set.pk_len()];
        let rc = unsafe { (self.pk_from_sk)(Self::lvl(set), pk.as_mut_ptr(), sk.as_ptr()) };
        if rc == 0 { Ok(pk) } else { Err(rc) }
    }
}
