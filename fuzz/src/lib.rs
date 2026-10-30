//! Shared harness code for the differential fuzz targets: parameter-set dispatch for our crate and for the
//! upstream oracle (RustCrypto `ml-dsa`, the revision the main crate's tests use), a byte cursor that
//! never fails (missing bytes read as zero), and the base (pk, sig, msg, ctx) pool used for mutation.
//!
//! The input formats are deliberately plain (explicit flag bytes and little-endian length prefixes) so
//! that `gen_seeds` can encode ACVP vectors into them and so that single-byte mutations stay meaningful.
#![allow(deprecated)]

use ml_dsa::{
    EncodedVerifyingKey, ExpandedSigningKey, ExpandedSigningKeyBytes, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Signature,
    VerifyingKey,
};
use ml_dsa_verified::api;
use ml_dsa_verified::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params, pk_len, sig_len, sk_len};
use ml_dsa_verified::sign::sign_internal;
use ml_dsa_verified::verify::verify_internal;
use std::cell::Cell;
use std::sync::OnceLock;

// ---------------------------------------------------------------------------------------------
// Parameter sets
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Set {
    S44,
    S65,
    S87,
}

impl Set {
    pub fn from_byte(b: u8) -> Set {
        match b % 3 {
            0 => Set::S44,
            1 => Set::S65,
            _ => Set::S87,
        }
    }
    pub fn to_byte(self) -> u8 {
        match self {
            Set::S44 => 0,
            Set::S65 => 1,
            Set::S87 => 2,
        }
    }
    pub fn params(self) -> &'static Params {
        match self {
            Set::S44 => &ML_DSA_44,
            Set::S65 => &ML_DSA_65,
            Set::S87 => &ML_DSA_87,
        }
    }
    pub fn pk_len(self) -> usize {
        pk_len(self.params())
    }
    pub fn sk_len(self) -> usize {
        sk_len(self.params())
    }
    pub fn sig_len(self) -> usize {
        sig_len(self.params())
    }
    pub fn from_name(s: &str) -> Option<Set> {
        match s {
            "ML-DSA-44" => Some(Set::S44),
            "ML-DSA-65" => Some(Set::S65),
            "ML-DSA-87" => Some(Set::S87),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Input cursor
// ---------------------------------------------------------------------------------------------

/// Reads from the fuzz input. Reading past the end yields zeros, so every byte string is a valid input.
pub struct Cur<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cur<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Cur { data, pos: 0 }
    }
    pub fn u8(&mut self) -> u8 {
        let b = self.data.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        b
    }
    pub fn u16(&mut self) -> u16 {
        let lo = self.u8() as u16;
        lo | (self.u8() as u16) << 8
    }
    /// Exactly `n` bytes, zero padded past the end of the input.
    pub fn take(&mut self, n: usize) -> Vec<u8> {
        let mut v = vec![0u8; n];
        let start = self.pos.min(self.data.len());
        let end = (self.pos + n).min(self.data.len());
        v[..end - start].copy_from_slice(&self.data[start..end]);
        self.pos += n;
        v
    }
    /// A u16 length prefix (at most `cap`) followed by that many bytes.
    pub fn blob(&mut self, cap: usize) -> Vec<u8> {
        let n = (self.u16() as usize).min(cap);
        self.take(n)
    }
    /// Everything that is left.
    pub fn rest(&mut self) -> Vec<u8> {
        let start = self.pos.min(self.data.len());
        self.pos = self.data.len();
        self.data[start..].to_vec()
    }
}

/// Encoder counterpart of `Cur`, used by `gen_seeds`.
#[derive(Default)]
pub struct Enc(pub Vec<u8>);

impl Enc {
    pub fn u8(&mut self, b: u8) -> &mut Self {
        self.0.push(b);
        self
    }
    pub fn raw(&mut self, b: &[u8]) -> &mut Self {
        self.0.extend_from_slice(b);
        self
    }
    pub fn blob(&mut self, b: &[u8]) -> &mut Self {
        self.0.extend_from_slice(&(b.len() as u16).to_le_bytes());
        self.0.extend_from_slice(b);
        self
    }
}

// ---------------------------------------------------------------------------------------------
// Our crate
// ---------------------------------------------------------------------------------------------

/// Algorithm 8 on slices of any length, M′ = prefix ‖ m.
pub fn ours_verify_internal(set: Set, pk: &[u8], prefix: &[u8], m: &[u8], sig: &[u8]) -> bool {
    match set {
        Set::S44 => verify_internal::<4, 4>(&ML_DSA_44, pk, prefix, m, sig),
        Set::S65 => verify_internal::<6, 5>(&ML_DSA_65, pk, prefix, m, sig),
        Set::S87 => verify_internal::<8, 7>(&ML_DSA_87, pk, prefix, m, sig),
    }
}

/// Algorithm 3 through the public API. Requires exact-length pk and sig (the API takes arrays).
pub fn ours_verify(set: Set, pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> bool {
    match set {
        Set::S44 => api::verify_44(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
        Set::S65 => api::verify_65(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
        Set::S87 => api::verify_87(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
    }
}

/// Algorithm 8 through the public API (exact lengths).
pub fn ours_verify_internal_api(set: Set, pk: &[u8], mp: &[u8], sig: &[u8]) -> bool {
    match set {
        Set::S44 => api::verify_internal_44(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
        Set::S65 => api::verify_internal_65(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
        Set::S87 => api::verify_internal_87(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
    }
}

pub fn ours_keygen(set: Set, xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
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

/// Algorithm 2 through the public API; `sk` must have exactly `sk_len` bytes.
pub fn ours_sign(set: Set, sk: &[u8], m: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Option<Vec<u8>> {
    match set {
        Set::S44 => api::sign_44(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
        Set::S65 => api::sign_65(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
        Set::S87 => api::sign_87(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
    }
}

/// Algorithm 7 through the public API; `sk` must have exactly `sk_len` bytes.
pub fn ours_sign_internal(set: Set, sk: &[u8], mp: &[u8], rnd: &[u8; 32]) -> Option<Vec<u8>> {
    match set {
        Set::S44 => api::sign_internal_44(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
        Set::S65 => api::sign_internal_65(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
        Set::S87 => api::sign_internal_87(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
    }
}

/// Algorithm 7 with an explicit prefix/message split (the API always passes an empty prefix or 0 ‖ |ctx| ‖ ctx).
pub fn ours_sign_split(set: Set, sk: &[u8], prefix: &[u8], m: &[u8], rnd: &[u8; 32]) -> Option<Vec<u8>> {
    let mut sig = vec![0u8; set.sig_len()];
    let ok = match set {
        Set::S44 => sign_internal::<4, 4>(&ML_DSA_44, sk, prefix, m, rnd, &mut sig),
        Set::S65 => sign_internal::<6, 5>(&ML_DSA_65, sk, prefix, m, rnd, &mut sig),
        Set::S87 => sign_internal::<8, 7>(&ML_DSA_87, sk, prefix, m, rnd, &mut sig),
    };
    ok.then_some(sig)
}

// ---------------------------------------------------------------------------------------------
// Upstream oracle
// ---------------------------------------------------------------------------------------------

/// Upstream verdicts for one (pk, sig, M′ or (m, ctx)) tuple: Verify_internal on `mp` and Verify on (m, ctx).
/// A pk or sig of the wrong length, or a sig that upstream's decoder rejects, is `false` for both.
fn up_verify_both_p<P: MlDsaParams>(pk: &[u8], sig: &[u8], mp: &[u8], m: &[u8], ctx: &[u8]) -> (bool, bool) {
    let Ok(enc) = EncodedVerifyingKey::<P>::try_from(pk) else { return (false, false) };
    let vk = VerifyingKey::<P>::decode(&enc);
    let Ok(s) = Signature::<P>::try_from(sig) else { return (false, false) };
    (vk.verify_internal(mp, &s), vk.verify_with_context(m, ctx, &s))
}

pub fn up_verify_both(set: Set, pk: &[u8], sig: &[u8], mp: &[u8], m: &[u8], ctx: &[u8]) -> (bool, bool) {
    match set {
        Set::S44 => up_verify_both_p::<MlDsa44>(pk, sig, mp, m, ctx),
        Set::S65 => up_verify_both_p::<MlDsa65>(pk, sig, mp, m, ctx),
        Set::S87 => up_verify_both_p::<MlDsa87>(pk, sig, mp, m, ctx),
    }
}

/// Upstream signing results for one key. `internal` is Sign_internal on M′ (panics inside upstream are caught and
/// reported as `None`, which upstream documents for rejection-sampling exhaustion); `det` is
/// `sign_deterministic(m, ctx)` (rnd = 0), `None` on error.
pub struct UpSign {
    pub internal: Option<Vec<u8>>,
    pub det: Option<Option<Vec<u8>>>,
}

thread_local! {
    /// While set, a panic is expected from upstream code under `catch_unwind`: the panic hook stays quiet.
    static IN_UPSTREAM: Cell<bool> = const { Cell::new(false) };
}

/// Installs a panic hook that prints and aborts (so libFuzzer records a crash), except while `IN_UPSTREAM` is set.
pub fn install_panic_hook() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if IN_UPSTREAM.with(|f| f.get()) {
            return;
        }
        prev(info);
        std::process::abort();
    }));
}

/// Runs `f` (upstream code that may panic on malformed input); a panic is returned as `Err(())`.
pub fn catch_upstream<R>(f: impl FnOnce() -> R) -> Result<R, ()> {
    let was = IN_UPSTREAM.with(|c| c.replace(true));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    IN_UPSTREAM.with(|c| c.set(was));
    r.map_err(|_| ())
}

fn up_sign_p<P: MlDsaParams>(
    sk: &[u8],
    mp: &[u8],
    rnd: &[u8; 32],
    det_args: Option<(&[u8], &[u8])>,
) -> Result<UpSign, ()> {
    let enc = ExpandedSigningKeyBytes::<P>::try_from(sk).map_err(|_| ())?;
    catch_upstream(|| {
        let esk = ExpandedSigningKey::<P>::from_expanded(&enc);
        let internal = catch_upstream(|| esk.sign_internal(&[mp], &ml_dsa::B32::from(*rnd)).encode().as_slice().to_vec())
            .ok();
        let det = det_args.map(|(m, ctx)| esk.sign_deterministic(m, ctx).ok().map(|s| s.encode().as_slice().to_vec()));
        UpSign { internal, det }
    })
}

/// `Err(())` means upstream panicked outside the rejection loop (while decoding the key).
pub fn up_sign(set: Set, sk: &[u8], mp: &[u8], rnd: &[u8; 32], det_args: Option<(&[u8], &[u8])>) -> Result<UpSign, ()> {
    match set {
        Set::S44 => up_sign_p::<MlDsa44>(sk, mp, rnd, det_args),
        Set::S65 => up_sign_p::<MlDsa65>(sk, mp, rnd, det_args),
        Set::S87 => up_sign_p::<MlDsa87>(sk, mp, rnd, det_args),
    }
}

/// Everything upstream produces from one seed: keygen output plus Sign_internal on each requested M′ and the optional
/// `sign_deterministic(m, ctx)`. One key derivation serves all of them.
pub struct UpAll {
    pub pk: Vec<u8>,
    pub sk: Vec<u8>,
    pub internals: Vec<Option<Vec<u8>>>,
    pub det: Option<Option<Vec<u8>>>,
}

fn up_all_p<P: MlDsaParams>(xi: &[u8; 32], mps: &[&[u8]], rnd: &[u8; 32], det_args: Option<(&[u8], &[u8])>) -> UpAll {
    let esk = ExpandedSigningKey::<P>::from_seed(&ml_dsa::B32::from(*xi));
    let internals = mps
        .iter()
        .map(|mp| catch_upstream(|| esk.sign_internal(&[mp], &ml_dsa::B32::from(*rnd)).encode().as_slice().to_vec()).ok())
        .collect();
    let det = det_args.map(|(m, ctx)| esk.sign_deterministic(m, ctx).ok().map(|s| s.encode().as_slice().to_vec()));
    UpAll {
        pk: esk.verifying_key().encode().as_slice().to_vec(),
        sk: esk.to_expanded().as_slice().to_vec(),
        internals,
        det,
    }
}

pub fn up_all(set: Set, xi: &[u8; 32], mps: &[&[u8]], rnd: &[u8; 32], det_args: Option<(&[u8], &[u8])>) -> UpAll {
    match set {
        Set::S44 => up_all_p::<MlDsa44>(xi, mps, rnd, det_args),
        Set::S65 => up_all_p::<MlDsa65>(xi, mps, rnd, det_args),
        Set::S87 => up_all_p::<MlDsa87>(xi, mps, rnd, det_args),
    }
}

// ---------------------------------------------------------------------------------------------
// M′ construction
// ---------------------------------------------------------------------------------------------

/// 0 ‖ |ctx| ‖ ctx (Algorithm 2 step 10), for |ctx| ≤ 255.
pub fn ctx_prefix(ctx: &[u8]) -> Vec<u8> {
    assert!(ctx.len() <= 255);
    let mut v = vec![0u8, ctx.len() as u8];
    v.extend_from_slice(ctx);
    v
}

/// A deterministic filler of `n` bytes, for the ctx lengths the fuzz inputs select by name (0, 255, 256).
pub fn pattern(n: usize, salt: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(7).wrapping_add(salt)).collect()
}

// ---------------------------------------------------------------------------------------------
// Pool of valid (pk, msg, ctx, sig) bases, per parameter set
// ---------------------------------------------------------------------------------------------

pub struct Base {
    pub pk: Vec<u8>,
    pub msg: Vec<u8>,
    pub ctx: Vec<u8>,
    pub sig: Vec<u8>,
}

pub const POOL_SIZE: usize = 8;
const POOL_CTX_LEN: [usize; POOL_SIZE] = [0, 1, 255, 7, 0, 255, 32, 0];
const POOL_MSG_LEN: [usize; POOL_SIZE] = [0, 1, 33, 136, 300, 0, 5, 137];

/// The base pool: keys from fixed seeds, signed with our crate (hedged for odd entries). Entries are checked once
/// against upstream, so a broken pool cannot make the targets vacuous.
pub fn pool(set: Set) -> &'static [Base] {
    static P44: OnceLock<Vec<Base>> = OnceLock::new();
    static P65: OnceLock<Vec<Base>> = OnceLock::new();
    static P87: OnceLock<Vec<Base>> = OnceLock::new();
    let cell = match set {
        Set::S44 => &P44,
        Set::S65 => &P65,
        Set::S87 => &P87,
    };
    cell.get_or_init(|| {
        (0..POOL_SIZE)
            .map(|i| {
                let xi: [u8; 32] = std::array::from_fn(|j| (j as u8).wrapping_mul(31).wrapping_add(i as u8 * 17 + set.to_byte()));
                let (pk, sk) = ours_keygen(set, &xi);
                let msg = pattern(POOL_MSG_LEN[i], 3 * i as u8);
                let ctx = pattern(POOL_CTX_LEN[i], 5 * i as u8);
                let rnd: [u8; 32] = if i % 2 == 1 { std::array::from_fn(|j| (j + i) as u8) } else { [0; 32] };
                let sig = ours_sign(set, &sk, &msg, &ctx, &rnd).expect("pool: sign failed");
                let (_, ext) = up_verify_both(set, &pk, &sig, &[], &msg, &ctx);
                assert!(ext, "pool: upstream rejects our signature");
                assert!(ours_verify(set, &pk, &msg, &ctx, &sig), "pool: we reject our signature");
                Base { pk, msg, ctx, sig }
            })
            .collect()
    })
}

/// Region boundaries of a signature, for hint-aware edits.
pub struct SigLayout {
    pub c_tilde: usize,
    pub hint_start: usize,
    pub omega: usize,
    pub len: usize,
}

pub fn sig_layout(set: Set) -> SigLayout {
    let p = set.params();
    SigLayout { c_tilde: p.c_tilde_len, hint_start: sig_len(p) - p.omega - p.k, omega: p.omega, len: sig_len(p) }
}

/// Which byte range an edit region addresses, for a buffer of `len` bytes.
/// Regions 0–4 address the signature (c̃, z, hint positions, hint counts, anywhere); 5–6 the pk (ρ, t1).
pub fn region_range(set: Set, region: u8, len: usize) -> (usize, usize) {
    let l = sig_layout(set);
    let (lo, hi) = match region % 8 {
        0 => (0, l.c_tilde),
        1 => (l.c_tilde, l.hint_start),
        2 => (l.hint_start, l.hint_start + l.omega),
        3 => (l.hint_start + l.omega, l.len),
        4 => (0, l.len),
        5 => (0, 32),
        6 => (32, set.pk_len()),
        _ => (0, len),
    };
    let hi = hi.min(len);
    (lo.min(hi), hi)
}
