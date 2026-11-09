//! Differential tests of the 4-way verify (`api::verify_*`, `verifying_key_*` and the prepared verify run it) against the
//! scalar functions it is proved equal to.
//!
//! The reference is `verify::verify_internal`, the scalar function. Compared with it on every input, for ML-DSA-44/65/87:
//!   * `verify::verify_internal_x4`, the function `api::verify_*` run;
//!   * `verify::prepare_vk_x4` and `prepare_vk_into_x4` against `prepare_vk` (Â, NTT(t1 · 2^d) and tr);
//!   * the public API: `verify_NN`, `verify_internal_NN`, and the prepared-key paths `verifying_key_NN` +
//!     `verify_prepared_NN` / `verify_internal_prepared_NN`.
//! Inputs: the NIST ACVP sigVer vectors, the Wycheproof verify vectors, and deterministic pseudo-random keys and messages
//! with valid, corrupted (signature, message, context, key), wrong-length and random inputs.
//!
//! Nothing here depends on a CPU check: which instructions the 4-way code uses is decided when the crate is compiled. Run the
//! suite as it is for the baseline build and with `RUSTFLAGS="-C target-feature=+avx2"` for the AVX2 build (the machine must
//! have AVX2); set `ML_DSA_REQUIRE_AVX2=1` (scripts/ci.sh does for its avx2 step) to make a build without AVX2 target
//! features a failure, so that the step cannot pass while testing the baseline code.
#![cfg(not(miri))]
#![allow(clippy::type_complexity)]
use flate2::read::GzDecoder;
use ml_dsa_lean::api;
use ml_dsa_lean::params::{self, ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use ml_dsa_lean::verify;
use serde::Deserialize;
use std::io::Read;

struct XorShift(u64);
impl XorShift {
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

/// One parameter set behind slices.
struct Set {
    name: &'static str,
    p: Params,
    keygen: fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    sign: fn(&[u8], &[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>,
    sign_internal: fn(&[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>,
    /// api::verify_NN; the slices must have the exact lengths.
    verify: fn(&[u8], &[u8], &[u8], &[u8]) -> bool,
    verify_internal: fn(&[u8], &[u8], &[u8]) -> bool,
    /// api::verifying_key_NN then verify_prepared_NN / verify_internal_prepared_NN.
    prepared: fn(&[u8], &[u8], &[u8], &[u8]) -> bool,
    prepared_internal: fn(&[u8], &[u8], &[u8]) -> bool,
    /// verify::verify_internal (scalar) and verify::verify_internal_x4.
    scalar: fn(&Params, &[u8], &[u8], &[u8], &[u8]) -> bool,
    x4: fn(&Params, &[u8], &[u8], &[u8], &[u8]) -> bool,
    /// Do `prepare_vk_x4` and the in-place `prepare_vk_into_x4` equal the scalar `prepare_vk`?
    prepare_matches: fn(&[u8]) -> bool,
}

macro_rules! set_of {
    ($name:literal, $p:expr, $k:literal, $l:literal, $kg:ident, $s:ident, $si:ident, $v:ident, $vi:ident, $vk:ident, $vp:ident, $vip:ident) => {
        Set {
            name: $name,
            p: $p,
            keygen: |xi| {
                let (pk, sk) = api::$kg(xi);
                (pk.to_vec(), sk.to_vec())
            },
            sign: |sk, m, ctx, rnd| api::$s(sk.try_into().unwrap(), m, ctx, rnd).map(|s| s.to_vec()),
            sign_internal: |sk, mp, rnd| api::$si(sk.try_into().unwrap(), mp, rnd).map(|s| s.to_vec()),
            verify: |pk, m, ctx, sig| api::$v(pk.try_into().unwrap(), m, ctx, sig.try_into().unwrap()),
            verify_internal: |pk, mp, sig| api::$vi(pk.try_into().unwrap(), mp, sig.try_into().unwrap()),
            prepared: |pk, m, ctx, sig| {
                let vk = Box::new(api::$vk(pk.try_into().unwrap()));
                api::$vp(&vk, m, ctx, sig.try_into().unwrap())
            },
            prepared_internal: |pk, mp, sig| {
                let vk = Box::new(api::$vk(pk.try_into().unwrap()));
                api::$vip(&vk, mp, sig.try_into().unwrap())
            },
            scalar: |p, pk, prefix, m, sig| verify::verify_internal::<$k, $l>(p, pk, prefix, m, sig),
            x4: |p, pk, prefix, m, sig| verify::verify_internal_x4::<$k, $l>(p, pk, prefix, m, sig),
            prepare_matches: |pk| {
                let slow = verify::prepare_vk::<$k, $l>(pk);
                let fast = verify::prepare_vk_x4::<$k, $l>(pk);
                let mut in_place = verify::PreparedVk::<$k, $l>::zeroed();
                verify::prepare_vk_into_x4::<$k, $l>(pk, &mut in_place);
                fast.a_hat == slow.a_hat
                    && fast.t1_2d_hat == slow.t1_2d_hat
                    && fast.tr == slow.tr
                    && in_place.a_hat == slow.a_hat
                    && in_place.t1_2d_hat == slow.t1_2d_hat
                    && in_place.tr == slow.tr
            },
        }
    };
}

fn sets() -> [Set; 3] {
    [
        set_of!("ML-DSA-44", ML_DSA_44, 4, 4, keygen_44, sign_44, sign_internal_44, verify_44, verify_internal_44, verifying_key_44, verify_prepared_44, verify_internal_prepared_44),
        set_of!("ML-DSA-65", ML_DSA_65, 6, 5, keygen_65, sign_65, sign_internal_65, verify_65, verify_internal_65, verifying_key_65, verify_prepared_65, verify_internal_prepared_65),
        set_of!("ML-DSA-87", ML_DSA_87, 8, 7, keygen_87, sign_87, sign_internal_87, verify_87, verify_internal_87, verifying_key_87, verify_prepared_87, verify_internal_prepared_87),
    ]
}

/// The build under test: with `ML_DSA_REQUIRE_AVX2=1` it must have been compiled with AVX2 target features.
#[test]
fn build_has_avx2_when_required() {
    if std::env::var("ML_DSA_REQUIRE_AVX2").as_deref() == Ok("1") {
        assert!(
            cfg!(target_feature = "avx2"),
            "ML_DSA_REQUIRE_AVX2=1 but this build has no AVX2 target feature: set RUSTFLAGS=\"-C target-feature=+avx2\""
        );
    }
    eprintln!("4-way code compiled with AVX2 target features: {}", cfg!(target_feature = "avx2"));
}

/// Counts the checks, so the summary line is evidence and not a claim.
#[derive(Default)]
struct Stats {
    cases: usize,
    accepted: usize,
}

/// All verdicts for one (pk, M' = prefix ‖ m, sig); panics with context on any disagreement. Returns the verdict.
fn check_slices(s: &Set, st: &mut Stats, what: &str, pk: &[u8], prefix: &[u8], m: &[u8], sig: &[u8]) -> bool {
    let want = (s.scalar)(&s.p, pk, prefix, m, sig);
    let got = (s.x4)(&s.p, pk, prefix, m, sig);
    assert_eq!(got, want, "{} {what}: 4-way slice verify vs scalar", s.name);
    // The fixed-size public API, when the lengths allow it.
    let lens_ok = pk.len() == params::pk_len(&s.p) && sig.len() == params::sig_len(&s.p);
    if lens_ok {
        let mut mp = prefix.to_vec();
        mp.extend_from_slice(m);
        assert_eq!((s.verify_internal)(pk, &mp, sig), want, "{} {what}: verify_internal_NN", s.name);
        assert_eq!((s.prepared_internal)(pk, &mp, sig), want, "{} {what}: verify_internal_prepared_NN", s.name);
        // verify_NN / verify_prepared_NN take the context separately: prefix = 0 ‖ |ctx| ‖ ctx.
        if prefix.len() >= 2 && prefix[0] == 0 && prefix[1] as usize == prefix.len() - 2 {
            let ctx = &prefix[2..];
            assert_eq!((s.verify)(pk, m, ctx, sig), want, "{} {what}: verify_NN", s.name);
            assert_eq!((s.prepared)(pk, m, ctx, sig), want, "{} {what}: verify_prepared_NN", s.name);
        }
    }
    st.cases += 1;
    st.accepted += want as usize;
    want
}

fn ext_prefix(ctx: &[u8]) -> Vec<u8> {
    let mut v = vec![0u8, ctx.len() as u8];
    v.extend_from_slice(ctx);
    v
}

fn flip(v: &mut [u8], r: &mut XorShift) {
    let i = r.below(v.len());
    v[i] ^= 1 << r.below(8);
}

fn run_random(s: &Set, seed: u64, keys: usize) -> Stats {
    let mut r = XorShift(seed);
    let mut st = Stats::default();
    let (c_len, sig_len, pk_len) = (s.p.c_tilde_len, params::sig_len(&s.p), params::pk_len(&s.p));
    for key in 0..keys {
        let xi: [u8; 32] = r.bytes(32).try_into().unwrap();
        let (pk, sk) = (s.keygen)(&xi);
        assert!((s.prepare_matches)(&pk), "{}: prepare_vk 4-way vs scalar", s.name);
        // 1-2 messages per key, one of them with a non-empty context.
        for msg_no in 0..2 {
            let m_len = if msg_no == 0 { r.below(40) } else { 200 + r.below(300) };
            let m = r.bytes(m_len);
            let ctx_len = if msg_no == 0 { 0 } else { 1 + r.below(255) };
            let ctx = r.bytes(ctx_len);
            let rnd: [u8; 32] = if r.below(2) == 0 { [0; 32] } else { r.bytes(32).try_into().unwrap() };
            let sig = (s.sign)(&sk, &m, &ctx, &rnd).expect("sign");
            assert_eq!(sig.len(), sig_len);
            let prefix = ext_prefix(&ctx);
            let what = |x: &str| format!("key {key} msg {msg_no} {x}");

            // Valid.
            assert!(check_slices(s, &mut st, &what("valid"), &pk, &prefix, &m, &sig), "{}: valid signature rejected", s.name);
            // Also through the internal interface (M' supplied by the caller, no prefix).
            let rnd0 = [7u8; 32];
            let isig = (s.sign_internal)(&sk, &m, &rnd0).expect("sign_internal");
            assert!(check_slices(s, &mut st, &what("valid internal"), &pk, &[], &m, &isig));

            // Corrupted signature: random bits in c̃, in z, in the hint area, and the fixed ends.
            for region in 0..4 {
                for _ in 0..6 {
                    let mut bad = sig.clone();
                    let (lo, hi) = match region {
                        0 => (0, c_len),
                        1 => (c_len, sig_len - s.p.k - s.p.omega),
                        2 => (sig_len - s.p.k - s.p.omega, sig_len),
                        _ => (0, sig_len),
                    };
                    let i = lo + r.below(hi - lo);
                    bad[i] ^= 1 << r.below(8);
                    check_slices(s, &mut st, &what(&format!("sig byte {i}")), &pk, &prefix, &m, &bad);
                }
            }
            for i in [0, c_len - 1, c_len, sig_len - 1, sig_len - s.p.k, sig_len - s.p.k - 1] {
                let mut bad = sig.clone();
                bad[i] ^= 0x80;
                assert!(!check_slices(s, &mut st, &what(&format!("sig fixed byte {i}")), &pk, &prefix, &m, &bad));
            }
            // Corrupted message / context.
            let mut bm = m.clone();
            if bm.is_empty() {
                bm.push(0);
            } else {
                flip(&mut bm, &mut r);
            }
            assert!(!check_slices(s, &mut st, &what("message"), &pk, &prefix, &bm, &sig));
            let mut longer = m.clone();
            longer.push(0);
            assert!(!check_slices(s, &mut st, &what("message+1"), &pk, &prefix, &longer, &sig));
            let mut bp = prefix.clone();
            bp[0] = 1;
            assert!(!check_slices(s, &mut st, &what("prefix domain byte"), &pk, &bp, &m, &sig));
            let other_len = r.below(10);
            let other = ext_prefix(&r.bytes(other_len));
            if other != prefix {
                assert!(!check_slices(s, &mut st, &what("other context"), &pk, &other, &m, &sig));
            }
            // Corrupted key: in ρ, in t1.
            for lo_hi in [(0, 32), (32, pk_len), (0, pk_len)] {
                let mut bad = pk.clone();
                let i = lo_hi.0 + r.below(lo_hi.1 - lo_hi.0);
                bad[i] ^= 1 << r.below(8);
                assert!(!check_slices(s, &mut st, &what(&format!("pk byte {i}")), &bad, &prefix, &m, &sig));
            }
            // Wrong lengths (slice API only).
            let mut longer_sig = sig.clone();
            longer_sig.push(0);
            assert!(!check_slices(s, &mut st, &what("sig+1"), &pk, &prefix, &m, &longer_sig));
            assert!(!check_slices(s, &mut st, &what("sig-1"), &pk, &prefix, &m, &sig[..sig_len - 1]));
            assert!(!check_slices(s, &mut st, &what("sig empty"), &pk, &prefix, &m, &[]));
            assert!(!check_slices(s, &mut st, &what("pk-1"), &pk[..pk_len - 1], &prefix, &m, &sig));
            let mut longer_pk = pk.clone();
            longer_pk.push(0);
            assert!(!check_slices(s, &mut st, &what("pk+1"), &longer_pk, &prefix, &m, &sig));
            assert!(!check_slices(s, &mut st, &what("pk empty"), &[], &prefix, &m, &sig));
            // A valid signature with another key.
            let (pk2, _) = (s.keygen)(&r.bytes(32).try_into().unwrap());
            assert!(!check_slices(s, &mut st, &what("other key"), &pk2, &prefix, &m, &sig));
        }
        // Fully random and structured signatures against this key (almost always rejected in sig_decode or by the hash).
        let rs = r.bytes(sig_len);
        check_slices(s, &mut st, "random sig", &pk, &[], b"msg", &rs);
        check_slices(s, &mut st, "zero sig", &pk, &[], b"msg", &vec![0u8; sig_len]);
        check_slices(s, &mut st, "ones sig", &pk, &[], b"msg", &vec![0xffu8; sig_len]);
    }
    st
}

#[test]
fn random_keys_and_messages_agree_with_scalar() {
    for (i, s) in sets().iter().enumerate() {
        let st = run_random(s, 0x4641_5354_5645_0000 + i as u64, if cfg!(debug_assertions) { 2 } else { 6 });
        eprintln!(
            "{}: {} random cases ({} accepted); 4-way compared on every one; 0 disagreements",
            s.name, st.cases, st.accepted
        );
        assert!(st.accepted > 0 && st.accepted < st.cases);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// ACVP sigVer and Wycheproof verify vectors through all paths
// ---------------------------------------------------------------------------------------------------------------

fn unhex(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd hex length");
    let v = |c: u8| match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => panic!("bad hex digit"),
    };
    s.as_bytes().chunks(2).map(|c| v(c[0]) << 4 | v(c[1])).collect()
}

fn read_gz(path: &str) -> String {
    let path = format!("{}/tests/data/{path}", env!("CARGO_MANIFEST_DIR"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut json = String::new();
    GzDecoder::new(&bytes[..]).read_to_string(&mut json).unwrap();
    json
}

fn set_by_name(name: &str) -> Set {
    sets().into_iter().find(|s| s.name == name).unwrap_or_else(|| panic!("unknown set {name}"))
}

#[derive(Deserialize)]
struct AcvpFile {
    #[serde(rename = "testGroups")]
    groups: Vec<AcvpGroup>,
}
#[derive(Deserialize)]
struct AcvpGroup {
    #[serde(rename = "parameterSet")]
    parameter_set: String,
    #[serde(rename = "signatureInterface")]
    interface: String,
    #[serde(rename = "preHash", default)]
    pre_hash: Option<String>,
    #[serde(rename = "externalMu", default)]
    external_mu: bool,
    tests: Vec<AcvpCase>,
}
#[derive(Deserialize)]
struct AcvpCase {
    pk: String,
    #[serde(default)]
    message: Option<String>,
    #[serde(default)]
    context: Option<String>,
    signature: String,
    #[serde(rename = "testPassed")]
    test_passed: bool,
}

#[test]
fn acvp_sigver_through_every_path() {
    let file: AcvpFile = serde_json::from_str(&read_gz("acvp/sigVer.json.gz")).unwrap();
    let mut st = Stats::default();
    let mut skipped = 0;
    for g in &file.groups {
        if g.pre_hash.as_deref() == Some("preHash") || g.external_mu {
            skipped += g.tests.len();
            continue;
        }
        let s = set_by_name(&g.parameter_set);
        for c in &g.tests {
            let (pk, sig) = (unhex(&c.pk), unhex(&c.signature));
            let msg = unhex(c.message.as_deref().unwrap());
            let prefix = if g.interface == "internal" { Vec::new() } else { ext_prefix(&unhex(c.context.as_deref().unwrap())) };
            let got = check_slices(&s, &mut st, &format!("ACVP {}", g.parameter_set), &pk, &prefix, &msg, &sig);
            assert_eq!(got, c.test_passed, "ACVP {} expected testPassed={}", g.parameter_set, c.test_passed);
        }
    }
    eprintln!("ACVP sigVer: {} cases through scalar, 4-way, verify_*, prepared ({} skipped: preHash / external mu)", st.cases, skipped);
    // The other 30 of the 60 vectors are preHash / external mu (not implemented); the 12 valid signatures are spread over both halves.
    assert!(st.cases == 30 && st.accepted > 0);
}

#[derive(Deserialize)]
struct WFile {
    #[serde(rename = "testGroups")]
    groups: Vec<WGroup>,
}
#[derive(Deserialize)]
struct WGroup {
    #[serde(rename = "publicKey")]
    public_key: String,
    tests: Vec<WCase>,
}
#[derive(Deserialize)]
struct WCase {
    #[serde(default)]
    msg: Option<String>,
    #[serde(default)]
    ctx: Option<String>,
    sig: String,
    result: String,
}

#[test]
fn wycheproof_verify_through_every_path() {
    let mut st = Stats::default();
    let mut per_set = Vec::new();
    for (num, name) in [("44", "ML-DSA-44"), ("65", "ML-DSA-65"), ("87", "ML-DSA-87")] {
        let s = set_by_name(name);
        let before = st.cases;
        let file: WFile = serde_json::from_str(&read_gz(&format!("wycheproof/mldsa_{num}_verify_test.json.gz"))).unwrap();
        for g in &file.groups {
            let pk = unhex(&g.public_key);
            for c in &g.tests {
                let msg = unhex(c.msg.as_deref().unwrap_or(""));
                let ctx = unhex(c.ctx.as_deref().unwrap_or(""));
                let sig = unhex(&c.sig);
                let want = match c.result.as_str() {
                    "valid" => true,
                    "invalid" => false,
                    other => panic!("unexpected result {other}"),
                };
                // Contexts longer than 255 bytes cannot form M' (the external interface rejects them): not a verify input.
                if ctx.len() > 255 {
                    assert!(!want);
                    continue;
                }
                let got = check_slices(&s, &mut st, &format!("Wycheproof {name}"), &pk, &ext_prefix(&ctx), &msg, &sig);
                assert_eq!(got, want, "Wycheproof {name}: expected {}", c.result);
            }
        }
        per_set.push(format!("{name}: {}", st.cases - before));
    }
    eprintln!("Wycheproof verify: {} cases ({}) through every path", st.cases, per_set.join(", "));
    assert!(st.cases > 300);
}
