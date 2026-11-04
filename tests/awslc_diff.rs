//! Differential test against aws-lc-rs 1.18.2, the library nearcore's ML-DSA-65 support runs on.
//!
//! nearcore calls (core/crypto/src/signature.rs, nearcore cd5a94457):
//!   verify:  `UnparsedPublicKey::new(&ML_DSA_65, &pk[..1952]).verify(msg, &sig[..3309]).is_ok()`
//!   keygen:  `PqdsaKeyPair::generate(&ML_DSA_65_SIGNING)`, `PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, &seed[..32])`
//!   sign:    `PqdsaKeyPair::from_raw_private_key(&ML_DSA_65_SIGNING, &sk[..4032])` then `kp.sign(msg, &mut sig)`
//! The aws-lc-rs API has no context parameter: it verifies and signs the pure interface with an empty context, i.e.
//! M′ = 0x00 ‖ 0x00 ‖ M. So the ctx lengths 0, 255, 256 of the task cannot be driven through this API; only ctx = "" is
//! compared (ours is called with an empty ctx, `verify_internal(.., prefix = [0, 0], ..)`).
//!
//! Everything is run for ML-DSA-44, -65 and -87 (aws-lc-rs 1.18.2 exposes all three; nearcore uses 65). The verdict of
//! `ml_dsa_lean::verify::verify_internal` (slice version: a wrong-length pk or σ is rejected) and of aws-lc-rs must be
//! equal on every case. Where FIPS 204 fixes the verdict (malformed hint encodings, z outside the bound, wrong lengths,
//! a valid signature) it is also asserted against ours.
//!
//! Our verify also goes through the public API, which is what nearcore would call: whenever pk and σ have the exact
//! lengths, `api::verify_NN(pk, m, &[], sig)` and `api::verifying_key_NN` + `api::verify_prepared_NN(&vk, m, &[], sig)`
//! must both return the slice verdict and the aws-lc verdict. These API comparisons are counted and printed separately
//! from the slice-verdict comparisons (the prepared key is reused while consecutive cases share a pk).
//!
//! Run time. Release (`cargo test --release --test awslc_diff -- --nocapture`) runs the full counts: about 160 s of test
//! time before the API comparisons were added, 340-370 s with them (measured on a shared box at load 30-100). A debug
//! build (plain `cargo test`) runs only a smoke subset (counts divided by about 100, strided sweeps, every category still
//! exercised at least once): 35 s of test time. Set `AWSLC_DIFF_FULL=1` to force the full counts in a debug build too
//! (very slow: a tenth of the counts took 13 minutes there; not meant for routine use).
//!
//! Failures. On any disagreement the failing inputs (pk, m, σ in hex) are written to `target/awslc-diff-dump/caseN.txt`
//! (override the directory with `AWSLC_DIFF_DUMP=<dir>`); the log names the file and never carries the full inputs.
//! The per-category RNG seeds are fixed, but aws-lc signing and `PqdsaKeyPair::generate` are randomized, so the cases
//! they produce (`valid`, `keygen`) differ between runs and a failure there may not reproduce: keep the dump.
//!
//! Sets of cases (counts are printed per run; the smoke run divides the bulk counts by `scale()`):
//! - `valid`: ours signs -> aws-lc verifies; aws-lc signs -> ours verifies; wrong message / wrong key.
//! - `keygen`: KeyGen from ξ against `PqdsaKeyPair::from_seed` (pk and expanded sk bytes), import of ours sk, aws-lc
//!   `generate` keys exported and re-derived by ours, and an informational sk-import matrix on mutated secret keys.
//! - `flips`: every single-bit flip of σ, pk and M (several keys), and random multi-bit / splice / fill mutations.
//! - `lengths`: σ and pk truncated to every length and extended.
//! - `hint`: hint-encoding edge cases (non-increasing or repeated indices, nonzero padding, counts above ω or decreasing,
//!   all 256 values at every position of the hint region, random regions), on valid signatures.
//! - `ctilde`: single-bit and multi-bit mutations of c̃.
//! - `zbound`: signatures forged with a signer that skips the ‖z‖∞ check and pins one z coefficient at and beyond
//!   ±(γ1 − β), so that c̃ matches and the norm check is the only thing that decides; and signatures with exactly ω hints.
//! - `edgekeys`: keys with t1 at its extremes (s1 = 0), ρ patterns including one that is a DER SPKI header (aws-lc-rs tries
//!   an SPKI parse of the public key bytes before the raw one), valid signatures and mutations under them.
//! - `wycheproof`: the vendored Wycheproof vectors through aws-lc-rs.
//!
#![allow(clippy::type_complexity, clippy::needless_range_loop)]
use aws_lc_rs::encoding::AsRawBytes;
use aws_lc_rs::signature::{self as aws, KeyPair, PqdsaKeyPair, PqdsaSigningAlgorithm, PqdsaVerificationAlgorithm, UnparsedPublicKey};
use flate2::read::GzDecoder;
use ml_dsa_lean::api;
use ml_dsa_lean::encode::{pk_encode, sig_decode, sig_encode, sk_decode, sk_encode, w1_encode};
use ml_dsa_lean::field::{add, neg};
use ml_dsa_lean::keccak::Shake;
use ml_dsa_lean::keygen::pk_from_sk;
use ml_dsa_lean::ntt::{add_poly, matrix_vector_ntt, ntt, ntt_inverse, ntt_vec, scalar_vector_ntt_inverse, sub_poly};
use ml_dsa_lean::params::{self as prm, Params};
use ml_dsa_lean::rounding::{make_hint, poly_high_bits, poly_low_bits, poly_power2round, vec_infinity_norm};
use ml_dsa_lean::sampling::{expand_a, sample_in_ball};
use ml_dsa_lean::verify::verify_internal;
use serde::Deserialize;
use std::collections::BTreeMap;
use std::io::Read;

/// Bulk-case divisor: 1 in release (and with `AWSLC_DIFF_FULL=1`), 100 in a debug build, where the full run costs
/// about 13 minutes. Every count goes through `sc`, which keeps at least one case.
fn scale() -> usize {
    static S: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *S.get_or_init(|| if cfg!(debug_assertions) && std::env::var_os("AWSLC_DIFF_FULL").is_none_or(|v| v != "1") { 100 } else { 1 })
}

/// `n / scale()`, at least 1.
fn sc(n: usize) -> usize {
    (n / scale()).max(1)
}

/// `n / min(scale(), cap)`: a count that shrinks in the smoke run but never below `n / cap`.
fn sc_cap(n: usize, cap: usize) -> usize {
    (n / scale().min(cap)).max(1)
}
const Q: i64 = 8_380_417;

// ---------------------------------------------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
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

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    let v = |c: u8| match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => panic!("bad hex digit"),
    };
    s.as_bytes().chunks(2).map(|c| v(c[0]) << 4 | v(c[1])).collect()
}

fn q_mod(x: i64) -> u32 {
    x.rem_euclid(Q) as u32
}

fn shake256(parts: &[&[u8]], out: &mut [u8]) {
    let mut h = Shake::shake256();
    for p in parts {
        h.absorb(p);
    }
    h.finalize();
    h.squeeze(out);
}

/// What nearcore does: `UnparsedPublicKey::new(&ML_DSA_xx, pk).verify(msg, sig).is_ok()`.
fn aws_verify(alg: &'static PqdsaVerificationAlgorithm, pk: &[u8], m: &[u8], sig: &[u8]) -> bool {
    UnparsedPublicKey::new(alg, pk).verify(m, sig).is_ok()
}

// ---------------------------------------------------------------------------------------------------------------
// One parameter set behind function pointers
// ---------------------------------------------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum Mode {
    Zero,
    Rand,
    Max,
    Min,
}

struct KeySpec {
    rho: [u8; 32],
    key: [u8; 32],
    s1: Mode,
    s2: Mode,
}

struct Forged {
    sig: Vec<u8>,
    znorm: u32,
    ones: usize,
}

/// Last pk and its prepared `api::VerifyingKeyNN`.
type VkCache = Option<(Vec<u8>, Box<dyn std::any::Any + Send>)>;

struct Set {
    name: &'static str,
    p: Params,
    oid_last: u8,
    aws_v: &'static PqdsaVerificationAlgorithm,
    aws_s: &'static PqdsaSigningAlgorithm,
    keygen: fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    /// sign_NN(sk, m, ctx = "", rnd)
    sign: fn(&[u8], &[u8], &[u8; 32]) -> Vec<u8>,
    /// verify_internal with the pure-interface prefix 0 ‖ 0 (empty ctx); wrong lengths are rejected.
    ours_verify: fn(&Params, &[u8], &[u8], &[u8]) -> bool,
    /// The public API with ctx = "": (`verify_NN`, `verifying_key_NN` + `verify_prepared_NN`); None unless pk and σ have
    /// exactly the right lengths. The cache holds the prepared key of the last pk.
    ours_verify_api: fn(&[u8], &[u8], &[u8], &mut VkCache) -> Option<(bool, bool)>,
    pk_from_sk: fn(&Params, &[u8]) -> Option<Vec<u8>>,
    sk_well_formed: fn(&[u8]) -> bool,
    rekey: fn(&Params, &KeySpec, &mut Rng) -> (Vec<u8>, Vec<u8>),
    forge: fn(&Params, &[u8], &[u8], Option<i64>, Option<usize>, &mut Rng) -> Option<Forged>,
    hint_off: usize,
}

macro_rules! make_set {
    ($name:literal, $oid:literal, $k:literal, $l:literal, $p:expr, $av:expr, $as:expr, $kg:ident, $sg:ident, $wf:ident, $vf:ident, $vkf:ident, $vpf:ident, $vkt:ident) => {
        Set {
            name: $name,
            p: $p,
            oid_last: $oid,
            aws_v: &$av,
            aws_s: &$as,
            keygen: |xi| {
                let (pk, sk) = api::$kg(xi);
                (pk.to_vec(), sk.to_vec())
            },
            sign: |sk, m, rnd| api::$sg(sk.try_into().unwrap(), m, &[], rnd).expect("kappa budget").to_vec(),
            ours_verify: |p, pk, m, sig| verify_internal::<$k, $l>(p, pk, &[0, 0], m, sig),
            ours_verify_api: |pk_s, m, sig, cache| {
                let pk = pk_s.try_into().ok()?;
                let sig = sig.try_into().ok()?;
                let direct = api::$vf(pk, m, &[], sig);
                if cache.as_ref().is_none_or(|(k, _)| k[..] != *pk_s) {
                    *cache = Some((pk_s.to_vec(), Box::new(api::$vkf(pk))));
                }
                let vk = cache.as_ref().unwrap().1.downcast_ref::<api::$vkt>().unwrap();
                Some((direct, api::$vpf(vk, m, &[], sig)))
            },
            pk_from_sk: |p, sk| {
                let mut pk = vec![0u8; prm::pk_len(p)];
                pk_from_sk::<$k, $l>(p, sk, &mut pk).then_some(pk)
            },
            sk_well_formed: |sk| api::$wf(sk.try_into().unwrap()),
            rekey: rekey_g::<$k, $l>,
            forge: forge_g::<$k, $l>,
            hint_off: $p.c_tilde_len + $l * 32 * $p.gamma1_bits,
        }
    };
}

fn set(idx: usize) -> Set {
    match idx {
        0 => make_set!("ML-DSA-44", 0x11, 4, 4, prm::ML_DSA_44, aws::ML_DSA_44, aws::ML_DSA_44_SIGNING, keygen_44, sign_44, sk_is_well_formed_44, verify_44, verifying_key_44, verify_prepared_44, VerifyingKey44),
        1 => make_set!("ML-DSA-65", 0x12, 6, 5, prm::ML_DSA_65, aws::ML_DSA_65, aws::ML_DSA_65_SIGNING, keygen_65, sign_65, sk_is_well_formed_65, verify_65, verifying_key_65, verify_prepared_65, VerifyingKey65),
        2 => make_set!("ML-DSA-87", 0x13, 8, 7, prm::ML_DSA_87, aws::ML_DSA_87, aws::ML_DSA_87_SIGNING, keygen_87, sign_87, sk_is_well_formed_87, verify_87, verifying_key_87, verify_prepared_87, VerifyingKey87),
        _ => unreachable!(),
    }
}

impl Set {
    fn pk_len(&self) -> usize {
        prm::pk_len(&self.p)
    }
    fn sig_len(&self) -> usize {
        prm::sig_len(&self.p)
    }
    fn aws_from_seed(&self, xi: &[u8; 32]) -> PqdsaKeyPair {
        PqdsaKeyPair::from_seed(self.aws_s, xi).expect("aws from_seed")
    }
    fn aws_sign(&self, kp: &PqdsaKeyPair, m: &[u8]) -> Vec<u8> {
        let mut buf = vec![0u8; self.aws_s.signature_len()];
        let n = kp.sign(m, &mut buf).expect("aws sign");
        buf.truncate(n);
        buf
    }
    /// Fresh key (ξ, pk, sk) from ours.
    fn key(&self, rng: &mut Rng) -> (Vec<u8>, Vec<u8>) {
        (self.keygen)(&rng.arr32())
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Tally
// ---------------------------------------------------------------------------------------------------------------

/// Writes (pk, m, sig) of a failing case to `target/awslc-diff-dump/case<n>.txt` (or `$AWSLC_DIFF_DUMP/case<n>.txt`);
/// returns where, or a note. The log itself never carries the full inputs.
fn dump_inputs(s: &Set, cat: &str, pk: &[u8], m: &[u8], sig: &[u8]) -> String {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::var_os("AWSLC_DIFF_DUMP")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/awslc-diff-dump"));
    if let Err(e) = std::fs::create_dir_all(&dir) {
        return format!("dump failed: {e}");
    }
    let path = dir.join(format!("case{}.txt", N.fetch_add(1, Ordering::Relaxed)));
    let body = format!("{} {cat}\npk={}\nm={}\nsig={}\n", s.name, hex(pk), hex(m), hex(sig));
    match std::fs::write(&path, body) {
        Ok(()) => path.display().to_string(),
        Err(e) => format!("dump failed: {e}"),
    }
}

#[derive(Default)]
struct Row {
    n: u64,
    acc: u64,
    rej: u64,
    dis: u64,
    spec_bad: u64,
}

#[derive(Default)]
struct Tally {
    rows: BTreeMap<&'static str, Row>,
    /// informational (not asserted): label -> (n, ours accepts, aws accepts)
    info: BTreeMap<&'static str, (u64, u64, u64)>,
    notes: Vec<String>,
    lines: Vec<String>,
    /// public-API comparisons: cases run (each calls `verify_NN` and `verify_prepared_NN`) and cases where either
    /// verdict differs from the slice verdict or from aws-lc
    api_n: u64,
    api_dis: u64,
    vk_cache: VkCache,
}

impl Tally {
    /// Runs both verifiers, records agreement, and (if given) the verdict FIPS 204 requires. Returns ours.
    fn check(&mut self, s: &Set, cat: &'static str, pk: &[u8], m: &[u8], sig: &[u8], expect: Option<bool>) -> bool {
        let ours = (s.ours_verify)(&s.p, pk, m, sig);
        let theirs = aws_verify(s.aws_v, pk, m, sig);
        if let Some((direct, prepared)) = (s.ours_verify_api)(pk, m, sig, &mut self.vk_cache) {
            self.api_n += 1;
            if direct != ours || prepared != ours || direct != theirs || prepared != theirs {
                self.api_dis += 1;
                if self.notes.len() < 6 {
                    self.notes.push(format!(
                        "API-DISAGREE [{}] {cat}: slice={ours} verify_NN={direct} verify_prepared_NN={prepared} aws={theirs} (full inputs: {})",
                        s.name,
                        dump_inputs(s, cat, pk, m, sig)
                    ));
                }
            }
        }
        let r = self.rows.entry(cat).or_default();
        r.n += 1;
        if ours == theirs {
            if ours {
                r.acc += 1
            } else {
                r.rej += 1
            }
        } else {
            r.dis += 1;
            if self.notes.len() < 6 {
                self.notes.push(format!(
                    "DISAGREE [{}] {cat}: ours={ours} aws={theirs} |pk|={} |m|={} |sig|={} (full inputs: {})",
                    s.name,
                    pk.len(),
                    m.len(),
                    sig.len(),
                    dump_inputs(s, cat, pk, m, sig)
                ));
            }
        }
        if let Some(e) = expect
            && ours != e
        {
            r.spec_bad += 1;
            if self.notes.len() < 6 {
                self.notes.push(format!(
                    "SPEC [{}] {cat}: ours={ours} but FIPS 204 requires {e}; |sig|={} (full inputs: {})",
                    s.name,
                    sig.len(),
                    dump_inputs(s, cat, pk, m, sig)
                ));
            }
        }
        ours
    }

    fn info(&mut self, cat: &'static str, ours: bool, theirs: bool) {
        let e = self.info.entry(cat).or_default();
        e.0 += 1;
        e.1 += ours as u64;
        e.2 += theirs as u64;
    }

    fn line(&mut self, l: String) {
        self.lines.push(l);
    }

    fn total(&self) -> u64 {
        self.rows.values().map(|r| r.n).sum()
    }

    fn bad(&self) -> u64 {
        self.rows.values().map(|r| r.dis + r.spec_bad).sum::<u64>() + self.api_dis
    }

    fn report(&self, set: &str, set_name: &str) {
        println!("== {set_name} / {set}: {} verify comparisons; API comparisons (verify_NN and verify_prepared_NN against slice and aws-lc): {}, API disagreements {}", self.total(), self.api_n, self.api_dis);
        for (cat, r) in &self.rows {
            println!(
                "   {cat:<44} n={:>8} both-accept={:>7} both-reject={:>8} DISAGREE={} SPEC-MISMATCH={}",
                r.n, r.acc, r.rej, r.dis, r.spec_bad
            );
        }
        for (cat, (n, o, a)) in &self.info {
            println!("   (info) {cat:<38} n={n:>8} ours-accepts={o:>7} aws-accepts={a:>7}");
        }
        for l in &self.lines {
            println!("   {l}");
        }
        for n in &self.notes {
            println!("   {n}");
        }
    }
}

/// Runs `f` for the three parameter sets in parallel threads and checks the tallies are clean.
fn run_sets(what: &'static str, f: fn(&Set, &mut Rng) -> Tally) {
    let tallies: Vec<(usize, Tally)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..3)
            .map(|i| {
                sc.spawn(move || {
                    let s = set(i);
                    let h = what.bytes().fold(0xcbf2_9ce4_8422_2325u64, |h, b| (h ^ b as u64).wrapping_mul(0x100_0000_01b3));
                    let mut rng = Rng::new(h ^ ((i as u64) << 56));
                    (i, f(&s, &mut rng))
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut bad = 0;
    for (i, t) in &tallies {
        t.report(what, set(*i).name);
        bad += t.bad();
    }
    let total: u64 = tallies.iter().map(|(_, t)| t.total()).sum();
    let (api_n, api_dis): (u64, u64) = tallies.iter().fold((0, 0), |a, (_, t)| (a.0 + t.api_n, a.1 + t.api_dis));
    println!("== {what}: {total} verify comparisons in total, {api_n} API comparisons ({api_dis} disagreements), {bad} disagreements or spec mismatches in total");
    assert_eq!(bad, 0, "{what}: disagreements or spec mismatches (details in the log above)");
}

// ---------------------------------------------------------------------------------------------------------------
// Messages and keys
// ---------------------------------------------------------------------------------------------------------------

fn rand_msg(rng: &mut Rng, i: usize) -> Vec<u8> {
    let n = match i {
        0 => 0,
        1 => 1,
        2 => 135,
        3 => 136,
        4 => 137,
        _ => match rng.below(5) {
            0 => rng.below(64),
            1 => rng.below(300),
            2 => rng.below(2000),
            3 => 0,
            _ => rng.below(10_000),
        },
    };
    rng.bytes(n)
}

// ---------------------------------------------------------------------------------------------------------------
// valid: cross-signing
// ---------------------------------------------------------------------------------------------------------------

fn cat_valid(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let (keys, per_key) = (sc_cap(20, 10), (150 / scale()).max(5));
    let (mut det_same, mut det_n) = (0, 0);
    for _ in 0..keys {
        let xi = rng.arr32();
        let (pk, sk) = (s.keygen)(&xi);
        let kp = s.aws_from_seed(&xi);
        let (other_pk, _) = s.key(rng);
        for j in 0..per_key {
            let m = rand_msg(rng, j);
            let rnd = if j % 3 == 0 { [0u8; 32] } else { rng.arr32() };
            let sig = (s.sign)(&sk, &m, &rnd);
            t.check(s, "ours signs -> both verify", &pk, &m, &sig, Some(true));
            let sig2 = s.aws_sign(&kp, &m);
            t.check(s, "aws-lc signs -> both verify", &pk, &m, &sig2, Some(true));
            // same message signed twice by aws-lc: is signing deterministic?
            if j % 10 == 0 {
                let sig3 = s.aws_sign(&kp, &m);
                det_n += 1;
                det_same += (sig2 == sig3) as u64;
                if sig2 == sig3 {
                    let det = (s.sign)(&sk, &m, &[0u8; 32]);
                    t.line(format!("aws-lc signing looks deterministic; equals ours with rnd = 0: {}", det == sig2));
                }
            }
            // wrong message, wrong key: rejected
            let mut wrong = m.clone();
            if wrong.is_empty() {
                wrong.push(1);
            } else {
                let pos = rng.below(wrong.len());
                wrong[pos] ^= 1 << rng.below(8);
            }
            t.check(s, "valid sig, wrong message", &pk, &wrong, &sig, Some(false));
            t.check(s, "valid sig, wrong message (aws sig)", &pk, &wrong, &sig2, Some(false));
            t.check(s, "valid sig, other key", &other_pk, &m, &sig, Some(false));
        }
    }
    t.line(format!("aws-lc signing repeated on the same (key, message): {det_same} of {det_n} pairs identical (0 means hedged: no byte comparison possible, only cross-verification)"));
    t
}

// ---------------------------------------------------------------------------------------------------------------
// keygen
// ---------------------------------------------------------------------------------------------------------------

fn cat_keygen(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let n = sc(5000).max(11);
    let (mut pk_eq, mut sk_eq, mut imp_ok, mut gen_ok) = (0u64, 0u64, 0u64, 0u64);
    for i in 0..n {
        let xi = match i {
            0 => [0u8; 32],
            1 => [0xffu8; 32],
            2 => core::array::from_fn(|j| j as u8),
            _ => rng.arr32(),
        };
        let (pk, sk) = (s.keygen)(&xi);
        let kp = s.aws_from_seed(&xi);
        let apk: &[u8] = kp.public_key().as_ref();
        let raw = kp.private_key().as_raw_bytes().expect("raw sk");
        let ask: &[u8] = raw.as_ref();
        assert_eq!(apk, &pk[..], "[{}] pk differs for xi={}", s.name, hex(&xi));
        pk_eq += 1;
        assert_eq!(ask, &sk[..], "[{}] sk differs for xi={}", s.name, hex(&xi));
        sk_eq += 1;
        // import ours sk into aws-lc (nearcore's signing path), sign, ours verifies
        if i % 10 == 0 {
            let kp2 = PqdsaKeyPair::from_raw_private_key(s.aws_s, &sk).expect("aws import of ours sk");
            let apk2: &[u8] = kp2.public_key().as_ref();
            assert_eq!(apk2, &pk[..], "[{}] pk from imported sk differs", s.name);
            let m = rand_msg(rng, i / 10);
            let sig = s.aws_sign(&kp2, &m);
            t.check(s, "sign with imported ours-sk (aws) -> both verify", &pk, &m, &sig, Some(true));
            imp_ok += 1;
        }
    }
    // keys generated by aws-lc: export, ours derives the same pk from the sk bytes and signs under it
    for i in 0..sc(300).max(3) {
        let kp = PqdsaKeyPair::generate(s.aws_s).expect("aws generate");
        let apk: Vec<u8> = kp.public_key().as_ref().to_vec();
        let raw = kp.private_key().as_raw_bytes().expect("raw sk");
        let ask: Vec<u8> = raw.as_ref().to_vec();
        assert_eq!(ask.len(), prm::sk_len(&s.p));
        assert_eq!((s.pk_from_sk)(&s.p, &ask).as_deref(), Some(&apk[..]), "[{}] pk_from_sk(aws sk) differs", s.name);
        assert!((s.sk_well_formed)(&ask));
        let m = rand_msg(rng, i);
        let sig = (s.sign)(&ask, &m, &rng.arr32());
        t.check(s, "ours signs with aws-generated sk -> both verify", &apk, &m, &sig, Some(true));
        gen_ok += 1;
    }
    // Wrong-length seeds are rejected by aws-lc (nearcore passes a fixed 32-byte seed).
    for len in [0usize, 31, 33, 64] {
        assert!(PqdsaKeyPair::from_seed(s.aws_s, &vec![7u8; len]).is_err());
    }
    t.line(format!(
        "keygen from seed: {n} xi, pk bytes equal {pk_eq}, expanded sk bytes equal {sk_eq}; ours-sk import + aws sign {imp_ok}; aws-generated keys re-derived {gen_ok}"
    ));

    // Informational: import of mutated secret keys. aws-lc `from_raw_private_key` vs ours `pk_from_sk` (None if any of
    // t0/tr/rho is inconsistent or s1/s2 out of range) and `sk_is_well_formed` (range check only). FIPS 204 leaves
    // skDecode on such bytes undefined, so nothing is asserted; both-accept must give the same pk.
    let mut m4 = [[0u64; 2]; 2]; // [aws accepts][ours pk_from_sk Some]
    let (mut both_same, mut both_diff, mut aws_acc_not_wf) = (0u64, 0u64, 0u64);
    let mut by_region: BTreeMap<&'static str, [u64; 3]> = BTreeMap::new(); // n, aws accepts, ours Some
    for i in 0..sc(3000) {
        let (_pk, sk) = s.key(rng);
        let mut bad = sk.clone();
        let pos = if i % 4 == 0 { rng.below(128) } else { rng.below(bad.len()) };
        bad[pos] ^= 1 << rng.below(8);
        let region = if pos < 32 {
            "rho"
        } else if pos < 64 {
            "K"
        } else if pos < 128 {
            "tr"
        } else if pos < 128 + s.p.l * 32 * s.p.eta_bits {
            "s1"
        } else if pos < 128 + (s.p.l + s.p.k) * 32 * s.p.eta_bits {
            "s2"
        } else {
            "t0"
        };
        let aws_kp = PqdsaKeyPair::from_raw_private_key(s.aws_s, &bad);
        let ours = (s.pk_from_sk)(&s.p, &bad);
        let e = by_region.entry(region).or_default();
        e[0] += 1;
        e[1] += aws_kp.is_ok() as u64;
        e[2] += ours.is_some() as u64;
        m4[aws_kp.is_ok() as usize][ours.is_some() as usize] += 1;
        if let (Ok(kp), Some(opk)) = (&aws_kp, &ours) {
            let apk: &[u8] = kp.public_key().as_ref();
            if apk == &opk[..] {
                both_same += 1
            } else {
                both_diff += 1
            }
        }
        if aws_kp.is_ok() && !(s.sk_well_formed)(&bad) {
            aws_acc_not_wf += 1;
        }
    }
    t.line(format!(
        "sk-import matrix (single-bit-flipped sk; informational): aws rejects & ours None {}, aws rejects & ours Some {}, aws accepts & ours None {}, aws accepts & ours Some {} (pk equal {both_same}, pk differs {both_diff}); aws accepts an sk with s1/s2 out of range: {aws_acc_not_wf}",
        m4[0][0], m4[0][1], m4[1][0], m4[1][1]
    ));
    for (reg, [n, a, o]) in by_region {
        t.line(format!("  sk flip in {reg:<3}: n={n:>5} aws accepts {a:>5}, ours pk_from_sk Some {o:>5}"));
    }
    t
}

// ---------------------------------------------------------------------------------------------------------------
// flips
// ---------------------------------------------------------------------------------------------------------------

fn cat_flips(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let (keys, extra) = if scale() > 1 { (2, 2) } else { (4, 4) };
    let stride = scale();
    let mut sigs: Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> = Vec::new(); // (pk, m, sig)
    for k in 0..keys + extra {
        let (pk, sk) = s.key(rng);
        let m = rand_msg(rng, 5 + k);
        let sig = (s.sign)(&sk, &m, &rng.arr32());
        sigs.push((pk, m, sig));
    }
    // exhaustive single-bit flips
    for (pk, m, sig) in sigs.iter().take(keys) {
        let mut x = sig.clone();
        for bit in (0..sig.len() * 8).step_by(stride) {
            x[bit / 8] ^= 1 << (bit % 8);
            t.check(s, "sigma single-bit flip (exhaustive)", pk, m, &x, Some(false));
            x[bit / 8] ^= 1 << (bit % 8);
        }
        let mut p2 = pk.clone();
        for bit in (0..pk.len() * 8).step_by(stride) {
            p2[bit / 8] ^= 1 << (bit % 8);
            t.check(s, "pk single-bit flip (exhaustive)", &p2, m, sig, Some(false));
            p2[bit / 8] ^= 1 << (bit % 8);
        }
        let mut m2 = m.clone();
        for bit in (0..m.len() * 8).step_by(stride) {
            m2[bit / 8] ^= 1 << (bit % 8);
            t.check(s, "message single-bit flip (exhaustive)", pk, &m2, sig, Some(false));
            m2[bit / 8] ^= 1 << (bit % 8);
        }
    }
    // random multi-bit flips, byte replacement, fills and splices
    let n_multi = sc(120_000).min(if scale() > 1 { 300 } else { usize::MAX });
    for i in 0..n_multi {
        let (pk, m, sig) = &sigs[rng.below(sigs.len())];
        let (mut pk2, mut m2, mut sg2) = (pk.clone(), m.clone(), sig.clone());
        // `strict`: FIPS 204 requires a rejection whenever the input actually changed (signatures are strongly
        // unforgeable; a mutation that cancels itself leaves the valid input, which must be accepted).
        let (cat, strict): (&'static str, bool) = match i % 6 {
            0 => {
                for _ in 0..2 + rng.below(15) {
                    let b = rng.below(sg2.len() * 8);
                    sg2[b / 8] ^= 1 << (b % 8);
                }
                ("sigma 2..16 bit flips", true)
            }
            1 => {
                for _ in 0..2 + rng.below(15) {
                    let b = rng.below(pk2.len() * 8);
                    pk2[b / 8] ^= 1 << (b % 8);
                }
                ("pk 2..16 bit flips", true)
            }
            2 => {
                if m2.is_empty() {
                    m2.push(0)
                }
                for _ in 0..2 + rng.below(7) {
                    let b = rng.below(m2.len() * 8);
                    m2[b / 8] ^= 1 << (b % 8);
                }
                ("message 2..8 bit flips", false)
            }
            3 => {
                for _ in 0..1 + rng.below(4) {
                    let pos = rng.below(sg2.len());
                    sg2[pos] = rng.next() as u8;
                }
                ("sigma 1..4 random byte replacements", true)
            }
            4 => {
                let a = rng.below(sg2.len());
                let len = 1 + rng.below(64.min(sg2.len() - a));
                let v = if rng.below(2) == 0 { 0u8 } else { 0xff };
                sg2[a..a + len].fill(v);
                ("sigma range fill 0x00/0xff", true)
            }
            _ => {
                // splice a region from another valid signature (same or other key / message)
                let (_, _, other) = &sigs[rng.below(sigs.len())];
                let a = rng.below(sg2.len());
                let len = 1 + rng.below(sg2.len() - a);
                sg2[a..a + len].copy_from_slice(&other[a..a + len]);
                ("sigma splice from another valid sigma", false)
            }
        };
        let unchanged = pk2 == *pk && m2 == *m && sg2 == *sig;
        let expect = if unchanged { Some(true) } else if strict { Some(false) } else { None };
        t.check(s, cat, &pk2, &m2, &sg2, expect);
    }
    t
}

// ---------------------------------------------------------------------------------------------------------------
// lengths
// ---------------------------------------------------------------------------------------------------------------

/// DER SubjectPublicKeyInfo of `pk` for this parameter set.
fn spki(s: &Set, pk: &[u8]) -> Vec<u8> {
    let n = pk.len();
    let mut v = vec![0x30, 0x82, ((n + 18) >> 8) as u8, (n + 18) as u8];
    v.extend_from_slice(&[0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, s.oid_last]);
    v.extend_from_slice(&[0x03, 0x82, ((n + 1) >> 8) as u8, (n + 1) as u8, 0x00]);
    v.extend_from_slice(pk);
    v
}

fn cat_lengths(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let n_cases = sc_cap(40, 20);
    let step = scale();
    let ext = scale().min(16);
    let (mut pk, mut sk) = s.key(rng);
    for c in 0..n_cases {
        if c % 8 == 0 {
            (pk, sk) = s.key(rng);
        }
        let m = rand_msg(rng, 5 + c);
        let sig = (s.sign)(&sk, &m, &rng.arr32());
        // control: the untouched pair at exact lengths (the only case here that also goes through the public API)
        t.check(s, "control: exact lengths, valid", &pk, &m, &sig, Some(true));
        for l in (0..sig.len()).step_by(step) {
            t.check(s, "sigma truncated (every length)", &pk, &m, &sig[..l], Some(false));
        }
        for e in (1..=64usize).step_by(ext) {
            let mut zx = sig.clone();
            zx.extend(std::iter::repeat_n(0u8, e));
            t.check(s, "sigma extended with zeros (1..64)", &pk, &m, &zx, Some(false));
            let mut rx = sig.clone();
            rx.extend(rng.bytes(e));
            t.check(s, "sigma extended with random (1..64)", &pk, &m, &rx, Some(false));
        }
        let mut dbl = sig.clone();
        dbl.extend_from_slice(&sig);
        t.check(s, "sigma doubled", &pk, &m, &dbl, Some(false));
        for l in (0..pk.len()).step_by(step) {
            t.check(s, "pk truncated (every length)", &pk[..l], &m, &sig, Some(false));
        }
        for e in (1..=64usize).step_by(ext) {
            let mut zx = pk.clone();
            zx.extend(std::iter::repeat_n(0u8, e));
            t.check(s, "pk extended with zeros (1..64)", &zx, &m, &sig, Some(false));
            let mut rx = pk.clone();
            rx.extend(rng.bytes(e));
            t.check(s, "pk extended with random (1..64)", &rx, &m, &sig, Some(false));
        }
        // pk of the other two parameter sets' lengths
        for other in 0..3 {
            let o = set(other);
            if o.pk_len() != pk.len() {
                let wrong_pk = rng.bytes(o.pk_len());
                t.check(s, "pk with another set's length", &wrong_pk, &m, &sig, Some(false));
                let wrong_sig = rng.bytes(o.sig_len());
                t.check(s, "sigma with another set's length", &pk, &m, &wrong_sig, Some(false));
            }
        }
        // Informational: aws-lc-rs also accepts a DER SubjectPublicKeyInfo where a raw public key is expected. Not
        // reachable through nearcore (its pk type is a fixed 1952-byte array), and ours takes raw bytes only.
        let wrapped = spki(s, &pk);
        t.info("pk wrapped in DER SPKI (|pk|+22 bytes)", (s.ours_verify)(&s.p, &wrapped, &m, &sig), aws_verify(s.aws_v, &wrapped, &m, &sig));
    }
    t
}

// ---------------------------------------------------------------------------------------------------------------
// hint-region edge cases
// ---------------------------------------------------------------------------------------------------------------

/// Parses the hint region of a valid signature into per-polynomial sorted index lists.
fn hint_lists(s: &Set, sig: &[u8]) -> Vec<Vec<u8>> {
    let (om, k) = (s.p.omega, s.p.k);
    let reg = &sig[s.hint_off..];
    let mut lists = Vec::new();
    let mut prev = 0usize;
    for i in 0..k {
        let cum = reg[om + i] as usize;
        lists.push(reg[prev..cum].to_vec());
        prev = cum;
    }
    lists
}

/// Hint region bytes from lists (cumulative counts computed), with optional overrides.
fn hint_region(s: &Set, lists: &[Vec<u8>], pad: &[(usize, u8)], cum_override: &[(usize, u8)]) -> Vec<u8> {
    let (om, k) = (s.p.omega, s.p.k);
    let mut reg = vec![0u8; om + k];
    let mut pos = 0;
    for (i, l) in lists.iter().enumerate() {
        for &x in l {
            if pos < om {
                reg[pos] = x;
            }
            pos += 1;
        }
        reg[om + i] = pos.min(255) as u8;
    }
    for &(slot, v) in pad {
        reg[slot] = v;
    }
    for &(i, v) in cum_override {
        reg[om + i] = v;
    }
    reg
}

fn with_region(s: &Set, sig: &[u8], reg: &[u8]) -> Vec<u8> {
    let mut x = sig[..s.hint_off].to_vec();
    x.extend_from_slice(reg);
    x
}

/// A limit of verdict-level testing: removing our 'decreasing cumulative count' check (FIPS 204 Algorithm 21 step 4)
/// is not detected by this file, because a mis-decoded h changes w1′ and c̃ rejects the signature anyway, so the verdict
/// is the same. That check is covered by the Lean HintBitUnpack theorem and by `tests/leaf.rs`
/// (`hint_unpack_bottom_cases`, 'count decreasing across polynomials', and `hint_unpack_alg21_corner_cases`, 'count
/// decreases after reaching ω'), which look at the decoder's output instead of the verdict.
fn cat_hint(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let (om, k) = (s.p.omega, s.p.k);
    let n_sigs = sc_cap(16, 16);
    let mut sigs = Vec::new();
    for i in 0..n_sigs {
        let (pk, sk) = s.key(rng);
        let m = rand_msg(rng, 5 + i);
        let sig = (s.sign)(&sk, &m, &rng.arr32());
        sigs.push((pk, m, sig));
    }
    for (pk, m, sig) in &sigs {
        let lists = hint_lists(s, sig);
        let total: usize = lists.iter().map(|l| l.len()).sum();
        // the base case: honest region re-encoded must equal the original and verify
        assert_eq!(hint_region(s, &lists, &[], &[]), sig[s.hint_off..], "hint re-encode");
        t.check(s, "hint: honest signature", pk, m, sig, Some(true));

        // (a) same hint set, indices out of order inside a polynomial
        for (pi, l) in lists.iter().enumerate() {
            for a in 0..l.len().saturating_sub(1) {
                let mut ls = lists.clone();
                ls[pi].swap(a, a + 1);
                t.check(s, "hint: adjacent indices swapped (same set)", pk, m, &with_region(s, sig, &hint_region(s, &ls, &[], &[])), Some(false));
            }
            if l.len() >= 2 {
                let mut ls = lists.clone();
                ls[pi].reverse();
                t.check(s, "hint: poly indices reversed (same set)", pk, m, &with_region(s, sig, &hint_region(s, &ls, &[], &[])), Some(false));
            }
        }
        // (b) nonzero bytes in unused index slots, same hint set
        for slot in (total..om).take(8) {
            for v in [1u8, 0x7f, 0x80, 0xff, lists.iter().flatten().last().copied().unwrap_or(3)] {
                if v != 0 {
                    t.check(s, "hint: nonzero padding in unused slot (same set)", pk, m, &with_region(s, sig, &hint_region(s, &lists, &[(slot, v)], &[])), Some(false));
                }
            }
        }
        // (c) an index repeated (same set, one more index, strictly-increasing rule violated)
        if total < om {
            for (pi, l) in lists.iter().enumerate() {
                for a in 0..l.len() {
                    let mut ls = lists.clone();
                    ls[pi].insert(a, l[a]);
                    t.check(s, "hint: index repeated (same set)", pk, m, &with_region(s, sig, &hint_region(s, &ls, &[], &[])), Some(false));
                }
            }
        }
        // (d) cumulative counts tampered
        for i in 0..k {
            let base = sig[s.hint_off + om + i];
            for v in [0u8, 1, base.wrapping_sub(1), base.wrapping_add(1), om as u8, om as u8 + 1, 0x80, 0xff] {
                if v == base {
                    continue;
                }
                let expect = if v as usize > om || (i > 0 && v < sig[s.hint_off + om + i - 1]) { Some(false) } else { None };
                t.check(s, "hint: cumulative count tampered", pk, m, &with_region(s, sig, &hint_region(s, &lists, &[], &[(i, v)])), expect);
            }
        }
        // (e) count of the last polynomial extended over zero padding (index 0 again, or a new index 0)
        for extra in 1..=(om - total).min(4) {
            t.check(s, "hint: last count extended over padding", pk, m, &with_region(s, sig, &hint_region(s, &lists, &[], &[(k - 1, (total + extra) as u8)])), None);
        }
        // (f) every value at every position of the hint region
        let step = scale().min(64);
        for pos in 0..om + k {
            for v in (0..=255u8).step_by(step) {
                if v == sig[s.hint_off + pos] {
                    continue;
                }
                let mut x = sig.clone();
                x[s.hint_off + pos] = v;
                t.check(s, "hint: any byte value at any region position", pk, m, &x, None);
            }
        }
        // (g) degenerate regions
        for fill in [0x00u8, 0xff, 0x01, om as u8, 0x55] {
            let x = with_region(s, sig, &vec![fill; om + k]);
            t.check(s, "hint: region filled with one byte value", pk, m, &x, if total == 0 && fill == 0 { Some(true) } else { None });
        }
        // (h) well-formed random hint sets (strictly increasing, counts consistent, total <= omega): reject by c~
        for _ in 0..sc(400) {
            let mut ls = vec![Vec::new(); k];
            let want = rng.below(om + 1);
            let mut left = want;
            for l in ls.iter_mut() {
                let n = if left == 0 { 0 } else { rng.below(left.min(256) + 1) };
                let mut set_: Vec<u8> = Vec::new();
                while set_.len() < n {
                    let v = rng.next() as u8;
                    if !set_.contains(&v) {
                        set_.push(v);
                    }
                }
                set_.sort_unstable();
                left -= n;
                *l = set_;
            }
            t.check(s, "hint: well-formed random hints", pk, m, &with_region(s, sig, &hint_region(s, &ls, &[], &[])), None);
        }
        // (i) random regions
        for _ in 0..sc(400) {
            let reg = rng.bytes(om + k);
            t.check(s, "hint: uniformly random region", pk, m, &with_region(s, sig, &reg), None);
        }
        // (j) random regions with small cumulative counts but arbitrary indices (unsorted / repeated)
        for _ in 0..sc(400) {
            let mut reg = rng.bytes(om + k);
            let mut c = 0usize;
            for i in 0..k {
                c = (c + rng.below(8)).min(om);
                reg[om + i] = c as u8;
            }
            t.check(s, "hint: valid counts, arbitrary index bytes", pk, m, &with_region(s, sig, &reg), None);
        }
    }
    t
}

// ---------------------------------------------------------------------------------------------------------------
// c~
// ---------------------------------------------------------------------------------------------------------------

fn cat_ctilde(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let ct = s.p.c_tilde_len;
    let n_sigs = sc_cap(40, 20);
    let mut sigs = Vec::new();
    for i in 0..n_sigs {
        let (pk, sk) = s.key(rng);
        let m = rand_msg(rng, 5 + i);
        let sig = (s.sign)(&sk, &m, &rng.arr32());
        sigs.push((pk, m, sig));
    }
    for (pk, m, sig) in &sigs {
        let mut x = sig.clone();
        for bit in 0..ct * 8 {
            x[bit / 8] ^= 1 << (bit % 8);
            t.check(s, "c~ single-bit flip (exhaustive)", pk, m, &x, Some(false));
            x[bit / 8] ^= 1 << (bit % 8);
        }
        for fill in [0x00u8, 0xff] {
            let mut y = sig.clone();
            y[..ct].fill(fill);
            t.check(s, "c~ all 0x00 / all 0xff", pk, m, &y, Some(false));
        }
        let mut y = sig.clone();
        y[..ct].reverse();
        t.check(s, "c~ reversed", pk, m, &y, None);
    }
    for i in 0..sc(100_000).min(if scale() > 1 { 300 } else { usize::MAX }) {
        let (pk, m, sig) = &sigs[rng.below(sigs.len())];
        let mut x = sig.clone();
        match i % 3 {
            0 => {
                for _ in 0..2 + rng.below(30) {
                    let b = rng.below(ct * 8);
                    x[b / 8] ^= 1 << (b % 8);
                }
                t.check(s, "c~ 2..31 bit flips", pk, m, &x, Some(x == *sig));
            }
            1 => {
                x[..ct].copy_from_slice(&rng.bytes(ct));
                t.check(s, "c~ replaced by random bytes", pk, m, &x, Some(false));
            }
            _ => {
                let (_, _, other) = &sigs[rng.below(sigs.len())];
                x[..ct].copy_from_slice(&other[..ct]);
                t.check(s, "c~ taken from another signature", pk, m, &x, None);
            }
        }
    }
    t
}

// ---------------------------------------------------------------------------------------------------------------
// Forging signer (skips the checks Verify makes, to put the verifier's norm check on its own)
// ---------------------------------------------------------------------------------------------------------------

/// Builds a signature (c̃, z, h) for sk and M = `m` from our own mask y (not ExpandMask). All checks of Sign step 23 and 28
/// are made except ‖z‖∞ when `pin` is set. With `pin = Some(t)` the mask coefficient `(i0, j0)` is chosen so that z's
/// coefficient there equals `t` (retrying until it does), every other z coefficient is far below the bound; the result
/// then fails Verify only through its norm check (c̃ matches). With `pin = None` this is an honest signer that keeps a
/// signature only if it has `want_ones` hints.
fn forge_g<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    m: &[u8],
    pin: Option<i64>,
    want_ones: Option<usize>,
    rng: &mut Rng,
) -> Option<Forged> {
    let d = sk_decode::<K, L>(p, sk);
    let a_hat = expand_a::<K, L>(&d.rho);
    let s1_hat = ntt_vec::<L>(&d.s1);
    let s2_hat = ntt_vec::<K>(&d.s2);
    let t0_hat = ntt_vec::<K>(&d.t0);
    let mut mu = [0u8; 64];
    shake256(&[&d.tr, &[0, 0], m], &mut mu);
    let g1 = p.gamma1 as i64;
    let bound = (p.gamma1 - p.beta) as i64;
    let (i0, j0) = (rng.below(L), rng.below(256));
    for _ in 0..400_000 {
        let mut y = [[0u32; 256]; L];
        for row in y.iter_mut() {
            for c in row.iter_mut() {
                let v = match pin {
                    Some(_) => rng.below(bound as usize + 1) as i64 - bound / 2,
                    None => rng.below(2 * g1 as usize) as i64 - g1 + 1,
                };
                *c = q_mod(v);
            }
        }
        if let Some(t) = pin {
            y[i0][j0] = q_mod(t);
        }
        let w_hat = matrix_vector_ntt::<K, L>(&a_hat, &ntt_vec::<L>(&y));
        let mut w = [[0u32; 256]; K];
        let mut w1 = [[0u32; 256]; K];
        for i in 0..K {
            w[i] = ntt_inverse(&w_hat[i]);
            w1[i] = poly_high_bits(p, &w[i]);
        }
        let mut w1_enc = [0u8; 8 * 192];
        w1_encode::<K>(p, &w1, &mut w1_enc);
        let mut ct = [0u8; 64];
        shake256(&[&mu, &w1_enc[..K * 32 * p.w1_bits]], &mut ct[..p.c_tilde_len]);
        let c_hat = ntt(&sample_in_ball(p, &ct[..p.c_tilde_len]));
        let cs1 = scalar_vector_ntt_inverse::<L>(&c_hat, &s1_hat);
        let mut z = [[0u32; 256]; L];
        for i in 0..L {
            for j in 0..256 {
                z[i][j] = add(y[i][j], cs1[i][j]);
            }
        }
        if let Some(t) = pin
            && z[i0][j0] != q_mod(t)
        {
            continue;
        }
        let znorm = vec_infinity_norm(&z);
        if pin.is_none() && znorm as i64 >= bound {
            continue;
        }
        let cs2 = scalar_vector_ntt_inverse::<K>(&c_hat, &s2_hat);
        let mut w_cs2 = [[0u32; 256]; K];
        let mut r0 = [[0u32; 256]; K];
        for i in 0..K {
            w_cs2[i] = sub_poly(&w[i], &cs2[i]);
            r0[i] = poly_low_bits(p, &w_cs2[i]);
        }
        if vec_infinity_norm(&r0) >= p.gamma2 - p.beta {
            continue;
        }
        let ct0 = scalar_vector_ntt_inverse::<K>(&c_hat, &t0_hat);
        let mut hint = [[false; 256]; K];
        let mut ones = 0;
        for i in 0..K {
            for j in 0..256 {
                hint[i][j] = make_hint(p, neg(ct0[i][j]), add(w_cs2[i][j], ct0[i][j]));
                ones += hint[i][j] as usize;
            }
        }
        if vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega {
            continue;
        }
        if let Some(wo) = want_ones
            && ones != wo
        {
            continue;
        }
        let mut sig = vec![0u8; prm::sig_len(p)];
        sig_encode::<K, L>(p, &ct[..p.c_tilde_len], &z, &hint, &mut sig);
        return Some(Forged { sig, znorm, ones });
    }
    None
}

/// Evidence that the 'reject' targets below reach the norm check and fail only there (rather than failing earlier, in the
/// decoder or the c̃ comparison): (1) the 'inside' targets, z = ±(γ1 − β − 1), built the same way, are accepted 150 of 150
/// times per target (full run), so the forged signatures decode, c̃ matches and the hint is fine; and (2) the mutant of
/// our norm check that replaces `<` by `<=` is killed by the z = ±(γ1 − β) rows, i.e. those rows do depend on the
/// comparison at exactly the bound.
fn cat_zbound(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let g1 = s.p.gamma1 as i64;
    let bound = (s.p.gamma1 - s.p.beta) as i64;
    let targets: [(&'static str, i64); 9] = [
        ("z = +(g1-b-1): norm just inside (valid)", bound - 1),
        ("z = -(g1-b-1): norm just inside (valid)", -(bound - 1)),
        ("z = +(g1-b): norm at the bound (reject)", bound),
        ("z = -(g1-b): norm at the bound (reject)", -bound),
        ("z = +(g1-b+1): just outside (reject)", bound + 1),
        ("z = -(g1-b+1): just outside (reject)", -(bound + 1)),
        ("z = +(g1-1): outside (reject)", g1 - 1),
        ("z = -(g1-1): outside (reject)", -(g1 - 1)),
        ("z = +g1 (encoding 0): outside (reject)", g1),
    ];
    let per_target = sc(150);
    let (mut pk, mut sk) = s.key(rng);
    let mut produced = 0;
    for (ti, (label, tv)) in targets.iter().enumerate() {
        for c in 0..per_target {
            if c % 6 == 0 {
                (pk, sk) = s.key(rng);
            }
            let m = rand_msg(rng, 5 + c);
            let f = (s.forge)(&s.p, &sk, &m, Some(*tv), None, rng).unwrap_or_else(|| panic!("[{}] forge failed for target {label}", s.name));
            produced += 1;
            let inside = tv.abs() < bound;
            assert_eq!(f.znorm as i64, tv.abs().min(Q - tv.abs()), "forged znorm");
            // sigma decodes (the hint is well formed), so it is the norm check alone that decides
            assert!(sig_decode_ok(s, &f.sig));
            let _ = (ti, f.ones);
            t.check(s, label, &pk, &m, &f.sig, Some(inside));
            // the same signature against the wrong message: reject
            let mut wm = m.clone();
            wm.push(0);
            t.check(s, "forged z-bound sigma, wrong message", &pk, &wm, &f.sig, Some(false));
        }
    }
    t.line(format!("{produced} forged signatures (norm check is the only failing condition for the 'reject' targets)"));
    // exactly omega hints (the maximum encodable), omega - 1, and 0 hints (honest signer filtered by the hint count)
    for want in [s.p.omega, s.p.omega - 1, s.p.omega - 2] {
        for c in 0..sc(40) {
            let (pk, sk) = s.key(rng);
            let m = rand_msg(rng, 5 + c);
            let f = (s.forge)(&s.p, &sk, &m, None, Some(want), rng).unwrap_or_else(|| panic!("[{}] no signature with {want} hints", s.name));
            assert_eq!(f.ones, want);
            t.check(s, "signature with omega / omega-1 / omega-2 hints", &pk, &m, &f.sig, Some(true));
            // one more index than omega cannot be encoded; try the region with count byte omega + 1
            let mut x = f.sig.clone();
            let last = s.hint_off + s.p.omega + s.p.k - 1;
            x[last] = (s.p.omega + 1) as u8;
            t.check(s, "omega hints, last count set to omega+1", &pk, &m, &x, Some(false));
        }
    }
    t
}

fn sig_decode_ok(s: &Set, sig: &[u8]) -> bool {
    // dispatch on K through the sizes
    match s.p.k {
        4 => sig_decode::<4, 4>(&s.p, sig).is_some(),
        6 => sig_decode::<6, 5>(&s.p, sig).is_some(),
        _ => sig_decode::<8, 7>(&s.p, sig).is_some(),
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Keys with edge values
// ---------------------------------------------------------------------------------------------------------------

fn coef(mode: Mode, eta: u32, rng: &mut Rng) -> u32 {
    match mode {
        Mode::Zero => 0,
        Mode::Rand => q_mod(rng.below(2 * eta as usize + 1) as i64 - eta as i64),
        Mode::Max => q_mod(eta as i64),
        Mode::Min => q_mod(-(eta as i64)),
    }
}

/// A key pair for chosen ρ, K and s1/s2 patterns: t, (t1, t0), pk, tr and sk as KeyGen_internal steps 5–10 compute them.
fn rekey_g<const K: usize, const L: usize>(p: &Params, spec: &KeySpec, rng: &mut Rng) -> (Vec<u8>, Vec<u8>) {
    let a_hat = expand_a::<K, L>(&spec.rho);
    let mut s1 = [[0u32; 256]; L];
    let mut s2 = [[0u32; 256]; K];
    for row in s1.iter_mut() {
        for c in row.iter_mut() {
            *c = coef(spec.s1, p.eta, rng);
        }
    }
    for row in s2.iter_mut() {
        for c in row.iter_mut() {
            *c = coef(spec.s2, p.eta, rng);
        }
    }
    let prod = matrix_vector_ntt::<K, L>(&a_hat, &ntt_vec::<L>(&s1));
    let mut t1 = [[0u32; 256]; K];
    let mut t0 = [[0u32; 256]; K];
    for i in 0..K {
        let t = add_poly(&ntt_inverse(&prod[i]), &s2[i]);
        (t1[i], t0[i]) = poly_power2round(&t);
    }
    let mut pk = vec![0u8; prm::pk_len(p)];
    pk_encode::<K>(&spec.rho, &t1, &mut pk);
    let mut tr = [0u8; 64];
    shake256(&[&pk], &mut tr);
    let mut sk = vec![0u8; prm::sk_len(p)];
    sk_encode::<K, L>(p, &spec.rho, &spec.key, &tr, &s1, &s2, &t0, &mut sk);
    (pk, sk)
}

fn spki_rho(s: &Set, rng: &mut Rng) -> [u8; 32] {
    // The first 22 bytes of a DER SubjectPublicKeyInfo whose total length is exactly |pk|: SEQUENCE { SEQUENCE { OID
    // 2.16.840.1.101.3.4.3.x }, BIT STRING } sized so that the whole input is exactly |pk| bytes, i.e. the BIT STRING
    // holds a key 22 bytes shorter than a real one.
    let n = s.pk_len();
    let mut rho = [0u8; 32];
    rho[..4].copy_from_slice(&[0x30, 0x82, ((n - 4) >> 8) as u8, (n - 4) as u8]);
    rho[4..17].copy_from_slice(&[0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, s.oid_last]);
    rho[17..22].copy_from_slice(&[0x03, 0x82, ((n - 21) >> 8) as u8, (n - 21) as u8, 0x00]);
    rho[22..].copy_from_slice(&rng.bytes(10));
    rho
}

fn cat_edgekeys(s: &Set, rng: &mut Rng) -> Tally {
    let mut t = Tally::default();
    let rhos: Vec<(&'static str, [u8; 32])> = vec![
        ("rho = 0x00..", [0u8; 32]),
        ("rho = 0xff..", [0xffu8; 32]),
        ("rho = DER SPKI header + random", spki_rho(s, rng)),
        ("rho = DER SPKI header + random", spki_rho(s, rng)),
        ("rho = random", rng.arr32()),
    ];
    let pats: [(Mode, Mode); 7] = [
        (Mode::Zero, Mode::Zero),
        (Mode::Zero, Mode::Max),
        (Mode::Zero, Mode::Min),
        (Mode::Zero, Mode::Rand),
        (Mode::Rand, Mode::Zero),
        (Mode::Max, Mode::Min),
        (Mode::Rand, Mode::Rand),
    ];
    let (mut keys, mut t1_zero, mut t1_max) = (0, 0, 0);
    let mut spki_like = 0;
    for (rname, rho) in &rhos {
        for (s1, s2) in pats {
            let spec = KeySpec { rho: *rho, key: rng.arr32(), s1, s2 };
            let (pk, sk) = (s.rekey)(&s.p, &spec, rng);
            keys += 1;
            // the t1 coefficients actually at their extremes
            let t1 = &pk[32..];
            t1_zero += t1.iter().filter(|&&b| b == 0).count();
            t1_max += t1.iter().filter(|&&b| b == 0xff).count();
            // the key is a valid one: pk_from_sk agrees
            assert_eq!((s.pk_from_sk)(&s.p, &sk).as_deref(), Some(&pk[..]), "rekey: inconsistent key");
            if *rname == "rho = DER SPKI header + random" {
                spki_like += 1;
            }
            for j in 0..sc(60) {
                let m = rand_msg(rng, j);
                let sig = (s.sign)(&sk, &m, &rng.arr32());
                t.check(s, "edge key: valid signature", &pk, &m, &sig, Some(true));
                t.check(s, "edge key: wrong message", &pk, &[&m[..], &[9]].concat(), &sig, Some(false));
                for _ in 0..4 {
                    let mut x = sig.clone();
                    let b = rng.below(x.len() * 8);
                    x[b / 8] ^= 1 << (b % 8);
                    t.check(s, "edge key: sigma bit flip", &pk, &m, &x, Some(false));
                    let mut p2 = pk.clone();
                    let b = rng.below(p2.len() * 8);
                    p2[b / 8] ^= 1 << (b % 8);
                    t.check(s, "edge key: pk bit flip", &p2, &m, &sig, Some(false));
                }
                // t1 forced to its extremes in the pk of a valid signature (signature then no longer matches)
                let mut p3 = pk.clone();
                p3[32..].fill(if j % 2 == 0 { 0x00 } else { 0xff });
                t.check(s, "edge key: pk t1 all 0x00 / all 0xff", &p3, &m, &sig, Some(p3 == pk));
                let mut p4 = pk.clone();
                for _ in 0..8 {
                    let pos = 32 + rng.below(p4.len() - 32);
                    p4[pos] = if rng.below(2) == 0 { 0 } else { 0xff };
                }
                t.check(s, "edge key: pk some t1 bytes 0x00/0xff", &p4, &m, &sig, if p4 == pk { Some(true) } else { None });
            }
        }
    }
    // honest keys: t1 extremes occur naturally (about 1 in 1024 coefficients); count how often in this run
    t.line(format!("{keys} constructed keys ({spki_like} with a DER-SPKI-header rho); t1 bytes 0x00: {t1_zero}, 0xff: {t1_max}"));
    t
}

// ---------------------------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn awslc_valid_cross_signing() {
    run_sets("valid", cat_valid);
}

#[test]
fn awslc_keygen_and_key_import() {
    run_sets("keygen", cat_keygen);
}

#[test]
fn awslc_bit_flips() {
    run_sets("flips", cat_flips);
}

#[test]
fn awslc_lengths() {
    run_sets("lengths", cat_lengths);
}

#[test]
fn awslc_hint_encoding() {
    run_sets("hint", cat_hint);
}

#[test]
fn awslc_ctilde() {
    run_sets("ctilde", cat_ctilde);
}

#[test]
fn awslc_z_bound_and_omega() {
    run_sets("zbound", cat_zbound);
}

#[test]
fn awslc_edge_keys() {
    run_sets("edgekeys", cat_edgekeys);
}

// ---------------------------------------------------------------------------------------------------------------
// Wycheproof through aws-lc-rs
// ---------------------------------------------------------------------------------------------------------------

#[derive(Deserialize)]
struct WFile {
    #[serde(rename = "testGroups")]
    groups: Vec<WGroup>,
}
#[derive(Deserialize)]
struct WGroup {
    #[serde(rename = "publicKey", default)]
    public_key: Option<String>,
    #[serde(rename = "privateSeed", default)]
    private_seed: Option<String>,
    #[serde(rename = "privateKey", default)]
    private_key: Option<String>,
    tests: Vec<WCase>,
}
#[derive(Deserialize)]
struct WCase {
    #[serde(rename = "tcId")]
    tc_id: serde_json::Value,
    comment: String,
    #[serde(default)]
    msg: Option<String>,
    #[serde(default)]
    ctx: Option<String>,
    #[serde(default)]
    sig: Option<String>,
    result: String,
    flags: Vec<String>,
}

fn wload(setno: &str, kind: &str) -> WFile {
    let path = format!("{}/tests/data/wycheproof/mldsa_{setno}_{kind}_test.json.gz", env!("CARGO_MANIFEST_DIR"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut json = String::new();
    GzDecoder::new(&bytes[..]).read_to_string(&mut json).unwrap();
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{path}: {e}"))
}

#[test]
fn awslc_wycheproof() {
    let mut problems: Vec<String> = Vec::new();
    for (idx, setno) in ["44", "65", "87"].iter().enumerate() {
        let s = set(idx);
        // verify vectors: expected verdict, aws-lc verdict, ours
        let (mut n, mut skipped_ctx, mut agree_expected) = (0, 0, 0);
        let (mut aws_ne_expected, mut aws_ne_ours) = (0, 0);
        let (mut valid_n, mut invalid_n) = (0, 0);
        for (gi, g) in wload(setno, "verify").groups.iter().enumerate() {
            let pk = unhex(g.public_key.as_deref().unwrap());
            for c in &g.tests {
                let msg = unhex(c.msg.as_deref().unwrap_or(""));
                let ctx = unhex(c.ctx.as_deref().unwrap_or(""));
                let sig = unhex(c.sig.as_deref().unwrap_or(""));
                let want = c.result == "valid";
                if !ctx.is_empty() {
                    // aws-lc-rs 1.18.2 has no context parameter
                    skipped_ctx += 1;
                    continue;
                }
                n += 1;
                if want {
                    valid_n += 1
                } else {
                    invalid_n += 1
                }
                let a = aws_verify(s.aws_v, &pk, &msg, &sig);
                let o = (s.ours_verify)(&s.p, &pk, &msg, &sig);
                if a == want {
                    agree_expected += 1;
                } else {
                    aws_ne_expected += 1;
                    problems.push(format!("[{}] verify group {gi} tcId {} [{}] ({}): expected {want}, aws-lc {a}, ours {o}", s.name, c.tc_id, c.flags.join(","), c.comment));
                }
                if a != o {
                    aws_ne_ours += 1;
                    problems.push(format!("[{}] verify group {gi} tcId {}: aws-lc {a} but ours {o}", s.name, c.tc_id));
                }
            }
        }
        println!("wycheproof verify ML-DSA-{setno}: {n} vectors with empty ctx ({valid_n} valid, {invalid_n} invalid) through aws-lc-rs; aws-lc = expected on {agree_expected}, != expected on {aws_ne_expected}, != ours on {aws_ne_ours}; {skipped_ctx} with non-empty ctx skipped (no ctx in the aws-lc-rs API)");

        // sign_seed: aws-lc from_seed must give the group public key; the vector signature must verify in aws-lc
        for kind in ["sign_seed", "sign_noseed"] {
            let (mut keys, mut key_ok, mut sig_n, mut sig_ok, mut sig_skipped) = (0, 0, 0, 0, 0);
            let (mut inv_key_n, mut inv_key_accepted) = (0, 0);
            for (gi, g) in wload(setno, kind).groups.iter().enumerate() {
                let group_pk = g.public_key.as_deref().map(unhex);
                if kind == "sign_seed" {
                    let seed = unhex(g.private_seed.as_deref().unwrap());
                    keys += 1;
                    match PqdsaKeyPair::from_seed(s.aws_s, &seed) {
                        Ok(kp) => {
                            let apk: &[u8] = kp.public_key().as_ref();
                            if group_pk.as_deref().map(|gp| gp == apk).unwrap_or(true) {
                                key_ok += 1
                            } else {
                                problems.push(format!("[{}] {kind} group {gi}: from_seed public key differs from the vector's", s.name));
                            }
                        }
                        Err(_) => {
                            // wrong-length seeds are invalid vectors
                            let invalid = g.tests.iter().all(|c| c.result == "invalid");
                            if seed.len() != 32 && invalid {
                                key_ok += 1
                            } else {
                                problems.push(format!("[{}] {kind} group {gi}: aws-lc from_seed failed on a usable seed", s.name));
                            }
                        }
                    }
                } else {
                    let sk = unhex(g.private_key.as_deref().unwrap());
                    keys += 1;
                    let all_invalid = g.tests.iter().all(|c| c.result == "invalid");
                    match PqdsaKeyPair::from_raw_private_key(s.aws_s, &sk) {
                        Ok(kp) => {
                            if all_invalid {
                                inv_key_n += 1;
                                inv_key_accepted += 1;
                                // informational: the vector expects rejection of this key
                            } else {
                                let apk: &[u8] = kp.public_key().as_ref();
                                if group_pk.as_deref().map(|gp| gp == apk).unwrap_or(true) {
                                    key_ok += 1
                                } else {
                                    problems.push(format!("[{}] {kind} group {gi}: raw private key gives a different public key", s.name));
                                }
                            }
                        }
                        Err(_) => {
                            if all_invalid {
                                inv_key_n += 1;
                                key_ok += 1;
                            } else {
                                problems.push(format!("[{}] {kind} group {gi}: aws-lc rejected a valid raw private key", s.name));
                            }
                        }
                    }
                }
                // vector signatures (deterministic or hedged with the vector's rnd) must verify in aws-lc under the group pk
                if let Some(gp) = &group_pk {
                    for c in &g.tests {
                        let (Some(msg), Some(sig)) = (&c.msg, &c.sig) else {
                            sig_skipped += 1;
                            continue;
                        };
                        let ctx = unhex(c.ctx.as_deref().unwrap_or(""));
                        if !ctx.is_empty() || c.result != "valid" {
                            sig_skipped += 1;
                            continue;
                        }
                        sig_n += 1;
                        if aws_verify(s.aws_v, gp, &unhex(msg), &unhex(sig)) {
                            sig_ok += 1
                        } else {
                            problems.push(format!("[{}] {kind} group {gi} tcId {} ({}): aws-lc rejects the vector's valid signature", s.name, c.tc_id, c.comment));
                        }
                    }
                }
            }
            println!("wycheproof {kind} ML-DSA-{setno}: {keys} groups, key import consistent in {key_ok}; {sig_n} vector signatures (empty ctx) verified by aws-lc: {sig_ok} accepted ({sig_skipped} skipped: non-empty ctx, no signature, or invalid); invalid-key groups {inv_key_n}, of which aws-lc imported {inv_key_accepted} (informational)");
        }
    }
    for p in &problems {
        println!("WYCHEPROOF PROBLEM {p}");
    }
    assert!(problems.is_empty(), "{} wycheproof problems (details in the log above)", problems.len());
}
