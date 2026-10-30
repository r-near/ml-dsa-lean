//! NIST ACVP ML-DSA (FIPS 204) vectors, vendored under tests/data/acvp (see the README there).
//!
//! - sigGen: pure (not preHash), not externalMu, internal + external, deterministic + hedged. Exact signature bytes.
//! - keyGen / sigVer: parsing is tested now; the runners are `#[ignore]`d until `keygen::keygen_internal` and
//!   `verify::verify_internal` exist (see the TODO markers below).
use flate2::read::GzDecoder;
use ml_dsa_verified::params::{self, Params, ML_DSA_44, ML_DSA_65, ML_DSA_87};
use serde::Deserialize;
use std::collections::BTreeMap;
use std::io::Read;

#[derive(Deserialize)]
struct File {
    #[serde(rename = "testGroups")]
    groups: Vec<Group>,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "tgId")]
    tg_id: u32,
    #[serde(rename = "parameterSet")]
    parameter_set: String,
    #[serde(default)]
    deterministic: Option<bool>,
    #[serde(rename = "signatureInterface", default)]
    interface: Option<String>,
    #[serde(rename = "preHash", default)]
    pre_hash: Option<String>,
    #[serde(rename = "externalMu", default)]
    external_mu: bool,
    tests: Vec<Case>,
}

#[derive(Deserialize)]
struct Case {
    #[serde(rename = "tcId")]
    tc_id: serde_json::Value,
    seed: Option<String>,
    pk: Option<String>,
    sk: Option<String>,
    message: Option<String>,
    mu: Option<String>,
    context: Option<String>,
    rnd: Option<String>,
    signature: Option<String>,
    #[serde(rename = "testPassed")]
    test_passed: Option<bool>,
    reason: Option<String>,
}

fn load(name: &str) -> File {
    let path = format!("{}/tests/data/acvp/{name}.json.gz", env!("CARGO_MANIFEST_DIR"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut json = String::new();
    GzDecoder::new(&bytes[..]).read_to_string(&mut json).unwrap();
    serde_json::from_str(&json).unwrap_or_else(|e| panic!("{name}: {e}"))
}

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

fn hex_field(f: &Option<String>, what: &str, c: &Case) -> Vec<u8> {
    unhex(f.as_deref().unwrap_or_else(|| panic!("tcId {}: missing {what}", c.tc_id)))
}

fn params_of(set: &str) -> Params {
    match set {
        "ML-DSA-44" => ML_DSA_44,
        "ML-DSA-65" => ML_DSA_65,
        "ML-DSA-87" => ML_DSA_87,
        _ => panic!("unknown parameter set {set}"),
    }
}

/// pk length: 32 + 320 * K (t1 packs 10 bits per coefficient).
fn pk_len(p: &Params) -> usize {
    32 + 320 * p.k
}

/// M′ prefix for the external pure interface: 0 ‖ |ctx| ‖ ctx.
fn external_prefix(ctx: &[u8]) -> Vec<u8> {
    assert!(ctx.len() <= 255);
    let mut v = vec![0u8, ctx.len() as u8];
    v.extend_from_slice(ctx);
    v
}

fn sign_for(p: &Params, sk: &[u8], prefix: &[u8], m: &[u8], rnd: &[u8; 32]) -> Option<Vec<u8>> {
    use ml_dsa_verified::sign::sign_internal;
    let mut sig = vec![0u8; params::sig_len(p)];
    let ok = match p.k {
        4 => sign_internal::<4, 4>(p, sk, prefix, m, rnd, &mut sig),
        6 => sign_internal::<6, 5>(p, sk, prefix, m, rnd, &mut sig),
        8 => sign_internal::<8, 7>(p, sk, prefix, m, rnd, &mut sig),
        _ => unreachable!(),
    };
    ok.then_some(sig)
}

#[derive(Default)]
struct Tally {
    passed: usize,
    skipped: BTreeMap<&'static str, usize>,
}

#[test]
fn sig_gen() {
    let file = load("sigGen");
    // key: (parameter set, interface, deterministic)
    let mut tallies: BTreeMap<(String, String, bool), Tally> = BTreeMap::new();
    let mut failures = Vec::new();
    for g in &file.groups {
        let iface = g.interface.clone().expect("interface");
        let det = g.deterministic.expect("deterministic");
        let pre = g.pre_hash.as_deref().expect("preHash");
        let t = tallies.entry((g.parameter_set.clone(), iface.clone(), det)).or_default();
        let skip = if pre == "preHash" {
            Some("preHash (HashML-DSA not implemented)")
        } else if g.external_mu {
            Some("externalMu (not implemented)")
        } else {
            None
        };
        if let Some(reason) = skip {
            *t.skipped.entry(reason).or_default() += g.tests.len();
            continue;
        }
        let p = params_of(&g.parameter_set);
        for c in &g.tests {
            let sk = hex_field(&c.sk, "sk", c);
            let msg = hex_field(&c.message, "message", c);
            let want = hex_field(&c.signature, "signature", c);
            assert_eq!(sk.len(), params::sk_len(&p), "tcId {} sk length", c.tc_id);
            let prefix = match iface.as_str() {
                "internal" => Vec::new(), // message is M′ directly
                "external" => external_prefix(&hex_field(&c.context, "context", c)),
                other => panic!("unknown interface {other}"),
            };
            let rnd: [u8; 32] = if det {
                [0u8; 32]
            } else {
                hex_field(&c.rnd, "rnd", c).try_into().expect("rnd is 32 bytes")
            };
            let got = sign_for(&p, &sk, &prefix, &msg, &rnd);
            if got.as_deref() == Some(&want[..]) {
                t.passed += 1;
            } else {
                failures.push(format!(
                    "{} {iface} det={det} tgId {} tcId {}: {}",
                    g.parameter_set,
                    g.tg_id,
                    c.tc_id,
                    if got.is_none() { "sign returned false (κ budget)" } else { "signature mismatch" }
                ));
            }
        }
    }
    println!("{:<10} {:<9} {:<13} {:>6}  skipped", "set", "interface", "mode", "passed");
    let mut per_set: BTreeMap<String, usize> = BTreeMap::new();
    for ((set, iface, det), t) in &tallies {
        let skipped: Vec<String> = t.skipped.iter().map(|(r, n)| format!("{n} {r}")).collect();
        println!(
            "{set:<10} {iface:<9} {:<13} {:>6}  {}",
            if *det { "deterministic" } else { "hedged" },
            t.passed,
            skipped.join("; ")
        );
        *per_set.entry(set.clone()).or_default() += t.passed;
    }
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
    for set in ["ML-DSA-44", "ML-DSA-65", "ML-DSA-87"] {
        assert!(per_set.get(set).copied().unwrap_or(0) > 0, "no sigGen cases ran for {set}");
    }
    for ((set, iface, det), t) in &tallies {
        assert!(t.passed > 0, "no sigGen cases ran for {set} {iface} det={det}");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Parsing tests (run now) and runners for keyGen / sigVer (ignored until the functions exist)
// ---------------------------------------------------------------------------------------------------------------

#[test]
fn vectors_parse() {
    let kg = load("keyGen");
    assert_eq!(kg.groups.len(), 3);
    for g in &kg.groups {
        let p = params_of(&g.parameter_set);
        assert_eq!(g.tests.len(), 25);
        for c in &g.tests {
            assert_eq!(hex_field(&c.seed, "seed", c).len(), 32);
            assert_eq!(hex_field(&c.pk, "pk", c).len(), pk_len(&p));
            assert_eq!(hex_field(&c.sk, "sk", c).len(), params::sk_len(&p));
        }
    }

    let sg = load("sigGen");
    assert_eq!(sg.groups.len(), 24);
    assert_eq!(sg.groups.iter().map(|g| g.tests.len()).sum::<usize>(), 120);
    for g in &sg.groups {
        let p = params_of(&g.parameter_set);
        for c in &g.tests {
            assert_eq!(hex_field(&c.pk, "pk", c).len(), pk_len(&p));
            assert_eq!(hex_field(&c.sk, "sk", c).len(), params::sk_len(&p));
            assert_eq!(hex_field(&c.signature, "signature", c).len(), params::sig_len(&p));
            assert_eq!(c.rnd.is_some(), g.deterministic == Some(false));
            if g.external_mu {
                assert_eq!(hex_field(&c.mu, "mu", c).len(), 64);
            } else {
                hex_field(&c.message, "message", c);
            }
            if g.interface.as_deref() == Some("external") {
                assert!(hex_field(&c.context, "context", c).len() <= 255);
            }
        }
    }

    let sv = load("sigVer");
    assert_eq!(sv.groups.len(), 12);
    assert_eq!(sv.groups.iter().map(|g| g.tests.len()).sum::<usize>(), 60);
    let mut accepts = 0;
    for g in &sv.groups {
        let p = params_of(&g.parameter_set);
        assert!(g.tests.iter().any(|c| c.test_passed == Some(true)), "group {} has no valid case", g.tg_id);
        for c in &g.tests {
            assert_eq!(hex_field(&c.pk, "pk", c).len(), pk_len(&p));
            assert_eq!(hex_field(&c.signature, "signature", c).len(), params::sig_len(&p));
            assert!(c.reason.is_some());
            accepts += c.test_passed.expect("testPassed") as usize;
        }
    }
    assert_eq!(accepts, 12);
}

/// TODO(wave 2): wire `keygen::keygen_internal`. Assumed signature (adjust the call below if it differs):
/// `keygen_internal::<K, L>(p: &Params, xi: &[u8; 32], pk: &mut [u8], sk: &mut [u8])`.
fn keygen_for(p: &Params, xi: &[u8; 32]) -> (Vec<u8>, Vec<u8>) {
    let (mut _pk, mut _sk) = (vec![0u8; pk_len(p)], vec![0u8; params::sk_len(p)]);
    let _ = xi;
    // match p.k {
    //     4 => ml_dsa_verified::keygen::keygen_internal::<4, 4>(p, xi, &mut _pk, &mut _sk),
    //     6 => ml_dsa_verified::keygen::keygen_internal::<6, 5>(p, xi, &mut _pk, &mut _sk),
    //     8 => ml_dsa_verified::keygen::keygen_internal::<8, 7>(p, xi, &mut _pk, &mut _sk),
    //     _ => unreachable!(),
    // }
    // (_pk, _sk)
    unimplemented!("TODO: keygen::keygen_internal (Algorithm 6) does not exist yet")
}

#[test]
#[ignore = "TODO: needs keygen::keygen_internal; wire it in keygen_for"]
fn key_gen() {
    let file = load("keyGen");
    let mut n = 0;
    for g in &file.groups {
        let p = params_of(&g.parameter_set);
        for c in &g.tests {
            let xi: [u8; 32] = hex_field(&c.seed, "seed", c).try_into().unwrap();
            let (pk, sk) = keygen_for(&p, &xi);
            assert_eq!(pk, hex_field(&c.pk, "pk", c), "{} tcId {} pk", g.parameter_set, c.tc_id);
            assert_eq!(sk, hex_field(&c.sk, "sk", c), "{} tcId {} sk", g.parameter_set, c.tc_id);
            n += 1;
        }
        println!("{}: {} keyGen cases passed", g.parameter_set, g.tests.len());
    }
    assert_eq!(n, 75);
}

/// TODO(wave 2): wire `verify::verify_internal`. Assumed signature (adjust the call below if it differs):
/// `verify_internal::<K, L>(p: &Params, pk: &[u8], m_prefix: &[u8], m: &[u8], sig: &[u8]) -> bool`.
fn verify_for(p: &Params, pk: &[u8], prefix: &[u8], m: &[u8], sig: &[u8]) -> bool {
    let _ = (p, pk, prefix, m, sig);
    // match p.k {
    //     4 => ml_dsa_verified::verify::verify_internal::<4, 4>(p, pk, prefix, m, sig),
    //     6 => ml_dsa_verified::verify::verify_internal::<6, 5>(p, pk, prefix, m, sig),
    //     8 => ml_dsa_verified::verify::verify_internal::<8, 7>(p, pk, prefix, m, sig),
    //     _ => unreachable!(),
    // }
    unimplemented!("TODO: verify::verify_internal (Algorithm 8) does not exist yet")
}

#[test]
#[ignore = "TODO: needs verify::verify_internal; wire it in verify_for"]
fn sig_ver() {
    let file = load("sigVer");
    // key: (set, interface); value: (passed, skipped)
    let mut tally: BTreeMap<(String, String), (usize, usize)> = BTreeMap::new();
    let mut failures = Vec::new();
    for g in &file.groups {
        let iface = g.interface.clone().expect("interface");
        let e = tally.entry((g.parameter_set.clone(), iface.clone())).or_default();
        if g.pre_hash.as_deref() == Some("preHash") || g.external_mu {
            e.1 += g.tests.len(); // HashML-DSA / external-μ not implemented
            continue;
        }
        let p = params_of(&g.parameter_set);
        for c in &g.tests {
            let pk = hex_field(&c.pk, "pk", c);
            let msg = hex_field(&c.message, "message", c);
            let sig = hex_field(&c.signature, "signature", c);
            let prefix = if iface == "internal" { Vec::new() } else { external_prefix(&hex_field(&c.context, "context", c)) };
            let got = verify_for(&p, &pk, &prefix, &msg, &sig);
            if got == c.test_passed.expect("testPassed") {
                e.0 += 1;
            } else {
                failures.push(format!("{} {iface} tcId {} ({:?}): got {got}", g.parameter_set, c.tc_id, c.reason));
            }
        }
    }
    for ((set, iface), (pass, skip)) in &tally {
        println!("{set} {iface}: {pass} passed, {skip} skipped");
        assert!(*pass > 0, "no sigVer cases ran for {set} {iface}");
    }
    assert!(failures.is_empty(), "{} failures:\n{}", failures.len(), failures.join("\n"));
}
