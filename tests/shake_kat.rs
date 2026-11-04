//! Cross-checks `keccak::Shake` against the known-answer hex strings in the Lean spec tests
//! (`lean/SpecTests/Keccak.lean`, constants `exp_<hash>_<message>_<outputBytes>`): one source of truth for
//! the expected outputs, checked by both the Rust implementation and the Lean specification.

use ml_dsa_lean::keccak::Shake;

const LEAN: &str = include_str!("../lean/SpecTests/Keccak.lean");

fn message(token: &str) -> Vec<u8> {
    if token == "empty" {
        Vec::new()
    } else if token == "abc" {
        b"abc".to_vec()
    } else if let Some(n) = token.strip_prefix("a3x") {
        vec![0xA3; n.parse().unwrap()]
    } else if let Some(n) = token.strip_prefix("seq") {
        (0..n.parse::<usize>().unwrap()).map(|i| (i % 251) as u8).collect()
    } else {
        panic!("unknown message token {token}");
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[test]
fn shake_matches_lean_kats() {
    let mut checked = 0;
    for line in LEAN.lines() {
        let Some(rest) = line.strip_prefix("def exp_") else { continue };
        let (name, tail) = rest.split_once(" : String := \"").expect("malformed def");
        let expected = tail.strip_suffix('"').expect("malformed hex");
        let parts: Vec<&str> = name.split('_').collect();
        assert_eq!(parts.len(), 3, "bad name {name}");
        let msg = message(parts[1]);
        let d: usize = parts[2].parse().unwrap();
        let mut sh = match parts[0] {
            "shake128" => Shake::shake128(),
            "shake256" => Shake::shake256(),
            h => panic!("unknown hash {h}"),
        };
        sh.absorb(&msg);
        sh.finalize();
        let mut out = vec![0u8; d];
        sh.squeeze(&mut out);
        assert_eq!(hex(&out), expected, "mismatch for {name}");
        checked += 1;
    }
    assert!(checked >= 30, "only {checked} cases found");
}

#[test]
fn shake_incremental_squeeze_matches_one_shot() {
    let msg = message("seq300");
    for make in [Shake::shake128, Shake::shake256] {
        let mut a = make();
        a.absorb(&msg);
        a.finalize();
        let mut whole = vec![0u8; 700];
        a.squeeze(&mut whole);
        let mut b = make();
        b.absorb(&msg);
        b.finalize();
        let mut parts = Vec::new();
        for n in [1usize, 167, 168, 5, 359] {
            let mut p = vec![0u8; n];
            b.squeeze(&mut p);
            parts.extend(p);
        }
        assert_eq!(parts, whole);
    }
}
