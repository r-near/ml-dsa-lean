//! The usage example in README.md must compile and run. The test holds the same code as the README block and
//! checks that the README still contains it verbatim, so the two cannot drift apart.

const README: &str = include_str!("../README.md");

const EXAMPLE: &str = r#"use ml_dsa_lean::api::{keygen_65, sign_65, verify_65};

fn main() {
    // The caller supplies all randomness: a 32-byte seed for key generation and 32 bytes for signing
    // (32 zero bytes make signing deterministic). Use a cryptographically secure generator in real code;
    // the all-zero values here are for the example only.
    let seed = [0u8; 32];
    let rnd = [0u8; 32];

    let (pk, sk) = keygen_65(&seed);

    // `ctx` is the FIPS 204 context string (at most 255 bytes); `sign_65` returns `None` if it is longer.
    let ctx = b"example";
    let sig = sign_65(&sk, b"message", ctx, &rnd).expect("context string is at most 255 bytes");

    assert!(verify_65(&pk, b"message", ctx, &sig));
    assert!(!verify_65(&pk, b"another message", ctx, &sig));
}"#;

#[test]
fn readme_contains_the_example() {
    assert!(
        README.contains(EXAMPLE),
        "the rust block in README.md differs from EXAMPLE in tests/readme_example.rs"
    );
}

#[test]
fn readme_example_runs() {
    use ml_dsa_lean::api::{keygen_65, sign_65, verify_65};

    let seed = [0u8; 32];
    let rnd = [0u8; 32];
    let (pk, sk) = keygen_65(&seed);
    let ctx = b"example";
    let sig = sign_65(&sk, b"message", ctx, &rnd).expect("context string is at most 255 bytes");
    assert!(verify_65(&pk, b"message", ctx, &sig));
    assert!(!verify_65(&pk, b"another message", ctx, &sig));
}
