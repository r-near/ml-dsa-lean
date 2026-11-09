//! Writes the test vectors that bench/emu/fw embeds: for each parameter set a public key, a message and a valid signature
//! (fixed seeds), as Rust statics. Usage: emu-gen OUT.rs
use ml_dsa_lean::api;
use std::fmt::Write;

fn arr(out: &mut String, name: &str, b: &[u8]) {
    writeln!(out, "pub static {name}: [u8; {}] = [", b.len()).unwrap();
    for c in b.chunks(32) {
        out.push_str("    ");
        for x in c {
            write!(out, "{x},").unwrap();
        }
        out.push('\n');
    }
    out.push_str("];\n");
}

fn main() {
    let path = std::env::args().nth(1).expect("OUT.rs");
    let mut out = String::new();
    let xi = [0x11u8; 32];
    let rnd = [0u8; 32];
    let msg = b"emu verify message: 32 bytes....".to_vec();
    arr(&mut out, "MSG", &msg);
    let (pk, sk) = api::keygen_44(&xi);
    let sig = api::sign_44(&sk, &msg, &[], &rnd).unwrap();
    assert!(api::verify_44(&pk, &msg, &[], &sig));
    arr(&mut out, "PK44", &pk);
    arr(&mut out, "SIG44", &sig);
    let (pk, sk) = api::keygen_65(&xi);
    let sig = api::sign_65(&sk, &msg, &[], &rnd).unwrap();
    assert!(api::verify_65(&pk, &msg, &[], &sig));
    arr(&mut out, "PK65", &pk);
    arr(&mut out, "SIG65", &sig);
    let (pk, sk) = api::keygen_87(&xi);
    let sig = api::sign_87(&sk, &msg, &[], &rnd).unwrap();
    assert!(api::verify_87(&pk, &msg, &[], &sig));
    arr(&mut out, "PK87", &pk);
    arr(&mut out, "SIG87", &sig);
    std::fs::write(path, out).unwrap();
}
