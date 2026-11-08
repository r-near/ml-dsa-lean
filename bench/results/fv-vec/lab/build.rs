// Copies ref_keccak4.rs (the fast-verify branch's src/keccak4.rs: Lanes4, Shim4, Avx2) with `round` made public and the inner docs stripped.
use std::{env, fs, path::PathBuf};
fn main() {
    let src = PathBuf::from("ref_keccak4.rs");
    println!("cargo:rerun-if-changed={}", src.display());
    let t = fs::read_to_string(&src).unwrap();
    let t: String = t
        .lines()
        .filter(|l| !l.starts_with("//!"))
        .map(|l| l.replacen("\nfn round<", "pub fn round<", 1).replacen("fn round<L: Lanes4>", "pub fn round<L: Lanes4>", 1))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(PathBuf::from(env::var("OUT_DIR").unwrap()).join("k4.rs"), t).unwrap();
}
