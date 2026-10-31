//! Records the build settings in the binary (printed in the first lines of every run).
fn main() {
    println!("cargo::rerun-if-env-changed=PROFILE");
    println!("cargo::rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo::rustc-env=BENCH_OPT={}", std::env::var("OPT_LEVEL").unwrap_or_default());
    let flags = std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default().replace('\u{1f}', " ");
    println!("cargo::rustc-env=BENCH_RUSTFLAGS=[{}]", if flags.is_empty() { "none".into() } else { flags });
}
