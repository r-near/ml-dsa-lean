//! Builds mldsa-native (vendored, pinned; see README) twice: a portable C build and, on x86_64, an AVX2 build
//! with the native arithmetic and Keccak backends. Both are multi-level (ML-DSA-44/65/87) single translation
//! units with distinct namespace prefixes, so they link into one binary. The environment variable
//! `XC_NO_AVX2=1` skips the AVX2 build.
use std::env;

fn base(name: &str) -> cc::Build {
    let mut b = cc::Build::new();
    b.include("csrc")
        .include("vendor/mldsa-native/mldsa")
        .opt_level(3)
        .flag_if_supported("-std=c11")
        .flag_if_supported("-fno-strict-aliasing")
        .warnings(false)
        .cargo_warnings(false);
    // Instrument the C code for libFuzzer coverage when building a fuzz target (clang only).
    if env::var("CARGO_ENCODED_RUSTFLAGS").map(|f| f.contains("fuzzing")).unwrap_or(false) && env::var("XC_NO_COV").is_err() {
        b.compiler("clang");
        b.flag("-fsanitize-coverage=inline-8bit-counters,pc-table,trace-cmp");
        println!("cargo::warning=mldsa-native {name}: coverage instrumentation on");
    }
    b
}

fn main() {
    println!("cargo::rerun-if-changed=csrc");
    println!("cargo::rerun-if-changed=vendor");
    println!("cargo::rerun-if-env-changed=XC_NO_AVX2");
    println!("cargo::rerun-if-env-changed=XC_NO_COV");
    println!("cargo::rustc-check-cfg=cfg(xc_avx2)");

    base("portable").file("csrc/xc_portable.c").compile("xc_mldsa_portable");

    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if arch == "x86_64" && os == "linux" && env::var("XC_NO_AVX2").is_err() {
        let mut b = base("avx2");
        b.file("csrc/xc_avx2.c")
            .file("csrc/xc_avx2_asm.S")
            .define("MLD_FORCE_X86_64", None)
            .flag("-mavx2")
            .flag("-mbmi2");
        b.compile("xc_mldsa_avx2");
        println!("cargo::rustc-cfg=xc_avx2");
    }
}
