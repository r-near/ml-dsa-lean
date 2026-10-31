//! Question 2: runtime and compile-time dispatch. This crate is std (not no_std) so that
//! `is_x86_feature_detected!` is available; each variant is its own root so one failure does not hide the others.
#![allow(unused)]

fn body(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    let mut c = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        c[i] = a[i].wrapping_add(b[i]);
        i += 1;
    }
    c
}

#[target_feature(enable = "avx2")]
fn body_avx2(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    body(a, b)
}

/// 2a. std runtime detection.
pub fn dispatch_std(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    if std::is_x86_feature_detected!("avx2") {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}

/// 2b. no_std-compatible detection with `core::arch::x86_64::__cpuid_count` (leaf 7, EBX bit 5 = AVX2).
/// (A complete check also needs OSXSAVE and XGETBV so the OS saves YMM state; omitted in this extraction probe.)
pub fn dispatch_cpuid(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    let r = unsafe { core::arch::x86_64::__cpuid_count(7, 0) };
    if (r.ebx >> 5) & 1 == 1 {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}

/// 2c. Compile-time selection with `cfg`: the other arm does not exist for rustc, hence not for Charon.
#[cfg(target_feature = "avx2")]
pub fn dispatch_cfg(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    unsafe { body_avx2(a, b) }
}
#[cfg(not(target_feature = "avx2"))]
pub fn dispatch_cfg(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    body(a, b)
}

/// 2d. `cfg!` as a constant inside ordinary code: both arms are type-checked, the condition is a literal.
pub fn dispatch_cfg_bang(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    if cfg!(target_feature = "avx2") {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}

/// 2e. The pattern already used by this crate (`barrier_u64` in src/field.rs): under `cfg(miri)` -- which is how
/// extraction is run -- the extracted function is the portable one; the shipped build has the dispatch.
#[cfg(miri)]
pub fn dispatch_miri(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    body(a, b)
}
#[cfg(not(miri))]
pub fn dispatch_miri(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    if std::is_x86_feature_detected!("avx2") {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}

/// 2f. Opaque predicate in the SymCrypt style: a plain function whose body is hidden from the extractor with
/// `#[cfg(not(miri))]`/`#[cfg(miri)]` twins would also work; here the extraction-visible twin is `extern`-like
/// via a function-pointer-free `fn has_avx2() -> bool` that the extractor sees without a body (see 2g).
pub fn has_avx2() -> bool {
    std::is_x86_feature_detected!("avx2")
}
pub fn dispatch_pred(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    if has_avx2() {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}

/// 2g. Cached detection through an atomic static (what a no_std shim usually does).
use core::sync::atomic::{AtomicU8, Ordering};
static CACHE: AtomicU8 = AtomicU8::new(0);
pub fn dispatch_atomic(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    let mut s = CACHE.load(Ordering::Relaxed);
    if s == 0 {
        let r = unsafe { core::arch::x86_64::__cpuid_count(7, 0) };
        s = if (r.ebx >> 5) & 1 == 1 { 2 } else { 1 };
        CACHE.store(s, Ordering::Relaxed);
    }
    if s == 2 {
        unsafe { body_avx2(a, b) }
    } else {
        body(a, b)
    }
}
