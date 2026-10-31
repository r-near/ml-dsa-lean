//! Question 1: does `#[target_feature(enable = "avx2")]` extract, and what happens at call sites?
#![no_std]

/// The body, shared. Plain loop in the crate's style.
fn add_body(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    let mut c = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        c[i] = a[i].wrapping_add(b[i]);
        i += 1;
    }
    c
}

/// 1a. A safe fn with the attribute (Rust 2024 / target_feature 1.1).
#[target_feature(enable = "avx2")]
pub fn add_avx2(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    add_body(a, b)
}

/// Baseline twin of 1a (same body, no attribute).
pub fn add_plain(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    add_body(a, b)
}

/// 1b. Call from a function without the feature: needs `unsafe`.
pub fn call_from_plain(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    unsafe { add_avx2(a, b) }
}

/// 1c. Call from a function that has the feature: safe call.
#[target_feature(enable = "avx2")]
pub fn call_from_tf(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    add_avx2(a, b)
}

/// 1d. `unsafe fn` with the attribute (the pre-1.86 shape).
#[target_feature(enable = "avx2")]
pub unsafe fn add_avx2_unsafe(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    add_body(a, b)
}

/// 1e. Const-generic body instantiated inside a target_feature fn: this is how a single extracted body
/// could be compiled twice. The generic fn itself carries no attribute and inlines into the caller.
#[inline(always)]
fn sum_n<const N: usize>(a: &[u32; N]) -> u32 {
    let mut s = 0u32;
    let mut i = 0;
    while i < N {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

#[target_feature(enable = "avx2")]
pub fn sum_avx2(a: &[u32; 64]) -> u32 {
    sum_n::<64>(a)
}

pub fn sum_plain(a: &[u32; 64]) -> u32 {
    sum_n::<64>(a)
}

/// 1f. Two feature names in one attribute, plus `#[inline]`.
#[inline]
#[target_feature(enable = "avx2,bmi2")]
pub fn add_avx2_bmi2(a: &[u32; 8], b: &[u32; 8]) -> [u32; 8] {
    add_body(a, b)
}
