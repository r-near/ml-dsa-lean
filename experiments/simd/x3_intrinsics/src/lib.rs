//! Question 3: do `core::arch::x86_64` intrinsics extract, and what does Aeneas emit for them?
#![no_std]
#![allow(unused)]

use core::arch::x86_64::*;

/// 3a. Simplest: add two vectors.
#[target_feature(enable = "avx2")]
pub fn vadd(a: __m256i, b: __m256i) -> __m256i {
    _mm256_add_epi32(a, b)
}

/// 3b. A butterfly-shaped composition: load, mullo, sub, add, store (unsafe pointer intrinsics).
#[target_feature(enable = "avx2")]
pub unsafe fn bfly(p: &mut [i32; 16]) {
    unsafe {
        let a = _mm256_loadu_si256(p.as_ptr() as *const __m256i);
        let b = _mm256_loadu_si256(p.as_ptr().add(8) as *const __m256i);
        let t = _mm256_mullo_epi32(b, _mm256_set1_epi32(3));
        let lo = _mm256_add_epi32(a, t);
        let hi = _mm256_sub_epi32(a, t);
        _mm256_storeu_si256(p.as_mut_ptr() as *mut __m256i, lo);
        _mm256_storeu_si256(p.as_mut_ptr().add(8) as *mut __m256i, hi);
    }
}

/// 3c. Intrinsics with an immediate const-generic argument.
#[target_feature(enable = "avx2")]
pub fn shuf(a: __m256i, b: __m256i) -> __m256i {
    let x = _mm256_shuffle_epi32::<0xB1>(a);
    let y = _mm256_blend_epi32::<0xAA>(x, b);
    _mm256_permute4x64_epi64::<0x4E>(y)
}

/// 3d. The signed 32x32 -> 64 multiply used by Montgomery reduction.
#[target_feature(enable = "avx2")]
pub fn mulw(a: __m256i, b: __m256i) -> __m256i {
    _mm256_mul_epi32(a, b)
}

/// 3e. Shifts and masks.
#[target_feature(enable = "avx2")]
pub fn shifts(a: __m256i) -> __m256i {
    let s = _mm256_srli_epi64::<32>(a);
    let m = _mm256_and_si256(s, _mm256_set1_epi32(0x7fffff));
    _mm256_srai_epi32::<31>(m)
}

/// 3f. Not an intrinsic: portable SIMD-free baseline for the type-level comparison (what does an `__m256i` look like
/// to Aeneas when it only flows through?).
pub fn passthrough(a: __m256i) -> __m256i {
    a
}
