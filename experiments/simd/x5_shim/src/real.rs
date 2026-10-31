//! The same operation names bound to the real `core::arch::x86_64` intrinsics. Each wrapper is `#[inline(always)]` and
//! is only ever inlined into a `#[target_feature(enable = "avx2")]` caller (the kernel entry points at the bottom).
//! Compiled only with `--features real` on x86-64; the extracted (proved) crate never sees this file.

use core::arch::x86_64::*;

pub type M256 = __m256i;

// SAFETY (all wrappers): these are only inlined into functions compiled with AVX2 enabled and executed after the
// run-time AVX2 check of the caller; the memory intrinsics are bounds-checked by slicing first.
#[inline(always)]
pub fn set1_epi32(x: u32) -> M256 {
    unsafe { _mm256_set1_epi32(x as i32) }
}
#[inline(always)]
pub fn setr_epi32(e0: u32, e1: u32, e2: u32, e3: u32, e4: u32, e5: u32, e6: u32, e7: u32) -> M256 {
    unsafe { _mm256_setr_epi32(e0 as i32, e1 as i32, e2 as i32, e3 as i32, e4 as i32, e5 as i32, e6 as i32, e7 as i32) }
}
#[inline(always)]
pub fn add_epi32(a: M256, b: M256) -> M256 {
    unsafe { _mm256_add_epi32(a, b) }
}
#[inline(always)]
pub fn sub_epi32(a: M256, b: M256) -> M256 {
    unsafe { _mm256_sub_epi32(a, b) }
}
#[inline(always)]
pub fn mullo_epi32(a: M256, b: M256) -> M256 {
    unsafe { _mm256_mullo_epi32(a, b) }
}
#[inline(always)]
pub fn mul_epi32(a: M256, b: M256) -> M256 {
    unsafe { _mm256_mul_epi32(a, b) }
}
#[inline(always)]
pub fn and_si256(a: M256, b: M256) -> M256 {
    unsafe { _mm256_and_si256(a, b) }
}
#[inline(always)]
pub fn srli_epi64<const IMM: i32>(a: M256) -> M256 {
    unsafe { _mm256_srli_epi64::<IMM>(a) }
}
#[inline(always)]
pub fn srai_epi32<const IMM: i32>(a: M256) -> M256 {
    unsafe { _mm256_srai_epi32::<IMM>(a) }
}
#[inline(always)]
pub fn cmpgt_epi32(a: M256, b: M256) -> M256 {
    unsafe { _mm256_cmpgt_epi32(a, b) }
}
#[inline(always)]
pub fn shuffle_epi32<const MASK: i32>(a: M256) -> M256 {
    unsafe { _mm256_shuffle_epi32::<MASK>(a) }
}
#[inline(always)]
pub fn permute4x64_epi64<const IMM: i32>(a: M256) -> M256 {
    unsafe { _mm256_permute4x64_epi64::<IMM>(a) }
}
#[inline(always)]
pub fn blend_epi32<const IMM: i32>(a: M256, b: M256) -> M256 {
    unsafe { _mm256_blend_epi32::<IMM>(a, b) }
}
#[inline(always)]
pub fn permutevar8x32_epi32(a: M256, idx: M256) -> M256 {
    unsafe { _mm256_permutevar8x32_epi32(a, idx) }
}
#[inline(always)]
pub fn unpacklo_epi64(a: M256, b: M256) -> M256 {
    unsafe { _mm256_unpacklo_epi64(a, b) }
}
#[inline(always)]
pub fn unpackhi_epi64(a: M256, b: M256) -> M256 {
    unsafe { _mm256_unpackhi_epi64(a, b) }
}
#[inline(always)]
pub fn permute2x128_si256<const IMM: i32>(a: M256, b: M256) -> M256 {
    unsafe { _mm256_permute2x128_si256::<IMM>(a, b) }
}
#[inline(always)]
pub fn loadu_si256(mem: &[u32; 256], at: usize) -> M256 {
    let s = &mem[at..at + 8];
    unsafe { _mm256_loadu_si256(s.as_ptr() as *const __m256i) }
}
#[inline(always)]
pub fn storeu_si256(mem: &mut [u32; 256], at: usize, v: M256) {
    let s = &mut mem[at..at + 8];
    unsafe { _mm256_storeu_si256(s.as_mut_ptr() as *mut __m256i, v) }
}

/// Lanes of a real register, for the differential tests.
#[inline(always)]
pub fn to_lanes(v: M256) -> [u32; 8] {
    // SAFETY: __m256i and [u32; 8] have the same size; every bit pattern is valid for both.
    unsafe { core::mem::transmute(v) }
}
#[inline(always)]
pub fn from_lanes(a: [u32; 8]) -> M256 {
    // SAFETY: as above.
    unsafe { core::mem::transmute(a) }
}
