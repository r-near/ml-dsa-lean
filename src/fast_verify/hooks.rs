//! Test and bench entry points (feature `internals`, `avx2`, x86_64, not Miri): the AVX2 compilations of the 4-way
//! pieces, each behind its own CPU check. They are never reached from `api`. The production wrappers in `dispatch.rs`
//! are called from here as well (`verify_internal_avx2_or_none`, `prepare_vk_x4_avx2_or_none`), so the tests compare
//! exactly the compiled code the API runs with the scalar functions.
//!
//! The production wrappers are reached through `cpu::avx2()` (the token), so they need no `unsafe` here. The other
//! `#[target_feature]` functions in this file are reached only through the functions below, each of which checks
//! `has_avx2` and returns `None` (or `false`) without AVX2.

use super::dispatch;
use crate::cpu::{self, has_avx2};
use crate::params::Params;
use crate::sampling::{expand_a_into_x4, expand_a_tr_into_x4, expand_a_x4, rej_ntt_poly_x4};
use crate::verify::{self, PreparedVk};

/// What `api::verify_*` run: `verify_internal_with(cpu::avx2(), ..)` (the AVX2 wrapper on a CPU with AVX2, else the scalar function).
pub fn verify_internal_dispatched<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    super::verify_internal_with::<K, L>(crate::cpu::avx2(), p, pk, m_prefix, m, sig)
}

/// `dispatch::verify_internal_on`, the entry point `fast_verify::verify_internal_with(Some(_), ..)` runs, or `None` without AVX2.
pub fn verify_internal_avx2_or_none<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> Option<bool> {
    let t = cpu::avx2()?;
    Some(dispatch::verify_internal_on::<K, L>(t, p, pk, m_prefix, m, sig))
}

/// `dispatch::verify_prepared_on`, the entry point `verify_prepared_internal_with(Some(_), ..)` runs, or `None` without AVX2.
pub fn verify_prepared_avx2_or_none<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> Option<bool> {
    let t = cpu::avx2()?;
    Some(dispatch::verify_prepared_on::<K, L>(t, p, vk, m_prefix, m, sig))
}

/// Whether the AVX2 `prepare_vk` returns exactly the scalar one (Â, NTT(t1 · 2^d) and tr); `None` without AVX2. The
/// `PreparedVk` fields are crate-private, so the comparison lives here.
pub fn prepare_vk_avx2_matches_scalar<const K: usize, const L: usize>(pk: &[u8]) -> Option<bool> {
    let t = cpu::avx2()?;
    let fast = dispatch::prepare_vk_on::<K, L>(t, pk);
    let slow = verify::prepare_vk::<K, L>(pk);
    Some(fast.a_hat == slow.a_hat && fast.t1_2d_hat == slow.t1_2d_hat && fast.tr == slow.tr)
}

/// `dispatch::prepare_vk_on`, or `None` without AVX2.
pub fn prepare_vk_x4_avx2_or_none<const K: usize, const L: usize>(pk: &[u8]) -> Option<PreparedVk<K, L>> {
    cpu::avx2().map(|t| dispatch::prepare_vk_on::<K, L>(t, pk))
}

#[target_feature(enable = "avx2")]
fn rej_ntt_poly_x4_avx2(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
    rej_ntt_poly_x4(rho, s, r)
}

#[target_feature(enable = "avx2")]
fn expand_a_x4_avx2<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
    expand_a_x4::<K, L>(rho)
}

#[target_feature(enable = "avx2")]
fn expand_a_into_x4_avx2<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
    expand_a_into_x4::<K, L>(rho, a)
}

#[target_feature(enable = "avx2")]
fn expand_a_tr_into_x4_avx2<const K: usize, const L: usize>(
    rho: &[u8; 32],
    pk: &[u8],
    a: &mut [[[u32; 256]; L]; K],
) -> [u8; 64] {
    expand_a_tr_into_x4::<K, L>(rho, pk, a)
}

/// `sampling::rej_ntt_poly_x4` compiled with AVX2, or `None` without AVX2.
pub fn rej_ntt_poly_x4_avx2_or_none(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> Option<[[u32; 256]; 4]> {
    // SAFETY: `has_avx2` checked CPU and OS support for AVX2 (here and in the three functions below).
    if has_avx2() { Some(unsafe { rej_ntt_poly_x4_avx2(rho, s, r) }) } else { None }
}

/// `sampling::expand_a_x4` compiled with AVX2, or `None` without AVX2.
pub fn expand_a_x4_avx2_or_none<const K: usize, const L: usize>(rho: &[u8; 32]) -> Option<[[[u32; 256]; L]; K]> {
    if has_avx2() { Some(unsafe { expand_a_x4_avx2::<K, L>(rho) }) } else { None }
}

/// `sampling::expand_a_into_x4` compiled with AVX2; returns `false` (and leaves `a` alone) without AVX2.
pub fn expand_a_into_x4_avx2_or_false<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) -> bool {
    if has_avx2() {
        unsafe { expand_a_into_x4_avx2::<K, L>(rho, a) };
        true
    } else {
        false
    }
}

/// `sampling::expand_a_tr_into_x4` compiled with AVX2 (ExpandA with `tr = H(pk, 64)` in the fourth lane), or `None` (and `a`
/// left alone) without AVX2.
pub fn expand_a_tr_into_x4_avx2_or_none<const K: usize, const L: usize>(
    rho: &[u8; 32],
    pk: &[u8],
    a: &mut [[[u32; 256]; L]; K],
) -> Option<[u8; 64]> {
    if has_avx2() { Some(unsafe { expand_a_tr_into_x4_avx2::<K, L>(rho, pk, a) }) } else { None }
}
