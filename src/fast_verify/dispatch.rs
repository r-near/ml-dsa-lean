//! The AVX2 dispatch behind `fast_verify.rs`; see the documentation there. Compiled only with the `avx2` feature on
//! x86_64, never under Miri.

use crate::cpu::has_avx2;
use crate::keccak4::avx2::Avx2;
use crate::params::Params;
use crate::verify::{self, PreparedVk};
use crate::verify::{prepare_vk_into_x4, verify_internal_x4};
#[cfg(feature = "internals")]
use crate::sampling::{expand_a_into_x4, expand_a_tr_into_x4, expand_a_x4, rej_ntt_poly_x4};

#[cfg(feature = "internals")]
use core::sync::atomic::{AtomicUsize, Ordering};

/// Number of calls that took the AVX2 path (verify and prepare together). Test builds only (`internals`): lets
/// `tests/fast_verify.rs` show that `api::verify_*` really reached the AVX2 wrapper.
#[cfg(feature = "internals")]
pub static AVX2_CALLS: AtomicUsize = AtomicUsize::new(0);

/// A 32-byte aligned object, for `align_frame` (its contents are never read).
#[allow(dead_code)]
#[repr(align(32))]
struct Align32([u8; 32]);

/// Makes the calling function realign its stack frame to 32 bytes. Call it first in every `#[target_feature(enable =
/// "avx2")]` wrapper below.
///
/// Why: the proved code inlined into a wrapper spills 256-bit vectors (the 25 Keccak lane vectors, the polynomials in the
/// NTT) to stack slots that LLVM places at the frame's 16-byte alignment, and loads and stores them with unaligned
/// instructions. When a slot starts at an address that is 16 mod 32, one access in the frame straddles a 4 KiB page
/// boundary if the frame happens to cover one, and a page-split access costs about 30 cycles on Zen 4 (measured:
/// `bench/results/2026-11-07-p6.md`). The permutation does several such accesses per round, so a call that starts at
/// the wrong stack offset (about one offset in seven) took up to 12 µs longer. A 32-byte aligned local makes LLVM
/// realign the frame (`and rsp, -32`), after which every 32-byte slot and array is 32-byte aligned and no vector access
/// can cross a page or a cache line. `black_box` keeps the local from being optimized away. This is plain safe Rust in
/// code outside the proof; it changes no value and no extracted function (`scripts/check-avx2-inlining.sh` checks that
/// every wrapper instantiation does realign its frame).
#[inline(always)]
fn align_frame() {
    let anchor = Align32([0; 32]);
    core::hint::black_box(&anchor);
}

#[inline(always)]
fn count_avx2_call() {
    #[cfg(feature = "internals")]
    AVX2_CALLS.fetch_add(1, Ordering::Relaxed);
}

/// The 4-way verify body with the AVX2 lane operations. `verify_internal_x4` is `#[inline(always)]` (and so are the
/// kernel and the trait methods below it), so everything that touches an intrinsic is compiled inside this function,
/// with AVX2 enabled.
#[target_feature(enable = "avx2")]
fn verify_internal_avx2<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    align_frame();
    verify_internal_x4::<K, L, Avx2>(p, pk, m_prefix, m, sig)
}

/// The prepared-key verify body with AVX2: `verify::verify_prepared_internal` is `#[inline(always)]` (and so are the
/// decoders and the verify-only arithmetic below it), so the NTTs, the multiply-accumulate rows, UseHint and the packing are
/// compiled inside this function with AVX2 enabled. There is no ExpandA to speed up, so this is the scalar proved function
/// itself, not an `X4` variant.
#[target_feature(enable = "avx2")]
fn verify_prepared_avx2<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    align_frame();
    verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig)
}

/// `verify::prepare_vk_x4` with the 4-way AVX2 lanes, built in place: the key is created as a local that is also the result
/// (so it is the caller's result slot) and `prepare_vk_into_x4` fills it. That is `prepare_vk_x4` itself
/// (`Proofs/FastVerify.lean`: `prepare_vk_into_x4_zero`, `prepare_vk_x4_zeroed_bind`), without the by-value function's
/// 57 KB (ML-DSA-87) matrix local and the copy of it into the result, which glibc runs as `rep movsb` and which is several
/// times slower when the two buffers happen to sit at a distance that is a small multiple of 4 KiB (`bench/results/2026-11-07-p6.md`).
#[target_feature(enable = "avx2")]
fn prepare_vk_avx2<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    align_frame();
    let mut vk = PreparedVk::<K, L>::zeroed();
    prepare_vk_into_x4::<K, L, Avx2>(pk, &mut vk);
    vk
}

/// `verify::verify_internal`, or its 4-way AVX2 version when this CPU has AVX2. Same signature, preconditions and
/// results (`tests/fast_verify.rs`).
pub fn verify_internal<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    if has_avx2() {
        count_avx2_call();
        // SAFETY: `has_avx2` checked CPU and OS support for AVX2 (`cpu.rs`).
        unsafe { verify_internal_avx2::<K, L>(p, pk, m_prefix, m, sig) }
    } else {
        verify::verify_internal::<K, L>(p, pk, m_prefix, m, sig)
    }
}

/// `verify::verify_prepared_internal` (`api::verify_prepared_*`), compiled with AVX2 when this CPU has it. Same signature,
/// preconditions and results (`tests/fast_verify.rs`); it is the same proved function, so no 4-way variant is involved.
pub fn verify_prepared_internal<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    if has_avx2() {
        count_avx2_call();
        // SAFETY: as above.
        unsafe { verify_prepared_avx2::<K, L>(p, vk, m_prefix, m, sig) }
    } else {
        verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig)
    }
}

/// `verify::prepare_vk` (`api::verifying_key_*`), or its 4-way AVX2 version when this CPU has AVX2.
pub fn prepare_vk<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    if has_avx2() {
        count_avx2_call();
        // SAFETY: as above.
        unsafe { prepare_vk_avx2::<K, L>(pk) }
    } else {
        verify::prepare_vk::<K, L>(pk)
    }
}

/// For tests: the AVX2 body regardless of dispatch counters, or `None` without AVX2. Same results as the dispatchers.
#[cfg(feature = "internals")]
pub fn verify_internal_avx2_or_none<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> Option<bool> {
    if !has_avx2() {
        return None;
    }
    // SAFETY: checked above.
    Some(unsafe { verify_internal_avx2::<K, L>(p, pk, m_prefix, m, sig) })
}

/// For tests: whether the AVX2 `prepare_vk` returns exactly the scalar one (Â, NTT(t1 · 2^d) and tr); `None` without
/// AVX2. The `PreparedVk` fields are crate-private, so the comparison lives here.
#[cfg(feature = "internals")]
pub fn prepare_vk_avx2_matches_scalar<const K: usize, const L: usize>(pk: &[u8]) -> Option<bool> {
    if !has_avx2() {
        return None;
    }
    // SAFETY: checked above.
    let fast = unsafe { prepare_vk_avx2::<K, L>(pk) };
    let slow = verify::prepare_vk::<K, L>(pk);
    Some(fast.a_hat == slow.a_hat && fast.t1_2d_hat == slow.t1_2d_hat && fast.tr == slow.tr)
}

// Test and bench entry points (feature `internals`). The lane-operation type `keccak4::avx2::Avx2` is crate-private
// (its safe trait methods execute AVX2 instructions), so outside code reaches the AVX2 instantiation of the 4-way
// pieces only through these functions, each of which checks `has_avx2` and returns `None` without AVX2.

#[cfg(feature = "internals")]
#[target_feature(enable = "avx2")]
fn rej_ntt_poly_x4_avx2(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
    align_frame();
    rej_ntt_poly_x4::<Avx2>(rho, s, r)
}

#[cfg(feature = "internals")]
#[target_feature(enable = "avx2")]
fn expand_a_x4_avx2<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
    align_frame();
    expand_a_x4::<K, L, Avx2>(rho)
}

#[cfg(feature = "internals")]
#[target_feature(enable = "avx2")]
fn expand_a_into_x4_avx2<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
    align_frame();
    expand_a_into_x4::<K, L, Avx2>(rho, a)
}

/// `sampling::rej_ntt_poly_x4::<Avx2>`, or `None` without AVX2.
#[cfg(feature = "internals")]
pub fn rej_ntt_poly_x4_avx2_or_none(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> Option<[[u32; 256]; 4]> {
    // SAFETY: `has_avx2` checked CPU and OS support for AVX2 (here and in the four functions below).
    if has_avx2() { Some(unsafe { rej_ntt_poly_x4_avx2(rho, s, r) }) } else { None }
}

/// `sampling::expand_a_x4::<K, L, Avx2>`, or `None` without AVX2.
#[cfg(feature = "internals")]
pub fn expand_a_x4_avx2_or_none<const K: usize, const L: usize>(rho: &[u8; 32]) -> Option<[[[u32; 256]; L]; K]> {
    if has_avx2() { Some(unsafe { expand_a_x4_avx2::<K, L>(rho) }) } else { None }
}

/// `sampling::expand_a_into_x4::<K, L, Avx2>`; returns `false` (and leaves `a` alone) without AVX2.
#[cfg(feature = "internals")]
pub fn expand_a_into_x4_avx2_or_false<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) -> bool {
    if has_avx2() {
        unsafe { expand_a_into_x4_avx2::<K, L>(rho, a) };
        true
    } else {
        false
    }
}

#[cfg(feature = "internals")]
#[target_feature(enable = "avx2")]
fn expand_a_tr_into_x4_avx2<const K: usize, const L: usize>(
    rho: &[u8; 32],
    pk: &[u8],
    a: &mut [[[u32; 256]; L]; K],
) -> [u8; 64] {
    align_frame();
    expand_a_tr_into_x4::<K, L, Avx2>(rho, pk, a)
}

/// `sampling::expand_a_tr_into_x4::<K, L, Avx2>` (ExpandA with `tr = H(pk, 64)` in the fourth lane), or `None` (and `a`
/// left alone) without AVX2.
#[cfg(feature = "internals")]
pub fn expand_a_tr_into_x4_avx2_or_none<const K: usize, const L: usize>(
    rho: &[u8; 32],
    pk: &[u8],
    a: &mut [[[u32; 256]; L]; K],
) -> Option<[u8; 64]> {
    if has_avx2() { Some(unsafe { expand_a_tr_into_x4_avx2::<K, L>(rho, pk, a) }) } else { None }
}

/// `verify::prepare_vk_x4::<K, L, Avx2>`, or `None` without AVX2.
#[cfg(feature = "internals")]
pub fn prepare_vk_x4_avx2_or_none<const K: usize, const L: usize>(pk: &[u8]) -> Option<PreparedVk<K, L>> {
    if has_avx2() { Some(unsafe { prepare_vk_avx2::<K, L>(pk) }) } else { None }
}
