//! The AVX2 wrappers behind `fast_verify.rs`; see the documentation there. Compiled only with the `avx2` feature on
//! x86_64, and under `--cfg miri` (the extraction), where they are ordinary functions.
//!
//! Each wrapper is one call of an extracted, proved function. Compiled inside a `#[target_feature(enable = "avx2")]`
//! function, the callee and everything it inlines (every link of the chain is `#[inline(always)]` in this build) is
//! generated with AVX2; LLVM's loop vectorizer then turns the Keccak loop (`keccak4.rs`) and the NTT, multiply-
//! accumulate and UseHint loops into 256-bit code. That is a performance property (`scripts/check-avx2-inlining.sh`);
//! the values are those of the called function.
//!
//! Stack frames. The spills of 256-bit vectors in a wrapper want 32-byte alignment (a spill at 16 mod 32 that crosses a
//! 4 KiB page costs about 30 cycles on Zen 4; `bench/results/2026-11-07-p6.md`). `PreparedVk` is
//! `#[repr(align(32))]`: a wrapper that owns one (`verify_internal_avx2`, `prepare_vk_avx2`) gets a 32-byte aligned
//! frame from it, with no code that exists only for that purpose. `verify_prepared_avx2` only borrows a key, so the type
//! does not help it, and `bench/stackscan.sh` does not show the cost; the interleaved A/B does: the prepared-key verify
//! is 2-8% slower without a realigned frame (`bench/results/2026-11-08-p8.md`; the mechanism was not isolated further).
//! Its wrapper therefore calls `align_frame()`, a 32-byte aligned local passed to `black_box`. Besides the CPU check
//! this is the one piece of code on a verify path that exists only under `cfg(not(miri))`; it reads and writes no value
//! (`scripts/check-avx2-inlining.sh` requires the realignment in all nine wrapper instantiations).

use crate::params::Params;
use crate::verify::{self, prepare_vk_into_x4, verify_internal_x4, PreparedVk};

/// A 32-byte aligned object for `align_frame` (its contents are never read).
#[cfg(not(miri))]
#[repr(align(32))]
struct Align32([u8; 32]);

/// Makes the calling function realign its stack frame to 32 bytes: the local is aligned, and passing it to `black_box`
/// keeps LLVM from removing it. No value is read or written. Under Miri (so in the extraction) it is the empty function,
/// as `field::opaque_u32` is the identity there.
#[cfg(not(miri))]
#[inline(always)]
fn align_frame() {
    let anchor = Align32([0; 32]);
    core::hint::black_box(&anchor);
}
#[cfg(miri)]
#[inline(always)]
fn align_frame() {}

/// The 4-way verify body. `verify_internal_x4` is `#[inline(always)]` (and so are the kernel and the functions below it), so
/// the whole chain down to `keccak4::keccak_f1600_x4` is compiled inside this function, with AVX2 enabled.
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
pub(super) fn verify_internal_avx2<const K: usize, const L: usize>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    verify_internal_x4::<K, L>(p, pk, m_prefix, m, sig)
}

/// The prepared-key verify body with AVX2: `verify::verify_prepared_internal` is `#[inline(always)]` (and so are the
/// decoders and the verify-only arithmetic below it), so the NTTs, the multiply-accumulate rows, UseHint and the packing are
/// compiled inside this function with AVX2 enabled. There is no ExpandA to speed up, so this is the scalar proved function
/// itself, not an `X4` variant.
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
pub(super) fn verify_prepared_avx2<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    align_frame();
    verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig)
}

/// `verify::prepare_vk_x4` built in place: the key is created as a local that is also the result (so it is the caller's
/// result slot) and `prepare_vk_into_x4` fills it. That is `prepare_vk_x4` itself (`Proofs/FastVerify.lean`:
/// `prepare_vk_into_x4_zero`, `prepare_vk_x4_zeroed_bind`), without the by-value function's 57 KB (ML-DSA-87) matrix local
/// and the copy of it into the result, which glibc runs as `rep movsb` and which is several times slower when the two
/// buffers happen to sit at a distance that is a small multiple of 4 KiB (`bench/results/2026-11-07-p6.md`).
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
pub(super) fn prepare_vk_avx2<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    let mut vk = PreparedVk::<K, L>::zeroed();
    prepare_vk_into_x4::<K, L>(pk, &mut vk);
    vk
}
