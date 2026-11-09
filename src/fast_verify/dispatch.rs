//! The AVX2 wrappers behind `fast_verify.rs`; see the documentation there. This module is compiled in every build.
//!
//! Each of the three entry points (`verify_internal_on`, `verify_prepared_on`, `prepare_vk_on`) is a safe function that
//! takes the `cpu::Avx2` token by value. It has two definitions, selected by the same condition as the token's type
//! (`cpu.rs`):
//!
//! * Where the dispatch exists (feature `avx2` on x86_64, and under `--cfg miri`, which is what the Lean extraction
//!   sees) the body is one `unsafe` call of the matching `*_avx2` function, which is a `#[target_feature(enable =
//!   "avx2")]` function whose body is one call of an extracted, proved function. The `unsafe` is justified by the
//!   token: only `cpu::avx2()` makes one, after it found AVX2 usable.
//! * Elsewhere `Avx2` is an uninhabited enum, so the body is `match t {}`: it cannot be called, and there is no `unsafe`
//!   and no AVX2 function in the build.
//!
//! These are the only production `unsafe` blocks of the verify dispatch (three, one per entry point). The callers in
//! `fast_verify.rs` are the same text in every build.
//!
//! Compiled inside a `#[target_feature(enable = "avx2")]` function, the callee and everything it inlines (every link of
//! the chain is `#[inline(always)]` in this build) is generated with AVX2; LLVM's loop vectorizer then turns the Keccak
//! loop (`keccak4.rs`) and the NTT, multiply-accumulate and UseHint loops into 256-bit code. That is a performance
//! property (`scripts/check-avx2-inlining.sh`); the values are those of the called function.
//!
//! Stack frames. The spills of 256-bit vectors in a wrapper want 32-byte alignment (a spill at 16 mod 32 that crosses a
//! 4 KiB page costs about 30 cycles on Zen 4; `bench/results/2026-11-07-p6.md`). Every wrapper gets a 32-byte aligned
//! frame from a `#[repr(align(32))]` object that the proved code computes in, with no code that exists only for that
//! purpose: `PreparedVk` for the two wrappers that own one (`verify_internal_avx2`, `prepare_vk_avx2`) and
//! `verify::VerifyScratch` (w′1 and its encoding, the working storage of `verify_core`) for all three, in particular for
//! `verify_prepared_avx2`, which only borrows a key. Without that the prepared-key verify is 2-8% slower
//! (`bench/results/2026-11-08-p8.md`; the earlier fix was a `black_box` anchor that exists only in the compiled
//! build, which is gone). The asm gate `scripts/check-avx2-inlining.sh` requires the realignment in all nine wrapper
//! instantiations, because LLVM could split or drop an aligned aggregate.

use crate::cpu::Avx2;
use crate::params::Params;
use crate::verify::PreparedVk;
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
use crate::verify::{self, prepare_vk_into_x4, verify_internal_x4};

// The entry points. Dispatch build: one `unsafe` call each.

/// `verify_internal_avx2` for a token: the 4-way verify. Equal to `verify::verify_internal` (`Proofs/Dispatch.lean`).
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(super) fn verify_internal_on<const K: usize, const L: usize>(
    _t: Avx2,
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    // SAFETY: an `Avx2` token exists only if `cpu::avx2()` found AVX2 usable (CPU and OS); nothing else makes one.
    unsafe { verify_internal_avx2::<K, L>(p, pk, m_prefix, m, sig) }
}

/// `verify_prepared_avx2` for a token. Equal to `verify::verify_prepared_internal`.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(super) fn verify_prepared_on<const K: usize, const L: usize>(
    _t: Avx2,
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    // SAFETY: as above.
    unsafe { verify_prepared_avx2::<K, L>(p, vk, m_prefix, m, sig) }
}

/// `prepare_vk_avx2` for a token. Equal to `verify::prepare_vk`.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(super) fn prepare_vk_on<const K: usize, const L: usize>(_t: Avx2, pk: &[u8]) -> PreparedVk<K, L> {
    // SAFETY: as above.
    unsafe { prepare_vk_avx2::<K, L>(pk) }
}

// The entry points. Build without the dispatch: `Avx2` has no value, so these cannot be called.

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
#[allow(unused_variables)]
pub(super) fn verify_internal_on<const K: usize, const L: usize>(
    t: Avx2,
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match t {}
}

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
#[allow(unused_variables)]
pub(super) fn verify_prepared_on<const K: usize, const L: usize>(
    t: Avx2,
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match t {}
}

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
#[allow(unused_variables)]
pub(super) fn prepare_vk_on<const K: usize, const L: usize>(t: Avx2, pk: &[u8]) -> PreparedVk<K, L> {
    match t {}
}

// The `#[target_feature]` functions (dispatch build only). Private: the entry points above are the only callers.
/// The 4-way verify body. `verify_internal_x4` is `#[inline(always)]` (and so are the kernel and the functions below it), so
/// the whole chain down to `keccak4::keccak_f1600_x4` is compiled inside this function, with AVX2 enabled.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
fn verify_internal_avx2<const K: usize, const L: usize>(
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
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
fn verify_prepared_avx2<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig)
}

/// `verify::prepare_vk_x4` built in place: the key is created as a local that is also the result (so it is the caller's
/// result slot) and `prepare_vk_into_x4` fills it. That is `prepare_vk_x4` itself (`Proofs/FastVerify.lean`:
/// `prepare_vk_into_x4_zero`, `prepare_vk_x4_zeroed_bind`), without the by-value function's 57 KB (ML-DSA-87) matrix local
/// and the copy of it into the result, which glibc runs as `rep movsb` and which is several times slower when the two
/// buffers happen to sit at a distance that is a small multiple of 4 KiB (`bench/results/2026-11-07-p6.md`).
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx2"))]
fn prepare_vk_avx2<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    let mut vk = PreparedVk::<K, L>::zeroed();
    prepare_vk_into_x4::<K, L>(pk, &mut vk);
    vk
}
