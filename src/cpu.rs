//! The CPU check of the opt-in `avx2` feature, and the token it hands out.
//!
//! `avx2()` is the only way to obtain an [`Avx2`] token. The verify dispatch (`fast_verify.rs`) takes an
//! `Option<Avx2>` and runs its `#[target_feature(enable = "avx2")]` wrappers only for `Some`, so a wrapper cannot be
//! reached without this check having found AVX2: the type, not a convention, carries the precondition of the
//! `unsafe` call. Which of the two functions runs is the only thing the token changes. Both compute the same value
//! (`Proofs/Dispatch.lean`: `verify_internal_with` and its two siblings are equal to the scalar functions for every
//! token value, including `None`), so a wrong answer from this module can cause a crash on a CPU without AVX2 but
//! never a wrong result.
//!
//! Outside the Lean proof, and not extracted. Under extraction (`--cfg miri`, scripts/extract.py) and in every build
//! that has no dispatch (feature `avx2` off, or not x86_64) `avx2()` is the one-line stub `None`. The real detector
//! is shared with the NTT dispatch (`ntt.rs`, which uses `has_avx2`). The answer is a function of the CPU and OS
//! only, never of secret data.

#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
use core::sync::atomic::{AtomicU8, Ordering};

/// Permission to execute AVX2 code: its only constructor, [`avx2`], returns one when this CPU and OS can run it.
/// The field is private, so no other module can make one.
#[cfg_attr(not(all(feature = "avx2", not(miri), target_arch = "x86_64")), allow(dead_code))]
pub(crate) struct Avx2(());

/// CPUID leaf 7 EBX bit 5 (AVX2), plus leaf 1 XSAVE, OSXSAVE and AVX, and XCR0 bits 1 and 2 (the OS saves XMM and YMM
/// state). Not for SGX enclaves, where CPUID faults; the `avx2` feature does not support them. CPUID traps to the
/// hypervisor on virtual machines (microseconds), so `has_avx2` caches the answer.
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
fn detect_avx2() -> bool {
    use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
    // SAFETY: CPUID exists on every x86_64 CPU; XGETBV is executed only after OSXSAVE is reported.
    #[allow(unused_unsafe)]
    unsafe {
        if __cpuid(0).eax < 7 {
            return false;
        }
        // Leaf 1 ECX: bit 26 XSAVE, bit 27 OSXSAVE (the OS enabled XSAVE), bit 28 AVX.
        if (__cpuid(1).ecx >> 26) & 0b111 != 0b111 {
            return false;
        }
        if _xgetbv(0) & 0b110 != 0b110 {
            return false;
        }
        (__cpuid_count(7, 0).ebx >> 5) & 1 == 1
    }
}

/// 0 = not yet checked, 1 = no AVX2, 2 = AVX2. Relaxed is enough: racing threads compute the same value.
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
static AVX2: AtomicU8 = AtomicU8::new(0);

/// Whether this CPU and OS can run AVX2 code. A build that already enables AVX2 statically
/// (`-C target-feature=+avx2`, `-C target-cpu=x86-64-v3`) answers `true` without a check. Otherwise the first call runs
/// CPUID/XGETBV and the answer is cached in an atomic (about 2 ns per cached call; CPUID alone is about 0.9 µs on a KVM
/// guest).
///
/// A wrong answer can only be "AVX2 reported but unusable" (SIGILL) or "AVX2 usable but not reported" (the scalar path,
/// slower); it cannot change a result, because the AVX2 path computes the same function as the scalar path it
/// replaces (`Proofs/Dispatch.lean`; `tests/fast_verify.rs`, `tests/dispatch.rs` compare the compiled code).
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
#[inline]
pub(crate) fn has_avx2() -> bool {
    if cfg!(target_feature = "avx2") {
        return true;
    }
    match AVX2.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let yes = detect_avx2();
            AVX2.store(if yes { 2 } else { 1 }, Ordering::Relaxed);
            yes
        }
    }
}

/// The CPU check: `Some(token)` when AVX2 can be executed, `None` otherwise.
#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
#[inline]
pub(crate) fn avx2() -> Option<Avx2> {
    if has_avx2() { Some(Avx2(())) } else { None }
}

/// The stub: never AVX2. This is what a build without the dispatch runs, and what extraction sees (the proofs quantify
/// over every `Option<Avx2>` value, so they do not depend on what the real check returns).
#[cfg(not(all(feature = "avx2", not(miri), target_arch = "x86_64")))]
#[inline]
pub(crate) fn avx2() -> Option<Avx2> {
    None
}

/// The uncached detector, for the test that checks `has_avx2` against the standard library's detection.
#[cfg(all(feature = "avx2", feature = "internals", not(miri), target_arch = "x86_64"))]
pub fn detect_avx2_uncached() -> bool {
    detect_avx2()
}

/// `has_avx2`, public for tests.
#[cfg(all(feature = "avx2", feature = "internals", not(miri), target_arch = "x86_64"))]
pub fn has_avx2_cached() -> bool {
    has_avx2()
}
