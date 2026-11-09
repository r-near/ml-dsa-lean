//! The CPU check of the opt-in `avx2` feature, and the token it hands out.
//!
//! `avx2()` is the only way to obtain an [`Avx2`] token. The verify dispatch (`fast_verify.rs`) takes an
//! `Option<Avx2>` and runs its `#[target_feature(enable = "avx2")]` wrappers only for `Some`, so a wrapper cannot be
//! reached without this check having found AVX2: the type, not a convention, carries the precondition of the
//! `unsafe` call. Which of the two functions runs is the only thing the token changes. Both compute the same value
//! (`Proofs/Dispatch.lean`: `verify_internal_with` and its two siblings are equal to the scalar functions for every
//! token value, including `None`), so a false negative (AVX2 present, not reported) only selects the scalar path. A
//! false positive (AVX2 reported on a CPU or OS that cannot run it) is not covered: it executes a
//! `#[target_feature(enable = "avx2")]` function there, which is undefined behavior (SIGILL is one possible outcome,
//! not a guaranteed one), and the equality theorem does not constrain it. "The CPU and OS support AVX2 whenever
//! `detect_avx2` reports it" is an assumption of the dispatch.
//!
//! What is extracted and what is not. The `Avx2` type and the stub `avx2() -> None` are ordinary code that the Lean
//! extraction sees (`Impl/Types.lean`, `Impl/Funs.lean`); the proofs quantify over every `Option<Avx2>`, so they do not
//! depend on what the real check returns. The real check, `detect_avx2` and the atomic cache are outside the Lean proof:
//! they exist only in a build with the dispatch (feature `avx2` on x86_64, not under `--cfg miri`). In every other build
//! (feature off, another target, or the extraction) `avx2()` is the one-line stub `None`. The real detector is shared
//! with the NTT dispatch (`ntt.rs`, which uses `has_avx2`). The answer is a function of the CPU and OS only, never of
//! secret data.

#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
use core::sync::atomic::{AtomicU8, Ordering};

/// Permission to execute AVX2 code: its only constructor, [`avx2`], returns one when this CPU and OS can run it.
/// The field is private, so no other module can make one.
///
/// This is an inhabited type only where the dispatch exists (feature `avx2` on x86_64, and under `--cfg miri`, which is
/// what the extraction sees). In every other build it is the uninhabited enum below: the dispatch wrappers
/// (`fast_verify/dispatch.rs`) then take a value that cannot exist, their body is `match t {}`, and the verify
/// functions in `fast_verify.rs` are the same text as in the dispatch build. The difference between the two builds is
/// therefore one the type system sees, not a computation the Lean extraction has not seen.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[cfg_attr(miri, allow(dead_code))]
pub(crate) struct Avx2(());

/// See above: without the dispatch, no `Avx2` value exists.
#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
pub(crate) enum Avx2 {}

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
/// A wrong answer is one of two things. "AVX2 usable but not reported" selects the scalar path (slower, same result:
/// the AVX2 path computes the same function as the scalar path it replaces, `Proofs/Dispatch.lean`). "AVX2 reported but
/// unusable" executes a `#[target_feature]` function on a CPU or OS that cannot run it: undefined behavior, which the
/// equality theorem does not cover. `tests/fast_verify.rs` and `tests/dispatch.rs` compare the compiled code and the
/// detector with the standard library's detection on the machines they run on.
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
