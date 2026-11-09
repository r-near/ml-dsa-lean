//! The CPU check of the opt-in `avx2` feature, used by the NTT dispatch (`ntt.rs`) only.
//!
//! The verify path has no CPU check any more (round 12): `api::verify_*`, `verifying_key_*` and the prepared verify call the
//! 4-way functions (`verify::verify_internal_x4`, `prepare_vk_into_x4`) directly, and a build that wants AVX2 code for them
//! says so at compile time (`-C target-feature=+avx2`, `-C target-cpu=x86-64-v3`). What remains here is the detector that
//! decides whether the NTT bodies, compiled a second time inside `#[target_feature(enable = "avx2")]` functions, may run.
//! A false positive (AVX2 reported on a CPU or OS that cannot run it) executes such a function there, which is undefined
//! behavior; "the CPU and OS support AVX2 whenever `detect_avx2` reports it" is an assumption of the NTT dispatch, and the
//! last commit of round 12 removes this file together with that dispatch.

#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
use core::sync::atomic::{AtomicU8, Ordering};

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
/// A wrong answer is one of two things. "AVX2 usable but not reported" selects the portable NTT body (slower, same
/// result: the AVX2 copy is the same source). "AVX2 reported but unusable" executes a `#[target_feature]` function on a
/// CPU or OS that cannot run it: undefined behavior. `tests/dispatch.rs` compares the detector with the standard
/// library's detection on the machines it runs on.
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
