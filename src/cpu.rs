//! Run-time CPU feature detection for the opt-in `avx2` feature (x86_64, not Miri). One detector, shared by the NTT
//! dispatch (`ntt.rs`) and the 4-way verify dispatch (`fast_verify.rs`).
//!
//! Outside the Lean proof. The answer is a function of the CPU and OS only, never of secret data.

use core::sync::atomic::{AtomicU8, Ordering};

/// CPUID leaf 7 EBX bit 5 (AVX2), plus leaf 1 XSAVE, OSXSAVE and AVX, and XCR0 bits 1 and 2 (the OS saves XMM and YMM
/// state). Not for SGX enclaves, where CPUID faults; the `avx2` feature does not support them. CPUID traps to the
/// hypervisor on virtual machines (microseconds), so `has_avx2` caches the answer.
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
static AVX2: AtomicU8 = AtomicU8::new(0);

/// Whether this CPU and OS can run AVX2 code. A build that already enables AVX2 statically
/// (`-C target-feature=+avx2`, `-C target-cpu=x86-64-v3`) answers `true` without a check. Otherwise the first call runs
/// CPUID/XGETBV and the answer is cached in an atomic (about 2 ns per cached call; CPUID alone is about 0.9 µs on a KVM
/// guest).
///
/// A wrong answer can only be "AVX2 reported but unusable" (SIGILL) or "AVX2 usable but not reported" (the scalar path,
/// slower); it cannot change a result, because every AVX2 path computes the same function as the scalar path it
/// replaces (`tests/fast_verify.rs`, `tests/keccak4_avx2.rs`, `tests/dispatch.rs`).
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
#[cfg(feature = "internals")]
pub fn detect_avx2_uncached() -> bool {
    detect_avx2()
}

/// `has_avx2`, public for tests.
#[cfg(feature = "internals")]
pub fn has_avx2_cached() -> bool {
    has_avx2()
}
