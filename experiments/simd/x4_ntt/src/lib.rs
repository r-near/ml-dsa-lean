//! Question 4 prototype. `field` and `ntt` are byte-for-byte copies of the main crate's `src/field.rs` and `src/ntt.rs`
//! (checked by `check-copies.sh`); `fold`, `shoup` and `lazy` are three semantically equal rewrites of the NTT's
//! modular multiply, each aimed at LLVM's loop vectorizer at `x86-64-v3`.
#![no_std]
#![allow(clippy::many_single_char_names, clippy::needless_range_loop)]

pub mod field;
pub mod fold;
pub mod lazy;
pub mod mont2;
pub mod ntt;
pub mod origl;
pub mod shoup;
pub mod tables;

/// Extraction-visible dispatch shim. Under `cfg(miri)` (how extraction is run) it is the portable body, so the proved
/// model has no dispatch at all; in a real build it selects the AVX2 compilation of the same body, with the CPU check
/// cached in a static (CPUID traps to the hypervisor on virtual machines, ~3 us per call).
pub fn ntt_dispatch(w: &[u32; 256]) -> [u32; 256] {
    #[cfg(any(miri, not(target_arch = "x86_64")))]
    {
        shoup::ntt_body(w)
    }
    #[cfg(all(not(miri), target_arch = "x86_64"))]
    {
        if avx2_cached() {
            // SAFETY: AVX2 (and OS support for YMM state) was detected.
            unsafe { shoup::ntt_avx2(w) }
        } else {
            shoup::ntt_body(w)
        }
    }
}

#[cfg(all(not(miri), target_arch = "x86_64"))]
fn avx2_cached() -> bool {
    use core::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0); // 0 = unknown, 1 = no, 2 = yes
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let yes = has_avx2();
            STATE.store(if yes { 2 } else { 1 }, Ordering::Relaxed);
            yes
        }
    }
}

#[cfg(all(not(miri), target_arch = "x86_64"))]
pub fn has_avx2() -> bool {
    use core::arch::x86_64::{__cpuid, __cpuid_count, _xgetbv};
    // SAFETY: CPUID exists on every x86-64 CPU; XGETBV is only executed after OSXSAVE is reported.
    unsafe {
        let max = __cpuid(0).eax;
        if max < 7 {
            return false;
        }
        let l1 = __cpuid(1);
        let osxsave = (l1.ecx >> 27) & 1 == 1;
        if !osxsave {
            return false;
        }
        let ymm_state = _xgetbv(0) & 0b110 == 0b110; // XMM and YMM state enabled by the OS
        let avx2 = (__cpuid_count(7, 0).ebx >> 5) & 1 == 1;
        ymm_state && avx2
    }
}
