//! Question 3 prototype: a SymCrypt-style intrinsic model for AVX2, and one real kernel written against it.
//!
//! * `shim`   : 19 Rust models of AVX2 operations (extractable, `core::arch`-free).
//! * `real`   : the same names bound to `core::arch::x86_64` (feature `real`, x86-64 only; not extracted).
//! * `kernel` : the lazy forward NTT written once against "the names", `include!`d into `kernel_shim` and `kernel_real`.
#![no_std]
#![allow(clippy::too_many_arguments, clippy::many_single_char_names)]

pub mod shim;
pub mod tables;

#[cfg(all(feature = "real", target_arch = "x86_64"))]
pub mod real;

/// The kernel against the shims: this is the module that is extracted to Lean.
pub mod kernel_shim {
    #[allow(unused_imports)]
    use crate::shim::*;
    include!("kernel.rs");
}

#[cfg(all(feature = "real", target_arch = "x86_64"))]
pub mod kernel_real {
    #[allow(unused_imports)]
    use crate::real::*;
    include!("kernel.rs");

    // Entry points: the kernel's `#[inline(always)]` bodies and the intrinsic wrappers are compiled with AVX2 here.
    #[target_feature(enable = "avx2")]
    pub fn ntt_lazy_vec_avx2(w: &mut [u32; 256]) {
        ntt_lazy_vec(w)
    }
    #[target_feature(enable = "avx2")]
    pub fn ntt_vec_avx2(w: &[u32; 256]) -> [u32; 256] {
        ntt_vec(w)
    }
    #[target_feature(enable = "avx2")]
    pub fn layer_wide_avx2<const LEN: usize, const ITERATIONS: usize, const M0: usize>(w: &mut [u32; 256]) {
        let mut m = M0;
        layer_wide::<LEN, ITERATIONS>(w, &mut m)
    }
    #[target_feature(enable = "avx2")]
    pub fn layer4_avx2(w: &mut [u32; 256]) {
        let mut m = 31;
        layer4(w, &mut m)
    }
    #[target_feature(enable = "avx2")]
    pub fn layer2_avx2(w: &mut [u32; 256]) {
        let mut m = 63;
        layer2(w, &mut m)
    }
    #[target_feature(enable = "avx2")]
    pub fn layer1_avx2(w: &mut [u32; 256]) {
        let mut m = 127;
        layer1(w, &mut m)
    }
}
