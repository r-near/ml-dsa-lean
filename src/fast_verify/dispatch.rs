//! The AVX2 dispatch behind `fast_verify.rs`; see the documentation there. Compiled only with the `avx2` feature on
//! x86_64, never under Miri.

use crate::cpu::has_avx2;
use crate::keccak4::avx2::Avx2;
use crate::params::Params;
use crate::verify::{self, PreparedVk};
// INTEGRATION: when `verify::{verify_internal_x4, prepare_vk_x4}` (stream W1) land, replace this line with
// `use crate::verify::{prepare_vk_x4, verify_internal_x4};` and delete `fast_verify_stub.rs`.
use crate::fast_verify_stub::{prepare_vk_x4, verify_internal_x4};

#[cfg(feature = "internals")]
use core::sync::atomic::{AtomicUsize, Ordering};

/// Number of calls that took the AVX2 path (verify and prepare together). Test builds only (`internals`): lets
/// `tests/fast_verify.rs` show that `api::verify_*` really reached the AVX2 wrapper.
#[cfg(feature = "internals")]
pub static AVX2_CALLS: AtomicUsize = AtomicUsize::new(0);

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
    verify_internal_x4::<K, L, Avx2>(p, pk, m_prefix, m, sig)
}

#[target_feature(enable = "avx2")]
fn prepare_vk_avx2<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
    prepare_vk_x4::<K, L, Avx2>(pk)
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
