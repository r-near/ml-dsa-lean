//! The verify dispatch: scalar function or its 4-way AVX2 version, chosen by an `Option<cpu::Avx2>` argument.
//! Opt-in (feature `avx2`), x86_64 only; extracted and proved like the rest of the crate.
//!
//! Each of the three dispatched functions has a `_with` form that takes the token and is the only code that decides:
//!
//! * `verify_internal_with(avx2, ..)` is `dispatch::verify_internal_avx2(..)` for `Some(_)` and
//!   `verify::verify_internal(..)` for `None`;
//! * `prepare_vk_with(avx2, ..)` likewise for `verify::prepare_vk`;
//! * `verify_prepared_internal_with(avx2, ..)` likewise for `verify::verify_prepared_internal`.
//!
//! The AVX2 wrappers (`fast_verify/dispatch.rs`) are `#[target_feature(enable = "avx2")]` functions whose bodies are one
//! call of the proved 4-way function (`verify::verify_internal_x4`, `prepare_vk_into_x4`) or of the scalar function
//! (`verify_prepared_internal`). Nothing in this module or in the wrappers is compiled differently from what the Lean
//! extraction sees, except the CPU check that makes the token (`cpu.rs`: under extraction, `cpu::avx2()` is the stub
//! `None`). `Proofs/Dispatch.lean` proves, for every value of the token argument (so for whatever the CPU check
//! returns), that each `_with` function equals the scalar function it replaces, as `RustM` values including
//! divergence; `api.rs` has the same for the public functions. The `_with` functions are crate-private: they are
//! reachable only with a token, and only `cpu::avx2()` makes one, after it found AVX2.
//!
//! What is not proved: that rustc/LLVM translate the 4-way functions inside a wrapper faithfully (the same trust as for
//! every other function), and the CPU check itself, which decides whether the wrapper may run. The CPU check is an
//! assumption, not a proof obligation with a harmless failure: when it reports AVX2 on a CPU or OS that cannot run it,
//! the `#[target_feature]` function executes there, which is undefined behavior (SIGILL is one possible outcome; the
//! equality theorem says nothing about it). When it misses AVX2, the scalar function runs. That LLVM
//! vectorizes the Keccak loop is a performance property, checked by `scripts/check-avx2-inlining.sh`, not a
//! correctness assumption.
//!
//! The `unsafe` calls: in production there is one in each of the three `_with` functions below, each needing the
//! token, and the token needing the CPU check. The `internals` hooks (`fast_verify/hooks.rs`, for tests and benchmarks)
//! have their own calls, each behind its own `has_avx2()` check.

use crate::cpu::Avx2;
use crate::params::Params;
use crate::verify::{self, PreparedVk};

// The wrappers, compiled in the same cases as the extraction sees them: feature `avx2` on x86_64, and under `--cfg miri`
// on any host (the extraction), where a host that is not x86_64 drops the `target_feature` attribute and nothing else.
// The explicit path (relative to this file's directory) gives the same file when `checkct/driver` includes this file by
// `#[path]` from another directory.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code)]
#[path = "fast_verify/dispatch.rs"]
mod dispatch;

// Test and bench entry points: the AVX2 compilations of the 4-way pieces, behind their own CPU check.
#[cfg(all(feature = "avx2", feature = "internals", not(miri), target_arch = "x86_64"))]
#[allow(unsafe_code)]
#[path = "fast_verify/hooks.rs"]
mod hooks;
#[cfg(all(feature = "avx2", feature = "internals", not(miri), target_arch = "x86_64"))]
pub use hooks::*;

/// `verify::verify_internal`, or its 4-way AVX2 version for `Some(_)`. Same signature (plus the token), preconditions
/// and results. For every value of `avx2` the result is `verify::verify_internal`'s (`Proofs/Dispatch.lean`).
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(crate) fn verify_internal_with<const K: usize, const L: usize>(
    avx2: Option<Avx2>,
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match avx2 {
        // SAFETY: an `Avx2` token exists only if `cpu::avx2()` found AVX2 usable (CPU and OS); nothing else makes one.
        Some(_) => unsafe { dispatch::verify_internal_avx2::<K, L>(p, pk, m_prefix, m, sig) },
        None => verify::verify_internal::<K, L>(p, pk, m_prefix, m, sig),
    }
}

/// `verify::verify_prepared_internal` (`api::verify_prepared_*`), compiled with AVX2 for `Some(_)`. It is the same
/// proved function in both arms; the wrapper only changes the code generation.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(crate) fn verify_prepared_internal_with<const K: usize, const L: usize>(
    avx2: Option<Avx2>,
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match avx2 {
        // SAFETY: as above.
        Some(_) => unsafe { dispatch::verify_prepared_avx2::<K, L>(p, vk, m_prefix, m, sig) },
        None => verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig),
    }
}

/// `verify::prepare_vk` (`api::verifying_key_*`), or its 4-way AVX2 version for `Some(_)`.
#[cfg(all(feature = "avx2", any(miri, target_arch = "x86_64")))]
#[allow(unsafe_code, unused_unsafe)]
pub(crate) fn prepare_vk_with<const K: usize, const L: usize>(avx2: Option<Avx2>, pk: &[u8]) -> PreparedVk<K, L> {
    match avx2 {
        // SAFETY: as above.
        Some(_) => unsafe { dispatch::prepare_vk_avx2::<K, L>(pk) },
        None => verify::prepare_vk::<K, L>(pk),
    }
}

// Without the dispatch (feature off, or not x86_64) the token is ignored and the scalar functions run. These are the
// same names with the same signatures, so `api.rs` is the same in every build.

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
pub(crate) fn verify_internal_with<const K: usize, const L: usize>(
    _avx2: Option<Avx2>,
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    verify::verify_internal::<K, L>(p, pk, m_prefix, m, sig)
}

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
pub(crate) fn verify_prepared_internal_with<const K: usize, const L: usize>(
    _avx2: Option<Avx2>,
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig)
}

#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]
pub(crate) fn prepare_vk_with<const K: usize, const L: usize>(_avx2: Option<Avx2>, pk: &[u8]) -> PreparedVk<K, L> {
    verify::prepare_vk::<K, L>(pk)
}
