//! The verify dispatch: scalar function or its 4-way AVX2 version, chosen by an `Option<cpu::Avx2>` argument.
//! Opt-in (feature `avx2`), x86_64 only; extracted and proved like the rest of the crate.
//!
//! Each of the three dispatched functions has a `_with` form that takes the token and is the only code that decides:
//!
//! * `verify_internal_with(avx2, ..)` is `dispatch::verify_internal_on(token, ..)` for `Some(token)` and
//!   `verify::verify_internal(..)` for `None`;
//! * `prepare_vk_with(avx2, ..)` likewise for `verify::prepare_vk`;
//! * `verify_prepared_internal_with(avx2, ..)` likewise for `verify::verify_prepared_internal`.
//!
//! **One text.** Each `_with` function has exactly one definition, with no `cfg` and no `unsafe` in it, so the text
//! that a default build, an `avx2` build and the Lean extraction compile is the same text. What differs between
//! configurations is below the `Some(token)` arm, and is selected by the type of the token (`cpu::Avx2`): where the
//! dispatch exists (feature `avx2` on x86_64, and under `--cfg miri`, which is what the extraction sees) it is an
//! inhabited struct and `dispatch::*_on` is one `unsafe` call of a `#[target_feature(enable = "avx2")]` function;
//! elsewhere it is an uninhabited enum and `dispatch::*_on` is `match t {}`, which no value can reach. The AVX2 functions
//! are one call each of the proved 4-way function (`verify::verify_internal_x4`, `prepare_vk_into_x4`) or of the scalar
//! function (`verify_prepared_internal`). `scripts/check-feature-independence.sh` extracts the crate a second time
//! without the dispatch and diffs the Lean it generates against the committed extraction.
//!
//! `Proofs/Dispatch.lean` proves, for every value of the token argument (so for whatever the CPU check returns), that
//! each `_with` function equals the scalar function it replaces, as `RustM` values including divergence; `api.rs`
//! has the same for the public functions. The `_with` functions are crate-private: they are reachable only with a
//! token, and only `cpu::avx2()` makes one, after it found AVX2. Under extraction `cpu::avx2()` is the stub `None`, and
//! the proofs quantify over every `Option<Avx2>`, so they do not depend on what the real check returns.
//!
//! What is not proved: that rustc/LLVM translate the 4-way functions inside a wrapper faithfully (the same trust as for
//! every other function), and the CPU check itself, which decides whether the wrapper may run. The CPU check is an
//! assumption, not a proof obligation with a harmless failure: when it reports AVX2 on a CPU or OS that cannot run it,
//! the `#[target_feature]` function executes there, which is undefined behavior (SIGILL is one possible outcome; the
//! equality theorem says nothing about it). When it misses AVX2, the scalar function runs. That LLVM
//! vectorizes the Keccak loop is a performance property, checked by `scripts/check-avx2-inlining.sh`, not a
//! correctness assumption.
//!
//! The `unsafe` calls: in production there is one in each of the three `dispatch::*_on` entry points
//! (`fast_verify/dispatch.rs`), each needing the token, and the token needing the CPU check; this file has none. The
//! `internals` hooks (`fast_verify/hooks.rs`, for tests and benchmarks) reach the same entry points through
//! `cpu::avx2()` and so need no `unsafe` for them.

use crate::cpu::Avx2;
use crate::params::Params;
use crate::verify::{self, PreparedVk};

// Compiled in every build (`dispatch.rs` has the two definitions of its entry points). The explicit path (relative to
// this file's directory) gives the same file when `checkct/driver` includes this file by `#[path]` from another
// directory. The `allow` exists only where `dispatch.rs` has its `unsafe` blocks; the default build forbids unsafe code.
#[cfg_attr(feature = "avx2", allow(unsafe_code))]
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
pub(crate) fn verify_internal_with<const K: usize, const L: usize>(
    avx2: Option<Avx2>,
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match avx2 {
        Some(t) => dispatch::verify_internal_on::<K, L>(t, p, pk, m_prefix, m, sig),
        None => verify::verify_internal::<K, L>(p, pk, m_prefix, m, sig),
    }
}

/// `verify::verify_prepared_internal` (`api::verify_prepared_*`), compiled with AVX2 for `Some(_)`. It is the same
/// proved function in both arms; the wrapper only changes the code generation.
pub(crate) fn verify_prepared_internal_with<const K: usize, const L: usize>(
    avx2: Option<Avx2>,
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    match avx2 {
        Some(t) => dispatch::verify_prepared_on::<K, L>(t, p, vk, m_prefix, m, sig),
        None => verify::verify_prepared_internal::<K, L>(p, vk, m_prefix, m, sig),
    }
}

/// `verify::prepare_vk` (`api::verifying_key_*`), or its 4-way AVX2 version for `Some(_)`.
pub(crate) fn prepare_vk_with<const K: usize, const L: usize>(avx2: Option<Avx2>, pk: &[u8]) -> PreparedVk<K, L> {
    match avx2 {
        Some(t) => dispatch::prepare_vk_on::<K, L>(t, pk),
        None => verify::prepare_vk::<K, L>(pk),
    }
}
