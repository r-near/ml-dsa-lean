//! THROWAWAY experiments (feature `experiments`, off in every sweep; run with `EXPERIMENTS=1 ONLY='__exp_'`). Candidate
//! source rewrites of the one construct that is `insecure` under `PROFILE=nearcore-exact`: the boolean short-circuit of
//! `encode::poly_in_eta` (`if w > eta && w + eta < Q { ok = false }`) inside `encode::sk_is_well_formed`. Nothing here is
//! used by the crate; `src/` is untouched. Each variant is a copy of `sk_is_well_formed::<K, L>` with only the range test
//! changed, the input is a secret sk (as in the `sk_is_well_formed_*` probes). Names: `exp_sk_wf_<variant>_<set>`.
//!
//! The range fact the integer variants rely on: a coefficient of `unpack_signed` is `field::sub(eta, z)`, canonical
//! (in [0, Q)), so `x < 2^31` and the sign-bit tricks `(a - b) >> 31` are exact. That is the same fact `ct_lt_mask`
//! documents for 2^63.
use crate::params::{self, Params};
use crate::rng::{PrivateRng, PublicRng};
use crate::{api, encode, field};
use checkct_macros::checkct;
use core::hint::black_box;

macro_rules! probe {
    ($name:ident, $body:expr) => {
        #[checkct]
        pub fn $name() {
            black_box(PublicRng.next_u32());
            black_box($body);
        }
    };
}

fn secret_sk<const N: usize>() -> [u8; N] {
    let mut b = [0u8; N];
    PrivateRng.fill_bytes(&mut b);
    b
}

/// `encode::unpack_signed` (private there), copied: BitUnpack then `eta - z`.
fn unpack_signed(v: &[u8], b: u32, c: usize) -> [u32; 256] {
    let z = encode::bit_unpack(v, c);
    let mut w = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        w[i] = field::sub(b, z[i]);
        i += 1;
    }
    w
}

// --- range tests: 0 = every coefficient in [-eta, eta], nonzero otherwise (the "bad" accumulator) ---

/// V0, verbatim `poly_in_eta` (returns the bool of the crate).
fn in_eta_orig(w: &[u32; 256], eta: u32) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < 256 {
        if w[i] > eta && w[i] + eta < field::Q {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// V1, same shape with `wrapping_add` (no overflow check, still `&&` and `if`).
fn in_eta_wrapadd(w: &[u32; 256], eta: u32) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < 256 {
        if w[i] > eta && w[i].wrapping_add(eta) < field::Q {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// V2, non-short-circuit `&` on the two comparisons and a bool accumulator, `wrapping_add`.
fn in_eta_bitand(w: &[u32; 256], eta: u32) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < 256 {
        ok &= !((w[i] > eta) & (w[i].wrapping_add(eta) < field::Q));
        i += 1;
    }
    ok
}

/// bad(x) = 1 iff eta < x < Q - eta, as two sign bits (x, eta, Q < 2^31): no add that can overflow, no bool.
#[inline(always)]
fn bad_bit(x: u32, eta: u32) -> u32 {
    (eta.wrapping_sub(x) >> 31) & (x.wrapping_sub(field::Q - eta) >> 31)
}

/// V3, integer mask accumulation: `bad |= bad_bit(x)`; one `== 0` at the end.
fn bad_mask(w: &[u32; 256], eta: u32) -> u32 {
    let mut bad = 0u32;
    let mut i = 0;
    while i < 256 {
        bad |= bad_bit(w[i], eta);
        i += 1;
    }
    bad
}

/// V4, V3 with the per-element mask behind `black_box` (keeps LLVM from vectorizing the OR-reduction into
/// SSE4.1 `ptest` / `pmovmskb` that BINSEC cannot lift).
fn bad_mask_bb(w: &[u32; 256], eta: u32) -> u32 {
    let mut bad = 0u32;
    let mut i = 0;
    while i < 256 {
        bad |= black_box(bad_bit(w[i], eta));
        i += 1;
    }
    bad
}

// --- the sk-level loop, copied from `encode::sk_is_well_formed` with the test swapped ---

fn sk_wf_bool<const K: usize, const L: usize>(p: &Params, sk: &[u8], f: fn(&[u32; 256], u32) -> bool) -> bool {
    let n = 32 * p.eta_bits;
    let mut o = 128;
    let mut ok = true;
    let mut i = 0;
    while i < L + K {
        if !f(&unpack_signed(&sk[o..o + n], p.eta, p.eta_bits), p.eta) {
            ok = false;
        }
        o += n;
        i += 1;
    }
    ok
}

/// Integer accumulation across blocks too: `bad |= block`, a single `bad == 0` at the very end.
fn sk_wf_int<const K: usize, const L: usize>(p: &Params, sk: &[u8], f: fn(&[u32; 256], u32) -> u32) -> bool {
    let n = 32 * p.eta_bits;
    let mut o = 128;
    let mut bad = 0u32;
    let mut i = 0;
    while i < L + K {
        bad |= f(&unpack_signed(&sk[o..o + n], p.eta, p.eta_bits), p.eta);
        o += n;
        i += 1;
    }
    bad == 0
}

// Control: the crate function itself, through this module's driver build (same code as `encode_sk_is_well_formed_44`).
probe!(exp_sk_wf_crate_44, api::sk_is_well_formed_44(&secret_sk::<2560>()));

probe!(exp_sk_wf_orig_44, sk_wf_bool::<4, 4>(&params::ML_DSA_44, &secret_sk::<2560>(), in_eta_orig));
probe!(exp_sk_wf_wrapadd_44, sk_wf_bool::<4, 4>(&params::ML_DSA_44, &secret_sk::<2560>(), in_eta_wrapadd));
probe!(exp_sk_wf_bitand_44, sk_wf_bool::<4, 4>(&params::ML_DSA_44, &secret_sk::<2560>(), in_eta_bitand));
probe!(exp_sk_wf_mask_44, sk_wf_int::<4, 4>(&params::ML_DSA_44, &secret_sk::<2560>(), bad_mask));
probe!(exp_sk_wf_maskbb_44, sk_wf_int::<4, 4>(&params::ML_DSA_44, &secret_sk::<2560>(), bad_mask_bb));
probe!(exp_sk_wf_mask_65, sk_wf_int::<6, 5>(&params::ML_DSA_65, &secret_sk::<4032>(), bad_mask));
probe!(exp_sk_wf_maskbb_65, sk_wf_int::<6, 5>(&params::ML_DSA_65, &secret_sk::<4032>(), bad_mask_bb));
probe!(exp_sk_wf_mask_87, sk_wf_int::<8, 7>(&params::ML_DSA_87, &secret_sk::<4896>(), bad_mask));
probe!(exp_sk_wf_maskbb_87, sk_wf_int::<8, 7>(&params::ML_DSA_87, &secret_sk::<4896>(), bad_mask_bb));
