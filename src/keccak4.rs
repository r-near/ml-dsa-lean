//! 4-way Keccak-f[1600]: four independent states permuted together, in plain safe Rust.
//!
//! There are no lane operations, no intrinsics and no trait: `keccak_f1600_x4` is a loop over the 24 rounds (two per
//! iteration) around a loop over the four states, whose body (`lane_rounds2`: load the 25 lanes of one state, two calls of the
//! straight-line scalar round `round25`, store them back) is scalar code on one state.
//! The state layout makes the loop over states a unit-stride loop: `s[k]` is lane `k = x + 5y` of all four states,
//! `s[k][i]` is lane `k` of state `i`, so iteration `i` loads and stores `s[0][i], s[1][i], ...`. LLVM's loop vectorizer
//! turns that loop into 256-bit code (one state per vector lane, `vpxor`, `vpandn`, `vpsllq`/`vpsrlq`/`vpor`) when the
//! function is compiled with AVX2, which is what `fast_verify::dispatch` does: it calls the proved code from
//! `#[target_feature(enable = "avx2")]` wrappers after a CPU check. The same source compiled without AVX2 is the
//! portable path (scalar, or SSE2 if LLVM finds it worthwhile). Whether LLVM vectorizes is a compiler heuristic that no
//! proof can pin down: the result is always correct, and `scripts/check-avx2-inlining.sh` fails if the permutation stops
//! being vector code.
//!
//! Why not `[u64; 4]` values with lane-wise helpers (the previous shape): LLVM's SLP vectorizer rejects that code as
//! "not beneficial" because it first rewrites each 64-bit rotate into a scalar funnel shift, which it prices above the
//! four-lane vector rotate, and the all-or-nothing tree that results never pays off (`bench/results/fv-vec/README.md`).
//! The loop vectorizer prices the whole loop body instead and widens it.
//!
//! The output of a round is produced row by row (`scripts/gen_keccak4_round.py` generates `round25` and `lane_rounds2`), so
//! that few values are live at a time.

use crate::keccak::RC;

// `round25` and `lane_rounds2` are `inline(always)` only where the kernel is compiled inside a
// `#[target_feature(enable = "avx2")]` wrapper: the loop in `keccak_f1600_x4` must see their bodies to vectorize it, and the
// wrapper's AVX2 only reaches code inlined into it.
//
// `round25` is one Keccak-f[1600] round (θ, ρ, π, χ, ι with round constant `rc`) on a scalar state, lane `k = x + 5y` at
// `a[k]`. The shared generated code below is `scripts/gen_keccak4_round.py`'s output (`--check` compares).
// BEGIN GENERATED
#[allow(clippy::manual_rotate)] // explicit shifts: they are what the extraction and the proof are about
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn round25(a: &[u64; 25], rc: u64) -> [u64; 25] {
    let c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20];
    let c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21];
    let c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22];
    let c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23];
    let c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24];
    let d0 = c4 ^ (c1 << 1u32 | c1 >> 63u32);
    let d1 = c0 ^ (c2 << 1u32 | c2 >> 63u32);
    let d2 = c1 ^ (c3 << 1u32 | c3 >> 63u32);
    let d3 = c2 ^ (c4 << 1u32 | c4 >> 63u32);
    let d4 = c3 ^ (c0 << 1u32 | c0 >> 63u32);
    let b0_0 = a[0] ^ d0;
    let t0_1 = a[6] ^ d1;
    let b0_1 = t0_1 << 44u32 | t0_1 >> 20u32;
    let t0_2 = a[12] ^ d2;
    let b0_2 = t0_2 << 43u32 | t0_2 >> 21u32;
    let t0_3 = a[18] ^ d3;
    let b0_3 = t0_3 << 21u32 | t0_3 >> 43u32;
    let t0_4 = a[24] ^ d4;
    let b0_4 = t0_4 << 14u32 | t0_4 >> 50u32;
    let o0 = b0_0 ^ (!b0_1 & b0_2) ^ rc;
    let o1 = b0_1 ^ (!b0_2 & b0_3);
    let o2 = b0_2 ^ (!b0_3 & b0_4);
    let o3 = b0_3 ^ (!b0_4 & b0_0);
    let o4 = b0_4 ^ (!b0_0 & b0_1);
    let t1_0 = a[3] ^ d3;
    let b1_0 = t1_0 << 28u32 | t1_0 >> 36u32;
    let t1_1 = a[9] ^ d4;
    let b1_1 = t1_1 << 20u32 | t1_1 >> 44u32;
    let t1_2 = a[10] ^ d0;
    let b1_2 = t1_2 << 3u32 | t1_2 >> 61u32;
    let t1_3 = a[16] ^ d1;
    let b1_3 = t1_3 << 45u32 | t1_3 >> 19u32;
    let t1_4 = a[22] ^ d2;
    let b1_4 = t1_4 << 61u32 | t1_4 >> 3u32;
    let o5 = b1_0 ^ (!b1_1 & b1_2);
    let o6 = b1_1 ^ (!b1_2 & b1_3);
    let o7 = b1_2 ^ (!b1_3 & b1_4);
    let o8 = b1_3 ^ (!b1_4 & b1_0);
    let o9 = b1_4 ^ (!b1_0 & b1_1);
    let t2_0 = a[1] ^ d1;
    let b2_0 = t2_0 << 1u32 | t2_0 >> 63u32;
    let t2_1 = a[7] ^ d2;
    let b2_1 = t2_1 << 6u32 | t2_1 >> 58u32;
    let t2_2 = a[13] ^ d3;
    let b2_2 = t2_2 << 25u32 | t2_2 >> 39u32;
    let t2_3 = a[19] ^ d4;
    let b2_3 = t2_3 << 8u32 | t2_3 >> 56u32;
    let t2_4 = a[20] ^ d0;
    let b2_4 = t2_4 << 18u32 | t2_4 >> 46u32;
    let o10 = b2_0 ^ (!b2_1 & b2_2);
    let o11 = b2_1 ^ (!b2_2 & b2_3);
    let o12 = b2_2 ^ (!b2_3 & b2_4);
    let o13 = b2_3 ^ (!b2_4 & b2_0);
    let o14 = b2_4 ^ (!b2_0 & b2_1);
    let t3_0 = a[4] ^ d4;
    let b3_0 = t3_0 << 27u32 | t3_0 >> 37u32;
    let t3_1 = a[5] ^ d0;
    let b3_1 = t3_1 << 36u32 | t3_1 >> 28u32;
    let t3_2 = a[11] ^ d1;
    let b3_2 = t3_2 << 10u32 | t3_2 >> 54u32;
    let t3_3 = a[17] ^ d2;
    let b3_3 = t3_3 << 15u32 | t3_3 >> 49u32;
    let t3_4 = a[23] ^ d3;
    let b3_4 = t3_4 << 56u32 | t3_4 >> 8u32;
    let o15 = b3_0 ^ (!b3_1 & b3_2);
    let o16 = b3_1 ^ (!b3_2 & b3_3);
    let o17 = b3_2 ^ (!b3_3 & b3_4);
    let o18 = b3_3 ^ (!b3_4 & b3_0);
    let o19 = b3_4 ^ (!b3_0 & b3_1);
    let t4_0 = a[2] ^ d2;
    let b4_0 = t4_0 << 62u32 | t4_0 >> 2u32;
    let t4_1 = a[8] ^ d3;
    let b4_1 = t4_1 << 55u32 | t4_1 >> 9u32;
    let t4_2 = a[14] ^ d4;
    let b4_2 = t4_2 << 39u32 | t4_2 >> 25u32;
    let t4_3 = a[15] ^ d0;
    let b4_3 = t4_3 << 41u32 | t4_3 >> 23u32;
    let t4_4 = a[21] ^ d1;
    let b4_4 = t4_4 << 2u32 | t4_4 >> 62u32;
    let o20 = b4_0 ^ (!b4_1 & b4_2);
    let o21 = b4_1 ^ (!b4_2 & b4_3);
    let o22 = b4_2 ^ (!b4_3 & b4_4);
    let o23 = b4_3 ^ (!b4_4 & b4_0);
    let o24 = b4_4 ^ (!b4_0 & b4_1);
    [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24]
}

/// Two rounds (`rc0` then `rc1`) on state `i` of the 4-way state `s`: lane `k` of state `i` is `s[k][i]`, and the other three
/// states are untouched. Requires `i < 4`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn lane_rounds2(s: &mut [[u64; 4]; 25], i: usize, rc0: u64, rc1: u64) {
    let a = [s[0][i], s[1][i], s[2][i], s[3][i], s[4][i], s[5][i], s[6][i], s[7][i], s[8][i], s[9][i], s[10][i], s[11][i], s[12][i], s[13][i], s[14][i], s[15][i], s[16][i], s[17][i], s[18][i], s[19][i], s[20][i], s[21][i], s[22][i], s[23][i], s[24][i]];
    let m = round25(&a, rc0);
    let z = round25(&m, rc1);
    s[0][i] = z[0];
    s[1][i] = z[1];
    s[2][i] = z[2];
    s[3][i] = z[3];
    s[4][i] = z[4];
    s[5][i] = z[5];
    s[6][i] = z[6];
    s[7][i] = z[7];
    s[8][i] = z[8];
    s[9][i] = z[9];
    s[10][i] = z[10];
    s[11][i] = z[11];
    s[12][i] = z[12];
    s[13][i] = z[13];
    s[14][i] = z[14];
    s[15][i] = z[15];
    s[16][i] = z[16];
    s[17][i] = z[17];
    s[18][i] = z[18];
    s[19][i] = z[19];
    s[20][i] = z[20];
    s[21][i] = z[21];
    s[22][i] = z[22];
    s[23][i] = z[23];
    s[24][i] = z[24];
}
// END GENERATED

/// Keccak-f[1600] on four states at once, lane `i` of every `s[k]` being state `i`: state `i` of the result is the
/// permutation of state `i` of the input.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn keccak_f1600_x4(s: &mut [[u64; 4]; 25]) {
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 {
            lane_rounds2(s, i, RC[r], RC[r + 1]);
            i += 1;
        }
        r += 2;
    }
}

/// The kernel compiled with AVX2, for the tests and benches (feature `internals`). It runs `cpu::has_avx2()` first and
/// returns `false` (leaving `s` alone) without AVX2, so it cannot raise SIGILL; with AVX2 the result is exactly
/// `keccak_f1600_x4`'s, computed by the code the dispatch wrappers run.
#[cfg(all(feature = "avx2", feature = "internals", not(miri), target_arch = "x86_64"))]
#[allow(unsafe_code)]
pub mod avx2_checked {
    use crate::cpu::has_avx2;

    #[target_feature(enable = "avx2")]
    fn keccak_f1600_x4_avx2(s: &mut [[u64; 4]; 25]) {
        super::keccak_f1600_x4(s)
    }

    /// `keccak_f1600_x4` compiled with AVX2 on `s`; returns `false` (and leaves `s` alone) without AVX2.
    pub fn keccak_f1600_x4(s: &mut [[u64; 4]; 25]) -> bool {
        if has_avx2() {
            // SAFETY: `has_avx2` just reported CPU and OS support for AVX2.
            unsafe { keccak_f1600_x4_avx2(s) };
            true
        } else {
            false
        }
    }
}
