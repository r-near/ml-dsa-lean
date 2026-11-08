//! The AVX2 compilation of the 4-way permutation (`keccak4::avx2_checked`, the same plain-Rust source the Lean proof is
//! about, compiled inside a `#[target_feature(enable = "avx2")]` function) against the portable compilation and four scalar
//! permutations.
//!
//! There are no AVX2 lane operations any more, so this is a check on the compiler's translation of proved source, not on a
//! second implementation. It must still be strong: 150,000+ whole states (random, one-hot, edge cases, equal-lane states),
//! compared with the portable compilation and with four runs of the scalar `keccak_f1600`, plus a long chain.
//! Fixed seeds; deterministic. Needs a CPU with AVX2 (`ML_DSA_REQUIRE_AVX2=1` makes a missing AVX2 a failure).
#![cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
#![allow(clippy::needless_range_loop)]
use ml_dsa_lean::keccak::keccak_f1600;
use ml_dsa_lean::keccak4::avx2_checked as avx2;
use ml_dsa_lean::keccak4::keccak_f1600_x4;

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

fn have_avx2() -> bool {
    let yes = std::arch::is_x86_feature_detected!("avx2");
    if std::env::var("ML_DSA_REQUIRE_AVX2").as_deref() == Ok("1") {
        assert!(yes, "ML_DSA_REQUIRE_AVX2=1 but this CPU has no AVX2");
    }
    yes
}

/// Random states mixed with edge cases (zero, all ones, one-hot, one lane different).
fn states(n: usize, seed: u64) -> Vec<[[u64; 4]; 25]> {
    let mut r = XorShift(seed);
    let mut v = vec![[[0u64; 4]; 25], [[u64::MAX; 4]; 25]];
    for i in 0..1600 {
        let mut s = [[0u64; 4]; 25];
        s[i / 64][i % 4] = 1u64 << (i % 64);
        v.push(s);
    }
    for _ in 0..n {
        let mut s = [[0u64; 4]; 25];
        for lane in s.iter_mut() {
            for w in lane.iter_mut() {
                *w = r.next();
            }
        }
        // Every 8th state: the four sponge states are equal, as in a padded duplicate lane.
        if v.len() % 8 == 0 {
            for lane in s.iter_mut() {
                *lane = [lane[0]; 4];
            }
        }
        v.push(s);
    }
    v
}

fn scalar(s: &[[u64; 4]; 25]) -> [[u64; 4]; 25] {
    let mut out = [[0u64; 4]; 25];
    for i in 0..4 {
        let mut a = [0u64; 25];
        for k in 0..25 {
            a[k] = s[k][i];
        }
        keccak_f1600(&mut a);
        for k in 0..25 {
            out[k][i] = a[k];
        }
    }
    out
}

#[test]
fn avx2_permutation_equals_portable_and_four_scalar_permutations() {
    if !have_avx2() {
        eprintln!("no AVX2: skipped");
        return;
    }
    let all = states(150_000, 0x4b45_4343_4146_5631);
    assert!(all.len() > 150_000);
    for s in &all {
        let mut a = *s;
        assert!(avx2::keccak_f1600_x4(&mut a));
        let mut p = *s;
        keccak_f1600_x4(&mut p);
        assert_eq!(a, p, "avx2 vs portable, input {s:x?}");
        assert_eq!(a, scalar(s), "avx2 vs four scalar permutations, input {s:x?}");
    }
    // Iterated: feed the output back in (the squeeze loop does exactly this), so state evolves through many blocks.
    let mut a = all[all.len() / 2];
    let mut p = a;
    for _ in 0..2_000 {
        assert!(avx2::keccak_f1600_x4(&mut a));
        keccak_f1600_x4(&mut p);
        assert_eq!(a, p);
    }
    eprintln!("avx2 x4 vs portable vs scalar: {} states, plus a 2000-permutation chain, 0 mismatches", all.len());
}
