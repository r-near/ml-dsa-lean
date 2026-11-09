//! A long check of the 4-way permutation (`keccak4::keccak_f1600_x4`, the plain-Rust source the Lean proof is about) against
//! four runs of the scalar `keccak_f1600`: 150,000+ whole states (random, one-hot, edge cases, equal-lane states) plus a
//! long chain.
//!
//! There is one compilation per build, so this is a check on the compiler's translation of proved source: run it as it is for
//! the baseline build and with `RUSTFLAGS="-C target-feature=+avx2"` for the AVX2 build, where LLVM turns the loop over the
//! four states into 256-bit code (scripts/ci.sh step `test-avx2`). Fixed seeds; deterministic.
#![allow(clippy::needless_range_loop)]
use ml_dsa_lean::keccak::keccak_f1600;
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
fn x4_permutation_equals_four_scalar_permutations() {
    let all = states(150_000, 0x4b45_4343_4146_5631);
    assert!(all.len() > 150_000);
    for s in &all {
        let mut a = *s;
        keccak_f1600_x4(&mut a);
        assert_eq!(a, scalar(s), "x4 vs four scalar permutations, input {s:x?}");
    }
    // Iterated: feed the output back in (the squeeze loop does exactly this), so state evolves through many blocks.
    let mut a = all[all.len() / 2];
    let mut want = a;
    for _ in 0..2_000 {
        keccak_f1600_x4(&mut a);
        want = scalar(&want);
        assert_eq!(a, want);
    }
    eprintln!("x4 vs four scalar permutations: {} states, plus a 2000-permutation chain, 0 mismatches", all.len());
}
