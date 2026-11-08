//! The 4-way Keccak-f[1600] kernel (src/keccak4.rs): the portable compilation and, with the `avx2` feature on an AVX2
//! machine, the AVX2 compilation agree with four runs of the scalar `keccak::keccak_f1600`.
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

/// Random states mixed with edge cases (zero, all ones, single bit).
fn states(n: usize, seed: u64) -> Vec<[[u64; 4]; 25]> {
    let mut r = XorShift(seed);
    let mut v = vec![[[0u64; 4]; 25], [[u64::MAX; 4]; 25]];
    for i in 0..256 {
        let mut s = [[0u64; 4]; 25];
        s[i / 64 % 25][i % 4] = 1u64 << (i % 64);
        v.push(s);
    }
    for _ in 0..n {
        let mut s = [[0u64; 4]; 25];
        for lane in s.iter_mut() {
            for w in lane.iter_mut() {
                *w = r.next();
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
fn portable_matches_four_scalar_permutations() {
    let all = states(20_000, 0x4b45_4343_414b_3478);
    for s in &all {
        let mut t = *s;
        keccak_f1600_x4(&mut t);
        assert_eq!(t, scalar(s));
    }
    eprintln!("portable x4 vs scalar: {} states, 0 mismatches", all.len());
}

#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
mod avx2 {
    use super::*;
    use ml_dsa_lean::keccak4::avx2_checked as avx2c;

    fn have_avx2() -> bool {
        std::arch::is_x86_feature_detected!("avx2")
    }

    #[test]
    fn avx2_matches_portable_and_scalar() {
        if !have_avx2() {
            eprintln!("no AVX2: skipped");
            return;
        }
        let all = states(20_000, 0x4156_5832_4b43_4b34);
        for s in &all {
            let mut a = *s;
            assert!(avx2c::keccak_f1600_x4(&mut a));
            let mut p = *s;
            keccak_f1600_x4(&mut p);
            assert_eq!(a, p, "avx2 vs portable");
            assert_eq!(a, scalar(s), "avx2 vs four scalar permutations");
        }
        eprintln!("avx2 x4 vs portable vs scalar: {} states, 0 mismatches", all.len());
    }

    /// Sanity timing, not a benchmark: `cargo test --release --features avx2 --test keccak4 -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn timing() {
        use std::hint::black_box;
        use std::time::Instant;
        if !have_avx2() {
            return;
        }
        let iters = 200_000;
        let base = states(0, 1)[100];
        let time = |f: &mut dyn FnMut(&mut [[u64; 4]; 25])| {
            let mut best = f64::MAX;
            for _ in 0..7 {
                let mut s = black_box(base);
                let t = Instant::now();
                for _ in 0..iters {
                    f(&mut s);
                    black_box(&mut s);
                }
                best = best.min(t.elapsed().as_secs_f64() * 1e9 / iters as f64);
            }
            best
        };
        let four_scalar = time(&mut |s| {
            for i in 0..4 {
                let mut a = [0u64; 25];
                for k in 0..25 {
                    a[k] = s[k][i];
                }
                keccak_f1600(&mut a);
                for k in 0..25 {
                    s[k][i] = a[k];
                }
            }
        });
        let portable = time(&mut |s| keccak_f1600_x4(s));
        let avx = time(&mut |s| {
            avx2c::keccak_f1600_x4(s);
        });
        eprintln!("ns per call (4 permutations): 4 x scalar {four_scalar:.0}, portable x4 {portable:.0}, avx2 x4 {avx:.0}; avx2 speedup over 4 x scalar {:.2}x", four_scalar / avx);
    }
}
