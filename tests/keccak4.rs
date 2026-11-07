//! The 4-way Keccak-f[1600] kernel (src/keccak4.rs): the portable (shim) instantiation and, with the `avx2` feature on
//! an AVX2 machine, the intrinsic instantiation agree with four runs of the scalar `keccak::keccak_f1600`, and every
//! shim operation agrees with its intrinsic for every rotation amount the kernel uses.
#![allow(clippy::needless_range_loop)]
use ml_dsa_lean::keccak::keccak_f1600;
use ml_dsa_lean::keccak4::keccak_f1600_x4_portable;

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
        keccak_f1600_x4_portable(&mut t);
        assert_eq!(t, scalar(s));
    }
    eprintln!("portable x4 vs scalar: {} states, 0 mismatches", all.len());
}

#[cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
mod avx2 {
    use super::*;
    use ml_dsa_lean::keccak4::avx2_checked as avx2c;
    use ml_dsa_lean::keccak4::{Lanes4, Shim4};

    fn have_avx2() -> bool {
        std::arch::is_x86_feature_detected!("avx2")
    }

    #[test]
    fn avx2_matches_shim_and_scalar() {
        if !have_avx2() {
            eprintln!("no AVX2: skipped");
            return;
        }
        let all = states(20_000, 0x4156_5832_4b43_4b34);
        for s in &all {
            let mut a = *s;
            assert!(avx2c::keccak_f1600_x4(&mut a));
            let mut p = *s;
            keccak_f1600_x4_portable(&mut p);
            assert_eq!(a, p, "avx2 vs shim");
            assert_eq!(a, scalar(s), "avx2 vs four scalar permutations");
        }
        eprintln!("avx2 x4 vs shim vs scalar: {} states, 0 mismatches", all.len());
    }

    fn xor_avx(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
        avx2c::xor(a, b).expect("AVX2 checked by the caller")
    }
    fn andnot_avx(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
        avx2c::andnot(a, b).expect("AVX2 checked by the caller")
    }
    fn splat_avx(x: u64) -> [u64; 4] {
        avx2c::splat(x).expect("AVX2 checked by the caller")
    }
    fn rotl_avx<const L: u32, const R: u32>(a: [u64; 4]) -> [u64; 4] {
        avx2c::rotl::<L, R>(a).expect("AVX2 checked by the caller")
    }

    fn vals(r: &mut XorShift) -> Vec<[u64; 4]> {
        let mut v = vec![[0; 4], [u64::MAX; 4], [1, 1 << 63, 0x8000_0000, 0xFFFF_FFFF]];
        for _ in 0..4000 {
            v.push([r.next(), r.next(), r.next(), r.next()]);
        }
        v
    }

    fn check_rot<const L: u32, const R: u32>(vs: &[[u64; 4]]) {
        for &a in vs {
            assert_eq!(rotl_avx::<L, R>(a), Shim4::rotl::<L, R>(a), "rotl {L}");
        }
    }

    #[test]
    fn each_shim_op_matches_its_intrinsic() {
        if !have_avx2() {
            return;
        }
        let mut r = XorShift(0x6f70_7331_6f70_7332);
        let vs = vals(&mut r);
        let ws = vals(&mut r);
        for (&a, &b) in vs.iter().zip(ws.iter()) {
            assert_eq!(xor_avx(a, b), Shim4::xor(a, b));
            assert_eq!(andnot_avx(a, b), Shim4::andnot(a, b));
            assert_eq!(splat_avx(a[0]), Shim4::splat(a[0]));
        }
        // Every rotation amount the kernel uses (ρ offsets, and 1 for θ), as the (L, 64 - L) the kernel passes.
        check_rot::<1, 63>(&vs);
        check_rot::<62, 2>(&vs);
        check_rot::<28, 36>(&vs);
        check_rot::<27, 37>(&vs);
        check_rot::<36, 28>(&vs);
        check_rot::<44, 20>(&vs);
        check_rot::<6, 58>(&vs);
        check_rot::<55, 9>(&vs);
        check_rot::<20, 44>(&vs);
        check_rot::<3, 61>(&vs);
        check_rot::<10, 54>(&vs);
        check_rot::<43, 21>(&vs);
        check_rot::<25, 39>(&vs);
        check_rot::<39, 25>(&vs);
        check_rot::<41, 23>(&vs);
        check_rot::<45, 19>(&vs);
        check_rot::<15, 49>(&vs);
        check_rot::<21, 43>(&vs);
        check_rot::<8, 56>(&vs);
        check_rot::<18, 46>(&vs);
        check_rot::<2, 62>(&vs);
        check_rot::<61, 3>(&vs);
        check_rot::<56, 8>(&vs);
        check_rot::<14, 50>(&vs);
        eprintln!("shim ops vs intrinsics: xor, andnot, splat and 24 rotations, {} inputs each, 0 mismatches", vs.len());
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
        let shim = time(&mut |s| keccak_f1600_x4_portable(s));
        let avx = time(&mut |s| {
            avx2c::keccak_f1600_x4(s);
        });
        eprintln!("ns per call (4 permutations): 4 x scalar {four_scalar:.0}, shim x4 {shim:.0}, avx2 x4 {avx:.0}; avx2 speedup over 4 x scalar {:.2}x", four_scalar / avx);
    }
}
