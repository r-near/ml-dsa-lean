//! The AVX2 lane operations (`keccak4::avx2::Avx2`) against the plain-Rust model the Lean proof is about (`Shim4`), and
//! the AVX2 permutation against `Shim4` and the scalar permutation.
//!
//! This is the evidence for the link that is tested, not proved: the proof covers the kernel over `Shim4`; the shipped
//! AVX2 build runs the same kernel over `Avx2`. So the tests must be strong and must not drift from the kernel:
//!   * every operation on random, structured and edge inputs, lane by lane;
//!   * every rotation immediate the kernel uses, with the list derived from the kernel's source text (and checked
//!     against the scalar permutation's rho table), each rotation on single-bit, edge and random inputs; in fact all
//!     63 non-trivial rotations are covered;
//!   * 150,000+ whole states: AVX2 vs `Shim4` vs four scalar permutations.
//! Fixed seeds; deterministic. Needs a CPU with AVX2 (`ML_DSA_REQUIRE_AVX2=1` makes a missing AVX2 a failure).
#![cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
#![allow(clippy::needless_range_loop)]
use ml_dsa_lean::keccak::keccak_f1600;
use ml_dsa_lean::keccak4::avx2::{Avx2, keccak_f1600_x4_avx2};
use ml_dsa_lean::keccak4::{Lanes4, Shim4, keccak_f1600_x4_portable};
use std::collections::BTreeSet;

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

// The Avx2 operations are only sound inside code compiled with AVX2, so every call goes through a
// `#[target_feature(enable = "avx2")]` function, as in the shipped wrapper.
#[target_feature(enable = "avx2")]
fn xor_avx(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    Avx2::xor(a, b)
}
#[target_feature(enable = "avx2")]
fn andnot_avx(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    Avx2::andnot(a, b)
}
#[target_feature(enable = "avx2")]
fn splat_avx(x: u64) -> [u64; 4] {
    Avx2::splat(x)
}
#[target_feature(enable = "avx2")]
fn rotl_avx<const L: u32, const R: u32>(a: [u64; 4]) -> [u64; 4] {
    Avx2::rotl::<L, R>(a)
}

/// Inputs for the lane-wise operations: edge values in every lane, one-hot words, every 0/all-ones pattern across the four
/// lanes, and random words.
fn operands(r: &mut XorShift, random: usize) -> Vec<[u64; 4]> {
    let mut v = Vec::new();
    let edge = [0u64, u64::MAX, 1, 1 << 63, 0x8000_0000, 0x7fff_ffff, 0xffff_ffff, 0xffff_ffff_0000_0000, 0x5555_5555_5555_5555, 0xaaaa_aaaa_aaaa_aaaa];
    for &e in &edge {
        for lane in 0..4 {
            let mut a = [0x0123_4567_89ab_cdefu64; 4];
            a[lane] = e;
            v.push(a);
        }
        v.push([e; 4]);
    }
    // One-hot: every bit position in every lane.
    for bit in 0..64 {
        for lane in 0..4 {
            let mut a = [0u64; 4];
            a[lane] = 1 << bit;
            v.push(a);
            let mut b = [u64::MAX; 4];
            b[lane] = !(1 << bit);
            v.push(b);
        }
    }
    // Which lanes are all-ones: all 16 patterns.
    for pat in 0..16u32 {
        let mut a = [0u64; 4];
        for lane in 0..4 {
            if pat >> lane & 1 == 1 {
                a[lane] = u64::MAX;
            }
        }
        v.push(a);
    }
    for _ in 0..random {
        v.push([r.next(), r.next(), r.next(), r.next()]);
    }
    v
}

/// The rotation amounts `L::rotl::<A, B>` in `round` of src/keccak4.rs, as (A, B) pairs.
fn kernel_rotations() -> BTreeSet<(u32, u32)> {
    let src = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/keccak4.rs")).unwrap();
    let mut out = BTreeSet::new();
    let needle = "L::rotl::<";
    let mut rest = src.as_str();
    while let Some(i) = rest.find(needle) {
        rest = &rest[i + needle.len()..];
        let end = rest.find(">(").expect("rotl turbofish");
        let args: Vec<u32> = rest[..end].split(',').map(|x| x.trim().parse().unwrap_or_else(|_| panic!("rotl arg {x:?}"))).collect();
        assert_eq!(args.len(), 2, "rotl::<L, R>");
        out.insert((args[0], args[1]));
    }
    out
}

/// The nonzero entries of the scalar permutation's rho table (src/keccak.rs `RHO`), plus 1 for theta: the rotations a
/// Keccak-f[1600] round needs.
fn expected_rotations() -> BTreeSet<u32> {
    let src = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/keccak.rs")).unwrap();
    let i = src.find("const RHO").expect("RHO table in keccak.rs");
    let body = &src[src[i..].find("= [").unwrap() + i + 3..];
    let body = &body[..body.find("];").unwrap()];
    let mut out: BTreeSet<u32> = body.split(',').filter_map(|x| x.trim().parse().ok()).filter(|&x| x != 0).collect();
    // theta's rotation by 1 coincides with the rho offset of lane 1.
    out.insert(1);
    assert_eq!(out.len(), 24, "24 distinct nonzero rotation amounts in the rho table");
    out
}

fn check_rot<const L: u32, const R: u32>(vs: &[[u64; 4]]) {
    assert_eq!(L + R, 64);
    for &a in vs {
        // SAFETY: the caller checked AVX2.
        assert_eq!(unsafe { rotl_avx::<L, R>(a) }, Shim4::rotl::<L, R>(a), "rotl {L} on {a:x?}");
    }
}

/// Runs `check_rot::<l, 64 - l>`: the const generics need literals, hence the table.
fn check_rot_dyn(l: u32, vs: &[[u64; 4]]) {
    match l {
            1 => check_rot::<1, 63>(vs),
            2 => check_rot::<2, 62>(vs),
            3 => check_rot::<3, 61>(vs),
            4 => check_rot::<4, 60>(vs),
            5 => check_rot::<5, 59>(vs),
            6 => check_rot::<6, 58>(vs),
            7 => check_rot::<7, 57>(vs),
            8 => check_rot::<8, 56>(vs),
            9 => check_rot::<9, 55>(vs),
            10 => check_rot::<10, 54>(vs),
            11 => check_rot::<11, 53>(vs),
            12 => check_rot::<12, 52>(vs),
            13 => check_rot::<13, 51>(vs),
            14 => check_rot::<14, 50>(vs),
            15 => check_rot::<15, 49>(vs),
            16 => check_rot::<16, 48>(vs),
            17 => check_rot::<17, 47>(vs),
            18 => check_rot::<18, 46>(vs),
            19 => check_rot::<19, 45>(vs),
            20 => check_rot::<20, 44>(vs),
            21 => check_rot::<21, 43>(vs),
            22 => check_rot::<22, 42>(vs),
            23 => check_rot::<23, 41>(vs),
            24 => check_rot::<24, 40>(vs),
            25 => check_rot::<25, 39>(vs),
            26 => check_rot::<26, 38>(vs),
            27 => check_rot::<27, 37>(vs),
            28 => check_rot::<28, 36>(vs),
            29 => check_rot::<29, 35>(vs),
            30 => check_rot::<30, 34>(vs),
            31 => check_rot::<31, 33>(vs),
            32 => check_rot::<32, 32>(vs),
            33 => check_rot::<33, 31>(vs),
            34 => check_rot::<34, 30>(vs),
            35 => check_rot::<35, 29>(vs),
            36 => check_rot::<36, 28>(vs),
            37 => check_rot::<37, 27>(vs),
            38 => check_rot::<38, 26>(vs),
            39 => check_rot::<39, 25>(vs),
            40 => check_rot::<40, 24>(vs),
            41 => check_rot::<41, 23>(vs),
            42 => check_rot::<42, 22>(vs),
            43 => check_rot::<43, 21>(vs),
            44 => check_rot::<44, 20>(vs),
            45 => check_rot::<45, 19>(vs),
            46 => check_rot::<46, 18>(vs),
            47 => check_rot::<47, 17>(vs),
            48 => check_rot::<48, 16>(vs),
            49 => check_rot::<49, 15>(vs),
            50 => check_rot::<50, 14>(vs),
            51 => check_rot::<51, 13>(vs),
            52 => check_rot::<52, 12>(vs),
            53 => check_rot::<53, 11>(vs),
            54 => check_rot::<54, 10>(vs),
            55 => check_rot::<55, 9>(vs),
            56 => check_rot::<56, 8>(vs),
            57 => check_rot::<57, 7>(vs),
            58 => check_rot::<58, 6>(vs),
            59 => check_rot::<59, 5>(vs),
            60 => check_rot::<60, 4>(vs),
            61 => check_rot::<61, 3>(vs),
            62 => check_rot::<62, 2>(vs),
            63 => check_rot::<63, 1>(vs),
        _ => panic!("rotation {l} is not in 1..=63"),
    }
}

#[test]
fn the_kernel_uses_exactly_the_rotations_of_keccak() {
    let used = kernel_rotations();
    assert!(used.iter().all(|&(l, r)| l + r == 64 && l > 0 && l < 64), "R must be 64 - L: {used:?}");
    let used_l: BTreeSet<u32> = used.iter().map(|&(l, _)| l).collect();
    // The rho table has one duplicate-free set of offsets; the kernel must use each one (and theta's 1), no others.
    assert_eq!(used_l, expected_rotations(), "kernel rotations vs the scalar RHO table");
}

#[test]
fn each_avx2_op_matches_shim4_lane_by_lane() {
    if !have_avx2() {
        eprintln!("no AVX2: skipped");
        return;
    }
    let mut r = XorShift(0x6f70_7331_6f70_7332);
    let vs = operands(&mut r, 20_000);
    let ws = operands(&mut r, 20_000);
    let mut n = 0;
    for (i, &a) in vs.iter().enumerate() {
        // Pair every operand with its partner at the same index and with a rotated partner, so edge x edge is covered.
        for &b in [ws[i], ws[(i * 7 + 3) % ws.len()], a].iter() {
            // SAFETY: AVX2 was detected above.
            unsafe {
                assert_eq!(xor_avx(a, b), Shim4::xor(a, b), "xor {a:x?} {b:x?}");
                assert_eq!(andnot_avx(a, b), Shim4::andnot(a, b), "andnot {a:x?} {b:x?}");
            }
            n += 1;
        }
        for lane in 0..4 {
            // SAFETY: as above.
            assert_eq!(unsafe { splat_avx(a[lane]) }, Shim4::splat(a[lane]));
        }
    }
    // Lane independence: changing one lane of one operand changes only that lane of the result.
    for &a in vs.iter().take(2000) {
        let b = [a[1], a[2], a[3], a[0]];
        // SAFETY: as above.
        let (x, y) = unsafe { (xor_avx(a, b), andnot_avx(a, b)) };
        for lane in 0..4 {
            assert_eq!(x[lane], a[lane] ^ b[lane]);
            assert_eq!(y[lane], !a[lane] & b[lane]);
        }
    }
    eprintln!("xor/andnot/splat: {n} operand pairs, 0 mismatches");
}

#[test]
fn every_rotation_the_kernel_uses_matches_shim4() {
    if !have_avx2() {
        eprintln!("no AVX2: skipped");
        return;
    }
    let mut r = XorShift(0x726f_746c_726f_746c);
    let vs = operands(&mut r, 4_000);
    let used: BTreeSet<u32> = kernel_rotations().iter().map(|&(l, _)| l).collect();
    // Every rotation the kernel uses (derived from its source) ...
    for &l in &used {
        check_rot_dyn(l, &vs);
    }
    // ... and, for good measure, every non-trivial rotation amount.
    let mut all = 0;
    for l in 1..64 {
        check_rot_dyn(l, &vs[..400]);
        all += 1;
    }
    eprintln!("rotations: {} used by the kernel x {} operands, plus all {all} amounts x 400 operands, 0 mismatches", used.len(), vs.len());
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
fn avx2_permutation_equals_shim4_and_four_scalar_permutations() {
    if !have_avx2() {
        eprintln!("no AVX2: skipped");
        return;
    }
    let all = states(150_000, 0x4b45_4343_4146_5631);
    assert!(all.len() > 150_000);
    for s in &all {
        let mut a = *s;
        // SAFETY: AVX2 was detected above.
        unsafe { keccak_f1600_x4_avx2(&mut a) };
        let mut p = *s;
        keccak_f1600_x4_portable(&mut p);
        assert_eq!(a, p, "avx2 vs shim, input {s:x?}");
        assert_eq!(a, scalar(s), "avx2 vs four scalar permutations, input {s:x?}");
    }
    // Iterated: feed the output back in (the squeeze loop does exactly this), so state evolves through many blocks.
    let mut a = all[all.len() / 2];
    let mut p = a;
    for _ in 0..2_000 {
        // SAFETY: as above.
        unsafe { keccak_f1600_x4_avx2(&mut a) };
        keccak_f1600_x4_portable(&mut p);
        assert_eq!(a, p);
    }
    eprintln!("avx2 x4 vs shim vs scalar: {} states, plus a 2000-permutation chain, 0 mismatches", all.len());
}
