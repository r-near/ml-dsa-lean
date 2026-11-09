//! The 4-way Keccak-f[1600] kernel (src/keccak4.rs) agrees with four runs of the scalar `keccak::keccak_f1600`
//! (`tests/keccak4_long.rs` is the longer version of this check).
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
fn x4_matches_four_scalar_permutations() {
    let all = states(20_000, 0x4b45_4343_414b_3478);
    for s in &all {
        let mut t = *s;
        keccak_f1600_x4(&mut t);
        assert_eq!(t, scalar(s));
    }
    eprintln!("x4 vs scalar: {} states, 0 mismatches", all.len());
}
