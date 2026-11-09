//! `tr = H(pk, 64)` in the fourth lane of the 4-way ExpandA (`sampling::expand_a_tr_into_x4`, used by
//! `verify::prepare_vk_into_x4` and `prepare_vk_x4`) against `expand_a` and the scalar SHAKE256.
//!
//! The code under test is the proved plain Rust (`lean/Proofs/TrOuter.lean` and `FastVerify.lean`); there is one compilation
//! per build (run the file with `RUSTFLAGS="-C target-feature=+avx2"` for the AVX2 build).
//!
//! Coverage: the three parameter-set shapes (K·L = 16, 30, 56) with a real-length pk (1312, 1952, 2592 bytes), small
//! matrices with pks of every length around the 136-byte block edges (0, 1, 135, 136, 137, 271, 272, 273, ...) so that the
//! lane finishes the hash (large matrix) or does not (the caller's fallback), and random and constant pks.
use ml_dsa_lean::keccak::Shake;
use ml_dsa_lean::sampling::{expand_a, expand_a_tr_into_x4};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn arr32(&mut self) -> [u8; 32] {
        let mut a = [0u8; 32];
        for b in a.iter_mut() {
            *b = self.next() as u8;
        }
        a
    }
}

fn h64(pk: &[u8]) -> [u8; 64] {
    let mut h = Shake::shake256();
    h.absorb(pk);
    h.finalize();
    let mut out = [0u8; 64];
    h.squeeze(&mut out);
    out
}

/// Runs the tr-lane ExpandA on garbage `a`; checks the matrix against `expand_a` and `tr` against `H(pk, 64)`.
fn check<const K: usize, const L: usize>(rho: &[u8; 32], pk: &[u8]) {
    let want_a = expand_a::<K, L>(rho);
    let want_tr = h64(pk);
    let mut a = [[[0xDEAD_BEEFu32; 256]; L]; K];
    let tr = expand_a_tr_into_x4::<K, L>(rho, pk, &mut a);
    assert!(a == want_a, "matrix, K={K} L={L} len={}", pk.len());
    assert_eq!(tr, want_tr, "tr, K={K} L={L} len={}", pk.len());
}

#[test]
fn parameter_set_shapes() {
    let mut rng = Rng(0x1234_5678_9ABC_DEF1);
    for _ in 0..6 {
        let rho = rng.arr32();
        check::<4, 4>(&rho, &rng.bytes(1312));
        check::<6, 5>(&rho, &rng.bytes(1952));
        check::<8, 7>(&rho, &rng.bytes(2592));
    }
    // constant and edge pks
    let rho = [0u8; 32];
    for fill in [0u8, 0xFF, 0x1F, 0x80] {
        check::<4, 4>(&rho, &vec![fill; 1312]);
        check::<6, 5>(&[0xFF; 32], &vec![fill; 1952]);
        check::<8, 7>(&rho, &vec![fill; 2592]);
    }
}

#[test]
fn every_length_around_the_block_edges() {
    let mut rng = Rng(0xDEAD_BEEF_0BAD_F00D);
    let rho = rng.arr32();
    let mut lens: Vec<usize> = (0..=3).collect();
    for m in 1..=20usize {
        for d in [-1i64, 0, 1] {
            lens.push((136 * m as i64 + d) as usize);
        }
    }
    lens.extend([8, 9, 15, 16, 17, 100, 134, 135]);
    // Matrices of every spare-lane count (n mod 4 = 0, 1, 2, 3) and size, so that the lane covers all, part or none of the
    // blocks of the pk and the scalar finish takes the rest.
    for &len in &lens {
        let pk = rng.bytes(len);
        check::<4, 4>(&rho, &pk);
        check::<6, 5>(&rho, &pk);
        check::<8, 7>(&rho, &pk);
        check::<1, 1>(&rho, &pk);
        check::<2, 1>(&rho, &pk);
        check::<1, 3>(&rho, &pk);
        check::<3, 3>(&rho, &pk);
        check::<5, 1>(&rho, &pk);
        check::<2, 7>(&rho, &pk);
    }
}
