//! The verify-only arithmetic (`verify_arith`, `rounding::vec_norm_lt_pub`, `encode::bit_pack_pub`) against the shared
//! constant-time functions it replaces on verify's path, on random and extreme inputs. These are compiled as ordinary
//! code here (not inside the AVX2 wrapper); the dispatched verify is compared with the scalar verify end to end in
//! `tests/fast_verify.rs`, and the equalities are proved in `Proofs/VerifyArith.lean`.
use ml_dsa_lean::encode::{bit_pack, bit_pack_pub};
use ml_dsa_lean::field::Q;
use ml_dsa_lean::ntt::{add_poly, multiply_ntt, ntt, ntt_inverse, sub_poly};
use ml_dsa_lean::rounding::{vec_infinity_norm, vec_norm_lt_pub};
use ml_dsa_lean::verify_arith::{mac_row_pub, ntt_inverse_pub, ntt_pub, ntt_vec_pub};

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
    fn coeff(&mut self) -> u32 {
        (self.next() % Q as u64) as u32
    }
    fn poly(&mut self) -> [u32; 256] {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = self.coeff();
        }
        p
    }
}

/// Canonical polynomials at the corners of the input range, besides the random ones.
fn extreme_polys() -> Vec<[u32; 256]> {
    let mut v = vec![[0u32; 256], [Q - 1; 256], [1; 256], [(Q - 1) / 2; 256], [(Q + 1) / 2; 256]];
    let mut alt = [0u32; 256];
    for (i, x) in alt.iter_mut().enumerate() {
        *x = if i % 2 == 0 { Q - 1 } else { 0 };
    }
    v.push(alt);
    for i in 0..256 {
        let mut one = [0u32; 256];
        one[i] = Q - 1;
        v.push(one);
    }
    v
}

#[test]
fn ntt_pub_matches_ntt() {
    let mut r = XorShift(0x1234_5678_9abc_def1);
    let mut inputs = extreme_polys();
    for _ in 0..4000 {
        inputs.push(r.poly());
    }
    for w in &inputs {
        assert_eq!(ntt_pub(w), ntt(w));
        assert_eq!(ntt_inverse_pub(w), ntt_inverse(w));
    }
    let v = [inputs[0], inputs[1], inputs[8], inputs[100], inputs[200]];
    let got = ntt_vec_pub(&v);
    for (g, w) in got.iter().zip(v.iter()) {
        assert_eq!(*g, ntt(w));
    }
}

fn mac_case<const L: usize>(r: &mut XorShift, special: u8) {
    let mut a = [[0u32; 256]; L];
    let mut z = [[0u32; 256]; L];
    for l in 0..L {
        a[l] = if special == 1 { [Q - 1; 256] } else { r.poly() };
        z[l] = if special == 1 { [Q - 1; 256] } else { r.poly() };
    }
    let c = if special == 1 { [Q - 1; 256] } else { r.poly() };
    let t = if special == 1 { [0; 256] } else { r.poly() };
    let t2 = if special == 1 { [Q - 1; 256] } else { t };
    for t in [t, t2] {
        // The shared computation: Σ multiply_ntt(a_l, z_l) via add_poly, minus multiply_ntt(c, t).
        let mut acc = [0u32; 256];
        for l in 0..L {
            acc = add_poly(&acc, &multiply_ntt(&a[l], &z[l]));
        }
        let want = sub_poly(&acc, &multiply_ntt(&c, &t));
        assert_eq!(mac_row_pub::<L>(&a, &z, &c, &t), want);
    }
}

#[test]
fn mac_row_pub_matches_matrix_vector_row() {
    let mut r = XorShift(0x0fed_cba9_8765_4321);
    for i in 0..300 {
        let special = if i % 50 == 0 { 1 } else { 0 };
        mac_case::<4>(&mut r, special);
        mac_case::<5>(&mut r, special);
        mac_case::<7>(&mut r, special);
    }
}

#[test]
fn vec_norm_lt_pub_matches_vec_infinity_norm() {
    let mut r = XorShift(0xdead_beef_cafe_f00d);
    // bounds γ1 − β of the three sets, and the edges around them
    let bounds = [131_072 - 196, 524_288 - 196, 524_288 - 120, 524_288 - 275, 1, 2, 4_190_208, Q - 1];
    for &bound in &bounds {
        // an entry of exactly the norm `n` at position `pos`, positive or negative, among small values
        for n in [0u32, 1, bound - 1, bound, bound + 1, (Q - 1) / 2, (Q - 1) / 2 - 1] {
            for neg in [false, true] {
                for pos in [0usize, 1, 255] {
                    let mut w = [[0u32; 256]; 3];
                    w[1][pos] = if neg && n != 0 { Q - n } else { n };
                    assert_eq!(vec_norm_lt_pub(&w, bound), vec_infinity_norm(&w) < bound, "bound {bound} n {n} neg {neg}");
                }
            }
        }
        for _ in 0..2000 {
            let mut w = [[0u32; 256]; 2];
            let spread = 1 + (r.next() % 32) as u32;
            for p in w.iter_mut() {
                for x in p.iter_mut() {
                    // mostly small entries, sometimes any canonical value
                    *x = if r.next() % 8 == 0 { r.coeff() } else { (r.next() % (bound as u64 * spread as u64 / 16 + 1) % Q as u64) as u32 };
                    let x2 = if r.next() % 2 == 0 { *x } else { (Q - *x) % Q };
                    *x = x2;
                }
            }
            assert_eq!(vec_norm_lt_pub(&w, bound), vec_infinity_norm(&w) < bound);
        }
    }
}

#[test]
fn bit_pack_pub_matches_bit_pack() {
    let mut r = XorShift(0x7777_1111_3333_5555);
    for c in [1usize, 4, 6, 8, 10] {
        for round in 0..400 {
            let mut w = [0u32; 256];
            for x in w.iter_mut() {
                *x = match round {
                    0 => 0,
                    1 => (1u32 << c) - 1,
                    _ => (r.next() as u32) & ((1u32 << c) - 1),
                };
            }
            let mut want = vec![0u8; 32 * c];
            let mut got = vec![0xa5u8; 32 * c];
            bit_pack(&w, c, &mut want);
            bit_pack_pub(&w, c, &mut got);
            assert_eq!(got, want, "c = {c}");
        }
    }
}
