//! The Shoup/Montgomery NTT arithmetic against plain `u64 %` arithmetic and the original Barrett butterflies.
use ml_dsa_lean::field::{self, Q};
use ml_dsa_lean::ntt::{self, F_SHOUP, ZETAS, ZETAS_NEG_SHOUP, ZETAS_SHOUP};

const QU: u64 = Q as u64;

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
        (self.next() % QU) as u32
    }
}

fn companion(z: u32) -> u32 {
    (((z as u64) << 32) / QU) as u32
}

#[test]
fn tables_match_their_definition() {
    for k in 0..256 {
        assert_eq!(ZETAS_SHOUP[k], companion(ZETAS[k]), "ZETAS_SHOUP[{k}]");
        assert_eq!(ZETAS_NEG_SHOUP[k], companion(Q - ZETAS[k]), "ZETAS_NEG_SHOUP[{k}]");
    }
    assert_eq!(F_SHOUP, companion(8_347_681));
    assert_eq!(8_347_681u64 * 256 % QU, 1);
}

#[test]
fn mul_shoup_exact() {
    let mut r = XorShift(0x9e37_79b9_7f4a_7c15);
    let mut zs: Vec<u32> = ZETAS.to_vec();
    zs.extend(ZETAS.iter().map(|z| Q - z));
    zs.extend([0, 1, Q - 1, 8_347_681]);
    for _ in 0..2000 {
        zs.push(r.coeff());
    }
    for &z in &zs {
        let zp = companion(z);
        let check = |x: u32| {
            let want = ((z as u64 * x as u64) % QU) as u32;
            assert_eq!(field::mul_shoup(z, zp, x), want, "z={z} x={x}");
            if x < Q {
                assert_eq!(field::mul(z, x), want);
            }
        };
        for x in [0, 1, 2, Q - 2, Q - 1, Q, Q + 1, 2 * Q - 1, u32::MAX, u32::MAX - 1, 1 << 31] {
            check(x);
        }
        for x in (0..Q).step_by(4093) {
            check(x);
        }
        for _ in 0..200 {
            check(r.next() as u32);
        }
    }
    // A few twiddles against every canonical x.
    for &z in &[ZETAS[1], ZETAS[255], Q - ZETAS[128], 8_347_681] {
        let zp = companion(z);
        for x in 0..Q {
            assert_eq!(field::mul_shoup(z, zp, x) as u64, z as u64 * x as u64 % QU);
        }
    }
}

#[test]
fn mul_mont_exact() {
    let mut r = XorShift(0x1234_5678_9abc_def1);
    let edge = [0, 1, 2, 3, 4096, 1 << 22, 1 << 23, Q / 2, Q / 2 + 1, Q - 3, Q - 2, Q - 1];
    for &a in &edge {
        for &b in &edge {
            assert_eq!(field::mul_mont(a, b) as u64, a as u64 * b as u64 % QU, "a={a} b={b}");
        }
    }
    for _ in 0..2_000_000 {
        let (a, b) = (r.coeff(), r.coeff());
        assert_eq!(field::mul_mont(a, b), field::mul(a, b));
    }
    for a in (0..Q).step_by(1019) {
        for b in (0..Q).step_by(7919) {
            assert_eq!(field::mul_mont(a, b) as u64, a as u64 * b as u64 % QU);
        }
    }
    // The reduction alone: a * 2^-32 mod q in [0, 2q) for a < 2^32 q.
    for _ in 0..200_000 {
        let a = r.next() % ((1u64 << 32) * QU);
        let y = field::mont_reduce(a) as u64;
        assert!(y < 2 * QU);
        assert_eq!(y * (1 << 32) % QU, a % QU);
    }
}

fn ref_ntt(w: &[u32; 256]) -> [u32; 256] {
    let mut w = *w;
    let (mut m, mut len) = (0, 128);
    while len >= 1 {
        let mut start = 0;
        while start < 256 {
            m += 1;
            let z = ZETAS[m] as u64;
            for j in start..start + len {
                let t = (z * w[j + len] as u64 % QU) as u32;
                w[j + len] = (w[j] + Q - t) % Q;
                w[j] = (w[j] + t) % Q;
            }
            start += 2 * len;
        }
        len /= 2;
    }
    w
}

fn ref_ntt_inverse(w: &[u32; 256]) -> [u32; 256] {
    let mut w = *w;
    let (mut m, mut len) = (256, 1);
    while len < 256 {
        let mut start = 0;
        while start < 256 {
            m -= 1;
            let z = (Q - ZETAS[m]) as u64;
            for j in start..start + len {
                let t = w[j];
                w[j] = (t + w[j + len]) % Q;
                w[j + len] = (z * ((t + Q - w[j + len]) % Q) as u64 % QU) as u32;
            }
            start += 2 * len;
        }
        len *= 2;
    }
    for x in w.iter_mut() {
        *x = (8_347_681u64 * *x as u64 % QU) as u32;
    }
    w
}

fn polys(r: &mut XorShift) -> Vec<[u32; 256]> {
    let mut v = vec![[0u32; 256], [Q - 1; 256], [1; 256]];
    let mut alt = [0u32; 256];
    for (i, x) in alt.iter_mut().enumerate() {
        *x = if i % 2 == 0 { Q - 1 } else { 0 };
    }
    v.push(alt);
    for _ in 0..300 {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = r.coeff();
        }
        v.push(p);
    }
    v
}

#[test]
fn ntt_matches_reference() {
    let mut r = XorShift(0xdead_beef_cafe_f00d);
    for p in polys(&mut r) {
        assert_eq!(ntt::ntt(&p), ref_ntt(&p));
        assert_eq!(ntt::ntt_inverse(&p), ref_ntt_inverse(&p));
        assert_eq!(ntt::ntt_inverse(&ntt::ntt(&p)), p);
    }
}

#[test]
fn multiply_ntt_matches_reference() {
    let mut r = XorShift(0x0bad_5eed_0bad_5eed);
    let ps = polys(&mut r);
    for (i, a) in ps.iter().enumerate() {
        let b = &ps[(i * 7 + 3) % ps.len()];
        let got = ntt::multiply_ntt(a, b);
        for k in 0..256 {
            assert_eq!(got[k] as u64, a[k] as u64 * b[k] as u64 % QU);
        }
    }
}
