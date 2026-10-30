//! Leaf-algorithm tests: encoders/decoders, ExpandS, Power2Round, HintBitUnpack, UseHint,
//! CoeffFromHalfByte, with RustCrypto `ml-dsa` as the oracle where it exposes the data.
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed};
use ml_dsa_verified::encode::*;
use ml_dsa_verified::field::Q;
use ml_dsa_verified::keccak::Shake;
use ml_dsa_verified::params::*;
use ml_dsa_verified::rounding::*;
use ml_dsa_verified::sampling::*;

fn seed(i: u8) -> Seed {
    let mut s = Seed::default();
    for (j, b) in s.iter_mut().enumerate() {
        *b = (j as u8).wrapping_mul(37).wrapping_add(i).wrapping_add(5);
    }
    s
}

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

const N_SEEDS: u8 = 12;

fn per_set<P: MlDsaParams, const K: usize, const L: usize>(p: &Params) {
    for i in 0..N_SEEDS {
        let xi = seed(i);
        let esk = ExpandedSigningKey::<P>::from_seed(&xi);
        let sk = esk.to_expanded();
        let sk = sk.as_slice();
        let pk = esk.verifying_key().encode();
        let pk = pk.as_slice();
        assert_eq!(sk.len(), sk_len(p));

        // skEncode round trip
        let d = sk_decode::<K, L>(p, sk);
        let mut out = vec![0u8; sk_len(p)];
        sk_encode::<K, L>(p, &d.rho, &d.key, &d.tr, &d.s1, &d.s2, &d.t0, &mut out);
        assert_eq!(out.as_slice(), sk, "skEncode round trip, seed {i}");

        // pk round trip
        let (rho, t1) = pk_decode::<K>(pk);
        let mut pout = vec![0u8; 32 + 320 * K];
        assert_eq!(pout.len(), pk.len());
        pk_encode::<K>(&rho, &t1, &mut pout);
        assert_eq!(pout.as_slice(), pk, "pkEncode round trip, seed {i}");
        assert_eq!(rho, d.rho);

        // sigDecode / sigEncode round trip on an upstream signature
        let msg: Vec<u8> = (0..(i as usize * 11) % 200).map(|j| (j * 7 + i as usize) as u8).collect();
        let rnd = ml_dsa::B32::from([i; 32]);
        let sig = esk.sign_internal(&[&msg], &rnd).encode();
        let sig = sig.as_slice();
        assert_eq!(sig.len(), sig_len(p));
        let (ct, z, h) = sig_decode::<K, L>(p, sig).expect("valid signature must decode");
        let mut sout = vec![0u8; sig_len(p)];
        sig_encode::<K, L>(p, &ct[..p.c_tilde_len], &z, &h, &mut sout);
        assert_eq!(sout.as_slice(), sig, "sigEncode round trip, seed {i}");

        // ExpandS against the secret key's s1, s2: ρ′ = bytes 32..96 of H(ξ || k || l, 128)
        let mut sh = Shake::shake256();
        sh.absorb(xi.as_slice());
        sh.absorb(&[K as u8, L as u8]);
        sh.finalize();
        let mut hout = [0u8; 128];
        sh.squeeze(&mut hout);
        assert_eq!(&hout[..32], &d.rho[..]);
        let mut rho_p = [0u8; 64];
        rho_p.copy_from_slice(&hout[32..96]);
        assert_eq!(&hout[96..], &d.key[..]);
        let (s1, s2) = expand_s::<K, L>(p, &rho_p);
        assert!(s1 == d.s1, "ExpandS s1, seed {i}");
        assert!(s2 == d.s2, "ExpandS s2, seed {i}");

        // Power2Round: t = t1·2^13 + t0 mod q
        for r in 0..K {
            let mut t = [0u32; 256];
            for j in 0..256 {
                t[j] = ((t1[r][j] as u64 * 8192 + d.t0[r][j] as u64) % Q as u64) as u32;
            }
            let (a, b) = poly_power2round(&t);
            assert!(a == t1[r] && b == d.t0[r], "Power2Round, seed {i} row {r}");
        }
    }
}

#[test]
fn encode_decode_roundtrips_and_expand_s() {
    per_set::<MlDsa44, 4, 4>(&ML_DSA_44);
    per_set::<MlDsa65, 6, 5>(&ML_DSA_65);
    per_set::<MlDsa87, 8, 7>(&ML_DSA_87);
}

#[test]
fn power2round_naive() {
    let mut x = 0u32;
    while x < Q {
        let (r1, r0) = power2round(x);
        // r0 = x mod± 2^13 in (−2^12, 2^12]
        let mut m = (x % 8192) as i64;
        if m > 4096 {
            m -= 8192;
        }
        let r0c = if m < 0 { (m + Q as i64) as u32 } else { m as u32 };
        assert_eq!(r0, r0c);
        assert_eq!(r1 as i64 * 8192 + m, x as i64);
        x += 7;
    }
}

// ---- HintBitUnpack ----

fn pack_unpack_params() -> [(&'static Params, usize); 3] {
    [(&ML_DSA_44, 4), (&ML_DSA_65, 6), (&ML_DSA_87, 8)]
}

#[test]
fn hint_roundtrip() {
    fn go<const K: usize>(p: &Params) {
        let mut rng = XorShift(0x1234_5678_9abc_def1);
        for _ in 0..200 {
            let mut h = [[false; 256]; K];
            let mut total = 0;
            while total < p.omega && rng.next() % 16 != 0 {
                let i = (rng.next() % K as u64) as usize;
                let j = (rng.next() % 256) as usize;
                if !h[i][j] {
                    h[i][j] = true;
                    total += 1;
                }
            }
            let mut y = vec![0u8; p.omega + K];
            hint_bit_pack::<K>(p, &h, &mut y);
            let back = hint_bit_unpack::<K>(p, &y).expect("packed hint must unpack");
            assert!(back == h);
        }
    }
    go::<4>(&ML_DSA_44);
    go::<6>(&ML_DSA_65);
    go::<8>(&ML_DSA_87);
}

#[test]
fn hint_unpack_bottom_cases() {
    for (p, k) in pack_unpack_params() {
        let w = p.omega;
        let mk = |idx: &[u8], counts: &[u8]| {
            let mut y = vec![0u8; w + k];
            for (i, b) in idx.iter().enumerate() {
                y[i] = *b;
            }
            for (i, c) in counts.iter().enumerate() {
                y[w + i] = *c;
            }
            // counts omitted for trailing polys repeat the last count
            let last = *counts.last().unwrap();
            for i in counts.len()..k {
                y[w + i] = last;
            }
            y
        };
        let un = |y: &[u8]| match k {
            4 => hint_bit_unpack::<4>(p, y).is_some(),
            6 => hint_bit_unpack::<6>(p, y).is_some(),
            _ => hint_bit_unpack::<8>(p, y).is_some(),
        };
        // sanity: valid
        assert!(un(&mk(&[1, 2, 3, 4, 5], &[3, 5])));
        assert!(un(&mk(&[0], &[0])));
        assert!(un(&mk(&[], &[0])));
        // count decreasing across polynomials
        assert!(!un(&mk(&[1, 2, 3, 4, 5], &[5, 3])));
        // count > ω (first, and later poly)
        assert!(!un(&mk(&[], &[w as u8 + 1])));
        assert!(!un(&mk(&[1], &[1, w as u8 + 1])));
        // count == ω is allowed only with ω valid increasing indices
        let full: Vec<u8> = (0..w as u8).collect();
        assert!(un(&mk(&full, &[w as u8])));
        // equal indices within a polynomial
        assert!(!un(&mk(&[7, 7], &[2])));
        // decreasing indices within a polynomial
        assert!(!un(&mk(&[9, 7], &[2])));
        // indices may restart (decrease) at a polynomial boundary
        assert!(un(&mk(&[9, 7], &[1, 2])));
        // equal across the boundary is fine too
        assert!(un(&mk(&[7, 7], &[1, 2])));
        // nonzero padding after the last index
        let mut y = mk(&[3, 4], &[2]);
        y[2] = 1;
        assert!(!un(&y));
        let mut y = mk(&[3, 4], &[2]);
        y[w - 1] = 1;
        assert!(!un(&y));
        // 0xFF index values are fine
        assert!(un(&mk(&[255], &[1])));
    }
}

// ---- UseHint / Decompose, naive i64 ----

fn naive_decompose(r: i64, g2: i64) -> (i64, i64) {
    let q = Q as i64;
    let a = 2 * g2;
    let rp = r.rem_euclid(q);
    let mut r0 = rp.rem_euclid(a);
    if r0 > a / 2 {
        r0 -= a;
    }
    if rp - r0 == q - 1 { (0, r0 - 1) } else { ((rp - r0) / a, r0) }
}
fn naive_use_hint(h: bool, r: i64, g2: i64) -> i64 {
    let m = (Q as i64 - 1) / (2 * g2);
    let (r1, r0) = naive_decompose(r, g2);
    if h {
        if r0 > 0 { (r1 + 1).rem_euclid(m) } else { (r1 - 1).rem_euclid(m) }
    } else {
        r1
    }
}

#[test]
fn use_hint_exhaustive() {
    for p in [&ML_DSA_44, &ML_DSA_65] {
        let g2 = p.gamma2 as i64;
        for r in 0..Q {
            for h in [false, true] {
                assert_eq!(
                    use_hint(p, h, r) as i64,
                    naive_use_hint(h, r as i64, g2),
                    "r={r} h={h} g2={g2}"
                );
            }
            if r % 1_000_003 == 0 {
                let (r1, r0) = decompose(p, r);
                let (n1, n0) = naive_decompose(r as i64, g2);
                assert_eq!(r1 as i64, n1);
                assert_eq!(r0 as i64, n0.rem_euclid(Q as i64));
            }
        }
    }
    // ML-DSA-87 shares γ2 with ML-DSA-65 but check the params anyway on a stride
    let g2 = ML_DSA_87.gamma2 as i64;
    for r in (0..Q).step_by(97) {
        assert_eq!(use_hint(&ML_DSA_87, true, r) as i64, naive_use_hint(true, r as i64, g2));
    }
}

#[test]
fn coeff_from_half_byte_naive() {
    for p in [&ML_DSA_44, &ML_DSA_65, &ML_DSA_87] {
        let eta = p.eta as i64;
        for b in 0..=255u8 {
            let naive: Option<i64> = if eta == 2 && b < 15 {
                Some(2 - (b as i64 % 5))
            } else if eta == 4 && b < 9 {
                Some(4 - b as i64)
            } else {
                None
            };
            let got = coeff_from_half_byte(p, b).map(|v| {
                assert!(v < Q);
                if v > Q / 2 { v as i64 - Q as i64 } else { v as i64 }
            });
            assert_eq!(got, naive, "eta={eta} b={b}");
        }
    }
}

// ---- no-panic fuzz ----

#[test]
fn sig_decode_no_panic() {
    fn go<const K: usize, const L: usize>(p: &Params, valid: &[u8]) {
        let mut rng = XorShift(0x9e37_79b9_7f4a_7c15);
        let len = sig_len(p);
        let hint_start = len - p.omega - K;
        let (mut some, mut none) = (0, 0);
        for n in 0..2000 {
            let mut s = vec![0u8; len];
            for b in s.iter_mut() {
                *b = rng.next() as u8;
            }
            if n % 2 == 1 {
                // plausible hint region: sorted indices, nondecreasing counts <= ω
                let mut cnt = 0usize;
                for i in 0..K {
                    cnt += (rng.next() as usize) % (p.omega / K + 2);
                    cnt = cnt.min(p.omega);
                    s[hint_start + p.omega + i] = cnt as u8;
                }
                let mut prev = 0u8;
                for j in 0..p.omega {
                    prev = prev.wrapping_add((rng.next() % 5) as u8 + 1);
                    s[hint_start + j] = if j < cnt { prev } else { 0 };
                }
            }
            if sig_decode::<K, L>(p, &s).is_some() { some += 1 } else { none += 1 }
        }
        // mutations of a valid signature's hint region
        for _ in 0..2000 {
            let mut s = valid.to_vec();
            let pos = hint_start + (rng.next() as usize) % (p.omega + K);
            s[pos] = rng.next() as u8;
            if sig_decode::<K, L>(p, &s).is_some() { some += 1 } else { none += 1 }
        }
        assert!(some > 0 && none > 0, "fuzz should hit both outcomes: {some}/{none}");
    }
    fn valid<P: MlDsaParams>() -> Vec<u8> {
        let esk = ExpandedSigningKey::<P>::from_seed(&seed(3));
        esk.sign_internal(&[b"m"], &ml_dsa::B32::from([1u8; 32])).encode().as_slice().to_vec()
    }
    go::<4, 4>(&ML_DSA_44, &valid::<MlDsa44>());
    go::<6, 5>(&ML_DSA_65, &valid::<MlDsa65>());
    go::<8, 7>(&ML_DSA_87, &valid::<MlDsa87>());
}
