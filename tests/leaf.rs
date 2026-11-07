//! Leaf-algorithm tests: encoders/decoders, ExpandS, Power2Round, HintBitUnpack, UseHint,
//! CoeffFromHalfByte, with RustCrypto `ml-dsa` as the oracle where it exposes the data.
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed};
use ml_dsa_lean::encode::*;
use ml_dsa_lean::field::Q;
use ml_dsa_lean::keccak::Shake;
use ml_dsa_lean::params::*;
use ml_dsa_lean::rounding::*;
use ml_dsa_lean::sampling::*;

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
        assert!(ct[p.c_tilde_len..].iter().all(|&b| b == 0), "c̃ buffer must be zero beyond c_tilde_len, seed {i}");
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
    // Exhaustive over 0..q.
    for x in 0..Q {
        let (r1, r0) = power2round(x);
        // r0 = x mod± 2^13 in (−2^12, 2^12]
        let mut m = (x % 8192) as i64;
        if m > 4096 {
            m -= 8192;
        }
        let r0c = if m < 0 { (m + Q as i64) as u32 } else { m as u32 };
        assert_eq!(r0, r0c, "x={x}");
        assert_eq!(r1 as i64 * 8192 + m, x as i64, "x={x}");
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
fn decompose_and_use_hint_exhaustive() {
    // Exhaustive over 0..q, both h values, for γ2 = 95232 (ML-DSA-44) and 261888 (ML-DSA-65 and -87).
    for p in [&ML_DSA_44, &ML_DSA_65, &ML_DSA_87] {
        let g2 = p.gamma2 as i64;
        assert!(g2 == 95_232 || g2 == 261_888);
        for r in 0..Q {
            let (r1, r0) = decompose(p, r);
            let (n1, n0) = naive_decompose(r as i64, g2);
            assert_eq!(r1 as i64, n1, "decompose r1, r={r} g2={g2}");
            assert_eq!(r0 as i64, n0.rem_euclid(Q as i64), "decompose r0, r={r} g2={g2}");
            for h in [false, true] {
                assert_eq!(use_hint(p, h, r) as i64, naive_use_hint(h, r as i64, g2), "r={r} h={h} g2={g2}");
            }
        }
    }
}

#[test]
fn poly_use_hint_pub_matches_poly_use_hint_exhaustive() {
    // The verify-path UseHint against the constant-time one on every r < q, both h values, all three parameter sets
    // (256 coefficients per call, hints alternating so that each r sees both).
    for p in [&ML_DSA_44, &ML_DSA_65, &ML_DSA_87] {
        let mut base = 0u32;
        while base < Q {
            for flip in [false, true] {
                let mut r = [0u32; 256];
                let mut h = [false; 256];
                for j in 0..256 {
                    // Coefficients past q - 1 repeat q - 1: they are not canonical otherwise.
                    r[j] = (base + j as u32).min(Q - 1);
                    h[j] = (j % 2 == 0) != flip;
                }
                assert_eq!(poly_use_hint_pub(p, &h, &r), poly_use_hint(p, &h, &r), "base={base} flip={flip} g2={}", p.gamma2);
            }
            base += 256;
        }
    }
}

#[test]
fn bit_unpack_pub_matches_bit_unpack() {
    // Random, all-zero, all-ones and single-bit inputs for the three widths of the verify path.
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for c in [10usize, 18, 20] {
        let n = 32 * c;
        let mut cases: Vec<Vec<u8>> = vec![vec![0; n], vec![0xff; n], vec![0xaa; n], vec![0x55; n]];
        for bit in 0..8 * n {
            let mut v = vec![0u8; n];
            v[bit / 8] = 1 << (bit % 8);
            cases.push(v);
        }
        for _ in 0..2000 {
            cases.push((0..n).map(|_| next() as u8).collect());
        }
        for v in &cases {
            assert_eq!(bit_unpack_pub(v, c), bit_unpack(v, c), "c={c}");
        }
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

// ---- HintBitUnpack, FIPS 204 Algorithm 21 corner cases ----
//
// Alg 21: Index ← 0; for each poly i: ⊥ if y[ω+i] < Index or y[ω+i] > ω; for Index in [First, y[ω+i]):
// ⊥ if Index > First and y[Index−1] ≥ y[Index]; set h_i[y[Index]]. Then ⊥ if any y[Index..ω) ≠ 0.
// So a count of ω is legal, but it consumes every index byte, which must then be strictly increasing within
// each polynomial; there is no padding left to check. A count < ω leaves y[count..ω) which must be zero.

/// All set positions (poly, coefficient) of the decoded hint, or None for ⊥.
fn unpack_bits(p: &Params, y: &[u8]) -> Option<Vec<(usize, usize)>> {
    fn flat<const K: usize>(h: [[bool; 256]; K]) -> Vec<(usize, usize)> {
        let mut v = Vec::new();
        for i in 0..K {
            for j in 0..256 {
                if h[i][j] {
                    v.push((i, j));
                }
            }
        }
        v
    }
    match p.k {
        4 => hint_bit_unpack::<4>(p, y).map(flat),
        6 => hint_bit_unpack::<6>(p, y).map(flat),
        _ => hint_bit_unpack::<8>(p, y).map(flat),
    }
}

/// Build y from per-polynomial index lists (counts are cumulative; trailing polys get the final count).
fn build_y(p: &Params, polys: &[&[u8]]) -> Vec<u8> {
    let mut y = vec![0u8; p.omega + p.k];
    let mut n = 0;
    for i in 0..p.k {
        if let Some(l) = polys.get(i) {
            for &b in *l {
                y[n] = b;
                n += 1;
            }
        }
        y[p.omega + i] = n as u8;
    }
    y
}

#[test]
fn hint_unpack_alg21_corner_cases() {
    for (p, k) in pack_unpack_params() {
        let w = p.omega;
        // count == ω with all-zero index bytes: ω indices of which only the first is "valid"; strictness fails (⊥)
        let mut y = vec![0u8; w + k];
        for i in 0..k {
            y[w + i] = w as u8;
        }
        assert!(unpack_bits(p, &y).is_none(), "ω zero indices in poly 0");
        // count == ω, all ω indices strictly increasing: accepted, no padding to check
        let inc: Vec<u8> = (0..w as u8).map(|i| i * 3).collect();
        let y = build_y(p, &[&inc]);
        assert_eq!(y[w], w as u8);
        let got = unpack_bits(p, &y).expect("ω increasing indices");
        assert_eq!(got.len(), w);
        assert!(got.iter().enumerate().all(|(n, &(i, j))| i == 0 && j == n * 3));
        // ... with the very last index byte repeated: ⊥
        let mut dup = inc.clone();
        dup[w - 1] = dup[w - 2];
        assert!(unpack_bits(p, &build_y(p, &[&dup])).is_none());
        // count == ω - 1: the final index byte is padding and must be zero
        let part: Vec<u8> = (1..w as u8).collect(); // ω - 1 indices
        let mut y = build_y(p, &[&part]);
        assert_eq!(y[w], (w - 1) as u8);
        assert!(unpack_bits(p, &y).is_some());
        y[w - 1] = 1;
        assert!(unpack_bits(p, &y).is_none(), "nonzero last padding byte");
        // ω indices that all lie in the first polynomial, count in later polynomials is the same ω: accepted
        // (later polynomials are empty); a later count below ω is decreasing: ⊥
        let mut y = build_y(p, &[&inc]);
        assert!(unpack_bits(p, &y).is_some());
        y[w + k - 1] = (w - 1) as u8;
        assert!(unpack_bits(p, &y).is_none(), "count decreases after reaching ω");
        // count == ω reached only in the last polynomial
        let half: Vec<u8> = (0..(w / 2) as u8).collect();
        let rest: Vec<u8> = (0..(w - w / 2) as u8).collect();
        let mut polys: Vec<&[u8]> = vec![&[]; k - 1];
        polys[0] = &half;
        polys.push(&rest);
        let y = build_y(p, &polys);
        assert_eq!(y[w + k - 1], w as u8);
        let got = unpack_bits(p, &y).expect("indices restart at each polynomial boundary");
        assert_eq!(got.len(), w);
        assert!(got.iter().take(w / 2).all(|&(i, _)| i == 0));
        assert!(got.iter().skip(w / 2).all(|&(i, _)| i == k - 1));

        // index 0 repeated at the start of one polynomial: [0, 0] is not strictly increasing
        assert!(unpack_bits(p, &build_y(p, &[&[0, 0]])).is_none());
        assert!(unpack_bits(p, &build_y(p, &[&[5], &[0, 0]])).is_none());
        assert!(unpack_bits(p, &build_y(p, &[&[], &[0, 0, 1]])).is_none());
        assert!(unpack_bits(p, &build_y(p, &[&[0, 1, 1]])).is_none());
        // ... but [0] in each of two (or three) adjacent polynomials is fine
        assert_eq!(unpack_bits(p, &build_y(p, &[&[0], &[0]])), Some(vec![(0, 0), (1, 0)]));
        assert_eq!(unpack_bits(p, &build_y(p, &[&[5], &[0], &[0]])), Some(vec![(0, 5), (1, 0), (2, 0)]));
        // indices restart (decrease) at a polynomial boundary: valid, and decoded into the right rows
        assert_eq!(
            unpack_bits(p, &build_y(p, &[&[10, 20, 30], &[1, 2], &[], &[0, 255]])),
            Some(vec![(0, 10), (0, 20), (0, 30), (1, 1), (1, 2), (3, 0), (3, 255)])
        );
        // 255 followed by a smaller index inside one polynomial is ⊥
        assert!(unpack_bits(p, &build_y(p, &[&[255, 3]])).is_none());
        // the same bytes cut into two polynomials are fine
        assert!(unpack_bits(p, &build_y(p, &[&[255], &[3]])).is_some());
        // a zero where padding is expected, then a nonzero after it
        let mut y = build_y(p, &[&[4]]);
        y[3] = 9;
        assert!(unpack_bits(p, &y).is_none());
    }
}

// ---- Hint region differential vs upstream (permanent) ----

#[test]
fn hint_region_differential_vs_upstream() {
    fn go<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, tag: u64) {
        let mut rng = XorShift(0xD1B5_4A32_D192_ED03 ^ tag);
        let len = sig_len(p);
        let hs = len - p.omega - K;
        let w = p.omega;
        let bases: Vec<Vec<u8>> = (0..8u8)
            .map(|i| {
                let esk = ExpandedSigningKey::<P>::from_seed(&seed(40 + i));
                let msg = [i; 17];
                esk.sign_internal(&[&msg], &ml_dsa::B32::from([i ^ 0x5a; 32])).encode().as_slice().to_vec()
            })
            .collect();
        let (mut both_ok, mut both_bad, mut total) = (0u64, 0u64, 0u64);
        let n_iter = 30_000;
        for n in 0..n_iter {
            let mut s = bases[(rng.next() % bases.len() as u64) as usize].clone();
            match n % 5 {
                // 0: whole hint region random bytes
                0 => {
                    for b in &mut s[hs..] {
                        *b = rng.next() as u8;
                    }
                }
                // 1: single-byte edit anywhere in the region
                1 => {
                    let pos = hs + (rng.next() as usize) % (w + K);
                    s[pos] = rng.next() as u8;
                }
                // 2: count byte edit: boundary-ish values or random
                2 => {
                    let i = (rng.next() as usize) % K;
                    let cur = s[hs + w + i];
                    s[hs + w + i] = match rng.next() % 8 {
                        0 => w as u8,
                        1 => (w + 1) as u8,
                        2 => cur.wrapping_add(1),
                        3 => cur.wrapping_sub(1),
                        4 => 0,
                        5 => 255,
                        _ => rng.next() as u8,
                    };
                }
                // 3: index byte edit: random, neighbor +-1, or duplicate of a neighbor
                3 => {
                    let j = (rng.next() as usize) % w;
                    let cur = s[hs + j];
                    s[hs + j] = match rng.next() % 6 {
                        0 => cur.wrapping_add(1),
                        1 => cur.wrapping_sub(1),
                        2 if j > 0 => s[hs + j - 1],
                        3 if j + 1 < w => s[hs + j + 1],
                        4 => 0,
                        _ => rng.next() as u8,
                    };
                }
                // 4: structured plausible region (sorted runs per polynomial), sometimes with one more edit
                _ => {
                    let mut cnt = 0usize;
                    let mut idx = 0usize;
                    for i in 0..K {
                        let take = (rng.next() as usize) % (w / K + 3);
                        let end = (cnt + take).min(w);
                        let mut prev: i32 = -1;
                        while cnt < end {
                            prev += 1 + (rng.next() % 40) as i32;
                            s[hs + idx] = prev.min(255) as u8; // clamp may produce a duplicate on purpose
                            idx += 1;
                            cnt += 1;
                        }
                        s[hs + w + i] = cnt as u8;
                    }
                    for b in &mut s[hs + idx..hs + w] {
                        *b = 0;
                    }
                    if rng.next() % 2 == 0 {
                        let pos = hs + (rng.next() as usize) % (w + K);
                        s[pos] = rng.next() as u8;
                    }
                }
            }
            total += 1;
            let ours = sig_decode::<K, L>(p, &s);
            let up = ml_dsa::Signature::<P>::try_from(&s[..]);
            assert_eq!(ours.is_some(), up.is_ok(), "accept/reject mismatch (n={n}); hint region {:?}", &s[hs..]);
            match (ours, up) {
                (Some((_, _, h)), Ok(sig)) => {
                    both_ok += 1;
                    // hints agree: ours re-encodes to the hint bytes, and upstream re-encodes to the whole input
                    let mut hb = vec![0u8; w + K];
                    hint_bit_pack::<K>(p, &h, &mut hb);
                    assert_eq!(&hb[..], &s[hs..], "ours hint re-encode (n={n})");
                    assert_eq!(sig.encode().as_slice(), &s[..], "upstream re-encode (n={n})");
                }
                _ => both_bad += 1,
            }
        }
        eprintln!("hint differential K={K}: {total} mutations, {both_ok} accepted by both, {both_bad} rejected by both");
        assert!(both_ok > 500 && both_bad > 500);
    }
    go::<MlDsa44, 4, 4>(&ML_DSA_44, 44);
    go::<MlDsa65, 6, 5>(&ML_DSA_65, 65);
    go::<MlDsa87, 8, 7>(&ML_DSA_87, 87);
}

// ---- RejBoundedPoly discard path ----

/// Naive Algorithm 31, one byte at a time, with its own CoeffFromHalfByte. Also returns the byte that was
/// consumed when j was already 255, z0 was valid and z1 was also valid (so z1 was discarded), if any.
fn naive_rej_bounded_poly(eta: i64, rho: &[u8; 66]) -> ([u32; 256], Option<u8>) {
    let half = |b: u8| -> Option<i64> {
        let b = b as i64;
        if eta == 2 && b < 15 {
            Some(2 - b % 5)
        } else if eta == 4 && b < 9 {
            Some(4 - b)
        } else {
            None
        }
    };
    let to_zq = |v: i64| v.rem_euclid(Q as i64) as u32;
    let mut ctx = Shake::shake256();
    ctx.absorb(rho);
    ctx.finalize();
    let mut a = [0u32; 256];
    let mut j = 0usize;
    let mut discarded = None;
    while j < 256 {
        let mut z = [0u8; 1];
        ctx.squeeze(&mut z);
        let z0 = half(z[0] % 16);
        let z1 = half(z[0] / 16);
        if let Some(v) = z0 {
            a[j] = to_zq(v);
            j += 1;
        }
        if let Some(v) = z1 {
            if j < 256 {
                a[j] = to_zq(v);
                j += 1;
            } else if z0.is_some() {
                discarded = Some(z[0]);
            }
        }
    }
    (a, discarded)
}

#[test]
fn rej_bounded_poly_discard_path() {
    let mut rng = XorShift(0x0123_4567_89ab_cdef);
    for p in [&ML_DSA_44, &ML_DSA_65, &ML_DSA_87] {
        let (mut found, mut tried, mut other) = (0, 0, 0);
        // bounded search over seeds for one where z0 fills a[255] and z1 would also have been valid
        while found < 8 && tried < 20_000 {
            tried += 1;
            let mut rho = [0u8; 66];
            for b in rho.iter_mut() {
                *b = rng.next() as u8;
            }
            let (naive, discarded) = naive_rej_bounded_poly(p.eta as i64, &rho);
            let got = rej_bounded_poly(p, &rho);
            assert!(got == naive, "RejBoundedPoly vs naive, eta={}, rho={:02x?}", p.eta, rho);
            if let Some(b) = discarded {
                found += 1;
                // a[255] is z0 of the discarding byte; z1 was dropped
                let z0 = coeff_from_half_byte(p, b & 15).unwrap();
                assert_eq!(got[255], z0);
                assert!(coeff_from_half_byte(p, b >> 4).is_some());
            } else {
                other += 1;
            }
        }
        assert!(found >= 8, "eta={}: discard path found only {found}x in {tried} seeds ({other} other)", p.eta);
    }
}
