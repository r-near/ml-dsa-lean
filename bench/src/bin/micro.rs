//! Step-level costs of ml-dsa-verified (needs the `internals` feature) and a stepwise replica of keygen, sign
//! and verify with a timer around every step.
//!
//! Part A: `MICRO` lines: nanoseconds per call of the building blocks (the permutation alone, a sponge squeeze of
//! one block, RejNTTPoly, one NTT, ...). Part B: `STEP` lines: the replica's time per step, summed over the same
//! 256 messages the bench uses and divided by the number of calls, next to the time of the public `api` function
//! (`API` lines), which checks that the replica adds up. The replica mirrors keygen_internal, sign_internal and
//! verify_internal call for call (including the rejection loop; `attempt`, `response` and `hint_step` are
//! crate-private, so their bodies are repeated here); its outputs are compared with the api's.
//! Part C: `PREP` lines: verify with a prepared public key (Â, and also t̂1·2^13 and tr, held in a struct), the
//! same code as `verify_internal` minus the work that a cache would skip. Prototype for the analysis; not in src/.
//!
//! Run pinned: taskset -c N micro [--rounds N]
#![allow(clippy::type_complexity, clippy::needless_range_loop)]

use ml_dsa_bench::*;
use ml_dsa_verified::api;
use ml_dsa_verified::encode::{pk_decode, pk_encode, sig_decode, sig_encode, sk_decode, sk_encode, w1_encode, bit_unpack, SecretKey};
use ml_dsa_verified::keccak::{keccak_f1600, Shake};
use ml_dsa_verified::ntt::{add_poly, matrix_vector_ntt, multiply_ntt, ntt, ntt_inverse, ntt_vec, scalar_vector_ntt_inverse, sub_poly};
use ml_dsa_verified::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use ml_dsa_verified::rounding::{make_hint, poly_high_bits, poly_low_bits, poly_power2round, poly_use_hint, vec_infinity_norm};
use ml_dsa_verified::sampling::{expand_a, expand_mask, expand_s, rej_bounded_poly, rej_ntt_poly, sample_in_ball};
use ml_dsa_verified::field::{add, neg};
use std::hint::black_box;
use std::time::Instant;

const NMSG: usize = 256;
const CTX: &[u8] = b"";

/// Forces `x` to be computed and stored.
fn sink<T>(x: T) -> u64 {
    black_box(&x);
    0
}

/// Median nanoseconds per call of `f`.
fn ns(rounds: usize, mut f: impl FnMut() -> u64) -> f64 {
    measure(1, rounds, 0, 0.1, 0.05, &mut |_| f()).0.median
}

struct Acc {
    rows: Vec<(&'static str, u128)>,
}
impl Acc {
    fn new() -> Acc {
        Acc { rows: vec![] }
    }
    fn t<R>(&mut self, name: &'static str, f: impl FnOnce() -> R) -> R {
        let t = Instant::now();
        let r = f();
        let d = t.elapsed().as_nanos();
        match self.rows.iter_mut().find(|(n, _)| *n == name) {
            Some(row) => row.1 += d,
            None => self.rows.push((name, d)),
        }
        r
    }
}

fn shake256(parts: &[&[u8]], out: &mut [u8]) {
    let mut h = Shake::shake256();
    for p in parts {
        h.absorb(p);
    }
    h.finalize();
    h.squeeze(out);
}

// ---- replicas -----------------------------------------------------------------------------------

fn verify_replica<const K: usize, const L: usize>(p: &Params, pk: &[u8], mp: &[u8], sig: &[u8], a: &mut Acc) -> bool {
    let (rho, t1) = a.t("pkDecode", || pk_decode::<K>(pk));
    let (c_tilde, z, h) = a.t("sigDecode", || sig_decode::<K, L>(p, sig)).unwrap();
    let a_hat = a.t("ExpandA", || expand_a::<K, L>(&rho));
    let mut tr = [0u8; 64];
    a.t("H(pk)", || shake256(&[pk], &mut tr));
    let mut mu = [0u8; 64];
    a.t("H(tr,M')", || shake256(&[&tr, mp], &mut mu));
    let c = a.t("SampleInBall", || sample_in_ball(p, &c_tilde[..p.c_tilde_len]));
    let z_hat = a.t("NTT(z)", || ntt_vec(&z));
    let az = a.t("A.z (matrix-vector)", || matrix_vector_ntt::<K, L>(&a_hat, &z_hat));
    let c_hat = a.t("NTT(c)", || ntt(&c));
    let t1_hat = a.t("NTT(t1*2^13)", || {
        let mut s = [[0u32; 256]; K];
        for i in 0..K {
            for j in 0..256 {
                s[i][j] = t1[i][j] << 13;
            }
        }
        ntt_vec(&s)
    });
    let mut w1 = [[0u32; 256]; K];
    for i in 0..K {
        let d = a.t("c.t1 and subtract", || sub_poly(&az[i], &multiply_ntt(&c_hat, &t1_hat[i])));
        let w = a.t("NTT^-1", || ntt_inverse(&d));
        w1[i] = a.t("UseHint", || poly_use_hint(p, &h[i], &w));
    }
    let mut w1_enc = [0u8; 8 * 192];
    a.t("w1Encode", || w1_encode(p, &w1, &mut w1_enc));
    let mut cp = [0u8; 64];
    a.t("H(mu,w1)", || shake256(&[&mu, &w1_enc[..K * 32 * p.w1_bits]], &mut cp[..p.c_tilde_len]));
    let norm_ok = a.t("norm and compare", || vec_infinity_norm(&z) < p.gamma1 - p.beta);
    norm_ok && cp[..p.c_tilde_len] == c_tilde[..p.c_tilde_len]
}

fn sign_replica<const K: usize, const L: usize>(
    p: &Params,
    sk: &[u8],
    mp: &[u8],
    rnd: &[u8; 32],
    a: &mut Acc,
    attempts: &mut u64,
) -> Vec<u8> {
    let key: SecretKey<K, L> = a.t("skDecode", || sk_decode::<K, L>(p, sk));
    let (s1h, s2h, t0h) = a.t("NTT(s1,s2,t0)", || (ntt_vec(&key.s1), ntt_vec(&key.s2), ntt_vec(&key.t0)));
    let a_hat = a.t("ExpandA", || expand_a::<K, L>(&key.rho));
    let mut mu = [0u8; 64];
    a.t("H(tr,M')", || shake256(&[&key.tr, mp], &mut mu));
    let mut rho_pp = [0u8; 64];
    a.t("H(K,rnd,mu)", || shake256(&[&key.key, rnd, &mu], &mut rho_pp));
    let mut kappa: u32 = 0;
    let mut sig = vec![0u8; ml_dsa_verified::params::sig_len(p)];
    while kappa + (L as u32) - 1 <= 0xFFFF {
        *attempts += 1;
        let y = a.t("ExpandMask", || expand_mask::<L>(p, &rho_pp, kappa as u16));
        let y_hat = a.t("NTT(y)", || ntt_vec(&y));
        let w_hat = a.t("A.y (matrix-vector)", || matrix_vector_ntt::<K, L>(&a_hat, &y_hat));
        let w = a.t("NTT^-1(w)", || {
            let mut w = [[0u32; 256]; K];
            for i in 0..K {
                w[i] = ntt_inverse(&w_hat[i]);
            }
            w
        });
        let w1 = a.t("HighBits(w)", || {
            let mut w1 = [[0u32; 256]; K];
            for i in 0..K {
                w1[i] = poly_high_bits(p, &w[i]);
            }
            w1
        });
        let mut w1_enc = [0u8; 8 * 192];
        a.t("w1Encode", || w1_encode(p, &w1, &mut w1_enc));
        let mut c_tilde = [0u8; 64];
        a.t("H(mu,w1)", || shake256(&[&mu, &w1_enc[..K * 32 * p.w1_bits]], &mut c_tilde[..p.c_tilde_len]));
        let c = a.t("SampleInBall", || sample_in_ball(p, &c_tilde[..p.c_tilde_len]));
        let c_hat = a.t("NTT(c)", || ntt(&c));
        let cs1 = a.t("c.s1, NTT^-1", || scalar_vector_ntt_inverse::<L>(&c_hat, &s1h));
        let cs2 = a.t("c.s2, NTT^-1", || scalar_vector_ntt_inverse::<K>(&c_hat, &s2h));
        let (z, w_cs2) = a.t("z=y+cs1, w-cs2", || {
            let mut z = [[0u32; 256]; L];
            for i in 0..L {
                for j in 0..256 {
                    z[i][j] = add(y[i][j], cs1[i][j]);
                }
            }
            let mut w_cs2 = [[0u32; 256]; K];
            for i in 0..K {
                w_cs2[i] = sub_poly(&w[i], &cs2[i]);
            }
            (z, w_cs2)
        });
        let r0 = a.t("LowBits(w-cs2)", || {
            let mut r0 = [[0u32; 256]; K];
            for i in 0..K {
                r0[i] = poly_low_bits(p, &w_cs2[i]);
            }
            r0
        });
        let rej1 = a.t("norms", || vec_infinity_norm(&z) >= p.gamma1 - p.beta || vec_infinity_norm(&r0) >= p.gamma2 - p.beta);
        if rej1 {
            kappa += L as u32;
            continue;
        }
        let ct0 = a.t("c.t0, NTT^-1", || scalar_vector_ntt_inverse::<K>(&c_hat, &t0h));
        let (hint, ones) = a.t("MakeHint", || {
            let mut hint = [[false; 256]; K];
            let mut ones = 0;
            for i in 0..K {
                for j in 0..256 {
                    hint[i][j] = make_hint(p, neg(ct0[i][j]), add(w_cs2[i][j], ct0[i][j]));
                    ones += hint[i][j] as usize;
                }
            }
            (hint, ones)
        });
        let rej2 = a.t("norms", || vec_infinity_norm(&ct0) >= p.gamma2 || ones > p.omega);
        if rej2 {
            kappa += L as u32;
            continue;
        }
        a.t("sigEncode", || sig_encode::<K, L>(p, &c_tilde, &z, &hint, &mut sig));
        return sig;
    }
    panic!("kappa exhausted");
}

fn keygen_replica<const K: usize, const L: usize>(p: &Params, xi: &[u8; 32], a: &mut Acc) -> (Vec<u8>, Vec<u8>) {
    let kl = [K as u8, L as u8];
    let mut expanded = [0u8; 128];
    a.t("H(xi) -> rho, rho', K", || shake256(&[xi, &kl], &mut expanded));
    let rho: [u8; 32] = expanded[..32].try_into().unwrap();
    let rho_prime: [u8; 64] = expanded[32..96].try_into().unwrap();
    let key: [u8; 32] = expanded[96..].try_into().unwrap();
    let a_hat = a.t("ExpandA", || expand_a::<K, L>(&rho));
    let (s1, s2) = a.t("ExpandS", || expand_s::<K, L>(p, &rho_prime));
    let s1_hat = a.t("NTT(s1)", || ntt_vec(&s1));
    let a_s1 = a.t("A.s1 (matrix-vector)", || matrix_vector_ntt::<K, L>(&a_hat, &s1_hat));
    let t = a.t("NTT^-1, + s2", || {
        let mut t = [[0u32; 256]; K];
        for i in 0..K {
            t[i] = add_poly(&ntt_inverse(&a_s1[i]), &s2[i]);
        }
        t
    });
    let (t1, t0) = a.t("Power2Round", || {
        let mut t1 = [[0u32; 256]; K];
        let mut t0 = [[0u32; 256]; K];
        for i in 0..K {
            (t1[i], t0[i]) = poly_power2round(&t[i]);
        }
        (t1, t0)
    });
    let mut pk = vec![0u8; 32 + 320 * K];
    a.t("pkEncode", || pk_encode::<K>(&rho, &t1, &mut pk));
    let mut tr = [0u8; 64];
    a.t("H(pk)", || shake256(&[&pk], &mut tr));
    let mut sk = vec![0u8; ml_dsa_verified::params::sk_len(p)];
    a.t("skEncode", || sk_encode::<K, L>(p, &rho, &key, &tr, &s1, &s2, &t0, &mut sk));
    (pk, sk)
}

/// Verify with a prepared key. `full` additionally caches t̂1·2^13 and tr (what RustCrypto's VerifyingKey holds).
struct Prepared<const K: usize, const L: usize> {
    a_hat: [[[u32; 256]; L]; K],
    t1_hat: [[u32; 256]; K],
    tr: [u8; 64],
}

impl<const K: usize, const L: usize> Prepared<K, L> {
    fn new(pk: &[u8]) -> Box<Self> {
        let (rho, t1) = pk_decode::<K>(pk);
        let mut s = [[0u32; 256]; K];
        for i in 0..K {
            for j in 0..256 {
                s[i][j] = t1[i][j] << 13;
            }
        }
        let mut tr = [0u8; 64];
        shake256(&[pk], &mut tr);
        Box::new(Prepared { a_hat: expand_a::<K, L>(&rho), t1_hat: ntt_vec(&s), tr })
    }
}

/// Same steps as verify_internal. `a_only`: only Â is cached (pk is decoded, t1 scaled and transformed, tr hashed
/// per call); otherwise t̂1 and tr come from `prep` too.
fn verify_prepared<const K: usize, const L: usize>(p: &Params, prep: &Prepared<K, L>, pk: &[u8], a_only: bool, mp: &[u8], sig: &[u8]) -> bool {
    let (c_tilde, z, h) = match sig_decode::<K, L>(p, sig) {
        Some(x) => x,
        None => return false,
    };
    let mut tr = prep.tr;
    let t1_local;
    let t1_hat: &[[u32; 256]; K] = if a_only {
        let (_, t1) = pk_decode::<K>(pk);
        let mut s = [[0u32; 256]; K];
        for i in 0..K {
            for j in 0..256 {
                s[i][j] = t1[i][j] << 13;
            }
        }
        shake256(&[pk], &mut tr);
        t1_local = ntt_vec(&s);
        &t1_local
    } else {
        &prep.t1_hat
    };
    let mut mu = [0u8; 64];
    shake256(&[&tr, mp], &mut mu);
    let c = sample_in_ball(p, &c_tilde[..p.c_tilde_len]);
    let az = matrix_vector_ntt::<K, L>(&prep.a_hat, &ntt_vec(&z));
    let c_hat = ntt(&c);
    let mut w1 = [[0u32; 256]; K];
    for i in 0..K {
        let w = ntt_inverse(&sub_poly(&az[i], &multiply_ntt(&c_hat, &t1_hat[i])));
        w1[i] = poly_use_hint(p, &h[i], &w);
    }
    let mut w1_enc = [0u8; 8 * 192];
    w1_encode(p, &w1, &mut w1_enc);
    let mut cp = [0u8; 64];
    shake256(&[&mu, &w1_enc[..K * 32 * p.w1_bits]], &mut cp[..p.c_tilde_len]);
    vec_infinity_norm(&z) < p.gamma1 - p.beta && cp[..p.c_tilde_len] == c_tilde[..p.c_tilde_len]
}


// ---- Part D: candidate arithmetic (prototypes, not in src/) -------------------------------------------------
// Plain `while`-loop Rust like the crate's own, so the same code could be extracted. Compared with the crate's
// `ntt`, `ntt_inverse` and `multiply_ntt` (canonical u32 in [0, q), Barrett through u128, a conditional subtract
// after every add and sub).
mod cand {
    use ml_dsa_verified::ntt::ZETAS;
    pub const Q: i32 = 8_380_417;
    const QU: u32 = 8_380_417;
    pub const QINV: u32 = 58_728_449; // q^-1 mod 2^32
    const QNEG: u32 = 0u32.wrapping_sub(QINV); // -q^-1 mod 2^32

    /// zeta * 2^32 mod q, as a canonical value in [0, q), and centered in (-q/2, q/2].
    pub fn zetas_mont() -> ([u32; 256], [i32; 256]) {
        let mut canon = [0u32; 256];
        let mut cent = [0i32; 256];
        let mut k = 0;
        while k < 256 {
            let v = ((ZETAS[k] as u64) << 32) % (QU as u64);
            canon[k] = v as u32;
            cent[k] = if v > (QU as u64) / 2 { v as i32 - Q } else { v as i32 };
            k += 1;
        }
        (canon, cent)
    }

    /// Signed Montgomery reduction: a * 2^-32 mod q in (-q, q), for |a| < 2^31 q.
    #[inline(always)]
    pub fn mont(a: i64) -> i32 {
        let t = (a as i32).wrapping_mul(QINV as i32);
        ((a - (t as i64) * (Q as i64)) >> 32) as i32
    }
    /// Unsigned Montgomery reduction: a * 2^-32 mod q in [0, 2q), for a < 2^32 q.
    #[inline(always)]
    fn mont_u(a: u64) -> u32 {
        let m = (a as u32).wrapping_mul(QNEG);
        ((a + (m as u64) * (QU as u64)) >> 32) as u32
    }
    #[inline(always)]
    fn cond_sub(x: u32) -> u32 {
        let mask = 0u32.wrapping_sub((x >= QU) as u32);
        x - (QU & mask)
    }

    /// (b) canonical in and out, as the crate's `ntt`, but the butterfly multiplies by zeta*R with a Montgomery
    /// reduction instead of Barrett (only the multiply changes; add and sub still reduce every time).
    pub fn ntt_canon_mont(w: &mut [u32; 256], zc: &[u32; 256]) {
        let mut k = 0;
        let mut len = 128;
        while len > 0 {
            let mut start = 0;
            while start < 256 {
                k += 1;
                let z = zc[k] as u64;
                let mut j = start;
                while j < start + len {
                    let t = cond_sub(mont_u(z * (w[j + len] as u64)));
                    let a = w[j];
                    w[j + len] = cond_sub(a + QU - t);
                    w[j] = cond_sub(a + t);
                    j += 1;
                }
                start += 2 * len;
            }
            len >>= 1;
        }
    }

    /// (c) lazy: signed i32 coefficients, no reduction in add/sub (|a| grows by < q per layer), centered Montgomery
    /// zetas (mldsa-native / reference style). Input canonical or centered, output in (-9q, 9q); `normalize`
    /// brings it back to [0, q).
    pub fn ntt_lazy(a: &mut [i32; 256], zm: &[i32; 256]) {
        let mut k = 0;
        let mut len = 128;
        while len > 0 {
            let mut start = 0;
            while start < 256 {
                k += 1;
                let z = zm[k] as i64;
                let mut j = start;
                while j < start + len {
                    let t = mont(z * (a[j + len] as i64));
                    a[j + len] = a[j] - t;
                    a[j] = a[j] + t;
                    j += 1;
                }
                start += 2 * len;
            }
            len >>= 1;
        }
    }

    /// Inverse, lazy; the last pass multiplies by 2^32/256 (so the result is the true NTT^-1) and leaves values in (-q, q).
    pub fn invntt_lazy(a: &mut [i32; 256], zm: &[i32; 256]) {
        let mut k = 256;
        let mut len = 1;
        while len < 256 {
            let mut start = 0;
            while start < 256 {
                k -= 1;
                let z = -(zm[k] as i64);
                let mut j = start;
                while j < start + len {
                    let t = a[j];
                    a[j] = t + a[j + len];
                    a[j + len] = mont(z * ((t - a[j + len]) as i64));
                    j += 1;
                }
                start += 2 * len;
            }
            len <<= 1;
        }
        let mut j = 0;
        while j < 256 {
            a[j] = mont(16382i64 * (a[j] as i64)); // 2^24 mod q
            j += 1;
        }
    }

    /// to [0, q)
    pub fn normalize(a: &[i32; 256], out: &mut [u32; 256]) {
        let mut j = 0;
        while j < 256 {
            let x = a[j];
            let t = (x + (1 << 22)) >> 23;
            let r = x - t * Q; // [-6283009, 6283008]
            out[j] = (r + ((r >> 31) & Q)) as u32;
            j += 1;
        }
    }

    /// pointwise, true product: two Montgomery reductions (the second multiplies by 2^64 mod q)
    pub fn pointwise_true(a: &[u32; 256], b: &[u32; 256], r2: u64, out: &mut [u32; 256]) {
        let mut j = 0;
        while j < 256 {
            let p = mont_u((a[j] as u64) * (b[j] as u64)); // [0, 2q): a*b/R
            out[j] = cond_sub(mont_u((p as u64) * r2)); // * R^2 / R
            j += 1;
        }
    }
    /// pointwise, leaving the factor R^-1 in the result (a 'Montgomery-domain' product): one reduction
    pub fn pointwise_lazy(a: &[i32; 256], b: &[i32; 256], out: &mut [i32; 256]) {
        let mut j = 0;
        while j < 256 {
            out[j] = mont((a[j] as i64) * (b[j] as i64));
            j += 1;
        }
    }
}

fn candidates(rounds: usize) {
    use cand::*;
    let (zc, zm) = zetas_mont();
    let r2 = ((1u128 << 64) % 8_380_417u128) as u64;
    let mut r = Rng::new("cand", 1);
    let mut input = [0u32; 256];
    for c in input.iter_mut() {
        *c = (r.next_u64() % 8_380_417) as u32;
    }
    let mut input_b = [0u32; 256];
    for c in input_b.iter_mut() {
        *c = (r.next_u64() % 8_380_417) as u32;
    }
    // correctness against the crate's own functions
    let want = ntt(&input);
    let mut got = input;
    ntt_canon_mont(&mut got, &zc);
    assert!(got == want, "ntt_canon_mont differs");
    let mut a = [0i32; 256];
    for i in 0..256 {
        a[i] = input[i] as i32;
    }
    ntt_lazy(&mut a, &zm);
    let mut norm = [0u32; 256];
    normalize(&a, &mut norm);
    assert!(norm == want, "ntt_lazy differs");
    let mut ai = [0i32; 256];
    for i in 0..256 {
        ai[i] = input[i] as i32;
    }
    invntt_lazy(&mut ai, &zm);
    normalize(&ai, &mut norm);
    assert!(norm == ntt_inverse(&input), "invntt_lazy differs");
    // worst-case inputs for the bounds
    for fill in [0u32, 1, 4_190_208, 8_380_416] {
        let x = [fill; 256];
        let mut y = x.map(|v| v as i32);
        invntt_lazy(&mut y, &zm);
        normalize(&y, &mut norm);
        assert!(norm == ntt_inverse(&x), "invntt_lazy differs on constant input {fill}");
        let mut y = x.map(|v| v as i32);
        ntt_lazy(&mut y, &zm);
        assert!(y.iter().all(|v| v.abs() < 9 * 8_380_417));
        normalize(&y, &mut norm);
        assert!(norm == ntt(&x), "ntt_lazy differs on constant input {fill}");
    }
    let mut pw = [0u32; 256];
    pointwise_true(&input, &input_b, r2, &mut pw);
    assert!(pw == multiply_ntt(&input, &input_b), "pointwise_true differs");

    let base_ntt = ns(rounds, || sink(ntt(black_box(&input))));
    let base_inv = ns(rounds, || sink(ntt_inverse(black_box(&input))));
    let base_pw = ns(rounds, || sink(multiply_ntt(black_box(&input), black_box(&input_b))));
    println!("CAND\tcrate ntt (Barrett u128, canonical)\t{base_ntt:.0}\t1.00");
    let t = ns(rounds, || {
        let mut w = black_box(input);
        ntt_canon_mont(&mut w, black_box(&zc));
        sink(w)
    });
    println!("CAND\tntt: canonical u32, Montgomery multiply by zeta*R, add/sub still reduce\t{t:.0}\t{:.2}", t / base_ntt);
    let ai0: [i32; 256] = input.map(|v| v as i32);
    let t = ns(rounds, || {
        let mut w = black_box(ai0);
        ntt_lazy(&mut w, black_box(&zm));
        sink(w)
    });
    println!("CAND\tntt: lazy signed i32, no add/sub reduction (output in (-9q, 9q))\t{t:.0}\t{:.2}", t / base_ntt);
    let t = ns(rounds, || {
        let mut w = black_box(ai0);
        ntt_lazy(&mut w, black_box(&zm));
        let mut o = [0u32; 256];
        normalize(&w, &mut o);
        sink(o)
    });
    println!("CAND\tntt: lazy signed i32 + normalize to [0, q) (drop-in for the crate's ntt)\t{t:.0}\t{:.2}", t / base_ntt);
    println!("CAND\tcrate ntt_inverse\t{base_inv:.0}\t1.00");
    let t = ns(rounds, || {
        let mut w = black_box(ai0);
        invntt_lazy(&mut w, black_box(&zm));
        let mut o = [0u32; 256];
        normalize(&w, &mut o);
        sink(o)
    });
    println!("CAND\tntt_inverse: lazy signed i32 + normalize (drop-in)\t{t:.0}\t{:.2}", t / base_inv);
    println!("CAND\tcrate multiply_ntt\t{base_pw:.0}\t1.00");
    let t = ns(rounds, || {
        let mut o = [0u32; 256];
        pointwise_true(black_box(&input), black_box(&input_b), r2, &mut o);
        sink(o)
    });
    println!("CAND\tmultiply_ntt: two Montgomery reductions (canonical in and out)\t{t:.0}\t{:.2}", t / base_pw);
    let bi: [i32; 256] = input_b.map(|v| v as i32);
    let t = ns(rounds, || {
        let mut o = [0i32; 256];
        pointwise_lazy(black_box(&ai0), black_box(&bi), &mut o);
        sink(o)
    });
    println!("CAND\tmultiply_ntt: one Montgomery reduction, result carries 2^-32 (signed i32)\t{t:.0}\t{:.2}", t / base_pw);
}

// ---- driver -------------------------------------------------------------------------------------

fn print_steps(set: u32, op: &str, acc: &Acc, calls: usize, api_ns: f64) {
    let total: u128 = acc.rows.iter().map(|r| r.1).sum();
    println!("API\t{set}\t{op}\t{api_ns:.0}\tns per call (public api function)");
    println!("REPLICA\t{set}\t{op}\t{:.0}\tns per call (sum of timed steps)", total as f64 / calls as f64);
    for (name, t) in &acc.rows {
        let per = *t as f64 / calls as f64;
        println!("STEP\t{set}\t{op}\t{name}\t{per:.0}\t{:.1}%", 100.0 * *t as f64 / total as f64);
    }
}

macro_rules! per_set {
    ($set:literal, $K:literal, $L:literal, $P:expr, $kg:ident, $sg:ident, $vf:ident, $rounds:expr) => {{
        let p: &Params = &$P;
        let mut r = Rng::new("inputs", $set);
        let seeds: Vec<[u8; 32]> = (0..64).map(|_| r.bytes()).collect();
        let key_seed: [u8; 32] = r.bytes();
        let msgs: Vec<Vec<u8>> = (0..NMSG).map(|_| r.bytes::<64>().to_vec()).collect();
        let rnd_h: Vec<[u8; 32]> = (0..NMSG).map(|_| r.bytes()).collect();
        let (pk, sk) = api::$kg(&key_seed);
        let mps: Vec<Vec<u8>> = msgs.iter().map(|m| [&[0u8, 0u8][..], CTX, m].concat()).collect();
        let sigs: Vec<[u8; _]> = msgs.iter().map(|m| api::$sg(&sk, m, CTX, &[0u8; 32]).unwrap()).collect();

        // ---- verify replica -------------------------------------------------------------
        let mut acc = Acc::new();
        for i in 0..NMSG {
            assert!(verify_replica::<$K, $L>(p, &pk, &mps[i], &sigs[i], &mut acc));
        }
        let mut acc = Acc::new();
        let passes = 8;
        for _ in 0..passes {
            for i in 0..NMSG {
                assert!(verify_replica::<$K, $L>(p, &pk, &mps[i], &sigs[i], &mut acc));
            }
        }
        let api_v = ns($rounds, || {
            let mut x = 0;
            for i in 0..NMSG {
                x += api::$vf(&pk, &msgs[i], CTX, &sigs[i]) as u64;
            }
            x
        }) / NMSG as f64;
        print_steps($set, "verify", &acc, passes * NMSG, api_v);

        // ---- prepared-key verify prototype ---------------------------------------------
        let prep = Prepared::<$K, $L>::new(&pk);
        for a_only in [true, false] {
            for i in 0..NMSG {
                assert!(verify_prepared::<$K, $L>(p, &prep, &pk, a_only, &mps[i], &sigs[i]));
            }
            let t = ns($rounds, || {
                let mut x = 0;
                for i in 0..NMSG {
                    x += verify_prepared::<$K, $L>(p, &prep, &pk, a_only, &mps[i], &sigs[i]) as u64;
                }
                x
            }) / NMSG as f64;
            println!("PREP\t{}\tverify\t{}\t{t:.0}\tns per call", $set, if a_only { "A-hat cached" } else { "A-hat, t1-hat, tr cached" });
        }
        // tamper checks: the prototype must reject what verify rejects
        let mut bad = sigs[0];
        bad[5] ^= 1;
        assert!(!verify_prepared::<$K, $L>(p, &prep, &pk, false, &mps[0], &bad));

        // ---- sign replica ---------------------------------------------------------------
        for (mode, rnds) in [("sign-det", vec![[0u8; 32]; NMSG]), ("sign-hedged", rnd_h.clone())] {
            let mut acc = Acc::new();
            let mut attempts = 0u64;
            let mut calls = 0;
            for _ in 0..3 {
                for i in 0..NMSG {
                    let s = sign_replica::<$K, $L>(p, &sk, &mps[i], &rnds[i], &mut acc, &mut attempts);
                    assert_eq!(s.as_slice(), &api::$sg(&sk, &msgs[i], CTX, &rnds[i]).unwrap()[..]);
                    calls += 1;
                }
            }
            // the assert above doubles the work; measure the replica without it for the totals
            let mut acc = Acc::new();
            let mut attempts = 0u64;
            let mut calls2 = 0;
            for i in 0..NMSG {
                sign_replica::<$K, $L>(p, &sk, &mps[i], &rnds[i], &mut acc, &mut attempts);
                calls2 += 1;
            }
            let _ = calls;
            let api_s = ns(3, || {
                let mut x = 0;
                for i in 0..NMSG {
                    x += tag(&api::$sg(&sk, &msgs[i], CTX, &rnds[i]).unwrap());
                }
                x
            }) / NMSG as f64;
            println!("ATTEMPTS\t{}\t{mode}\t{:.3}\tmean attempts per sign over {NMSG} messages", $set, attempts as f64 / calls2 as f64);
            print_steps($set, mode, &acc, calls2, api_s);
        }

        // ---- keygen replica -------------------------------------------------------------
        let mut acc = Acc::new();
        for _ in 0..4 {
            for s in &seeds {
                let (pk2, sk2) = keygen_replica::<$K, $L>(p, s, &mut acc);
                let (pk3, sk3) = api::$kg(s);
                assert!(pk2 == pk3 && sk2 == sk3);
            }
        }
        let mut acc = Acc::new();
        for s in &seeds {
            keygen_replica::<$K, $L>(p, s, &mut acc);
        }
        let api_k = ns($rounds, || {
            let mut x = 0;
            for s in &seeds {
                let (a, b) = api::$kg(s);
                x ^= tag(&a) ^ tag(&b);
            }
            x
        }) / seeds.len() as f64;
        print_steps($set, "keygen", &acc, seeds.len(), api_k);

        // ---- building blocks for this set -----------------------------------------------
        let rho: [u8; 32] = r.bytes();
        let rho64: [u8; 64] = r.bytes();
        let t = ns($rounds, || sink(expand_a::<$K, $L>(black_box(&rho))));
        println!("MICRO\t{}\texpand_a\t{t:.0}", $set);
        let t = ns($rounds, || sink(expand_mask::<$L>(p, black_box(&rho64), 0)));
        println!("MICRO\t{}\texpand_mask\t{t:.0}", $set);
        let t = ns($rounds, || sink(expand_s::<$K, $L>(p, black_box(&rho64))));
        println!("MICRO\t{}\texpand_s\t{t:.0}", $set);
        let a_fixed = expand_a::<$K, $L>(&rho);
        let y_fixed: [[u32; 256]; $L] = ntt_vec(&expand_mask::<$L>(p, &rho64, 0));
        let t = ns($rounds, || sink(matrix_vector_ntt::<$K, $L>(black_box(&a_fixed), black_box(&y_fixed))));
        println!("MICRO\t{}\tmatrix_vector_ntt\t{t:.0}", $set);
        let t = ns($rounds, || sink(ntt_vec(black_box(&y_fixed))));
        println!("MICRO\t{}\tntt_vec (L polys)\t{t:.0}", $set);
        let tw = ns($rounds, || sink(sample_in_ball(p, black_box(&rho64[..p.c_tilde_len]))));
        println!("MICRO\t{}\tsample_in_ball\t{tw:.0}", $set);
        let pk_ref = pk.clone();
        let t = ns($rounds, || sink(pk_decode::<$K>(black_box(&pk_ref))));
        println!("MICRO\t{}\tpk_decode\t{t:.0}", $set);
        let sig_ref = sigs[0];
        let t = ns($rounds, || sink(sig_decode::<$K, $L>(p, black_box(&sig_ref))));
        println!("MICRO\t{}\tsig_decode\t{t:.0}", $set);
        let t = ns($rounds, || sink(sk_decode::<$K, $L>(p, black_box(&sk))));
        println!("MICRO\t{}\tsk_decode\t{t:.0}", $set);
        let z = bit_unpack(&vec![0xA5u8; 32 * p.gamma1_bits], p.gamma1_bits);
        let t = ns($rounds, || sink(poly_use_hint(p, black_box(&[false; 256]), black_box(&z))));
        println!("MICRO\t{}\tpoly_use_hint (one poly)\t{t:.0}", $set);
        let t = ns($rounds, || sink(poly_high_bits(p, black_box(&z))));
        println!("MICRO\t{}\tpoly_high_bits (one poly)\t{t:.0}", $set);
        let t = ns($rounds, || sink(poly_low_bits(p, black_box(&z))));
        println!("MICRO\t{}\tpoly_low_bits (one poly)\t{t:.0}", $set);
    }};
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let rounds: usize = args.iter().position(|a| a == "--rounds").and_then(|i| args.get(i + 1)).map(|s| s.parse().unwrap()).unwrap_or(11);
    println!("# micro: stepwise costs of ml-dsa-verified");
    for l in sysinfo() {
        println!("# {l}");
    }
    println!("# build opt-level={} rustflags={}", env!("BENCH_OPT"), env!("BENCH_RUSTFLAGS"));

    // ---- Part A: building blocks, independent of the set ---------------------------------------
    let mut st = [0x0123_4567_89ab_cdefu64; 25];
    let perm = ns(rounds, || {
        for _ in 0..100 {
            keccak_f1600(black_box(&mut st));
        }
        st[0]
    }) / 100.0;
    println!("MICRO\t-\tkeccak_f1600 (one permutation)\t{perm:.1}");

    let seed34 = [9u8; 34];
    let t = ns(rounds, || {
        let mut h = Shake::shake128();
        h.absorb(black_box(&seed34));
        h.finalize();
        let mut o = [0u8; 1];
        h.squeeze(&mut o);
        o[0] as u64
    });
    println!("MICRO\t-\tshake128 absorb 34 B + finalize (1 permutation)\t{t:.1}");
    let t = ns(rounds, || {
        let mut h = Shake::shake128();
        h.absorb(black_box(&seed34));
        h.finalize();
        let mut out = [0u8; 168];
        h.squeeze(&mut out);
        out[5] as u64
    });
    println!("MICRO\t-\t... + squeeze 168 B in one call\t{t:.1}");
    let t = ns(rounds, || {
        let mut h = Shake::shake128();
        h.absorb(black_box(&seed34));
        h.finalize();
        let mut x = 0u64;
        for _ in 0..56 {
            let mut o = [0u8; 3];
            h.squeeze(&mut o);
            x += o[2] as u64;
        }
        x
    });
    println!("MICRO\t-\t... + squeeze 168 B as 56 calls of 3 B (the RejNTTPoly pattern)\t{t:.1}");
    let t = ns(rounds, || {
        let mut h = Shake::shake128();
        h.absorb(black_box(&seed34));
        h.finalize();
        let mut out = [0u8; 840];
        h.squeeze(&mut out);
        out[5] as u64
    });
    println!("MICRO\t-\tshake128 34 B in, 840 B out in one call (5 permutations)\t{t:.1}");
    let t = ns(rounds, || sink(rej_ntt_poly(black_box(&seed34))));
    println!("MICRO\t-\trej_ntt_poly\t{t:.1}");
    // The same 34 B -> 840 B job in other implementations, and the bare permutation of the keccak crate.
    let t = ns(rounds, || {
        let mut out = [0u8; 840];
        libcrux_sha3::portable::shake128(&mut out, black_box(&seed34));
        out[5] as u64
    });
    println!("MICRO\t-\tlibcrux-sha3 portable shake128, 34 B in, 840 B out\t{t:.1}");
    #[cfg(target_arch = "x86_64")]
    if avx2() {
        #[target_feature(enable = "avx2")]
        unsafe fn x4(b: &[u8; 34]) -> u64 {
            use libcrux_sha3::avx2::x4::incremental::*;
            let mut s = init();
            let (mut o0, mut o1, mut o2, mut o3) = ([0u8; 840], [0u8; 840], [0u8; 840], [0u8; 840]);
            shake128_absorb_final(&mut s, b, b, b, b);
            shake128_squeeze_first_five_blocks(&mut s, &mut o0, &mut o1, &mut o2, &mut o3);
            (o0[5] ^ o1[6] ^ o2[7] ^ o3[8]) as u64
        }
        let t = ns(rounds, || unsafe { x4(black_box(&seed34)) });
        println!("MICRO\t-\tlibcrux-sha3 AVX2 4-way shake128, 4 x (34 B in, 840 B out)\t{t:.1}");
    }
    let mut fp: Option<fn(&mut [u64; 25])> = None;
    keccak::Keccak::new().with_f1600(|f| fp = Some(f));
    let fp = fp.unwrap();
    let mut st2 = [0x0123_4567_89ab_cdefu64; 25];
    let t = ns(rounds, || {
        for _ in 0..100 {
            fp(black_box(&mut st2));
        }
        st2[0]
    }) / 100.0;
    println!("MICRO\t-\tkeccak crate 0.2.2 f1600 (one permutation)\t{t:.1}");
    let seed66 = [9u8; 66];
    let t = ns(rounds, || {
        let mut h = Shake::shake256();
        h.absorb(black_box(&seed66));
        h.finalize();
        let mut out = [0u8; 136];
        h.squeeze(&mut out);
        out[5] as u64
    });
    println!("MICRO\t-\tshake256 66 B in, 136 B out in one call (2 permutations)\t{t:.1}");
    let t = ns(rounds, || sink(rej_bounded_poly(&ML_DSA_44, black_box(&seed66))));
    println!("MICRO\t-\trej_bounded_poly (eta 2)\t{t:.1}");
    let t = ns(rounds, || sink(rej_bounded_poly(&ML_DSA_65, black_box(&seed66))));
    println!("MICRO\t-\trej_bounded_poly (eta 4)\t{t:.1}");
    let big = vec![0x5Au8; 2592];
    let t = ns(rounds, || {
        let mut h = Shake::shake256();
        h.absorb(black_box(&big));
        h.finalize();
        let mut o = [0u8; 1];
        h.squeeze(&mut o);
        o[0] as u64
    });
    println!("MICRO\t-\tshake256 absorb 2592 B + finalize (20 permutations)\t{t:.1}");

    let mut poly = [0u32; 256];
    for (i, c) in poly.iter_mut().enumerate() {
        *c = (i as u32 * 32771) % 8_380_417;
    }
    let t = ns(rounds, || sink(ntt(black_box(&poly))));
    println!("MICRO\t-\tntt (one poly)\t{t:.1}");
    let t = ns(rounds, || sink(ntt_inverse(black_box(&poly))));
    println!("MICRO\t-\tntt_inverse (one poly)\t{t:.1}");
    let t = ns(rounds, || sink(multiply_ntt(black_box(&poly), black_box(&poly))));
    println!("MICRO\t-\tmultiply_ntt (one poly)\t{t:.1}");
    let t = ns(rounds, || sink(add_poly(black_box(&poly), black_box(&poly))));
    println!("MICRO\t-\tadd_poly (one poly)\t{t:.1}");
    let t = ns(rounds, || {
        let mut o = [0u8; 8 * 192];
        w1_encode(&ML_DSA_65, &[poly; 6].map(|mut q| { for c in q.iter_mut() { *c &= 15 } q }), &mut o);
        o[7] as u64
    });
    println!("MICRO\t-\tw1_encode (ML-DSA-65 shape, 6 polys, incl. building the input)\t{t:.1}");

    // ---- Part D: candidate arithmetic ---------------------------------------------------------------
    candidates(rounds);

    // ---- Part B/C: per set --------------------------------------------------------------------
    per_set!(44, 4, 4, ML_DSA_44, keygen_44, sign_44, verify_44, rounds);
    per_set!(65, 6, 5, ML_DSA_65, keygen_65, sign_65, verify_65, rounds);
    per_set!(87, 8, 7, ML_DSA_87, keygen_87, sign_87, verify_87, rounds);
}
