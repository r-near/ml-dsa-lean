//! FIPS 204 §7.3: CoeffFromThreeBytes (Alg 14), SampleInBall (Alg 29), RejNTTPoly (Alg 30),
//! ExpandA (Alg 32), ExpandMask (Alg 34).

use crate::encode::bit_unpack;
use crate::field::{Q, sub};
use crate::keccak::Shake;
use crate::params::Params;

/// Algorithm 14 CoeffFromThreeBytes(b0, b1, b2).
pub fn coeff_from_three_bytes(b0: u8, b1: u8, b2: u8) -> Option<u32> {
    let b2p = (b2 & 127) as u32;
    let z = (b2p << 16) | ((b1 as u32) << 8) | (b0 as u32);
    if z < Q { Some(z) } else { None }
}

/// Algorithm 29 SampleInBall(ρ): c with τ coefficients in {−1, 1} (as q − 1, 1) and the rest 0.
pub fn sample_in_ball(p: &Params, rho: &[u8]) -> [u32; 256] {
    let mut c = [0u32; 256];
    let mut ctx = Shake::shake256();
    ctx.absorb(rho);
    ctx.finalize();
    let mut s = [0u8; 8];
    ctx.squeeze(&mut s);
    let mut h: u64 = 0;
    let mut k = 0;
    while k < 8 {
        h |= (s[k] as u64) << (8 * k);
        k += 1;
    }
    let mut i = 256 - p.tau;
    while i < 256 {
        let mut j = [0u8; 1];
        ctx.squeeze(&mut j);
        while (j[0] as usize) > i {
            ctx.squeeze(&mut j);
        }
        let jj = j[0] as usize;
        c[i] = c[jj];
        let bit = (h >> (i + p.tau - 256)) & 1;
        c[jj] = if bit == 1 { Q - 1 } else { 1 };
        i += 1;
    }
    c
}

/// Algorithm 30 RejNTTPoly(ρ), ρ a 34-byte seed.
pub fn rej_ntt_poly(rho: &[u8; 34]) -> [u32; 256] {
    let mut a = [0u32; 256];
    let mut ctx = Shake::shake128();
    ctx.absorb(rho);
    ctx.finalize();
    let mut j = 0;
    while j < 256 {
        let mut s = [0u8; 3];
        ctx.squeeze(&mut s);
        if let Some(x) = coeff_from_three_bytes(s[0], s[1], s[2]) {
            a[j] = x;
            j += 1;
        }
    }
    a
}

/// Algorithm 32 ExpandA(ρ).
pub fn expand_a<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
    let mut a = [[[0u32; 256]; L]; K];
    let mut r = 0;
    while r < K {
        let mut s = 0;
        while s < L {
            let mut seed = [0u8; 34];
            let mut b = 0;
            while b < 32 {
                seed[b] = rho[b];
                b += 1;
            }
            seed[32] = s as u8;
            seed[33] = r as u8;
            a[r][s] = rej_ntt_poly(&seed);
            s += 1;
        }
        r += 1;
    }
    a
}

/// Algorithm 34 ExpandMask(ρ, μ). Requires μ + L − 1 < 2^16.
pub fn expand_mask<const L: usize>(p: &Params, rho: &[u8; 64], mu: u16) -> [[u32; 256]; L] {
    let mut y = [[0u32; 256]; L];
    let c = p.gamma1_bits;
    let mut v = [0u8; 640];
    let mut r = 0;
    while r < L {
        let nonce = mu + (r as u16);
        let mut ctx = Shake::shake256();
        ctx.absorb(rho);
        ctx.absorb(&[nonce as u8, (nonce >> 8) as u8]); // IntegerToBytes(μ + r, 2)
        ctx.finalize();
        ctx.squeeze(&mut v[..32 * c]);
        let z = bit_unpack(&v[..32 * c], c);
        let mut i = 0;
        while i < 256 {
            y[r][i] = sub(p.gamma1, z[i]); // BitUnpack(v, γ1 − 1, γ1): b − z
            i += 1;
        }
        r += 1;
    }
    y
}
