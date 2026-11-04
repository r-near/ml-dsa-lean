//! FIPS 204 §7.4: Power2Round, Decompose, HighBits, LowBits, MakeHint (Algorithms 35–39),
//! UseHint (Alg 40), and the infinity norm. Values are canonical in Z_q; a "signed" result r stands for r mod± q.

use crate::field::{Q, ct_lt_mask, ct_select, opaque_u32, small_reduce, sub};
use crate::params::Params;

/// Barrett reduction x mod m for x < q (upstream `BarrettReduce::reduce`).
fn reduce_mod(x: u32, m: u32, shift: u32, mult: u64) -> u32 {
    let m64 = m as u64;
    let x = x as u64;
    // wrapping_*: x < q and mult <= 524800 give x * mult < 2^63, and quotient * m <= x, so nothing wraps; the plain operators
    // would carry overflow-check guards on secret data (checkct/README.md).
    let quotient = x.wrapping_mul(mult) >> shift;
    let remainder = x.wrapping_sub(quotient.wrapping_mul(m64));
    let r_small = remainder as u32;
    let r_large = remainder.wrapping_sub(m64) as u32;
    ct_select(r_large, r_small, ct_lt_mask(remainder, m64) as u32)
}

/// r mod± m (m even), as an element of Z_q.
fn mod_plus_minus(r: u32, m: u32, shift: u32, mult: u64) -> u32 {
    let raw = reduce_mod(r, m, shift, mult);
    let lower = !ct_lt_mask((m >> 1) as u64, raw as u64) as u32; // all-ones iff raw <= m/2
    ct_select(small_reduce(raw.wrapping_add(Q).wrapping_sub(m)), raw, lower)
}

/// Algorithm 35 Power2Round(r): returns (r1, r0) with r = r1·2^13 + r0.
pub fn power2round(r: u32) -> (u32, u32) {
    let r0 = mod_plus_minus(r, 1 << 13, 28, 32_768);
    let r1 = sub(r, r0) >> 13;
    (r1, r0)
}

/// Algorithm 36 Decompose(r): returns (r1, r0).
pub fn decompose(p: &Params, r: u32) -> (u32, u32) {
    let two_gamma2 = 2 * p.gamma2;
    let r0 = mod_plus_minus(r, two_gamma2, p.two_gamma2_shift, p.two_gamma2_mult);
    let diff = sub(r, r0);
    let is_edge = opaque_u32(!ct_lt_mask(0, (diff ^ (Q - 1)) as u64) as u32); // all-ones iff diff == q - 1
    let r1 = (((diff as u64).wrapping_mul(p.two_gamma2_div_mult)) >> 48) as u32;
    (ct_select(r1, 0, is_edge), ct_select(r0, sub(r0, 1), is_edge))
}

/// Algorithm 37 HighBits(r).
pub fn high_bits(p: &Params, r: u32) -> u32 {
    decompose(p, r).0
}

/// Algorithm 38 LowBits(r).
pub fn low_bits(p: &Params, r: u32) -> u32 {
    decompose(p, r).1
}

/// HighBits applied coefficient-wise.
pub fn poly_high_bits(p: &Params, w: &[u32; 256]) -> [u32; 256] {
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = high_bits(p, w[j]);
        j += 1;
    }
    out
}

/// LowBits applied coefficient-wise.
pub fn poly_low_bits(p: &Params, w: &[u32; 256]) -> [u32; 256] {
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = low_bits(p, w[j]);
        j += 1;
    }
    out
}

/// Algorithm 39 MakeHint(z, r): 1 iff HighBits(r) != HighBits(r + z).
pub fn make_hint(p: &Params, z: u32, r: u32) -> bool {
    let r1 = high_bits(p, r);
    let v1 = high_bits(p, crate::field::add(r, z));
    r1 != v1
}

/// |r mod± q|.
pub fn infinity_norm(r: u32) -> u32 {
    let lower = !ct_lt_mask((Q >> 1) as u64, r as u64) as u32; // all-ones iff r <= (q-1)/2
    ct_select(Q.wrapping_sub(r), r, lower)
}

/// max_i |w_i mod± q| over a polynomial vector (constant-time max).
pub fn vec_infinity_norm<const N: usize>(w: &[[u32; 256]; N]) -> u32 {
    let mut acc = 0u32;
    let mut i = 0;
    while i < N {
        let mut j = 0;
        while j < 256 {
            let x = infinity_norm(w[i][j]);
            // opaque_u32: without it LLVM's x86 cmov-to-branch conversion turns this running maximum into `cmp; ja` in
            // the non-vectorized build (checkct response_*/hint_step_* under nearcore-novec).
            acc = ct_select(acc, x, opaque_u32(ct_lt_mask(acc as u64, x as u64) as u32));
            j += 1;
        }
        i += 1;
    }
    acc
}

/// Algorithm 40 UseHint(h, r). Public data (Verify): branches are fine.
pub fn use_hint(p: &Params, h: bool, r: u32) -> u32 {
    // 1: m ← (q − 1)/(2γ2)
    let m = (Q - 1) / (2 * p.gamma2);
    // 2: (r1, r0) ← Decompose(r)
    let (r1, r0) = decompose(p, r);
    if h {
        // r0 > 0 as a signed value: canonical r0 in (0, (q−1)/2]
        if r0 != 0 && r0 <= (Q >> 1) {
            // 4: (r1 + 1) mod m
            (r1 + 1) % m
        } else {
            // 5: (r1 − 1) mod m
            (r1 + m - 1) % m
        }
    } else {
        r1
    }
}

/// UseHint applied coefficient-wise.
pub fn poly_use_hint(p: &Params, h: &[bool; 256], r: &[u32; 256]) -> [u32; 256] {
    let mut out = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        out[j] = use_hint(p, h[j], r[j]);
        j += 1;
    }
    out
}

/// Power2Round applied coefficient-wise: returns (t1, t0).
pub fn poly_power2round(t: &[u32; 256]) -> ([u32; 256], [u32; 256]) {
    let mut t1 = [0u32; 256];
    let mut t0 = [0u32; 256];
    let mut j = 0;
    while j < 256 {
        let (a, b) = power2round(t[j]);
        t1[j] = a;
        t0[j] = b;
        j += 1;
    }
    (t1, t0)
}
