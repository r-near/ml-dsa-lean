//! FIPS 204 §7.3: CoeffFromThreeBytes (Alg 14), SampleInBall (Alg 29), RejNTTPoly (Alg 30),
//! ExpandA (Alg 32), ExpandMask (Alg 34), plus CoeffFromHalfByte (Alg 15), RejBoundedPoly (Alg 31),
//! ExpandS (Alg 33).

use crate::encode::bit_unpack;
use crate::field::{Q, sub};
use crate::keccak::{Shake, load_lane};
use crate::keccak4::{Lanes4, keccak_f1600_x4};
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

/// Byte `p` (`p < 168`) of the rate part of state `i` of a 4-way Keccak state, as the scalar sponge reads it
/// (`squeeze`): lane `p / 8`, shifted right by `8 * (p % 8)` bits.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn lane_byte_x4(st: &[[u64; 4]; 25], i: usize, p: usize) -> u8 {
    (st[p / 8][i] >> (8 * (p % 8))) as u8
}

/// Algorithm 30's loop on one 168-byte SHAKE128 block of state `i` of a 4-way state: the block is 56 whole
/// three-byte candidates (168 = 56 · 3), so none straddles a block boundary. Every candidate is one step of the
/// byte-wise sampler `rej_ntt_poly`: once `j = 256` coefficients are accepted the remaining candidates are ignored.
/// Returns the new number of accepted coefficients. Requires nothing: `j ≤ 256` on entry and exit.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn rej_ntt_block_x4(st: &[[u64; 4]; 25], i: usize, a: &mut [u32; 256], j: usize) -> usize {
    let mut j = j;
    let mut t = 0;
    while t < 56 {
        if j < 256 {
            let b0 = lane_byte_x4(st, i, 3 * t);
            let b1 = lane_byte_x4(st, i, 3 * t + 1);
            let b2 = lane_byte_x4(st, i, 3 * t + 2);
            if let Some(x) = coeff_from_three_bytes(b0, b1, b2) {
                a[j] = x;
                j += 1;
            }
        }
        t += 1;
    }
    j
}

/// The four SHAKE128 states `SHAKE128.Init(); Absorb(ρ ‖ s[i] ‖ r[i])` just before their first permutation, i.e.
/// with the SHAKE padding in place (`0x1F` after the 34-byte message, `0x80` as the last byte of the 168-byte
/// block), as one interleaved 4-way state. Lane `k` of state `i` is `s[k][i]`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn init_state_x4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u64; 4]; 25] {
    let mut st = [[0u64; 4]; 25];
    let mut w = 0;
    while w < 4 {
        let x = load_lane(rho, 8 * w);
        st[w] = [x, x, x, x];
        w += 1;
    }
    // Bytes 32, 33 of the message are s and r, byte 34 is the SHAKE domain/padding byte 0x1F.
    st[4] = [
        (s[0] as u64) | ((r[0] as u64) << 8) | (0x1Fu64 << 16),
        (s[1] as u64) | ((r[1] as u64) << 8) | (0x1Fu64 << 16),
        (s[2] as u64) | ((r[2] as u64) << 8) | (0x1Fu64 << 16),
        (s[3] as u64) | ((r[3] as u64) << 8) | (0x1Fu64 << 16),
    ];
    // Byte 167 = 0x80 is the top byte of lane 20.
    let last = 0x80u64 << 56;
    st[20] = [last, last, last, last];
    st
}

/// Algorithm 30 RejNTTPoly on four seeds at once: the polynomial for the seeds `ρ ‖ s[i] ‖ r[i]`, `i < 4`.
/// The four SHAKE128 streams are permuted together (`keccak_f1600_x4`); candidates are parsed per state in plain
/// Rust, block by block. State `i` stops contributing once it has accepted 256 coefficients and the loop ends when
/// all four have. Diverges exactly when one of the four unbounded samplers does (as `rej_ntt_poly` does).
///
/// The result for seed `i` is `rej_ntt_poly(ρ ‖ s[i] ‖ r[i])` (proved equal for the `Shim4` instantiation,
/// `Proofs/Sample4.lean`).
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn rej_ntt_poly_x4<X: Lanes4>(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
    let mut st = init_state_x4(rho, s, r);
    let mut p0 = [0u32; 256];
    let mut p1 = [0u32; 256];
    let mut p2 = [0u32; 256];
    let mut p3 = [0u32; 256];
    let mut j0 = 0;
    let mut j1 = 0;
    let mut j2 = 0;
    let mut j3 = 0;
    while j0 < 256 || j1 < 256 || j2 < 256 || j3 < 256 {
        keccak_f1600_x4::<X>(&mut st);
        j0 = rej_ntt_block_x4(&st, 0, &mut p0, j0);
        j1 = rej_ntt_block_x4(&st, 1, &mut p1, j1);
        j2 = rej_ntt_block_x4(&st, 2, &mut p2, j2);
        j3 = rej_ntt_block_x4(&st, 3, &mut p3, j3);
    }
    [p0, p1, p2, p3]
}

/// The matrix entry (flattened `r * L + s`) that lane `l` of the group starting at `first` computes: `first + l`,
/// or the last entry `n - 1` for a lane past the end (its polynomial is the last entry's again, written twice).
/// Requires `first < n`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
fn entry_x4(first: usize, l: usize, n: usize) -> usize {
    if first + l < n { first + l } else { n - 1 }
}

/// Algorithm 32 ExpandA(ρ) written into `a` (every entry is overwritten), four entries per call of the 4-way
/// sampler: the entries are taken in the flattened order `e = r * L + s`, in groups of four; a last group with fewer
/// than four real entries repeats the last entry.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn expand_a_into_x4<X: Lanes4, const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
    let n = K * L;
    let mut first = 0;
    while first < n {
        let e0 = entry_x4(first, 0, n);
        let e1 = entry_x4(first, 1, n);
        let e2 = entry_x4(first, 2, n);
        let e3 = entry_x4(first, 3, n);
        let polys = rej_ntt_poly_x4::<X>(
            rho,
            [(e0 % L) as u8, (e1 % L) as u8, (e2 % L) as u8, (e3 % L) as u8],
            [(e0 / L) as u8, (e1 / L) as u8, (e2 / L) as u8, (e3 / L) as u8],
        );
        a[e0 / L][e0 % L] = polys[0];
        a[e1 / L][e1 % L] = polys[1];
        a[e2 / L][e2 % L] = polys[2];
        a[e3 / L][e3 % L] = polys[3];
        first += 4;
    }
}

/// Algorithm 32 ExpandA(ρ) with the 4-way sampler, returned by value (`expand_a_into_x4` on a zero matrix).
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn expand_a_x4<X: Lanes4, const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
    let mut a = [[[0u32; 256]; L]; K];
    expand_a_into_x4::<X, K, L>(rho, &mut a);
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
        #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
        let mut z = bit_unpack(&v[..32 * c], c);
        let mut i = 0;
        while i < 256 {
            y[r][i] = sub(p.gamma1, z[i]); // BitUnpack(v, γ1 − 1, γ1): b − z
            i += 1;
        }
        // The sponge absorbed ρ″ and holds y's bits, as do `v` and `z`; y itself is returned and is the caller's.
        #[cfg(feature = "zeroize")]
        {
            use zeroize::Zeroize;
            ctx.wipe();
            z.zeroize();
        }
        r += 1;
    }
    #[cfg(feature = "zeroize")]
    {
        use zeroize::Zeroize;
        v.zeroize();
    }
    y
}

/// Algorithm 15 CoeffFromHalfByte(b): an element of [−η, η] as a canonical Z_q value, or ⊥.
pub fn coeff_from_half_byte(p: &Params, b: u8) -> Option<u32> {
    if p.eta == 2 {
        // 1: if η = 2 and b < 15 then return 2 − (b mod 5)
        if b < 15 { Some(sub(2, (b % 5) as u32)) } else { None }
    } else {
        // 2: if η = 4 and b < 9 then return 4 − b
        if b < 9 { Some(sub(4, b as u32)) } else { None }
    }
}

/// Algorithm 31 RejBoundedPoly(ρ), ρ a 66-byte seed.
pub fn rej_bounded_poly(p: &Params, rho: &[u8; 66]) -> [u32; 256] {
    let mut a = [0u32; 256];
    // 1: ctx ← H.Init(); 2: H.Absorb(ctx, ρ)
    let mut ctx = Shake::shake256();
    ctx.absorb(rho);
    ctx.finalize();
    // 3: j ← 0
    let mut j = 0;
    // 4: while j < 256
    while j < 256 {
        // 5: z ← H.Squeeze(ctx, 1)
        let mut zb = [0u8; 1];
        ctx.squeeze(&mut zb);
        // 6–7: z0 ← CoeffFromHalfByte(z mod 16); z1 ← CoeffFromHalfByte(⌊z/16⌋)
        let z0 = coeff_from_half_byte(p, zb[0] & 15);
        let z1 = coeff_from_half_byte(p, zb[0] >> 4);
        // 8–11: if z0 ≠ ⊥ then a_j ← z0; j ← j + 1
        if let Some(x) = z0 {
            a[j] = x;
            j += 1;
        }
        // 12–15: if z1 ≠ ⊥ and j < 256 then a_j ← z1; j ← j + 1
        if let Some(y) = z1 {
            if j < 256 {
                a[j] = y;
                j += 1;
            }
        }
    }
    // The sponge absorbed the seed (ρ′ for ExpandS) and holds the sampled bytes; this function does not know
    // whether they are secret.
    #[cfg(feature = "zeroize")]
    ctx.wipe();
    a
}

/// Algorithm 33 ExpandS(ρ): returns (s1, s2). Nonces r (for s1) and r + L (for s2) are
/// IntegerToBytes(·, 2), little-endian; r + L < 256 so the high byte is 0.
pub fn expand_s<const K: usize, const L: usize>(
    p: &Params,
    rho: &[u8; 64],
) -> ([[u32; 256]; L], [[u32; 256]; K]) {
    let mut s1 = [[0u32; 256]; L];
    let mut s2 = [[0u32; 256]; K];
    let mut seed = [0u8; 66];
    let mut b = 0;
    while b < 64 {
        seed[b] = rho[b];
        b += 1;
    }
    // 1–3: s1_r ← RejBoundedPoly(ρ || IntegerToBytes(r, 2))
    let mut r = 0;
    while r < L {
        seed[64] = r as u8;
        seed[65] = 0;
        s1[r] = rej_bounded_poly(p, &seed);
        r += 1;
    }
    // 4–6: s2_r ← RejBoundedPoly(ρ || IntegerToBytes(r + L, 2))
    let mut r = 0;
    while r < K {
        seed[64] = (r + L) as u8;
        seed[65] = 0;
        s2[r] = rej_bounded_poly(p, &seed);
        r += 1;
    }
    // `seed` holds ρ′. The returned s1 and s2 are the caller's. With `zeroize`, the locals are wiped after the copy
    // into the result tuple (arrays are `Copy`): `s1` and `s2` here would otherwise stay in the dead frame.
    let out = (s1, s2);
    #[cfg(feature = "zeroize")]
    {
        use zeroize::Zeroize;
        seed.zeroize();
        s1.zeroize();
        s2.zeroize();
    }
    out
}
