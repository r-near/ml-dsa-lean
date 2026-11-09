//! FIPS 204 §7.3: CoeffFromThreeBytes (Alg 14), SampleInBall (Alg 29), RejNTTPoly (Alg 30),
//! ExpandA (Alg 32), ExpandMask (Alg 34), plus CoeffFromHalfByte (Alg 15), RejBoundedPoly (Alg 31),
//! ExpandS (Alg 33).

use crate::encode::bit_unpack;
use crate::field::{Q, sub};
use crate::keccak::{Shake, keccak_f1600, load_lane};
use crate::keccak4::keccak_f1600_x4;
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

/// The mask of the 23 bits CoeffFromThreeBytes keeps: `z` is bits 0..22 of the three-byte little-endian value (the top
/// bit of the third byte is cleared).
const M23: u64 = 0x7F_FFFF;

/// One candidate of Algorithm 30's loop, branchless: `z` is written to `a[j]` and `j` advances only when `z < q`, so a
/// rejected candidate's word is overwritten by the next one. Requires `j < 312`.
fn push_candidate(a: &mut [u32; 312], j: usize, z: u32) -> usize {
    a[j] = z;
    j + (z < Q) as usize
}

/// The eight three-byte candidates in 24 consecutive rate bytes, which are three whole lanes `w0, w1, w2` (little-endian
/// bytes): candidate `t` is bits `24t .. 24t+22` of the 192-bit value `w0 + 2^64 w1 + 2^128 w2`, taken from the lanes by
/// shifts and masks instead of byte by byte. Candidates 2 and 5 straddle a lane boundary. Requires `j + 7 < 312`.
fn rej_ntt_cands8(w0: u64, w1: u64, w2: u64, a: &mut [u32; 312], j: usize) -> usize {
    let j = push_candidate(a, j, (w0 & M23) as u32);
    let j = push_candidate(a, j, ((w0 >> 24) & M23) as u32);
    let j = push_candidate(a, j, ((w0 >> 48).wrapping_add(w1 << 16) & M23) as u32);
    let j = push_candidate(a, j, ((w1 >> 8) & M23) as u32);
    let j = push_candidate(a, j, ((w1 >> 32) & M23) as u32);
    let j = push_candidate(a, j, ((w1 >> 56).wrapping_add(w2 << 8) & M23) as u32);
    let j = push_candidate(a, j, ((w2 >> 16) & M23) as u32);
    push_candidate(a, j, ((w2 >> 40) & M23) as u32)
}

/// Algorithm 30's loop on one SHAKE128 block of state `i`: the block is the 21 rate lanes `st[0..21][i]` (168 bytes =
/// 56 whole three-byte candidates, so none straddles a block boundary), parsed straight from the lanes in seven groups
/// of three. All 56 candidates are parsed even if `j` reaches 256 inside the block; `a` has 56 words of slack past the
/// 256 coefficients for that, and the words from index `min(j, 256)` on are unspecified (the caller keeps only the
/// first 256 words, and only blocks entered with `j < 256` are parsed). Returns the new `j`. Requires `i < 4` and
/// `j < 256` (so every write index is at most 255 + 55 = 310).
fn rej_ntt_block_x4(st: &[[u64; 4]; 25], i: usize, a: &mut [u32; 312], j: usize) -> usize {
    let mut j = j;
    let mut g = 0;
    while g < 7 {
        j = rej_ntt_cands8(st[3 * g][i], st[3 * g + 1][i], st[3 * g + 2][i], a, j);
        g += 1;
    }
    j
}

/// The four SHAKE128 states `SHAKE128.Init(); Absorb(ρ ‖ s[i] ‖ r[i])` just before their first permutation, i.e.
/// with the SHAKE padding in place (`0x1F` after the 34-byte message, `0x80` as the last byte of the 168-byte
/// block), as one interleaved 4-way state. Lane `k` of state `i` is `s[k][i]`.
fn init_state_x4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u64; 4]; 25] {
    let mut st = [[0u64; 4]; 25];
    // Bytes 0..32 of the message are ρ, the same in all four states.
    let x0 = load_lane(rho, 0);
    let x1 = load_lane(rho, 8);
    let x2 = load_lane(rho, 16);
    let x3 = load_lane(rho, 24);
    st[0] = [x0, x0, x0, x0];
    st[1] = [x1, x1, x1, x1];
    st[2] = [x2, x2, x2, x2];
    st[3] = [x3, x3, x3, x3];
    // Bytes 32, 33 of the message are s and r, byte 34 is the SHAKE domain/padding byte 0x1F (bits 16..24 of the lane).
    st[4] = [
        (s[0] as u64) | ((r[0] as u64) << 8usize) | 0x1F_0000u64,
        (s[1] as u64) | ((r[1] as u64) << 8usize) | 0x1F_0000u64,
        (s[2] as u64) | ((r[2] as u64) << 8usize) | 0x1F_0000u64,
        (s[3] as u64) | ((r[3] as u64) << 8usize) | 0x1F_0000u64,
    ];
    // Byte 167 = 0x80 is the top byte of lane 20.
    let last = 0x8000_0000_0000_0000u64;
    st[20] = [last, last, last, last];
    st
}

/// One lane's step of the 4-way sampler: parses the lane's block into its 312-word scratch while it still needs
/// coefficients (`j < 256`), and does nothing once it has 256.
fn rej_ntt_lane_x4(st: &[[u64; 4]; 25], i: usize, a: &mut [u32; 312], j: usize) -> usize {
    if j < 256 { rej_ntt_block_x4(st, i, a, j) } else { j }
}

/// The first 256 words of a lane's 312-word scratch.
fn first_256(a: &[u32; 312]) -> [u32; 256] {
    let mut r = [0u32; 256];
    let mut k = 0;
    while k < 256 {
        r[k] = a[k];
        k += 1;
    }
    r
}

/// Algorithm 30 RejNTTPoly on four seeds at once: the polynomial for the seeds `ρ ‖ s[i] ‖ r[i]`, `i < 4`.
/// The four SHAKE128 streams are permuted together (`keccak_f1600_x4`); each state's block is then stored as bytes and
/// parsed without branches (`rej_ntt_block_x4`), block by block. State `i` stops contributing once it has accepted 256
/// coefficients and the loop ends when all four have. Diverges exactly when one of the four unbounded samplers does (as
/// `rej_ntt_poly` does).
///
/// The result for seed `i` is `rej_ntt_poly(ρ ‖ s[i] ‖ r[i])` (proved equal, `Proofs/Sample4.lean`).
pub fn rej_ntt_poly_x4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
    let mut st = init_state_x4(rho, s, r);
    let mut p0 = [0u32; 312];
    let mut p1 = [0u32; 312];
    let mut p2 = [0u32; 312];
    let mut p3 = [0u32; 312];
    let mut j0 = 0;
    let mut j1 = 0;
    let mut j2 = 0;
    let mut j3 = 0;
    // `more`: some state still needs coefficients. The first pass is always needed (all four counts are 0).
    let mut more = true;
    while more {
        keccak_f1600_x4(&mut st);
        j0 = rej_ntt_lane_x4(&st, 0, &mut p0, j0);
        j1 = rej_ntt_lane_x4(&st, 1, &mut p1, j1);
        j2 = rej_ntt_lane_x4(&st, 2, &mut p2, j2);
        j3 = rej_ntt_lane_x4(&st, 3, &mut p3, j3);
        more = j0 < 256 || j1 < 256 || j2 < 256 || j3 < 256;
    }
    [first_256(&p0), first_256(&p1), first_256(&p2), first_256(&p3)]
}

/// The matrix entry (flattened `r * L + s`) that lane `l` of the group starting at `first` computes: `first + l`,
/// or the last entry `n - 1` for a lane past the end (its polynomial is the last entry's again, written twice).
/// Requires `first < n`.
fn entry_x4(first: usize, l: usize, n: usize) -> usize {
    if first + l < n { first + l } else { n - 1 }
}

/// Algorithm 32 ExpandA(ρ) written into `a` (every entry is overwritten), four entries per call of the 4-way
/// sampler: the entries are taken in the flattened order `e = r * L + s`, in groups of four; a last group with fewer
/// than four real entries repeats the last entry.
#[cfg_attr(not(feature = "internals"), allow(dead_code))]
pub fn expand_a_into_x4<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
    expand_a_from_x4::<K, L>(rho, a, 0)
}

/// The group loop of `expand_a_into_x4`, starting at entry `first0`: entries `first0, first0 + 1, ...` (flattened as
/// there) in groups of four until all `K * L` are done. Entries before `first0` are not touched.
pub fn expand_a_from_x4<const K: usize, const L: usize>(
    rho: &[u8; 32],
    a: &mut [[[u32; 256]; L]; K],
    first0: usize,
) {
    let n = K * L;
    let mut first = first0;
    while first < n {
        let e0 = entry_x4(first, 0, n);
        let e1 = entry_x4(first, 1, n);
        let e2 = entry_x4(first, 2, n);
        let e3 = entry_x4(first, 3, n);
        let polys = rej_ntt_poly_x4(
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
#[cfg_attr(not(feature = "internals"), allow(dead_code))]
pub fn expand_a_x4<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
    let mut a = [[[0u32; 256]; L]; K];
    expand_a_into_x4::<K, L>(rho, &mut a);
    a
}

/// The SHAKE256 rate in bytes.
const RATE256: usize = 136;

/// The last block of `SHAKE256.Absorb(pk)` with the padding in place, as 17 little-endian lanes: the `pk.len() % 136`
/// bytes of `pk` after its last whole block, then the domain byte `0x1F` and the final padding bit `0x80` (`pad10*1`
/// of FIPS 202; they share a byte, as XOR, only when a single byte is left).
fn tr_tail_lanes(pk: &[u8]) -> [u64; 17] {
    let base = RATE256 * (pk.len() / RATE256);
    let rem = pk.len() - base;
    let mut w = [0u64; 17];
    let mut i = 0;
    while i < rem {
        w[i / 8] ^= (pk[base + i] as u64) << (8 * (i % 8));
        i += 1;
    }
    w[rem / 8] ^= 0x1Fu64 << (8 * (rem % 8));
    w[16] ^= 0x8000_0000_0000_0000u64;
    w
}

/// XORs block `t` of the padded `pk` (17 lanes: whole block `t` of `pk` when `t < q`, else the padded `tail`) into
/// lane 3 of the 4-way state. Requires `q = pk.len() / 136`; lanes 0 to 2 and rate-external words are untouched.
fn absorb_block_lane3(st: &mut [[u64; 4]; 25], pk: &[u8], tail: &[u64; 17], q: usize, t: usize) {
    let mut k = 0;
    while k < 17 {
        let w = if t < q { load_lane(pk, RATE256 * t + 8 * k) } else { tail[k] };
        st[k][3] ^= w;
        k += 1;
    }
}

/// Lane 3 of the 4-way state, as a scalar Keccak state.
fn lane3_state(st: &[[u64; 4]; 25]) -> [u64; 25] {
    let mut s = [0u64; 25];
    let mut k = 0;
    while k < 25 {
        s[k] = st[k][3];
        k += 1;
    }
    s
}

/// Replaces lane 3 of the 4-way state by the scalar state `s`.
fn set_lane3(st: &mut [[u64; 4]; 25], s: &[u64; 25]) {
    let mut k = 0;
    while k < 25 {
        st[k][3] = s[k];
        k += 1;
    }
}

/// Algorithm 30 RejNTTPoly on three seeds, with a SHAKE256 absorb of `pk` running in the fourth lane of the same
/// permutations. Lanes 0 to 2 are exactly `rej_ntt_poly_x4`'s lanes 0 to 2 (the seeds `ρ ‖ s[i] ‖ r[i]`; `s[3]` and `r[3]`
/// are unused but must be given and are what lane 3 would sample); lane 3 holds the SHAKE256 sponge whose state before this call
/// is `trs` after `t` permutations, i.e. with the first `t` blocks of the padded `pk` absorbed (`t <= q + 1`, where
/// `q + 1 = ⌈(pk.len() + 1) / 136⌉` is the number of blocks). Each permutation of the sampler loop first XORs block `t` into lane 3 (while
/// `t <= q`) and so advances the sponge by one block. Returns the three polynomials and the sponge's `(trs, t)` after the call (`t`
/// grows by one per permutation until it reaches `q + 1`, where `trs` is the sponge state after its last permutation
/// and later permutations of the group no longer matter). Requires `q = pk.len() / 136` and `tail = tr_tail_lanes(pk)`.
pub fn rej_ntt_poly_x3_tr(
    rho: &[u8; 32],
    s: [u8; 4],
    r: [u8; 4],
    pk: &[u8],
    tail: &[u64; 17],
    q: usize,
    trs0: [u64; 25],
    t0: usize,
) -> ([[u32; 256]; 3], [u64; 25], usize) {
    let mut st = init_state_x4(rho, s, r);
    set_lane3(&mut st, &trs0);
    let mut trs = trs0;
    let mut t = t0;
    let mut p0 = [0u32; 312];
    let mut p1 = [0u32; 312];
    let mut p2 = [0u32; 312];
    let mut j0 = 0;
    let mut j1 = 0;
    let mut j2 = 0;
    let mut more = true;
    while more {
        if t <= q {
            absorb_block_lane3(&mut st, pk, tail, q, t);
        }
        keccak_f1600_x4(&mut st);
        j0 = rej_ntt_lane_x4(&st, 0, &mut p0, j0);
        j1 = rej_ntt_lane_x4(&st, 1, &mut p1, j1);
        j2 = rej_ntt_lane_x4(&st, 2, &mut p2, j2);
        if t <= q {
            t += 1;
            if t == q + 1 {
                trs = lane3_state(&st);
            }
        }
        more = j0 < 256 || j1 < 256 || j2 < 256;
    }
    if t <= q {
        trs = lane3_state(&st);
    }
    ([first_256(&p0), first_256(&p1), first_256(&p2)], trs, t)
}

/// The first 64 bytes of the sponge state, little-endian: `SHAKE256.Squeeze(ctx, 64)` right after the last permutation.
fn squeeze64(s: &[u64; 25]) -> [u8; 64] {
    let mut out = [0u8; 64];
    let mut j = 0;
    while j < 64 {
        out[j] = (s[j / 8] >> (8 * (j % 8))) as u8;
        j += 1;
    }
    out
}

/// The scalar rest of the SHAKE256 absorb of `pk`: from the sponge state `trs` after `t` permutations (`t <= q + 1`), absorbs
/// the remaining blocks of the padded `pk` (block `t` and on) with the scalar permutation and returns the first 64 bytes of the
/// final state, `H(pk, 64)`. Requires `q = pk.len() / 136` and `tail = tr_tail_lanes(pk)`.
fn tr_finish_scalar(pk: &[u8], tail: &[u64; 17], q: usize, trs: [u64; 25], t0: usize) -> [u8; 64] {
    let mut s = trs;
    let mut t = t0;
    while t <= q {
        let mut k = 0;
        while k < 17 {
            s[k] ^= if t < q { load_lane(pk, RATE256 * t + 8 * k) } else { tail[k] };
            k += 1;
        }
        keccak_f1600(&mut s);
        t += 1;
    }
    squeeze64(&s)
}

/// How many of the first groups of ExpandA take three entries and run the SHAKE256 absorb of `pk` in the fourth lane, for
/// `n` entries and a pk of `q * 136 + rem` bytes. The hash is correct for any value (`expand_a_tr_into_x4` finishes what the
/// lane did not reach with the scalar permutation); this only picks the faster schedule. A group takes at least 5
/// permutations (256 coefficients need at least 5 blocks of 56 candidates), so `want = ⌈(q + 1) / 5⌉` groups (2, 3, 4 for the
/// three parameter sets) hash the whole pk. The groups of four leave `spare = 4 * ⌈n / 4⌉ - n` lanes empty (2 for
/// ML-DSA-65, none for -44 and -87), and a 3-wide group in a spare lane costs nothing; with no spare lane left, one extra group
/// (about 2.7 µs) hosts up to four hashing groups and pays when it hosts at least two (5 scalar permutations, about 1.85 µs,
/// each). So: `spare` groups when `want` is just one more (ML-DSA-65: the third hashing group would cost an extra group
/// for 1.85 µs), else all `want`.
fn tr_groups(n: usize, q: usize) -> usize {
    let want = (q + 5) / 5;
    let spare = 4 * ((n + 3) / 4) - n;
    if want == spare + 1 { spare } else { want }
}

/// Algorithm 32 ExpandA(ρ) written into `a`, and `H(pk, 64)` (FIPS 204's `tr`), in the same permutations: the first
/// `tr_groups` groups take three entries each and run the SHAKE256 absorb of `pk` in the fourth lane
/// (`rej_ntt_poly_x3_tr`), the rest are groups of four as in `expand_a_into_x4`, and whatever of the hash the lane did
/// not reach (for ML-DSA-65 the last five permutations) is finished with the scalar permutation.
pub fn expand_a_tr_into_x4<const K: usize, const L: usize>(
    rho: &[u8; 32],
    pk: &[u8],
    a: &mut [[[u32; 256]; L]; K],
) -> [u8; 64] {
    let n = K * L;
    let q = pk.len() / RATE256;
    let g3 = tr_groups(n, q);
    let tail = tr_tail_lanes(pk);
    let mut trs = [0u64; 25];
    let mut t = 0;
    let mut first = 0;
    let mut g = 0;
    while first < n && g < g3 {
        let e0 = entry_x4(first, 0, n);
        let e1 = entry_x4(first, 1, n);
        let e2 = entry_x4(first, 2, n);
        let (polys, trs2, t2) = rej_ntt_poly_x3_tr(
            rho,
            [(e0 % L) as u8, (e1 % L) as u8, (e2 % L) as u8, (e2 % L) as u8],
            [(e0 / L) as u8, (e1 / L) as u8, (e2 / L) as u8, (e2 / L) as u8],
            pk,
            &tail,
            q,
            trs,
            t,
        );
        trs = trs2;
        t = t2;
        a[e0 / L][e0 % L] = polys[0];
        a[e1 / L][e1 % L] = polys[1];
        a[e2 / L][e2 % L] = polys[2];
        first += 3;
        g += 1;
    }
    expand_a_from_x4::<K, L>(rho, a, first);
    tr_finish_scalar(pk, &tail, q, trs, t)
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

#[cfg(test)]
mod boundary_tests {
    //! Deterministic boundary tests of the branchless 4-way rejection parse, on rate bytes chosen to sit on the edges of
    //! Algorithm 14 and Algorithm 30: candidates q − 1, q, q + 1, values with bit 23 set (which CoeffFromThreeBytes masks
    //! off), candidates that straddle a lane boundary, and the cutoff at 256 accepted coefficients. SHAKE output cannot be
    //! steered, so these build the interleaved state from chosen bytes and call the parse on it, and compare every case
    //! with the scalar `coeff_from_three_bytes`. They pin down, for example, the mutants `z < Q` → `z <= Q`,
    //! `& M23` → `& 0xFF_FFFF`, a wrong shift in `rej_ntt_cands8`, `j < 256` → `j <= 256` in `rej_ntt_lane_x4`, and an
    //! off-by-one in `first_256`. The parse does not involve the permutation; the permutation compiled with AVX2 target features is
    //! tested against the scalar one in `tests/keccak4_long.rs` and on whole samplers in `tests/fast_verify.rs`.
    extern crate std;
    use super::*;
    use std::vec::Vec;

    const QU: u32 = Q;

    /// 56 candidates (24-bit little-endian triples) as a 168-byte block.
    fn block(cands: &[u32; 56]) -> [u8; 168] {
        let mut b = [0u8; 168];
        for (t, &v) in cands.iter().enumerate() {
            b[3 * t] = v as u8;
            b[3 * t + 1] = (v >> 8) as u8;
            b[3 * t + 2] = (v >> 16) as u8;
        }
        b
    }

    /// A 4-way state whose lane `i` holds `buf` as its 21 rate lanes (little-endian bytes); the other three states hold
    /// unrelated words that must not leak into state `i`'s candidates.
    fn state_with(buf: &[u8; 168], i: usize) -> [[u64; 4]; 25] {
        let mut st = [[0u64; 4]; 25];
        for k in 0..25 {
            for lane in 0..4 {
                st[k][lane] = (k as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ ((lane as u64) << 59) ^ 0x5555_5555_5555_5555;
            }
        }
        for k in 0..21 {
            let mut w = 0u64;
            for b in 0..8 {
                w |= (buf[8 * k + b] as u64) << (8 * b);
            }
            st[k][i] = w;
        }
        st
    }

    /// The accepted values of a block per Algorithm 14, in order.
    fn accepted(buf: &[u8; 168]) -> Vec<u32> {
        (0..56).filter_map(|t| coeff_from_three_bytes(buf[3 * t], buf[3 * t + 1], buf[3 * t + 2])).collect()
    }

    /// Candidate lists around the boundaries, rotated so that each edge value is tried at every position mod 56 (so at
    /// every offset within a lane, including the two candidates per group of three lanes that straddle one).
    fn edge_blocks() -> Vec<[u8; 168]> {
        let edges: [u32; 20] = [
            QU - 2, QU - 1, QU, QU + 1, QU + 2, 0x7F_FFFF, 0x80_0000, 0x80_0001, 0x80_0000 | (QU - 1), 0x80_0000 | QU,
            0x80_0000 | (QU + 1), 0xFF_FFFF, 0xFF_FFFE, 0x7F_FFFE, 0, 1, 0xFF_E000 | 1, 0x80_0000 | 0x7F_E000, 1 << 22, (1 << 22) - 1,
        ];
        let mut out = Vec::new();
        for rot in 0..56 {
            let mut c = [0u32; 56];
            for (t, x) in c.iter_mut().enumerate() {
                *x = edges[(t + rot) % edges.len()];
            }
            out.push(block(&c));
        }
        // All accepted at the top of the range, all rejected just above it, and alternating q - 1 / q.
        out.push(block(&[QU - 1; 56]));
        out.push(block(&[QU; 56]));
        out.push(block(&[0x80_0000 | QU; 56]));
        out.push(block(&[0x80_0000 | (QU - 1); 56]));
        let mut alt = [0u32; 56];
        for (t, x) in alt.iter_mut().enumerate() {
            *x = if t % 2 == 0 { QU - 1 } else { QU };
        }
        out.push(block(&alt));
        out
    }

    /// The eight candidates of three lanes, one by one, including the two that straddle a lane boundary.
    #[test]
    fn cands8_reads_each_candidate_from_the_right_bits() {
        // Candidate t = 24t.. of the 192-bit value; use a value whose candidates are distinct and have bit 23 set in some.
        let cands: [u32; 8] = [0x7F_E000, 0xFF_E001, 0x12_3456, 0x89_ABCD, 0x7F_FFFF, 0x80_0000, 0x00_0001, 0xFE_DCBA];
        let mut bytes = [0u8; 24];
        for (t, &v) in cands.iter().enumerate() {
            bytes[3 * t] = v as u8;
            bytes[3 * t + 1] = (v >> 8) as u8;
            bytes[3 * t + 2] = (v >> 16) as u8;
        }
        let w = |k: usize| u64::from_le_bytes(bytes[8 * k..8 * k + 8].try_into().unwrap());
        let mut a = [0u32; 312];
        let j = rej_ntt_cands8(w(0), w(1), w(2), &mut a, 0);
        let want: Vec<u32> = cands.iter().filter_map(|&v| if (v & 0x7F_FFFF) < QU { Some(v & 0x7F_FFFF) } else { None }).collect();
        assert_eq!(j, want.len());
        assert_eq!(&a[..j], &want[..]);
        // Every candidate position written, accepted or not: the word stored at the call's end for rejected candidates is
        // the masked value, so the stores are exactly the 23-bit values, in order, at j(t).
        let mut a2 = [0u32; 312];
        let mut jj = 0;
        for &v in &cands {
            if (v & 0x7F_FFFF) < QU {
                jj += 1;
            }
        }
        assert_eq!(rej_ntt_cands8(w(0), w(1), w(2), &mut a2, 5), 5 + jj);
        assert_eq!(&a2[5..5 + jj], &want[..]);
    }

    #[test]
    fn block_parse_matches_scalar_on_boundary_candidates() {
        for buf in edge_blocks() {
            let acc = accepted(&buf);
            for i in 0..4 {
                let st = state_with(&buf, i);
                for j0 in [0usize, 1, 100, 199, 200, 254, 255] {
                    let mut a = [0xDEAD_BEEFu32; 312];
                    let j1 = rej_ntt_block_x4(&st, i, &mut a, j0);
                    assert_eq!(j1, j0 + acc.len(), "count, state {i}, j0={j0}");
                    // Every accepted word is stored at its position (the slack words keep them past 256 too).
                    assert_eq!(&a[j0..j1], &acc[..], "words, state {i}, j0={j0}");
                }
            }
        }
    }

    /// The cutoff at 256: a lane that already has 256 coefficients is not parsed; one with 255 is, and its 256th word is the
    /// first accepted candidate of the block.
    #[test]
    fn lane_step_stops_exactly_at_256() {
        for lane in 0..4 {
            let st = state_with(&block(&[QU - 1; 56]), lane);
            // 256 already: untouched, same j.
            let mut a = [7u32; 312];
            assert_eq!(rej_ntt_lane_x4(&st, lane, &mut a, 256), 256);
            assert_eq!(a, [7u32; 312], "a lane with 256 coefficients must not be parsed");
            // 255: parsed, 56 more accepted.
            let mut a = [7u32; 312];
            assert_eq!(rej_ntt_lane_x4(&st, lane, &mut a, 255), 255 + 56);
            assert_eq!(a[255], QU - 1);
            assert_eq!(first_256(&a)[255], QU - 1);
            // 255 with every candidate rejected: j stays (the word at 255 is then unspecified, so only j is checked).
            let st2 = state_with(&block(&[QU; 56]), lane);
            let mut a = [7u32; 312];
            assert_eq!(rej_ntt_lane_x4(&st2, lane, &mut a, 255), 255);
        }
    }

    /// `first_256` returns words 0..255 in order, including word 255.
    #[test]
    fn first_256_keeps_word_255_and_drops_256() {
        let mut a = [0u32; 312];
        for (k, x) in a.iter_mut().enumerate() {
            *x = k as u32 + 1;
        }
        let r = first_256(&a);
        assert_eq!(r[0], 1);
        assert_eq!(r[255], 256);
        assert!(r.iter().all(|&x| x <= 256));
    }
}
