//! FIPS 204 §7.1–7.2: SimpleBitPack/BitPack/BitUnpack (Alg 16–19), HintBitPack (Alg 20),
//! skDecode (Alg 25), sigEncode (Alg 26), w1Encode (Alg 28),
//! pkEncode/pkDecode (Alg 22/23), skEncode (Alg 24), HintBitUnpack (Alg 21), sigDecode (Alg 27). Bit order is little-endian.

use crate::field::{Q, sub};
use crate::params::Params;

/// Pack 256 values of `c` bits each (each value < 2^c) into 32·c bytes.
pub fn bit_pack(w: &[u32; 256], c: usize, out: &mut [u8]) {
    let mut acc: u64 = 0;
    let mut nbits = 0;
    let mut o = 0;
    let mut i = 0;
    while i < 256 {
        acc |= (w[i] as u64) << nbits;
        nbits += c;
        while nbits >= 8 {
            out[o] = acc as u8;
            acc >>= 8;
            nbits -= 8;
            o += 1;
        }
        i += 1;
    }
}

/// Inverse of `bit_pack`: 256 values of `c` bits from 32·c bytes.
pub fn bit_unpack(v: &[u8], c: usize) -> [u32; 256] {
    let mut w = [0u32; 256];
    let mut acc: u64 = 0;
    let mut nbits = 0;
    let mut o = 0;
    let mask = (1u64 << c) - 1;
    let mut i = 0;
    while i < 256 {
        while nbits < c {
            acc |= (v[o] as u64) << nbits;
            nbits += 8;
            o += 1;
        }
        w[i] = (acc & mask) as u32;
        acc >>= c;
        nbits -= c;
        i += 1;
    }
    w
}

/// `bit_unpack` for the public inputs of verify, where `c` is 10 (t1 in pkDecode) or 18 or 20 (z in sigDecode): the
/// same function, computed a fixed number of bytes at a time with constant offsets and shifts, so that no bit accumulator
/// runs through the loop and the compiler can drop the bounds checks. Any other `c` takes the generic `bit_unpack`.
/// `v` must hold `32·c` bytes (as for `bit_unpack`; a shorter `v` panics). Equal to `bit_unpack` for every `v`
/// (`Proofs/Encode.lean`, `bit_unpack_pub_core` and `bit_unpack_pub_spec_repr`; `tests/leaf.rs` compares them on random and extreme inputs).
/// Not for secret data (the generic one is what the secret-key decoders use).
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn bit_unpack_pub(v: &[u8], c: usize) -> [u32; 256] {
    let mut w = [0u32; 256];
    if c == 20 {
        // two values per five bytes
        let v = &v[..640];
        let mut g = 0;
        while g < 128 {
            let o = 5 * g;
            let b0 = v[o] as u32;
            let b1 = v[o + 1] as u32;
            let b2 = v[o + 2] as u32;
            let b3 = v[o + 3] as u32;
            let b4 = v[o + 4] as u32;
            w[2 * g] = b0 | (b1 << 8) | ((b2 & 15) << 16);
            w[2 * g + 1] = (b2 >> 4) | (b3 << 4) | (b4 << 12);
            g += 1;
        }
        w
    } else if c == 18 {
        // four values per nine bytes
        let v = &v[..576];
        let mut g = 0;
        while g < 64 {
            let o = 9 * g;
            let b0 = v[o] as u32;
            let b1 = v[o + 1] as u32;
            let b2 = v[o + 2] as u32;
            let b3 = v[o + 3] as u32;
            let b4 = v[o + 4] as u32;
            let b5 = v[o + 5] as u32;
            let b6 = v[o + 6] as u32;
            let b7 = v[o + 7] as u32;
            let b8 = v[o + 8] as u32;
            w[4 * g] = b0 | (b1 << 8) | ((b2 & 3) << 16);
            w[4 * g + 1] = (b2 >> 2) | (b3 << 6) | ((b4 & 15) << 14);
            w[4 * g + 2] = (b4 >> 4) | (b5 << 4) | ((b6 & 63) << 12);
            w[4 * g + 3] = (b6 >> 6) | (b7 << 2) | (b8 << 10);
            g += 1;
        }
        w
    } else if c == 10 {
        // four values per five bytes
        let v = &v[..320];
        let mut g = 0;
        while g < 64 {
            let o = 5 * g;
            let b0 = v[o] as u32;
            let b1 = v[o + 1] as u32;
            let b2 = v[o + 2] as u32;
            let b3 = v[o + 3] as u32;
            let b4 = v[o + 4] as u32;
            w[4 * g] = b0 | ((b1 & 3) << 8);
            w[4 * g + 1] = (b1 >> 2) | ((b2 & 15) << 6);
            w[4 * g + 2] = (b2 >> 4) | ((b3 & 63) << 4);
            w[4 * g + 3] = (b3 >> 6) | (b4 << 2);
            g += 1;
        }
        w
    } else {
        bit_unpack(v, c)
    }
}

/// Algorithm 17/19 with a = b − 1 or a = b: coefficients w ∈ [−a, b] are stored as b − w.
fn pack_signed(w: &[u32; 256], b: u32, c: usize, out: &mut [u8]) {
    let mut t = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        t[i] = sub(b, w[i]);
        i += 1;
    }
    bit_pack(&t, c, out);
}
/// Algorithm 19 BitUnpack with a = b − 1 or a = b, written into `w` (every entry is overwritten): w[i] = b − z[i]
/// for the c-bit fields z of `v`. The secret-key decoder passes the destination polynomial itself, so a decoded
/// secret is never returned by value (a by-value result is built in the callee's frame and copied out, which leaves
/// a copy in the dead frame). `z` holds the raw bit fields of a secret coefficient vector; with the `zeroize`
/// feature it is wiped before returning.
fn unpack_signed_into(v: &[u8], b: u32, c: usize, w: &mut [u32; 256]) {
    #[cfg_attr(not(feature = "zeroize"), allow(unused_mut))]
    let mut z = bit_unpack(v, c);
    let mut i = 0;
    while i < 256 {
        w[i] = sub(b, z[i]);
        i += 1;
    }
    #[cfg(feature = "zeroize")]
    {
        use zeroize::Zeroize;
        z.zeroize();
    }
}
/// `unpack_signed_into` returning a fresh polynomial. For public inputs (the signature's z); the secret-key
/// decoders use `unpack_signed_into`.
fn unpack_signed(v: &[u8], b: u32, c: usize) -> [u32; 256] {
    let z = bit_unpack_pub(v, c);
    let mut w = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        w[i] = sub(b, z[i]);
        i += 1;
    }
    w
}

/// `bit_pack` for the public input of verify's w1Encode, where `c` is 4 (ML-DSA-65 and -87) or 6 (ML-DSA-44) and
/// every value is below `2^c` (UseHint's output is below m = 16 or 44): the same bytes, written a fixed number of values
/// at a time with constant shifts, so that no bit accumulator runs through the loop and the compiler can vectorize it.
/// Any other `c` takes the generic `bit_pack`. `out` must hold `32·c` bytes. Equal to `bit_pack` whenever all values
/// are below `2^c` (`Proofs/Encode.lean`, `bit_pack_pub_spec`). Not for secret data.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn bit_pack_pub(w: &[u32; 256], c: usize, out: &mut [u8]) {
    if c == 4 {
        // two values per byte
        let out = &mut out[..128];
        let mut g = 0;
        while g < 128 {
            out[g] = (w[2 * g] | (w[2 * g + 1] << 4)) as u8;
            g += 1;
        }
    } else if c == 6 {
        // four values per three bytes
        let out = &mut out[..192];
        let mut g = 0;
        while g < 64 {
            let w0 = w[4 * g];
            let w1 = w[4 * g + 1];
            let w2 = w[4 * g + 2];
            let w3 = w[4 * g + 3];
            out[3 * g] = (w0 | (w1 << 6)) as u8;
            out[3 * g + 1] = ((w1 >> 2) | (w2 << 4)) as u8;
            out[3 * g + 2] = ((w2 >> 4) | (w3 << 2)) as u8;
            g += 1;
        }
    } else {
        bit_pack(w, c, out)
    }
}

/// Algorithm 28 w1Encode(w1).
pub fn w1_encode<const K: usize>(p: &Params, w1: &[[u32; 256]; K], out: &mut [u8]) {
    let n = 32 * p.w1_bits;
    let mut i = 0;
    while i < K {
        bit_pack(&w1[i], p.w1_bits, &mut out[i * n..(i + 1) * n]);
        i += 1;
    }
}

/// `w1_encode` with `bit_pack_pub`, for verify: w1 is public and every entry is below `2^w1_bits`.
#[cfg_attr(all(feature = "avx2", not(miri), target_arch = "x86_64"), inline(always))]
pub fn w1_encode_pub<const K: usize>(p: &Params, w1: &[[u32; 256]; K], out: &mut [u8]) {
    let n = 32 * p.w1_bits;
    let mut i = 0;
    while i < K {
        bit_pack_pub(&w1[i], p.w1_bits, &mut out[i * n..(i + 1) * n]);
        i += 1;
    }
}

/// Algorithm 20 HintBitPack(h).
pub fn hint_bit_pack<const K: usize>(p: &Params, h: &[[bool; 256]; K], out: &mut [u8]) {
    let mut i = 0;
    while i < p.omega + K {
        out[i] = 0;
        i += 1;
    }
    let mut index = 0;
    let mut i = 0;
    while i < K {
        let mut j = 0;
        while j < 256 {
            if h[i][j] {
                out[index] = j as u8;
                index += 1;
            }
            j += 1;
        }
        out[p.omega + i] = index as u8;
        i += 1;
    }
}

/// Decoded private key (Algorithm 25 output).
pub struct SecretKey<const K: usize, const L: usize> {
    pub rho: [u8; 32],
    pub key: [u8; 32],
    pub tr: [u8; 64],
    pub s1: [[u32; 256]; L],
    pub s2: [[u32; 256]; K],
    pub t0: [[u32; 256]; K],
}

/// Algorithm 25 skDecode(sk), written into `out` (every field is overwritten, so its previous contents do not
/// matter). `prepare_sk_into` passes a local it wipes: the decoded s1, s2 and t0 are never returned by value, so no
/// copy of them is left in the dead frame of this function (they are decoded in place, `unpack_signed_into`).
pub fn sk_decode_into<const K: usize, const L: usize>(p: &Params, sk: &[u8], out: &mut SecretKey<K, L>) {
    let mut i = 0;
    while i < 32 {
        out.rho[i] = sk[i];
        out.key[i] = sk[32 + i];
        i += 1;
    }
    let mut i = 0;
    while i < 64 {
        out.tr[i] = sk[64 + i];
        i += 1;
    }
    let n = 32 * p.eta_bits;
    let mut o = 128;
    let mut i = 0;
    while i < L {
        unpack_signed_into(&sk[o..o + n], p.eta, p.eta_bits, &mut out.s1[i]);
        o += n;
        i += 1;
    }
    let mut i = 0;
    while i < K {
        unpack_signed_into(&sk[o..o + n], p.eta, p.eta_bits, &mut out.s2[i]);
        o += n;
        i += 1;
    }
    let mut i = 0;
    while i < K {
        unpack_signed_into(&sk[o..o + 416], 1 << 12, 13, &mut out.t0[i]);
        o += 416;
        i += 1;
    }
}

/// Algorithm 25 skDecode(sk), returning the decoded key by value: `sk_decode_into` on a fresh `SecretKey`. For callers
/// that do not hold the result as a secret (the tests); the library's own callers use `sk_decode_into`.
#[cfg_attr(not(feature = "internals"), allow(dead_code))]
pub fn sk_decode<const K: usize, const L: usize>(p: &Params, sk: &[u8]) -> SecretKey<K, L> {
    let mut out = SecretKey {
        rho: [0; 32],
        key: [0; 32],
        tr: [0; 64],
        s1: [[0; 256]; L],
        s2: [[0; 256]; K],
        t0: [[0; 256]; K],
    };
    sk_decode_into::<K, L>(p, sk, &mut out);
    out
}

/// Zero iff every coefficient of `w` (canonical mod q) is in [−η, η], i.e. `w ≤ η` or `w ≥ q − η`; otherwise 1.
/// Branch-free on the coefficients and free of overflow-checked arithmetic on them: each coefficient contributes the
/// bit `[w > η] & [w < q − η]`, computed as the sign bits of two wrapping differences (exact because `w`, η and q are
/// below 2³¹), and the bits are OR-ed. A `w[i] > eta && w[i] + eta < Q` test would stay a branch on the sign of every
/// coefficient of s₁ and s₂ in a build with overflow checks (its right operand can panic), see docs/assurance.md, CT-3.
fn poly_eta_bad(w: &[u32; 256], eta: u32) -> u32 {
    let lo = Q - eta;
    let mut bad = 0u32;
    let mut i = 0;
    while i < 256 {
        let x = w[i];
        bad |= (eta.wrapping_sub(x) >> 31) & (x.wrapping_sub(lo) >> 31);
        i += 1;
    }
    bad
}

/// Zero iff the η-block `v` (32·bitlen(2η) bytes) decodes, as in skDecode (BitUnpack with a = b = η), to
/// coefficients all in [−η, η]; otherwise 1.
fn eta_block_bad(p: &Params, v: &[u8]) -> u32 {
    let mut w = [0u32; 256];
    unpack_signed_into(v, p.eta, p.eta_bits, &mut w);
    let bad = poly_eta_bad(&w, p.eta);
    // `w` holds a decoded s1 or s2 polynomial of a stored secret key.
    #[cfg(feature = "zeroize")]
    {
        use zeroize::Zeroize;
        w.zeroize();
    }
    bad
}

/// True iff every coefficient of s₁ and s₂ as decoded by `sk_decode` (Algorithm 25) lies in [−η, η]. The L + K
/// η-blocks of `sk` are contiguous from byte 128. (t₀ is a 13-bit field decoded as 4096 − z for z < 2¹³, so
/// it is always in [−4095, 4096] and needs no check.) Requires `sk.len() == sk_len(p)`.
/// The blocks are OR-ed into one integer and compared with zero once, at the end: no branch depends on a coefficient.
pub fn sk_is_well_formed<const K: usize, const L: usize>(p: &Params, sk: &[u8]) -> bool {
    let n = 32 * p.eta_bits;
    let mut o = 128;
    let mut bad = 0u32;
    let mut i = 0;
    while i < L + K {
        bad |= eta_block_bad(p, &sk[o..o + n]);
        o += n;
        i += 1;
    }
    bad == 0
}

/// Algorithm 26 sigEncode(c̃, z, h).
pub fn sig_encode<const K: usize, const L: usize>(
    p: &Params,
    c_tilde: &[u8],
    z: &[[u32; 256]; L],
    h: &[[bool; 256]; K],
    out: &mut [u8],
) {
    let ct = p.c_tilde_len;
    let mut i = 0;
    while i < ct {
        out[i] = c_tilde[i];
        i += 1;
    }
    let n = 32 * p.gamma1_bits;
    let mut i = 0;
    while i < L {
        pack_signed(&z[i], p.gamma1, p.gamma1_bits, &mut out[ct + i * n..ct + (i + 1) * n]);
        i += 1;
    }
    hint_bit_pack(p, h, &mut out[ct + L * n..]);
}

/// Algorithm 22 pkEncode(ρ, t1). `out` has 32 + 320·K bytes; each t1 coefficient is < 2^10.
pub fn pk_encode<const K: usize>(rho: &[u8; 32], t1: &[[u32; 256]; K], out: &mut [u8]) {
    // 1: pk ← ρ
    let mut i = 0;
    while i < 32 {
        out[i] = rho[i];
        i += 1;
    }
    // 2–4: pk ← pk || SimpleBitPack(t1_i, 2^10 − 1)
    let mut i = 0;
    while i < K {
        bit_pack(&t1[i], 10, &mut out[32 + i * 320..32 + (i + 1) * 320]);
        i += 1;
    }
}

/// Algorithm 23 pkDecode(pk). `pk` has 32 + 320·K bytes. Total: every byte string decodes.
pub fn pk_decode<const K: usize>(pk: &[u8]) -> ([u8; 32], [[u32; 256]; K]) {
    let mut rho = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        rho[i] = pk[i];
        i += 1;
    }
    let mut t1 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        t1[i] = bit_unpack_pub(&pk[32 + i * 320..32 + (i + 1) * 320], 10);
        i += 1;
    }
    (rho, t1)
}

/// Algorithm 24 skEncode(ρ, K, tr, s1, s2, t0). `out` has sk_len bytes.
pub fn sk_encode<const K: usize, const L: usize>(
    p: &Params,
    rho: &[u8; 32],
    key: &[u8; 32],
    tr: &[u8; 64],
    s1: &[[u32; 256]; L],
    s2: &[[u32; 256]; K],
    t0: &[[u32; 256]; K],
    out: &mut [u8],
) {
    // 1: sk ← ρ || K || tr
    let mut i = 0;
    while i < 32 {
        out[i] = rho[i];
        out[32 + i] = key[i];
        i += 1;
    }
    let mut i = 0;
    while i < 64 {
        out[64 + i] = tr[i];
        i += 1;
    }
    let n = 32 * p.eta_bits;
    let mut o = 128;
    // 2–4: sk ← sk || BitPack(s1_i, η, η)
    let mut i = 0;
    while i < L {
        pack_signed(&s1[i], p.eta, p.eta_bits, &mut out[o..o + n]);
        o += n;
        i += 1;
    }
    // 5–7: sk ← sk || BitPack(s2_i, η, η)
    let mut i = 0;
    while i < K {
        pack_signed(&s2[i], p.eta, p.eta_bits, &mut out[o..o + n]);
        o += n;
        i += 1;
    }
    // 8–10: sk ← sk || BitPack(t0_i, 2^12 − 1, 2^12)
    let mut i = 0;
    while i < K {
        pack_signed(&t0[i], 1 << 12, 13, &mut out[o..o + 416]);
        o += 416;
        i += 1;
    }
}

/// Steps 7–14 of Algorithm 21 for polynomial i: sets h_i[y[Index]] for Index from `first` to `end` − 1,
/// returning false (⊥) if the positions are not strictly increasing. Requires `end` ≤ ω < y.len().
/// Lifted out of `hint_bit_unpack` because Aeneas cannot extract a return from a nested loop.
fn hint_bit_unpack_row(y: &[u8], first: usize, end: usize, row: &mut [bool; 256]) -> bool {
    // 7: First ← Index
    let mut index = first;
    // 8: while Index < y[ω + i]
    while index < end {
        // 9–11: if Index > First and y[Index − 1] ≥ y[Index] then return ⊥
        if index > first && y[index - 1] >= y[index] {
            return false;
        }
        // 12: h_i[y[Index]] ← 1; 13: Index ← Index + 1
        row[y[index] as usize] = true;
        index += 1;
    }
    true
}

/// Steps 2–15 of Algorithm 21: fills `h` and returns the final Index, or `None` (⊥).
/// Each loop that can return ⊥ lives in its own function: Aeneas cannot extract a return out of a
/// loop that is followed by further loops in the same body.
fn hint_bit_unpack_rows<const K: usize>(p: &Params, y: &[u8], h: &mut [[bool; 256]; K]) -> Option<usize> {
    let omega = p.omega;
    // 2: Index ← 0
    let mut index: usize = 0;
    // 3: for i from 0 to k − 1
    let mut i = 0;
    while i < K {
        let end = y[omega + i] as usize;
        // 4–6: if y[ω + i] < Index or y[ω + i] > ω then return ⊥
        if end < index || end > omega {
            return None;
        }
        // 7–14 (after the loop, Index = y[ω + i])
        if !hint_bit_unpack_row(y, index, end, &mut h[i]) {
            return None;
        }
        index = end;
        i += 1;
    }
    Some(index)
}

/// Steps 16–20 of Algorithm 21: true iff y[Index..ω] are all zero.
fn hint_bit_unpack_padding(p: &Params, y: &[u8], index: usize) -> bool {
    let mut j = index;
    while j < p.omega {
        if y[j] != 0 {
            return false;
        }
        j += 1;
    }
    true
}

/// Algorithm 21 HintBitUnpack(y). `y` has ω + K bytes. `None` is ⊥ (malformed encoding).
/// Safety of indexing: y[ω + i] ≤ ω is checked before use, so `index` ≤ ω and `index` < ω
/// whenever y[index] is read; y[index] < 256 indexes h[i].
pub fn hint_bit_unpack<const K: usize>(p: &Params, y: &[u8]) -> Option<[[bool; 256]; K]> {
    // 1: h ← 0^{k × 256}
    let mut h = [[false; 256]; K];
    match hint_bit_unpack_rows(p, y, &mut h) {
        None => None,
        Some(index) => {
            if hint_bit_unpack_padding(p, y, index) {
                Some(h)
            } else {
                None
            }
        }
    }
}

/// Algorithm 27 sigDecode(σ). `sig` has sig_len bytes. Returns (c̃ in the first λ/4 bytes, z, h),
/// or `None` iff HintBitUnpack returns ⊥. (No ‖z‖∞ check here; that is Verify's step.)
#[allow(clippy::type_complexity)]
pub fn sig_decode<const K: usize, const L: usize>(
    p: &Params,
    sig: &[u8],
) -> Option<([u8; 64], [[u32; 256]; L], [[bool; 256]; K])> {
    let ct = p.c_tilde_len;
    let mut c_tilde = [0u8; 64];
    let mut i = 0;
    while i < ct {
        c_tilde[i] = sig[i];
        i += 1;
    }
    let n = 32 * p.gamma1_bits;
    let mut z = [[0u32; 256]; L];
    let mut i = 0;
    while i < L {
        z[i] = unpack_signed(&sig[ct + i * n..ct + (i + 1) * n], p.gamma1, p.gamma1_bits);
        i += 1;
    }
    match hint_bit_unpack::<K>(p, &sig[ct + L * n..]) {
        Some(h) => Some((c_tilde, z, h)),
        None => None,
    }
}
