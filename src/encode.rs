//! FIPS 204 §7.1–7.2: SimpleBitPack/BitPack/BitUnpack (Alg 16–19), HintBitPack (Alg 20),
//! skDecode (Alg 25), sigEncode (Alg 26), w1Encode (Alg 28). Bit order is little-endian.

use crate::field::sub;
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
fn unpack_signed(v: &[u8], b: u32, c: usize) -> [u32; 256] {
    let z = bit_unpack(v, c);
    let mut w = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        w[i] = sub(b, z[i]);
        i += 1;
    }
    w
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

/// Algorithm 25 skDecode(sk).
pub fn sk_decode<const K: usize, const L: usize>(p: &Params, sk: &[u8]) -> SecretKey<K, L> {
    let mut out = SecretKey {
        rho: [0; 32],
        key: [0; 32],
        tr: [0; 64],
        s1: [[0; 256]; L],
        s2: [[0; 256]; K],
        t0: [[0; 256]; K],
    };
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
        out.s1[i] = unpack_signed(&sk[o..o + n], p.eta, p.eta_bits);
        o += n;
        i += 1;
    }
    let mut i = 0;
    while i < K {
        out.s2[i] = unpack_signed(&sk[o..o + n], p.eta, p.eta_bits);
        o += n;
        i += 1;
    }
    let mut i = 0;
    while i < K {
        out.t0[i] = unpack_signed(&sk[o..o + 416], 1 << 12, 13);
        o += 416;
        i += 1;
    }
    out
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
