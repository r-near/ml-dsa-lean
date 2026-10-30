//! Leaf probes: field/mask primitives, rounding, NTT, Keccak-f, encoders. Every input is secret.
use crate::rng::{PrivateRng, PublicRng};
use crate::{encode, field, keccak, ntt, params, rounding};
use checkct_macros::checkct;
use core::hint::black_box;
use params::Params;

// All canonical field elements are reachable. Reduce with the mask primitives (a secret-dependent
// guard would itself fail the analysis).
pub(crate) fn secret_elem() -> u32 {
    let x = PrivateRng.next_u32() & 0x7f_ffff;
    field::ct_select(x, x - field::Q, !(field::ct_lt_mask(x as u64, field::Q as u64) as u32))
}

pub(crate) fn secret_poly() -> [u32; 256] {
    let mut p = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        p[i] = secret_elem();
        i += 1;
    }
    p
}

pub(crate) fn secret_vec<const N: usize>() -> [[u32; 256]; N] {
    let mut v = [[0u32; 256]; N];
    let mut i = 0;
    while i < N {
        v[i] = secret_poly();
        i += 1;
    }
    v
}

pub(crate) fn secret_mask() -> u32 {
    0u32.wrapping_sub(PrivateRng.next_u32() & 1)
}

macro_rules! probe {
    ($name:ident, $body:expr) => {
        #[checkct]
        pub fn $name() {
            // Generated BINSEC scripts reference both RNG hooks.
            black_box(PublicRng.next_u32());
            black_box($body);
        }
    };
}

// field / mask primitives
probe!(field_small_reduce, field::small_reduce(secret_elem() + secret_elem()));
probe!(barrett_reduce, field::barrett_reduce((secret_elem() as u64) * (secret_elem() as u64)));
probe!(field_add, field::add(secret_elem(), secret_elem()));
probe!(field_sub, field::sub(secret_elem(), secret_elem()));
probe!(field_neg, field::neg(secret_elem()));
probe!(field_mul, field::mul(secret_elem(), secret_elem()));
probe!(ct_lt_mask, field::ct_lt_mask(PrivateRng.next_u64() >> 1, PrivateRng.next_u64() >> 1));
probe!(ct_select, field::ct_select(PrivateRng.next_u32(), PrivateRng.next_u32(), secret_mask()));

// rounding
probe!(power2round, rounding::power2round(secret_elem()));
probe!(decompose_44, rounding::decompose(&params::ML_DSA_44, secret_elem()));
probe!(decompose_65_87, rounding::decompose(&params::ML_DSA_65, secret_elem()));
probe!(high_bits_44, rounding::high_bits(&params::ML_DSA_44, secret_elem()));
probe!(high_bits_65_87, rounding::high_bits(&params::ML_DSA_65, secret_elem()));
probe!(low_bits_44, rounding::low_bits(&params::ML_DSA_44, secret_elem()));
probe!(low_bits_65_87, rounding::low_bits(&params::ML_DSA_65, secret_elem()));
probe!(make_hint_44, rounding::make_hint(&params::ML_DSA_44, secret_elem(), secret_elem()));
probe!(make_hint_65_87, rounding::make_hint(&params::ML_DSA_65, secret_elem(), secret_elem()));
probe!(infinity_norm, rounding::infinity_norm(secret_elem()));
probe!(vec_infinity_norm, rounding::vec_infinity_norm::<4>(&secret_vec::<4>()));

// NTT
probe!(ntt, ntt::ntt(&secret_poly()));
probe!(ntt_inverse, ntt::ntt_inverse(&secret_poly()));
probe!(multiply_ntt, ntt::multiply_ntt(&secret_poly(), &secret_poly()));

// Keccak-f[1600] with a secret state
probe!(keccak_f1600, {
    let mut a = [0u64; 25];
    let mut i = 0;
    while i < 25 {
        a[i] = PrivateRng.next_u64();
        i += 1;
    }
    keccak::keccak_f1600(&mut a);
    a
});

// encoders. bit_pack requires each value < 2^c, so mask to c bits (a public operation on secret data).
fn packed<const C: usize>() -> [u8; 32 * 20] {
    let mut w = secret_poly();
    let mut i = 0;
    while i < 256 {
        w[i] &= (1u32 << C) - 1;
        i += 1;
    }
    let mut out = [0u8; 32 * 20];
    encode::bit_pack(&w, C, &mut out[..32 * C]);
    out
}
probe!(bit_pack_3, packed::<3>());
probe!(bit_pack_4, packed::<4>());
probe!(bit_pack_13, packed::<13>());
probe!(bit_pack_18, packed::<18>());
probe!(bit_pack_20, packed::<20>());

fn sk_enc<const K: usize, const L: usize>(p: &Params) -> [u8; 4896] {
    let mut rho = [0u8; 32];
    let mut key = [0u8; 32];
    let mut tr = [0u8; 64];
    PublicRng.fill_bytes(&mut rho);
    PrivateRng.fill_bytes(&mut key);
    PublicRng.fill_bytes(&mut tr);
    let (s1, s2, t0) = (secret_vec::<L>(), secret_vec::<K>(), secret_vec::<K>());
    let mut out = [0u8; 4896];
    encode::sk_encode::<K, L>(p, &rho, &key, &tr, &s1, &s2, &t0, &mut out[..params::sk_len(p)]);
    out
}
probe!(sk_encode_44, sk_enc::<4, 4>(&params::ML_DSA_44));
probe!(sk_encode_65, sk_enc::<6, 5>(&params::ML_DSA_65));
probe!(sk_encode_87, sk_enc::<8, 7>(&params::ML_DSA_87));

fn sk_dec<const K: usize, const L: usize>(p: &Params) -> encode::SecretKey<K, L> {
    let mut sk = [0u8; 4896];
    PrivateRng.fill_bytes(&mut sk[..params::sk_len(p)]);
    encode::sk_decode::<K, L>(p, &sk[..params::sk_len(p)])
}
probe!(sk_decode_44, sk_dec::<4, 4>(&params::ML_DSA_44));
probe!(sk_decode_65, sk_dec::<6, 5>(&params::ML_DSA_65));
probe!(sk_decode_87, sk_dec::<8, 7>(&params::ML_DSA_87));
