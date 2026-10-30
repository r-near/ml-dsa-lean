//! Signing-stage probes, composed from the public building blocks exactly as `sign::attempt` does
//! (FIPS 204 Algorithm 7 steps 18-21, 23, 25-26, 28). `attempt` itself is private, so these are
//! re-compositions, not the production code path; see README for the recommended `response` /
//! `hint_step` split. The two rejection branches are not probed: they are accepted public-outcome
//! branches. Only the norms feeding them are.
use crate::probes::secret_vec;
use crate::rng::PublicRng;
use crate::{field, ntt, params, rounding};
use checkct_macros::checkct;
use core::hint::black_box;
use params::Params;

type Vecn<const N: usize> = [[u32; 256]; N];

/// Steps 18-21: cs1, cs2, z = y + cs1, r0 = LowBits(w - cs2), plus both norms.
fn response<const K: usize, const L: usize>(p: &Params) {
    let y: Vecn<L> = secret_vec();
    let w: Vecn<K> = secret_vec();
    let s1_hat: Vecn<L> = secret_vec();
    let s2_hat: Vecn<K> = secret_vec();
    // c is public (derived from the public challenge hash), so c_hat is public.
    let c_hat = secret_public_poly();
    let cs1 = ntt::scalar_vector_ntt_inverse::<L>(&c_hat, &s1_hat);
    let cs2 = ntt::scalar_vector_ntt_inverse::<K>(&c_hat, &s2_hat);
    let mut z = [[0u32; 256]; L];
    let mut i = 0;
    while i < L {
        let mut j = 0;
        while j < 256 {
            z[i][j] = field::add(y[i][j], cs1[i][j]);
            j += 1;
        }
        i += 1;
    }
    let mut w_cs2 = [[0u32; 256]; K];
    let mut r0 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        w_cs2[i] = ntt::sub_poly(&w[i], &cs2[i]);
        r0[i] = rounding::poly_low_bits(p, &w_cs2[i]);
        i += 1;
    }
    black_box((rounding::vec_infinity_norm(&z), rounding::vec_infinity_norm(&r0), z, w_cs2));
}

/// Steps 25-26 and the ct0 norm: ct0, h = MakeHint(-ct0, w - cs2 + ct0), hamming weight.
fn hint_step<const K: usize>(p: &Params) {
    let w_cs2: Vecn<K> = secret_vec();
    let t0_hat: Vecn<K> = secret_vec();
    let c_hat = secret_public_poly();
    let ct0 = ntt::scalar_vector_ntt_inverse::<K>(&c_hat, &t0_hat);
    let mut ones = 0usize;
    let mut hint = [[false; 256]; K];
    let mut i = 0;
    while i < K {
        let mut j = 0;
        while j < 256 {
            hint[i][j] = rounding::make_hint(p, field::neg(ct0[i][j]), field::add(w_cs2[i][j], ct0[i][j]));
            ones += hint[i][j] as usize;
            j += 1;
        }
        i += 1;
    }
    black_box((rounding::vec_infinity_norm(&ct0), ones, hint));
}

/// A public NTT-domain polynomial (c_hat).
fn secret_public_poly() -> [u32; 256] {
    let mut p = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        p[i] = PublicRng.next_u32() % field::Q;
        i += 1;
    }
    p
}

macro_rules! probe {
    ($name:ident, $body:expr) => {
        #[checkct]
        pub fn $name() {
            black_box(PublicRng.next_u32());
            $body;
        }
    };
}

probe!(response_44, response::<4, 4>(&params::ML_DSA_44));
probe!(response_65, response::<6, 5>(&params::ML_DSA_65));
probe!(response_87, response::<8, 7>(&params::ML_DSA_87));
probe!(hint_step_44, hint_step::<4>(&params::ML_DSA_44));
probe!(hint_step_65, hint_step::<6>(&params::ML_DSA_65));
probe!(hint_step_87, hint_step::<8>(&params::ML_DSA_87));
