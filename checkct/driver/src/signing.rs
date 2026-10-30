//! Signing-stage probes. They call the production `sign::response` (FIPS 204 Algorithm 7 steps 18-21)
//! and `sign::hint_step` (steps 25-26) directly; the norms that feed the rejection branches (steps 23 and
//! 28) are computed here on the returned vectors with the production `vec_infinity_norm`. The two
//! rejection branches themselves are not probed: they are accepted public-outcome branches.
use crate::probes::secret_vec;
use crate::rng::PublicRng;
use crate::{field, params, rounding, sign};
use checkct_macros::checkct;
use core::hint::black_box;
use params::Params;

type Vecn<const N: usize> = [[u32; 256]; N];

/// Steps 18-21 plus both norms.
fn response<const K: usize, const L: usize>(p: &Params) {
    let y: Vecn<L> = secret_vec();
    let w: Vecn<K> = secret_vec();
    let s1_hat: Vecn<L> = secret_vec();
    let s2_hat: Vecn<K> = secret_vec();
    // c is public (derived from the public challenge hash), so c_hat is public.
    let c_hat = secret_public_poly();
    let (z, w_cs2, r0) = sign::response::<K, L>(p, &y, &c_hat, &s1_hat, &s2_hat, &w);
    black_box((rounding::vec_infinity_norm(&z), rounding::vec_infinity_norm(&r0), z, w_cs2));
}

/// Steps 25-26 plus the ct0 norm.
fn hint_step<const K: usize>(p: &Params) {
    let w_cs2: Vecn<K> = secret_vec();
    let t0_hat: Vecn<K> = secret_vec();
    let c_hat = secret_public_poly();
    let (hint, ct0, ones) = sign::hint_step::<K>(p, &c_hat, &t0_hat, &w_cs2);
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

// Split probes for the riscv32imac signing steps whose full-size versions exceed the BINSEC timeout.
// K = L = 1: the per-coefficient code is identical, only the loop counts differ (the generics are
// parameterized by const K and L). Both gamma2 sets are covered (44: (q-1)/88, 65/87: (q-1)/32).
probe!(response_1x1_44, response::<1, 1>(&params::ML_DSA_44));
probe!(response_1x1_65, response::<1, 1>(&params::ML_DSA_65));
probe!(hint_step_1_44, hint_step::<1>(&params::ML_DSA_44));
probe!(hint_step_1_65, hint_step::<1>(&params::ML_DSA_65));
