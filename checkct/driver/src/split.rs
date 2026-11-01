//! Split probes: smaller instantiations of the same code as probes whose full-size version gives BINSEC no verdict
//! (one path stuck in one solver query). Each probe here calls the same functions as the probe it splits, with
//! smaller const-generic loop bounds (K, L) and nothing else changed, so every loop body, every table and every
//! inlined helper is shared; `checkct/README.md` ("Split probes") has the coverage argument per split. Names start with
//! `split_`, so `ONLY=split_` selects them all. Every input is secret as in the probe it splits, except what the
//! comments of that probe say is public (A-hat, rho, tr).
use crate::probes::secret_vec;
use crate::rng::{PrivateRng, PublicRng};
use crate::{ntt, params, rounding, sign};
use checkct_macros::checkct;
use core::hint::black_box;
use params::Params;

type Vecn<const N: usize> = [[u32; 256]; N];

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

// ---------------------------------------------------------------------------------------------
// compute_t (extra.rs `compute_t_44`): t = NTT^-1(A-hat o NTT(s1)) + s2, A-hat public, s1 and s2 secret.
// The body is the one of extra.rs `compute_t`, copied (that function is private to its module).
// ---------------------------------------------------------------------------------------------
fn public_poly() -> [u32; 256] {
    let mut p = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        p[i] = PublicRng.next_u32() % crate::field::Q;
        i += 1;
    }
    p
}

fn public_matrix<const K: usize, const L: usize>() -> [[[u32; 256]; L]; K] {
    let mut a = [[[0u32; 256]; L]; K];
    let mut r = 0;
    while r < K {
        let mut s = 0;
        while s < L {
            a[r][s] = public_poly();
            s += 1;
        }
        r += 1;
    }
    a
}

fn compute_t<const K: usize, const L: usize>() -> Vecn<K> {
    let a_hat = public_matrix::<K, L>();
    let s1: Vecn<L> = secret_vec();
    let s2: Vecn<K> = secret_vec();
    let prod = ntt::matrix_vector_ntt::<K, L>(&a_hat, &ntt::ntt_vec::<L>(&s1));
    let mut t = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        t[i] = ntt::add_poly(&ntt::ntt_inverse(&prod[i]), &s2[i]);
        i += 1;
    }
    t
}
// One row of the ML-DSA-44 product (K = 1, L = 4): NTT of all four s1 polynomials, the four-term accumulation
// of a row of A-hat o s1-hat, one inverse NTT, one add of s2.
probe!(split_compute_t_44_row, compute_t::<1, 4>());
// All four rows of the product against one column (K = 4, L = 1): the four row iterations with a one-term accumulation.
probe!(split_compute_t_44_col, compute_t::<4, 1>());
// Two rows by two columns (K = 2, L = 2): the smallest shape with both loops iterating more than once.
probe!(split_compute_t_44_2x2, compute_t::<2, 2>());

// ---------------------------------------------------------------------------------------------
// vec_power2round (extra.rs `vec_power2round_87`), K = 8 entries. The body is the one of extra.rs, copied.
// ---------------------------------------------------------------------------------------------
fn vec_power2round<const K: usize>() -> (Vecn<K>, Vecn<K>) {
    let t: Vecn<K> = secret_vec();
    let mut t1 = [[0u32; 256]; K];
    let mut t0 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        let (a, b) = rounding::poly_power2round(&t[i]);
        t1[i] = a;
        t0[i] = b;
        i += 1;
    }
    (t1, t0)
}
probe!(split_vec_power2round_1, vec_power2round::<1>());
probe!(split_vec_power2round_2, vec_power2round::<2>());
probe!(split_vec_power2round_6, vec_power2round::<6>());
probe!(split_vec_power2round_7, vec_power2round::<7>());

// ---------------------------------------------------------------------------------------------
// prepare_sk (prepared.rs `prepare_sk_{44,65,87}`, and `signing_key_*`, which is `sign::prepare_sk_into` plus a
// move of the key object). Same input as prepared.rs `sk_input`: rho (0..32) and tr (64..128) public constants,
// K (32..64) and s1, s2, t0 (128..) secret; the buffer has the full length N of the parameter set, `prepare_sk`
// reads its prefix. `row` is K = 1 with the full L (skDecode of all of s1, the whole in-place NTT of s1), `col` is
// the full K with L = 1 (all of s2 and t0).
// ---------------------------------------------------------------------------------------------
fn sk_input<const N: usize>() -> [u8; N] {
    let mut sk = [0u8; N];
    let mut i = 0;
    while i < 32 {
        sk[i] = black_box(0x42u8 ^ (i as u8)); // rho
        i += 1;
    }
    PrivateRng.fill_bytes(&mut sk[32..64]); // K
    let mut i = 64;
    while i < 128 {
        sk[i] = black_box(0x9du8 ^ (i as u8)); // tr
        i += 1;
    }
    PrivateRng.fill_bytes(&mut sk[128..]); // s1, s2, t0
    sk
}

fn prepare_sk_fn<const K: usize, const L: usize, const N: usize>(p: &Params) -> sign::PreparedSk<K, L> {
    let sk = sk_input::<N>();
    sign::prepare_sk::<K, L>(p, &sk)
}
probe!(split_prepare_sk_44_row, prepare_sk_fn::<1, 4, 2560>(&params::ML_DSA_44));
probe!(split_prepare_sk_44_col, prepare_sk_fn::<4, 1, 2560>(&params::ML_DSA_44));
probe!(split_prepare_sk_65_row, prepare_sk_fn::<1, 5, 4032>(&params::ML_DSA_65));
probe!(split_prepare_sk_65_col, prepare_sk_fn::<6, 1, 4032>(&params::ML_DSA_65));
probe!(split_prepare_sk_87_row, prepare_sk_fn::<1, 7, 4896>(&params::ML_DSA_87));
probe!(split_prepare_sk_87_col, prepare_sk_fn::<8, 1, 4896>(&params::ML_DSA_87));

// Smaller column shapes of ML-DSA-87 (K = 8, L = 1 gave AArch64 no verdict): K = 2, 4, 6 and 7 rows against one
// column, same function, same parameter set, only the loop bound K differs.
probe!(split_prepare_sk_87_2x1, prepare_sk_fn::<2, 1, 4896>(&params::ML_DSA_87));
probe!(split_prepare_sk_87_4x1, prepare_sk_fn::<4, 1, 4896>(&params::ML_DSA_87));
probe!(split_prepare_sk_87_6x1, prepare_sk_fn::<6, 1, 4896>(&params::ML_DSA_87));
probe!(split_prepare_sk_87_7x1, prepare_sk_fn::<7, 1, 4896>(&params::ML_DSA_87));

// The stages of `sign::prepare_sk_into` on their own, for the shapes whose whole is out of reach: the in-place NTT
// of a secret vector of K = 8 polynomials into a key field (`ntt::ntt_vec_into`, called for s2 and t0 with N = K), and
// its L = 1 instance (s1). skDecode alone is the existing `sk_decode_87`; ExpandA runs on the public rho.
probe!(split_ntt_vec_into_8, {
    let v: Vecn<8> = secret_vec();
    let mut out = [[0u32; 256]; 8];
    ntt::ntt_vec_into::<8>(&v, &mut out);
    out
});
probe!(split_ntt_vec_into_7, {
    let v: Vecn<7> = secret_vec();
    let mut out = [[0u32; 256]; 7];
    ntt::ntt_vec_into::<7>(&v, &mut out);
    out
});
probe!(split_ntt_vec_into_1, {
    let v: Vecn<1> = secret_vec();
    let mut out = [[0u32; 256]; 1];
    ntt::ntt_vec_into::<1>(&v, &mut out);
    out
});

// Windows of the K = 8 loop of `vec_power2round_87`: the same loop over the same eight secret polynomials, run for
// i in LO..HI only. The windows of a partition (halves, or pairs) together run every iteration of the full loop.
fn vec_power2round_window<const LO: usize, const HI: usize>() -> (Vecn<8>, Vecn<8>) {
    let t: Vecn<8> = secret_vec();
    let mut t1 = [[0u32; 256]; 8];
    let mut t0 = [[0u32; 256]; 8];
    let mut i = LO;
    while i < HI {
        let (a, b) = rounding::poly_power2round(&t[i]);
        t1[i] = a;
        t0[i] = b;
        i += 1;
    }
    (t1, t0)
}
probe!(split_vec_power2round_8_lo, vec_power2round_window::<0, 4>());
probe!(split_vec_power2round_8_hi, vec_power2round_window::<4, 8>());
probe!(split_vec_power2round_8_q0, vec_power2round_window::<0, 2>());
probe!(split_vec_power2round_8_q1, vec_power2round_window::<2, 4>());
probe!(split_vec_power2round_8_q2, vec_power2round_window::<4, 6>());
probe!(split_vec_power2round_8_q3, vec_power2round_window::<6, 8>());
probe!(split_vec_power2round_3, vec_power2round::<3>());
probe!(split_vec_power2round_4, vec_power2round::<4>());
probe!(split_vec_power2round_5, vec_power2round::<5>());
