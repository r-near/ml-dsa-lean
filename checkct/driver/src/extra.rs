//! Probes for the secret-data paths that `probes.rs` and `signing.rs` do not reach: the optional key check
//! `sk_is_well_formed`, the secret-seeded SHAKE calls of KeyGen and Sign, ExpandMask, the KeyGen pieces
//! (`t = NTT^-1(A * NTT(s1)) + s2`, Power2Round over a vector, the ExpandS sampler), and the matrix-vector
//! product of Sign. Every input is secret unless the comment says it is public (A, c-hat, nonces, mu).
use crate::probes::{secret_poly, secret_vec};
use crate::rng::{PrivateRng, PublicRng};
use crate::{api, encode, field, keccak, ntt, params, rounding, sampling};
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

fn secret_bytes<const N: usize>() -> [u8; N] {
    let mut b = [0u8; N];
    PrivateRng.fill_bytes(&mut b);
    b
}

/// A public NTT-domain polynomial (a coefficient of A-hat or c-hat).
fn public_poly() -> [u32; 256] {
    let mut p = [0u32; 256];
    let mut i = 0;
    while i < 256 {
        p[i] = PublicRng.next_u32() % field::Q;
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

// ---------------------------------------------------------------------------------------------
// sk_is_well_formed: the secret key is the input. Entered through the public API function and through
// the encode function it wraps (the latter takes a slice and a Params value).
// ---------------------------------------------------------------------------------------------
probe!(sk_is_well_formed_44, api::sk_is_well_formed_44(&secret_bytes::<2560>()));
probe!(sk_is_well_formed_65, api::sk_is_well_formed_65(&secret_bytes::<4032>()));
probe!(sk_is_well_formed_87, api::sk_is_well_formed_87(&secret_bytes::<4896>()));

fn sk_wf_encode<const K: usize, const L: usize>(p: &Params) -> bool {
    let sk = secret_bytes::<4896>();
    encode::sk_is_well_formed::<K, L>(p, &sk[..params::sk_len(p)])
}
probe!(encode_sk_is_well_formed_44, sk_wf_encode::<4, 4>(&params::ML_DSA_44));
probe!(encode_sk_is_well_formed_65, sk_wf_encode::<6, 5>(&params::ML_DSA_65));
probe!(encode_sk_is_well_formed_87, sk_wf_encode::<8, 7>(&params::ML_DSA_87));

// ---------------------------------------------------------------------------------------------
// SHAKE with secret absorb data. keccak_f1600 alone is probed in probes.rs.
// ---------------------------------------------------------------------------------------------

/// KeyGen step 1: (rho, rho', K) = H(xi || k || l, 128), xi secret.
fn keygen_seed_hash_fn() -> [u8; 128] {
    let xi = secret_bytes::<32>();
    let kl = [8u8, 7u8];
    let mut h = keccak::Shake::shake256();
    h.absorb(&xi);
    h.absorb(&kl);
    h.finalize();
    let mut out = [0u8; 128];
    h.squeeze(&mut out);
    out
}
probe!(keygen_seed_hash, keygen_seed_hash_fn());

/// Sign step 7: rho'' = H(K || rnd || mu, 64), K and rnd secret, mu public.
fn sign_rho_pp_hash_fn() -> [u8; 64] {
    let key = secret_bytes::<32>();
    let rnd = secret_bytes::<32>();
    let mut mu = [0u8; 64];
    PublicRng.fill_bytes(&mut mu);
    let mut h = keccak::Shake::shake256();
    h.absorb(&key);
    h.absorb(&rnd);
    h.absorb(&mu);
    h.finalize();
    let mut out = [0u8; 64];
    h.squeeze(&mut out);
    out
}
probe!(sign_rho_pp_hash, sign_rho_pp_hash_fn());

// ---------------------------------------------------------------------------------------------
// Sign step 11: y = ExpandMask(rho'', kappa), rho'' secret, kappa public.
// ---------------------------------------------------------------------------------------------
fn expand_mask<const L: usize>(p: &Params) -> Vecn<L> {
    let rho = secret_bytes::<64>();
    let kappa = (PublicRng.next_u32() as u16) >> 1;
    sampling::expand_mask::<L>(p, &rho, kappa)
}
probe!(expand_mask_44, expand_mask::<4>(&params::ML_DSA_44));
probe!(expand_mask_65, expand_mask::<5>(&params::ML_DSA_65));
probe!(expand_mask_87, expand_mask::<7>(&params::ML_DSA_87));

// ---------------------------------------------------------------------------------------------
// KeyGen
// ---------------------------------------------------------------------------------------------

// ExpandS. The accepted-value path: a half-byte already known to be below the rejection bound, so the
// compiler drops the `None` arm and what remains is the computation of the coefficient from a secret.
probe!(coeff_from_half_byte_eta2, sampling::coeff_from_half_byte(&params::ML_DSA_44, (secret_bytes::<1>()[0]) % 15));
probe!(coeff_from_half_byte_eta4, sampling::coeff_from_half_byte(&params::ML_DSA_65, (secret_bytes::<1>()[0]) % 9));
// The full sampler on a secret seed. Expected insecure: it branches on whether each secret half-byte is
// rejected (the standard rejection-sampling leak; the rejected values are discarded, so what leaks is
// independent of the accepted coefficients). Included to show that these branches are the only leaks.
probe!(rej_bounded_poly_eta2, sampling::rej_bounded_poly(&params::ML_DSA_44, &secret_bytes::<66>()));
probe!(rej_bounded_poly_eta4, sampling::rej_bounded_poly(&params::ML_DSA_65, &secret_bytes::<66>()));

/// Step 5 of Algorithm 6, `keygen::compute_t` (private there): t = NTT^-1(A-hat o NTT(s1)) + s2.
/// A-hat is public (derived from the public rho); s1 and s2 are secret.
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
probe!(compute_t_1x1, compute_t::<1, 1>());
probe!(compute_t_44, compute_t::<4, 4>());
probe!(compute_t_65, compute_t::<6, 5>());
probe!(compute_t_87, compute_t::<8, 7>());

/// Step 6, `keygen::vec_power2round` (private there): Power2Round on every entry of a secret t.
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
probe!(poly_power2round, rounding::poly_power2round(&secret_poly()));
probe!(vec_power2round_44, vec_power2round::<4>());
probe!(vec_power2round_87, vec_power2round::<8>());

// ---------------------------------------------------------------------------------------------
// Sign: matrix-vector product A-hat o NTT(y) (step 12), A-hat public, y secret.
// ---------------------------------------------------------------------------------------------
fn matrix_vector<const K: usize, const L: usize>() -> Vecn<K> {
    let a_hat = public_matrix::<K, L>();
    let y: Vecn<L> = secret_vec();
    ntt::matrix_vector_ntt::<K, L>(&a_hat, &y)
}
probe!(matrix_vector_ntt_1x1, matrix_vector::<1, 1>());
probe!(matrix_vector_ntt_44, matrix_vector::<4, 4>());
probe!(matrix_vector_ntt_65, matrix_vector::<6, 5>());
probe!(matrix_vector_ntt_87, matrix_vector::<8, 7>());
probe!(ntt_vec_44, ntt::ntt_vec::<4>(&secret_vec()));

// Smallest pieces of the signing steps (c-hat public): <<c s>> = NTT^-1(c-hat o s-hat) for one polynomial.
probe!(scalar_vector_ntt_inverse_1, ntt::scalar_vector_ntt_inverse::<1>(&public_poly(), &secret_vec::<1>()));

// ---------------------------------------------------------------------------------------------
// Census probe: the whole production Sign_internal for ML-DSA-44. The key is a real one (generated with a fixed
// seed, so rho and tr are concrete public values; this keeps ExpandA and the rest of the public computation from
// forking BINSEC), with K, s1, s2 and t0 replaced by secret bytes, a secret rnd and a concrete message. It is
// EXPECTED to be insecure: SampleInBall's rejection loop, the two rejection `if`s of `attempt` and
// HintBitPack's `if h[i][j]` branch on secret-derived values whose outcome is public by design. The point is the list
// of leaking source lines, mapped with checkct/leaks.sh: a leak anywhere else would be a real finding. BINSEC
// explores both sides of every such branch, so this ends `unknown` or `insecure` at the timeout; read the leak list.
// ---------------------------------------------------------------------------------------------
fn census_sign_fn() -> Option<[u8; 2420]> {
    let (_pk, mut sk) = api::keygen_44(&[0x42u8; 32]);
    PrivateRng.fill_bytes(&mut sk[32..64]); // K
    PrivateRng.fill_bytes(&mut sk[128..]); // s1, s2, t0
    let rnd = secret_bytes::<32>();
    api::sign_internal_44(&sk, b"census message", &rnd)
}
probe!(census_sign_internal_44, census_sign_fn());

// ---------------------------------------------------------------------------------------------
// Positive control for the sk_is_well_formed probes. The same range check as `encode::sk_is_well_formed` for
// ML-DSA-44 (eta = 2), but returning at the first out-of-range coefficient, so the compiler cannot make it
// branch-free. EXPECTED insecure on every target; if it ever reports secure, the sk_is_well_formed verdicts mean nothing.
// ---------------------------------------------------------------------------------------------
fn control_early_exit_fn() -> bool {
    let sk = secret_bytes::<2560>();
    let mut o = 128;
    let mut b = 0;
    while b < 8 {
        // 96 = 32 * bitlen(2 * eta); a coefficient is z = eta - w, in range iff z <= 2 * eta = 4
        let z = encode::bit_unpack(&sk[o..o + 96], 3);
        let mut i = 0;
        while i < 256 {
            // black_box keeps the loop from being turned into a vector reduction (which BINSEC cannot follow)
            if black_box(z[i]) > 4 {
                return false;
            }
            i += 1;
        }
        o += 96;
        b += 1;
    }
    true
}
probe!(control_early_exit_44, control_early_exit_fn());
