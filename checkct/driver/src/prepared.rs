//! Probes for the prepared signing key (`sign::prepare_sk`, `api::signing_key_NN`) and the whole prepared signing
//! path. The secret is the secret key: K (bytes 32..64) and the packed s1, s2, t0 (bytes 128..). The seed rho
//! (bytes 0..32) and the hash tr (bytes 64..128) are public values of a real key, so they are fixed constants here
//! (no consistency with s1, s2, t0 is needed: `prepare_sk` does not check it). That keeps ExpandA, whose rejection
//! sampler branches on the (public) seed, a concrete computation instead of a flagged branch on a "secret" input.
//! The constants go through `black_box` so the compiler cannot fold ExpandA away at build time.
use crate::rng::{PrivateRng, PublicRng};
use crate::{api, params, sign};
use checkct_macros::checkct;
use core::hint::black_box;
use params::Params;

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

/// A secret key of N bytes with public rho and tr and secret K, s1, s2, t0.
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

// `sign::prepare_sk` itself: skDecode, three NTTs, ExpandA (Algorithm 7 steps 1-5).
fn prepare_sk_fn<const K: usize, const L: usize, const N: usize>(p: &Params) -> sign::PreparedSk<K, L> {
    let sk = sk_input::<N>();
    sign::prepare_sk::<K, L>(p, &sk)
}
probe!(prepare_sk_44, prepare_sk_fn::<4, 4, 2560>(&params::ML_DSA_44));
probe!(prepare_sk_65, prepare_sk_fn::<6, 5, 4032>(&params::ML_DSA_65));
probe!(prepare_sk_87, prepare_sk_fn::<8, 7, 4896>(&params::ML_DSA_87));

// The public constructor, end to end (a wrapper around `prepare_sk`).
probe!(signing_key_44, api::signing_key_44(&sk_input::<2560>()));
probe!(signing_key_65, api::signing_key_65(&sk_input::<4032>()));
probe!(signing_key_87, api::signing_key_87(&sk_input::<4896>()));

// Census of the whole prepared signing path for ML-DSA-44, the mirror of `census_sign_internal_44`: signing_key_44
// then sign_prepared_44, with concrete message and context and a public rnd. No per-attempt probe of
// `sign_prepared_internal` exists to mirror (`attempt` is private to sign.rs; the secret halves of an attempt are
// `response_*` and `hint_step_*`, which the refactor did not touch). EXPECTED to be insecure or unfinished, for the
// same reasons as the other census: the rejection samplers and the two rejection `if`s of `attempt` branch on
// secret-derived values whose outcome is public by design. Read the list of leaking lines, not the verdict.
fn census_prepared_fn() -> Option<[u8; 2420]> {
    let sk = sk_input::<2560>();
    let ssk = api::signing_key_44(&sk);
    let mut rnd = [0u8; 32];
    PublicRng.fill_bytes(&mut rnd);
    api::sign_prepared_44(&ssk, b"census message", b"ctx", &rnd)
}
probe!(census_sign_prepared_44, census_prepared_fn());

// Positive control for the probes above: the same prepare_sk, followed by a branch on a bit of the secret ŝ1. EXPECTED
// insecure on every target. If it ever reports secure, the `prepare_sk_*` / `signing_key_*` verdicts mean nothing.
fn control_prepared_branch_fn() -> u32 {
    let sk = sk_input::<2560>();
    let ps = sign::prepare_sk::<4, 4>(&params::ML_DSA_44, &sk);
    if black_box(ps.s1_hat[0][0]) & 1 == 1 {
        black_box(1)
    } else {
        black_box(2)
    }
}
probe!(control_prepared_branch_44, control_prepared_branch_fn());

// One-polynomial splits of `prepare_sk` (K = L = 1), for the targets where the full-size probes exceed the BINSEC
// timeout (riscv32imac). The per-coefficient code is the same; only the loop counts differ. Both eta sets are covered.
probe!(prepare_sk_1x1_44, prepare_sk_fn::<1, 1, 2560>(&params::ML_DSA_44));
probe!(prepare_sk_1x1_65, prepare_sk_fn::<1, 1, 4032>(&params::ML_DSA_65));

// Second positive control: a table lookup indexed by a byte of the secret ŝ1. A secret-dependent memory access cannot be
// compiled to a conditional move, so this is EXPECTED insecure on every target, including those where the branch of
// `control_prepared_branch_44` is lowered to a select.
fn control_prepared_index_fn() -> u32 {
    let sk = sk_input::<2560>();
    let ps = sign::prepare_sk::<4, 4>(&params::ML_DSA_44, &sk);
    let idx = (black_box(ps.s1_hat[0][0]) & 255) as usize;
    black_box(ps.s2_hat[0][idx])
}
probe!(control_prepared_index_44, control_prepared_index_fn());
