//! The 4-way ExpandA and the 4-way verify body (`sampling::rej_ntt_poly_x4`, `expand_a_into_x4`, `expand_a_x4`,
//! `verify::prepare_vk_x4`, `verify::verify_internal_x4`) against the scalar functions they must equal.
//!
//! * `Shim4` (portable, the instantiation proved equal to the scalar code in `lean/Proofs/Sample4.lean` and
//!   `lean/Proofs/FastVerify.lean`): always run.
//! * `Avx2` (feature `avx2`, x86_64, CPU with AVX2): the same checks with the intrinsic instantiation, run from a
//!   `#[target_feature(enable = "avx2")]` wrapper like the shipped fast path.
//!
//! Coverage per parameter set (K·L = 16, 30, 56 entries; ML-DSA-65's 30 is a multiple of 4 plus 2, so its last group
//! has two real and two repeated entries; ML-DSA-44 and -87 have no padded lanes):
//! * `rej_ntt_poly_x4` on four distinct random (s, r) pairs and on repeated pairs, each lane against `rej_ntt_poly`;
//! * `expand_a_x4` / `expand_a_into_x4` (on a garbage matrix) against `expand_a` for random and edge-case ρ;
//! * `verify_internal_x4` and `verify_prepared_internal` over `prepare_vk_x4` against `verify_internal` on valid
//!   signatures, bit-flipped signatures, wrong messages, wrong public keys, random signatures and wrong lengths.
use ml_dsa_lean::keccak4::{Lanes4, Shim4};
use ml_dsa_lean::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use ml_dsa_lean::sampling::{expand_a, expand_a_into_x4, expand_a_x4, rej_ntt_poly, rej_ntt_poly_x4};
use ml_dsa_lean::verify::{PreparedVk, prepare_vk_x4, verify_internal, verify_internal_x4, verify_prepared_internal};

const SCALE: usize = if cfg!(debug_assertions) { 4 } else { 1 };

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn arr32(&mut self) -> [u8; 32] {
        let mut a = [0u8; 32];
        for b in a.iter_mut() {
            *b = self.next() as u8;
        }
        a
    }
}

/// The instantiation under test, as run code: `Shim4` directly, `Avx2` through a `target_feature` wrapper.
trait Backend {
    const NAME: &'static str;
    fn available() -> bool;
    fn rej4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4];
    fn expand<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K];
    fn expand_into<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]);
    fn prepare<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L>;
    fn verify<const K: usize, const L: usize>(p: &Params, pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8]) -> bool;
}

struct ShimB;
impl Backend for ShimB {
    const NAME: &'static str = "Shim4";
    fn available() -> bool {
        true
    }
    fn rej4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
        rej_ntt_poly_x4::<Shim4>(rho, s, r)
    }
    fn expand<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
        expand_a_x4::<Shim4, K, L>(rho)
    }
    fn expand_into<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
        expand_a_into_x4::<Shim4, K, L>(rho, a)
    }
    fn prepare<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
        prepare_vk_x4::<Shim4, K, L>(pk)
    }
    fn verify<const K: usize, const L: usize>(p: &Params, pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8]) -> bool {
        verify_internal_x4::<Shim4, K, L>(p, pk, pre, m, sig)
    }
}

#[cfg(all(feature = "avx2", target_arch = "x86_64", not(miri)))]
mod avx2_backend {
    use super::*;
    use ml_dsa_lean::keccak4::avx2::Avx2;

    #[target_feature(enable = "avx2")]
    fn rej4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
        rej_ntt_poly_x4::<Avx2>(rho, s, r)
    }
    #[target_feature(enable = "avx2")]
    fn expand<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
        expand_a_x4::<Avx2, K, L>(rho)
    }
    #[target_feature(enable = "avx2")]
    fn expand_into<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
        expand_a_into_x4::<Avx2, K, L>(rho, a)
    }
    #[target_feature(enable = "avx2")]
    fn prepare<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
        prepare_vk_x4::<Avx2, K, L>(pk)
    }
    #[target_feature(enable = "avx2")]
    fn verify<const K: usize, const L: usize>(p: &Params, pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8]) -> bool {
        verify_internal_x4::<Avx2, K, L>(p, pk, pre, m, sig)
    }

    pub struct Avx2B;
    impl Backend for Avx2B {
        const NAME: &'static str = "Avx2";
        fn available() -> bool {
            std::arch::is_x86_feature_detected!("avx2")
        }
        // SAFETY (all methods): `available()` is checked by every test before it runs.
        fn rej4(rho: &[u8; 32], s: [u8; 4], r: [u8; 4]) -> [[u32; 256]; 4] {
            unsafe { rej4(rho, s, r) }
        }
        fn expand<const K: usize, const L: usize>(rho: &[u8; 32]) -> [[[u32; 256]; L]; K] {
            unsafe { expand::<K, L>(rho) }
        }
        fn expand_into<const K: usize, const L: usize>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
            unsafe { expand_into::<K, L>(rho, a) }
        }
        fn prepare<const K: usize, const L: usize>(pk: &[u8]) -> PreparedVk<K, L> {
            unsafe { prepare::<K, L>(pk) }
        }
        fn verify<const K: usize, const L: usize>(p: &Params, pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8]) -> bool {
            unsafe { verify::<K, L>(p, pk, pre, m, sig) }
        }
    }
}

/// `rej_ntt_poly_x4` lane by lane against `rej_ntt_poly`.
fn check_rej4<B: Backend>() {
    if !B::available() {
        eprintln!("{}: not available on this CPU, skipped", B::NAME);
        return;
    }
    let mut rng = Rng(0x7265_6a34_7834_0001);
    let mut cases = 0;
    for it in 0..(60 / SCALE) {
        let rho = if it == 0 { [0u8; 32] } else if it == 1 { [0xffu8; 32] } else { rng.arr32() };
        // Four distinct pairs, then the same pair in all lanes, then pairs with a repeated last entry.
        let mut sets: Vec<([u8; 4], [u8; 4])> = Vec::new();
        sets.push((
            [rng.next() as u8, rng.next() as u8, rng.next() as u8, rng.next() as u8],
            [rng.next() as u8, rng.next() as u8, rng.next() as u8, rng.next() as u8],
        ));
        let (s0, r0) = (rng.next() as u8, rng.next() as u8);
        sets.push(([s0; 4], [r0; 4]));
        sets.push(([0, 1, 2, 2], [0, 0, 0, 0]));
        sets.push(([255, 0, 255, 0], [255, 255, 0, 0]));
        for (s, r) in sets {
            let out = B::rej4(&rho, s, r);
            for i in 0..4 {
                let mut seed = [0u8; 34];
                seed[..32].copy_from_slice(&rho);
                seed[32] = s[i];
                seed[33] = r[i];
                assert_eq!(out[i], rej_ntt_poly(&seed), "{}: rho {rho:?} lane {i} s {} r {}", B::NAME, s[i], r[i]);
            }
            cases += 1;
        }
    }
    eprintln!("{}: rej_ntt_poly_x4: {cases} groups of four, 0 mismatches", B::NAME);
}

/// `expand_a_x4` and `expand_a_into_x4` (on a garbage matrix: every entry must be overwritten) against `expand_a`.
fn check_expand<B: Backend, const K: usize, const L: usize>() {
    if !B::available() {
        return;
    }
    let mut rng = Rng(0x6578_7034_0000_0000 ^ (K * 16 + L) as u64);
    let mut n = 0;
    for it in 0..(40 / SCALE) {
        let rho = if it == 0 { [0u8; 32] } else if it == 1 { [0xa5u8; 32] } else { rng.arr32() };
        let want = expand_a::<K, L>(&rho);
        assert!(B::expand::<K, L>(&rho) == want, "{}: expand_a_x4 K={K} L={L} rho {rho:?}", B::NAME);
        let mut a = [[[0xdead_beefu32; 256]; L]; K];
        B::expand_into::<K, L>(&rho, &mut a);
        assert!(a == want, "{}: expand_a_into_x4 K={K} L={L} rho {rho:?}", B::NAME);
        n += 1;
    }
    eprintln!("{}: expand_a K={K} L={L}: {n} seeds, 0 mismatches", B::NAME);
}

/// Valid and invalid verifications: the 4-way body, and the prepared key built by the 4-way constructor, must give the
/// scalar verdict on every input.
fn check_verify<B: Backend, const K: usize, const L: usize>(
    p: &Params,
    keygen: impl Fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    sign: impl Fn(&[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>,
) {
    if !B::available() {
        return;
    }
    let mut rng = Rng(0x7665_7269_6679_0000 ^ (K * 16 + L) as u64);
    let (mut valid, mut invalid, mut calls) = (0, 0, 0);
    let mut check = |pk: &[u8], pre: &[u8], m: &[u8], sig: &[u8], expect_valid: Option<bool>| {
        let want = verify_internal::<K, L>(p, pk, pre, m, sig);
        let got = B::verify::<K, L>(p, pk, pre, m, sig);
        assert_eq!(got, want, "{}: verify_internal_x4 K={K} L={L}", B::NAME);
        if pk.len() == ml_dsa_lean::params::pk_len(p) && sig.len() == ml_dsa_lean::params::sig_len(p) {
            let vk_x4 = B::prepare::<K, L>(pk);
            let a = verify_prepared_internal::<K, L>(p, &vk_x4, pre, m, sig);
            assert_eq!(a, want, "{}: prepare_vk_x4 then verify_prepared_internal vs one-shot K={K} L={L}", B::NAME);
        }
        if let Some(e) = expect_valid {
            assert_eq!(want, e);
        }
        calls += 1;
        if want {
            valid += 1;
        } else {
            invalid += 1;
        }
    };
    for _ in 0..(4 / SCALE.min(4)).max(1) {
        let (pk, sk) = keygen(&rng.arr32());
        for _ in 0..(6 / SCALE.min(3)).max(2) {
            let mlen = rng.below(200);
            let m = rng.bytes(mlen);
            let rnd = rng.arr32();
            let sig = sign(&sk, &m, &rnd).expect("sign");
            // The signature is over M' = m_prefix || m with an empty prefix here (sign_internal).
            check(&pk, &[], &m, &sig, Some(true));
            // Mutations: bit flips in c~, z and the hint region.
            for _ in 0..(8 / SCALE.min(4)).max(2) {
                let mut s = sig.clone();
                let at = match rng.below(3) {
                    0 => rng.below(p_ctilde_len(p)),
                    1 => p_ctilde_len(p) + rng.below(sig.len() - p_ctilde_len(p)),
                    _ => sig.len() - 1 - rng.below(K + 10),
                };
                s[at] ^= 1 << rng.below(8);
                check(&pk, &[], &m, &s, None);
            }
            // Wrong message, wrong prefix, wrong key.
            let mut m2 = m.clone();
            m2.push(1);
            check(&pk, &[], &m2, &sig, Some(false));
            check(&pk, &[1, 0], &m, &sig, Some(false));
            let (pk2, _) = keygen(&rng.arr32());
            check(&pk2, &[], &m, &sig, Some(false));
            // Random signature, wrong lengths.
            let rs = rng.bytes(sig.len());
            check(&pk, &[], &m, &rs, None);
            check(&pk, &[], &m, &sig[..sig.len() - 1], Some(false));
            check(&pk[..pk.len() - 1], &[], &m, &sig, Some(false));
        }
    }
    // A random public key (not produced by keygen) with random signatures.
    let pk = rng.bytes(ml_dsa_lean::params::pk_len(p));
    for _ in 0..3 {
        let sig = rng.bytes(ml_dsa_lean::params::sig_len(p));
        check(&pk, &[], b"msg", &sig, None);
    }
    eprintln!("{}: verify K={K} L={L}: {calls} calls ({valid} valid, {invalid} invalid), 0 mismatches", B::NAME);
}

fn p_ctilde_len(p: &Params) -> usize {
    p.c_tilde_len
}

fn run_all<B: Backend>() {
    check_rej4::<B>();
    check_expand::<B, 4, 4>();
    check_expand::<B, 6, 5>();
    check_expand::<B, 8, 7>();
    use ml_dsa_lean::api::*;
    check_verify::<B, 4, 4>(
        &ML_DSA_44,
        |xi| {
            let (pk, sk) = keygen_44(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, rnd| sign_internal_44(sk.try_into().unwrap(), m, rnd).map(|s| s.to_vec()),
    );
    check_verify::<B, 6, 5>(
        &ML_DSA_65,
        |xi| {
            let (pk, sk) = keygen_65(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, rnd| sign_internal_65(sk.try_into().unwrap(), m, rnd).map(|s| s.to_vec()),
    );
    check_verify::<B, 8, 7>(
        &ML_DSA_87,
        |xi| {
            let (pk, sk) = keygen_87(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, rnd| sign_internal_87(sk.try_into().unwrap(), m, rnd).map(|s| s.to_vec()),
    );
}

#[test]
fn shim_x4_matches_scalar() {
    run_all::<ShimB>();
}

#[cfg(all(feature = "avx2", target_arch = "x86_64", not(miri)))]
#[test]
fn avx2_x4_matches_scalar() {
    run_all::<avx2_backend::Avx2B>();
}

/// Documentation of the trait bound the tests rely on.
#[allow(dead_code)]
fn _lanes4_is_the_bound<X: Lanes4>() {}
