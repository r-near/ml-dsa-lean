//! Differential test: fork KeyGen_internal(ξ) vs upstream pk and expanded sk.
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed};
use ml_dsa_verified::keygen::keygen_internal;
use ml_dsa_verified::params::{pk_len, sk_len, Params, ML_DSA_44, ML_DSA_65, ML_DSA_87};

fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn check<P: MlDsaParams, const K: usize, const L: usize>(p: &Params, salt: u64) {
    let mut st = 0x9E37_79B9_7F4A_7C15u64 ^ salt;
    for case in 0..30 {
        let mut xi = [0u8; 32];
        for b in xi.iter_mut() {
            *b = xorshift(&mut st) as u8;
        }
        let mut seed = Seed::default();
        seed.copy_from_slice(&xi);
        let esk = ExpandedSigningKey::<P>::from_seed(&seed);
        let up_pk = esk.verifying_key().encode();
        let up_sk = esk.to_expanded();
        let mut pk = vec![0u8; pk_len(p)];
        let mut sk = vec![0u8; sk_len(p)];
        keygen_internal::<K, L>(p, &xi, &mut pk, &mut sk);
        assert_eq!(up_pk.as_slice(), pk.as_slice(), "pk mismatch, K={K} case {case}");
        assert_eq!(up_sk.as_slice(), sk.as_slice(), "sk mismatch, K={K} case {case}");
    }
}

#[test]
fn keygen_internal_matches_upstream() {
    check::<MlDsa44, 4, 4>(&ML_DSA_44, 44);
    check::<MlDsa65, 6, 5>(&ML_DSA_65, 65);
    check::<MlDsa87, 8, 7>(&ML_DSA_87, 87);
}
