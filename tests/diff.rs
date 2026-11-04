//! Differential test against upstream master: skEncode bytes from upstream, then
//! fork Sign_internal(sk, M′, rnd) must equal upstream `sign_internal(&[M′], rnd).encode()`.
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed};

fn seed(i: u8) -> Seed {
    let mut s = Seed::default();
    for (j, b) in s.iter_mut().enumerate() {
        *b = (j as u8).wrapping_mul(31).wrapping_add(i);
    }
    s
}

fn check<P: MlDsaParams>(n: usize, fork: impl Fn(&[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>) {
    for i in 0..n {
        let esk = ExpandedSigningKey::<P>::from_seed(&seed(i as u8));
        let sk_bytes = esk.to_expanded();
        let msg: Vec<u8> = (0..(i * 7) % 300).map(|j| (j * 13 + i) as u8).collect();
        let mut rnd = [0u8; 32];
        rnd[0] = i as u8;
        let rnd_arr = ml_dsa::B32::from(rnd);
        let upstream = esk.sign_internal(&[&msg], &rnd_arr).encode();
        let mine = fork(&sk_bytes, &msg, &rnd).expect("fork exhausted");
        assert_eq!(upstream.as_slice(), mine.as_slice(), "mismatch at case {i}");
    }
}

#[test]
fn sign_internal_matches_upstream() {
    use ml_dsa_lean::api::*;
    check::<MlDsa44>(25, |sk, m, r| sign_internal_44(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()));
    check::<MlDsa65>(25, |sk, m, r| sign_internal_65(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()));
    check::<MlDsa87>(25, |sk, m, r| sign_internal_87(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()));
}
