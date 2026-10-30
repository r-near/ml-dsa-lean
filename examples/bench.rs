//! Rough timing of Sign_internal: fork vs upstream master (same key, message, rnd).
#![allow(deprecated)]
use ml_dsa::{ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed};
use std::time::Instant;

fn run<P: MlDsaParams>(name: &str, fork: impl Fn(&[u8], &[u8], &[u8; 32]) -> bool) {
    let esk = ExpandedSigningKey::<P>::from_seed(&Seed::default());
    let sk = esk.to_expanded();
    let iters = 300u32;
    let t = Instant::now();
    for i in 0..iters {
        let mut rnd = [0u8; 32];
        rnd[..4].copy_from_slice(&i.to_le_bytes());
        let r = ml_dsa::B32::from(rnd);
        std::hint::black_box(esk.sign_internal(&[b"benchmark message"], &r));
    }
    let up = t.elapsed() / iters;
    let t = Instant::now();
    for i in 0..iters {
        let mut rnd = [0u8; 32];
        rnd[..4].copy_from_slice(&i.to_le_bytes());
        std::hint::black_box(fork(&sk, b"benchmark message", &rnd));
    }
    let fk = t.elapsed() / iters;
    println!("{name}: upstream sign_internal {up:?}, fork sign_internal (incl. skDecode+NTT+ExpandA per call) {fk:?}, ratio {:.2}", fk.as_secs_f64() / up.as_secs_f64());
}

fn main() {
    use ml_dsa_fork_skeleton::api::*;
    run::<MlDsa44>("ML-DSA-44", |sk, m, r| sign_internal_44(sk.try_into().unwrap(), m, r).is_some());
    run::<MlDsa65>("ML-DSA-65", |sk, m, r| sign_internal_65(sk.try_into().unwrap(), m, r).is_some());
    run::<MlDsa87>("ML-DSA-87", |sk, m, r| sign_internal_87(sk.try_into().unwrap(), m, r).is_some());
}
