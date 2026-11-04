//! Timing of keygen, sign (external API, deterministic) and verify: this crate vs upstream RustCrypto.
#![allow(deprecated)]
use ml_dsa::{
    EncodedVerifyingKey, ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed, Signature, VerifyingKey,
};
use std::time::{Duration, Instant};

const ITERS: u32 = 300;
const MSG: &[u8] = b"benchmark message";
const CTX: &[u8] = b"bench";

fn time(mut f: impl FnMut(u32)) -> Duration {
    f(0); // warm up
    let t = Instant::now();
    for i in 0..ITERS {
        f(i);
    }
    t.elapsed() / ITERS
}

fn seed(i: u32) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..4].copy_from_slice(&i.to_le_bytes());
    s
}

fn row(name: &str, op: &str, up: Duration, fk: Duration) {
    println!("{name:<10} {op:<7} {up:>12.1?} {fk:>12.1?} {:>7.2}", fk.as_secs_f64() / up.as_secs_f64());
}

fn run<P: MlDsaParams>(
    name: &str,
    keygen: impl Fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    sign: impl Fn(&[u8], &[u8], &[u8], &[u8; 32]) -> bool,
    verify: impl Fn(&[u8], &[u8], &[u8], &[u8]) -> bool,
) {
    // keygen
    let up = time(|i| {
        let esk = ExpandedSigningKey::<P>::from_seed(&Seed::from(seed(i)));
        std::hint::black_box(esk.verifying_key().encode());
    });
    let fk = time(|i| {
        std::hint::black_box(keygen(&seed(i)));
    });
    row(name, "keygen", up, fk);

    let esk = ExpandedSigningKey::<P>::from_seed(&Seed::from(seed(7)));
    let (pk, sk) = keygen(&seed(7));
    let msgs: Vec<Vec<u8>> = (0..ITERS).map(|i| [MSG, &i.to_le_bytes()[..]].concat()).collect();

    // sign (deterministic, external API with ctx)
    let up = time(|i| {
        std::hint::black_box(esk.sign_deterministic(&msgs[i as usize], CTX).unwrap());
    });
    let fk = time(|i| {
        assert!(sign(&sk, &msgs[i as usize], CTX, &[0u8; 32]));
    });
    row(name, "sign", up, fk);

    // verify
    let vk = VerifyingKey::<P>::decode(&EncodedVerifyingKey::<P>::try_from(pk.as_slice()).unwrap());
    let sigs: Vec<Signature<P>> = msgs.iter().map(|m| esk.sign_deterministic(m, CTX).unwrap()).collect();
    let sig_bytes: Vec<Vec<u8>> = sigs.iter().map(|s| s.encode().to_vec()).collect();
    let up = time(|i| {
        assert!(vk.verify_with_context(&msgs[i as usize], CTX, &sigs[i as usize]));
    });
    let fk = time(|i| {
        assert!(verify(&pk, &msgs[i as usize], CTX, &sig_bytes[i as usize]));
    });
    row(name, "verify", up, fk);
}

fn main() {
    use ml_dsa_lean::api::*;
    println!("{:<10} {:<7} {:>12} {:>12} {:>7}", "set", "op", "upstream", "this crate", "ratio");
    run::<MlDsa44>(
        "ML-DSA-44",
        |xi| {
            let (pk, sk) = keygen_44(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, c, r| sign_44(sk.try_into().unwrap(), m, c, r).is_some(),
        |pk, m, c, s| verify_44(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
    );
    run::<MlDsa65>(
        "ML-DSA-65",
        |xi| {
            let (pk, sk) = keygen_65(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, c, r| sign_65(sk.try_into().unwrap(), m, c, r).is_some(),
        |pk, m, c, s| verify_65(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
    );
    run::<MlDsa87>(
        "ML-DSA-87",
        |xi| {
            let (pk, sk) = keygen_87(xi);
            (pk.to_vec(), sk.to_vec())
        },
        |sk, m, c, r| sign_87(sk.try_into().unwrap(), m, c, r).is_some(),
        |pk, m, c, s| verify_87(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
    );
}
