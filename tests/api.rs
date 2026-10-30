//! Public API (FIPS 204 Algorithms 1, 2, 3) against upstream RustCrypto ml-dsa (a3690c4):
//! keygen bytes, deterministic and hedged signatures, cross-verification, context handling.
#![allow(deprecated)]
use ml_dsa::{
    B32, EncodedVerifyingKey, ExpandedSigningKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed, Signature,
    VerifyingKey,
};
use ml_dsa_verified::api::*;

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
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn array32(&mut self) -> [u8; 32] {
        self.bytes(32).try_into().unwrap()
    }
}

/// One parameter set's functions, as slice-based adapters.
struct Ours {
    keygen: fn(&[u8; 32]) -> (Vec<u8>, Vec<u8>),
    sign: fn(&[u8], &[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>,
    verify: fn(&[u8], &[u8], &[u8], &[u8]) -> bool,
    sign_internal: fn(&[u8], &[u8], &[u8; 32]) -> Option<Vec<u8>>,
    verify_internal: fn(&[u8], &[u8], &[u8]) -> bool,
}

fn ours44() -> Ours {
    Ours {
        keygen: |xi| {
            let (pk, sk) = keygen_44(xi);
            (pk.to_vec(), sk.to_vec())
        },
        sign: |sk, m, c, r| sign_44(sk.try_into().unwrap(), m, c, r).map(|s| s.to_vec()),
        verify: |pk, m, c, s| verify_44(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
        sign_internal: |sk, m, r| sign_internal_44(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()),
        verify_internal: |pk, m, s| verify_internal_44(pk.try_into().unwrap(), m, s.try_into().unwrap()),
    }
}
fn ours65() -> Ours {
    Ours {
        keygen: |xi| {
            let (pk, sk) = keygen_65(xi);
            (pk.to_vec(), sk.to_vec())
        },
        sign: |sk, m, c, r| sign_65(sk.try_into().unwrap(), m, c, r).map(|s| s.to_vec()),
        verify: |pk, m, c, s| verify_65(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
        sign_internal: |sk, m, r| sign_internal_65(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()),
        verify_internal: |pk, m, s| verify_internal_65(pk.try_into().unwrap(), m, s.try_into().unwrap()),
    }
}
fn ours87() -> Ours {
    Ours {
        keygen: |xi| {
            let (pk, sk) = keygen_87(xi);
            (pk.to_vec(), sk.to_vec())
        },
        sign: |sk, m, c, r| sign_87(sk.try_into().unwrap(), m, c, r).map(|s| s.to_vec()),
        verify: |pk, m, c, s| verify_87(pk.try_into().unwrap(), m, c, s.try_into().unwrap()),
        sign_internal: |sk, m, r| sign_internal_87(sk.try_into().unwrap(), m, r).map(|s| s.to_vec()),
        verify_internal: |pk, m, s| verify_internal_87(pk.try_into().unwrap(), m, s.try_into().unwrap()),
    }
}

fn up_verify<P: MlDsaParams>(pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8]) -> bool {
    let vk = VerifyingKey::<P>::decode(&EncodedVerifyingKey::<P>::try_from(pk).unwrap());
    match Signature::<P>::try_from(sig) {
        Ok(s) => vk.verify_with_context(m, ctx, &s),
        Err(_) => false,
    }
}

const CTX_LENS: [usize; 6] = [0, 1, 7, 100, 254, 255];

fn check<P: MlDsaParams>(o: &Ours, tag: u64) -> usize {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03 ^ tag);
    let mut cases = 0;
    for case in 0..24usize {
        let xi = rng.array32();
        let ctx_len = CTX_LENS[case % CTX_LENS.len()];
        let ctx = rng.bytes(ctx_len);
        let m_len = [0, 1, 33, 300][case % 4];
        let m = rng.bytes(m_len);

        // Algorithm 1: keygen bytes equal.
        let esk = ExpandedSigningKey::<P>::from_seed(&Seed::from(xi));
        let up_pk = esk.verifying_key().encode();
        let up_sk = esk.to_expanded();
        let (pk, sk) = (o.keygen)(&xi);
        assert_eq!(up_pk.as_slice(), pk.as_slice(), "pk, case {case}");
        assert_eq!(up_sk.as_slice(), sk.as_slice(), "sk, case {case}");

        // Algorithm 2, deterministic: bytes equal to upstream's deterministic signature.
        let up_sig = esk.sign_deterministic(&m, &ctx).unwrap().encode();
        let sig = (o.sign)(&sk, &m, &ctx, &[0u8; 32]).expect("sign exhausted");
        assert_eq!(up_sig.as_slice(), sig.as_slice(), "deterministic sig, case {case}");

        // Algorithm 3: cross verification.
        assert!((o.verify)(&pk, &m, &ctx, up_sig.as_slice()), "ours rejects upstream sig, case {case}");
        assert!(up_verify::<P>(&pk, &m, &ctx, &sig), "upstream rejects our sig, case {case}");

        // Wrong ctx must reject (both implementations).
        let mut bad_ctx = ctx.clone();
        if bad_ctx.is_empty() {
            bad_ctx.push(1);
        } else {
            bad_ctx[0] ^= 1;
        }
        assert!(!(o.verify)(&pk, &m, &bad_ctx, &sig), "wrong ctx accepted, case {case}");
        assert!(!up_verify::<P>(&pk, &m, &bad_ctx, &sig));
        // ctx = prefix of the right ctx (different length) must also reject.
        if !ctx.is_empty() {
            assert!(!(o.verify)(&pk, &m, &ctx[..ctx.len() - 1], &sig));
        }

        // |ctx| = 256: sign None, verify false, upstream also rejects.
        let long_ctx = rng.bytes(256);
        assert!((o.sign)(&sk, &m, &long_ctx, &[0u8; 32]).is_none(), "sign accepted 256-byte ctx");
        assert!(!(o.verify)(&pk, &m, &long_ctx, &sig), "verify accepted 256-byte ctx");
        assert!(esk.sign_deterministic(&m, &long_ctx).is_err());
        let up_sig_obj = Signature::<P>::try_from(sig.as_slice()).unwrap();
        assert!(!VerifyingKey::<P>::decode(&EncodedVerifyingKey::<P>::try_from(pk.as_slice()).unwrap())
            .verify_with_context(&m, &long_ctx, &up_sig_obj));

        // Hedged: fixed rnd, equals upstream sign_internal on M' = 0 || |ctx| || ctx || M.
        let rnd = rng.array32();
        let mut mp = vec![0u8, ctx.len() as u8];
        mp.extend_from_slice(&ctx);
        mp.extend_from_slice(&m);
        let up_h = esk.sign_internal(&[&mp], &B32::from(rnd)).encode();
        let hedged = (o.sign)(&sk, &m, &ctx, &rnd).expect("hedged sign exhausted");
        assert_eq!(up_h.as_slice(), hedged.as_slice(), "hedged sig, case {case}");
        assert!((o.verify)(&pk, &m, &ctx, &hedged));
        assert!(up_verify::<P>(&pk, &m, &ctx, &hedged));

        // Internal interface: sign_internal / verify_internal on M'.
        let si = (o.sign_internal)(&sk, &mp, &rnd).unwrap();
        assert_eq!(si, hedged, "sign_internal(M') != sign(M, ctx)");
        assert!((o.verify_internal)(&pk, &mp, &si));
        assert!(!(o.verify_internal)(&pk, &mp[1..], &si));

        // Tampered signature rejects.
        let mut tampered = sig.clone();
        tampered[case % 32] ^= 0x80;
        assert!(!(o.verify)(&pk, &m, &ctx, &tampered));
        cases += 1;
    }
    cases
}

#[test]
fn api_44_matches_upstream() {
    assert_eq!(check::<MlDsa44>(&ours44(), 44), 24);
}
#[test]
fn api_65_matches_upstream() {
    assert_eq!(check::<MlDsa65>(&ours65(), 65), 24);
}
#[test]
fn api_87_matches_upstream() {
    assert_eq!(check::<MlDsa87>(&ours87(), 87), 24);
}
