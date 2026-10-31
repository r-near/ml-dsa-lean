//! Prepared keys (`VerifyingKey*`, `verifying_key_*`, `verify_prepared_*`, `verify_internal_prepared_*`) against
//! the unprepared functions they must equal: keygen -> sign -> verify, mutated signatures, wrong keys, wrong
//! messages, random public keys, and every context length class including 255 (largest valid), 256 (rejected).
//!
//! Counts per parameter set (release; debug uses `SCALE` = 10x fewer of the bulk cases):
//! 20 key pairs x 20 messages with a context from {0, 1, 2, 100, 255, 256, 300} bytes; for every valid signature:
//! 20 mutated copies (bit flips in c~, z and the hint region; truncation is impossible with fixed arrays; all-random
//! signatures); each also with a wrong message and a wrong context; 3 random public keys with 10 random signatures.
//! Every result of the prepared function is compared with the unprepared one, so a disagreement in either
//! direction fails (the valid signatures must also verify).
use ml_dsa_verified::api::*;

const SCALE: usize = if cfg!(debug_assertions) { 10 } else { 1 };

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
    /// Random bytes of a random length below `n`.
    fn bytes_below(&mut self, n: usize) -> Vec<u8> {
        let len = self.below(n);
        self.bytes(len)
    }
    fn pick(&mut self, lens: &[usize]) -> usize {
        lens[self.below(lens.len())]
    }
    fn arr32(&mut self) -> [u8; 32] {
        let mut a = [0u8; 32];
        for b in a.iter_mut() {
            *b = self.next() as u8;
        }
        a
    }
}

const CTX_LENS: [usize; 7] = [0, 1, 2, 100, 255, 256, 300];

macro_rules! prepared_tests {
    ($modname:ident, $seed:expr, $size:expr, $pk:literal, $sig:literal, $keygen:ident, $sign:ident, $verify:ident,
     $verify_internal:ident, $sign_internal:ident, $vk_ty:ident, $vk:ident, $vp:ident, $vip:ident) => {
        mod $modname {
            use super::*;

            #[test]
            fn size_matches_the_documented_value() {
                assert_eq!(std::mem::size_of::<$vk_ty>(), $size);
            }

            /// Prepared and unprepared agree on one (m, ctx, sig), and on the internal variant with M' = m.
            fn agree(pk: &[u8; $pk], vk: &$vk_ty, m: &[u8], ctx: &[u8], sig: &[u8; $sig]) -> bool {
                let a = $verify(pk, m, ctx, sig);
                let b = $vp(vk, m, ctx, sig);
                assert_eq!(a, b, "verify vs verify_prepared, |m| = {}, |ctx| = {}", m.len(), ctx.len());
                let c = $verify_internal(pk, m, sig);
                let d = $vip(vk, m, sig);
                assert_eq!(c, d, "verify_internal vs verify_internal_prepared, |m| = {}", m.len());
                a
            }

            #[test]
            fn prepared_equals_unprepared() {
                let mut r = Rng($seed);
                for _ in 0..20 {
                    let (pk, sk) = $keygen(&r.arr32());
                    let vk = Box::new($vk(&pk));
                    let (pk2, _) = $keygen(&r.arr32());
                    let vk2 = Box::new($vk(&pk2));
                    for _ in 0..20 {
                        let m = r.bytes_below(300);
                        let ctx_len = r.pick(&CTX_LENS);
                        let ctx = r.bytes(ctx_len);
                        let rnd = if r.below(2) == 0 { [0u8; 32] } else { r.arr32() };
                        match $sign(&sk, &m, &ctx, &rnd) {
                            None => {
                                // |ctx| > 255: both reject, whatever the signature
                                assert!(ctx.len() > 255);
                                let junk: [u8; $sig] = r.bytes($sig).try_into().unwrap();
                                assert!(!agree(&pk, &vk, &m, &ctx, &junk));
                                continue;
                            }
                            Some(sig) => {
                                assert!(agree(&pk, &vk, &m, &ctx, &sig), "valid signature rejected");
                                // wrong message / wrong context
                                let mut m2 = m.clone();
                                m2.push(r.next() as u8);
                                assert!(!agree(&pk, &vk, &m2, &ctx, &sig));
                                let mut ctx2 = ctx.clone();
                                ctx2.push(r.next() as u8);
                                agree(&pk, &vk, &m, &ctx2, &sig);
                                // another key's prepared key, same signature
                                assert!(!agree(&pk2, &vk2, &m, &ctx, &sig));
                                // mutated signatures
                                for i in 0..(20 / SCALE).max(2) {
                                    let mut s = sig;
                                    let pos = match i % 3 {
                                        0 => r.below(32),            // c~
                                        1 => 48 + r.below($sig - 48 - 100), // z
                                        _ => $sig - 1 - r.below(90), // hint region
                                    };
                                    s[pos] ^= 1 << r.below(8);
                                    agree(&pk, &vk, &m, &ctx, &s);
                                }
                                let rs: [u8; $sig] = r.bytes($sig).try_into().unwrap();
                                assert!(!agree(&pk, &vk, &m, &ctx, &rs));
                            }
                        }
                    }
                }
            }

            #[test]
            fn random_public_keys_and_signatures() {
                let mut r = Rng($seed ^ 0x9e37_79b9);
                for _ in 0..3 {
                    let pk: [u8; $pk] = r.bytes($pk).try_into().unwrap();
                    let vk = Box::new($vk(&pk));
                    for _ in 0..(10 / SCALE).max(2) {
                        let sig: [u8; $sig] = r.bytes($sig).try_into().unwrap();
                        let m = r.bytes_below(100);
                        let ctx = r.bytes_below(40);
                        agree(&pk, &vk, &m, &ctx, &sig);
                    }
                }
            }

            #[test]
            fn internal_signatures_verify_prepared() {
                let mut r = Rng($seed ^ 0x1234_5678);
                let (pk, sk) = $keygen(&r.arr32());
                let vk = Box::new($vk(&pk));
                for _ in 0..(8 / SCALE).max(2) {
                    let mp = r.bytes_below(400);
                    let sig = $sign_internal(&sk, &mp, &r.arr32()).unwrap();
                    assert!($vip(&vk, &mp, &sig));
                    assert!($verify_internal(&pk, &mp, &sig));
                    let mut bad = sig;
                    bad[r.below(32)] ^= 1;
                    assert!(!$vip(&vk, &mp, &bad));
                }
            }

            #[test]
            fn one_prepared_key_serves_many_signatures_and_clones_alike() {
                let mut r = Rng($seed ^ 0xabcd);
                let (pk, sk) = $keygen(&r.arr32());
                let vk = Box::new($vk(&pk));
                let vk_clone = vk.clone();
                for _ in 0..(10 / SCALE).max(2) {
                    let m = r.bytes_below(64);
                    let sig = $sign(&sk, &m, b"ctx", &r.arr32()).unwrap();
                    assert!($vp(&vk, &m, b"ctx", &sig));
                    assert!($vp(&vk_clone, &m, b"ctx", &sig));
                }
            }
        }
    };
}

prepared_tests!(p44, 0x4444_0001, 20_544, 1312, 2420, keygen_44, sign_44, verify_44, verify_internal_44, sign_internal_44,
    VerifyingKey44, verifying_key_44, verify_prepared_44, verify_internal_prepared_44);
prepared_tests!(p65, 0x6565_0001, 36_928, 1952, 3309, keygen_65, sign_65, verify_65, verify_internal_65, sign_internal_65,
    VerifyingKey65, verifying_key_65, verify_prepared_65, verify_internal_prepared_65);
prepared_tests!(p87, 0x8787_0001, 65_600, 2592, 4627, keygen_87, sign_87, verify_87, verify_internal_87, sign_internal_87,
    VerifyingKey87, verifying_key_87, verify_prepared_87, verify_internal_prepared_87);
