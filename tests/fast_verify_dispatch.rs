//! The public API reaches the AVX2 wrapper. One test function only: it reads a process-wide counter
//! (`fast_verify::AVX2_CALLS`), so nothing else may run dispatched code concurrently in this binary.
//!
//! On a CPU without AVX2 the API must take the scalar path (the counter stays at 0). Set `ML_DSA_REQUIRE_AVX2=1` to
//! make a missing AVX2 a failure.
#![cfg(all(feature = "avx2", not(miri), target_arch = "x86_64"))]
use ml_dsa_lean::api;
use ml_dsa_lean::fast_verify::AVX2_CALLS;
use std::sync::atomic::Ordering;

fn calls() -> usize {
    AVX2_CALLS.load(Ordering::SeqCst)
}

#[test]
fn api_functions_take_the_avx2_path_exactly_when_the_cpu_has_it() {
    let avx2 = std::arch::is_x86_feature_detected!("avx2");
    if std::env::var("ML_DSA_REQUIRE_AVX2").as_deref() == Ok("1") {
        assert!(avx2, "ML_DSA_REQUIRE_AVX2=1 but this CPU has no AVX2");
    }
    let step = usize::from(avx2);
    let xi = [3u8; 32];
    let mut total = 0;
    macro_rules! per_set {
        ($kg:ident, $s:ident, $v:ident, $vi:ident, $vk:ident, $vp:ident, $vip:ident) => {{
            let (pk, sk) = api::$kg(&xi);
            let sig = api::$s(&sk, b"msg", b"ctx", &[0; 32]).unwrap();
            assert_eq!(calls(), total, "keygen and sign do not use the verify dispatch");

            assert!(api::$v(&pk, b"msg", b"ctx", &sig));
            total += step;
            assert_eq!(calls(), total, concat!(stringify!($v), ": one dispatched call"));

            let mut mp = vec![0u8, 3];
            mp.extend_from_slice(b"ctxmsg");
            assert!(api::$vi(&pk, &mp, &sig));
            total += step;
            assert_eq!(calls(), total, concat!(stringify!($vi), ": one dispatched call"));

            // verify_* with a context longer than 255 bytes returns false before any verification work.
            assert!(!api::$v(&pk, b"msg", &[0u8; 256], &sig));
            assert_eq!(calls(), total, "context too long: no dispatch");

            let vk = Box::new(api::$vk(&pk));
            total += step;
            assert_eq!(calls(), total, concat!(stringify!($vk), ": one dispatched call"));

            // The prepared verify has no ExpandA to speed up; it is not dispatched.
            assert!(api::$vp(&vk, b"msg", b"ctx", &sig));
            assert!(api::$vip(&vk, &mp, &sig));
            assert_eq!(calls(), total, "prepared verify is the scalar path");
        }};
    }
    per_set!(keygen_44, sign_44, verify_44, verify_internal_44, verifying_key_44, verify_prepared_44, verify_internal_prepared_44);
    per_set!(keygen_65, sign_65, verify_65, verify_internal_65, verifying_key_65, verify_prepared_65, verify_internal_prepared_65);
    per_set!(keygen_87, sign_87, verify_87, verify_internal_87, verifying_key_87, verify_prepared_87, verify_internal_prepared_87);
    eprintln!("AVX2 detected: {avx2}; dispatched calls counted: {}", calls());
}
