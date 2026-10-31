//! The portable and the AVX2 compilation of the NTT bodies agree (they are the same source), and the dispatching entry
//! points agree with both. On a CPU without AVX2 (or a build that is statically AVX2 or not x86_64) there is only one
//! compilation and the comparison is skipped.
use ml_dsa_verified::field::Q;
use ml_dsa_verified::ntt;

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

fn polys() -> Vec<[u32; 256]> {
    let mut r = XorShift(0x5eed_5eed_1234_4321);
    let mut v = vec![[0u32; 256], [Q - 1; 256], [1; 256]];
    for _ in 0..2000 {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = (r.next() % Q as u64) as u32;
        }
        v.push(p);
    }
    v
}

#[test]
fn compilations_agree() {
    let mut compared = 0;
    for p in polys() {
        let want_ntt = ntt::ntt(&p);
        let want_inv = ntt::ntt_inverse(&p);
        let want_mul = ntt::multiply_ntt(&p, &want_ntt);
        if let Some(pairs) = ntt::compare_compilations(&p) {
            compared += 1;
            assert_eq!(pairs[0].0, pairs[0].1, "ntt");
            assert_eq!(pairs[1].0, pairs[1].1, "ntt_inverse");
            assert_eq!(pairs[2].0, pairs[2].1, "multiply_ntt");
            assert_eq!(pairs[0].0, want_ntt);
            assert_eq!(pairs[1].0, want_inv);
            assert_eq!(pairs[2].0, want_mul);
        }
    }
    eprintln!("compared {compared} polynomials across the two compilations");
    // The crate's own CPU check must agree with the standard library's on a dynamic-dispatch build.
    #[cfg(all(not(miri), target_arch = "x86_64", not(target_feature = "avx2")))]
    assert_eq!(compared > 0, std::arch::is_x86_feature_detected!("avx2"));
}
