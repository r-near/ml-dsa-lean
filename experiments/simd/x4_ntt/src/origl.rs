//! The crate's own `ntt_layer` / `ntt_inverse_layer` (src/ntt.rs, private there), duplicated verbatim so single layers can be
//! timed. Same field functions (`crate::field`), same loop shape.
use crate::field::{add, mul, sub};
use crate::ntt::ZETAS;

pub fn ntt_layer<const LEN: usize, const ITERATIONS: usize>(w: &mut [u32; 256], m: &mut usize) {
    let mut i = 0;
    while i < ITERATIONS {
        let start = i * 2 * LEN;
        *m += 1;
        let z = ZETAS[*m];
        let mut j = start;
        while j < (start + LEN) {
            let t = mul(z, w[j + LEN]);
            w[j + LEN] = sub(w[j], t);
            w[j] = add(w[j], t);
            j += 1;
        }
        i += 1;
    }
}

pub fn layer128(w: &mut [u32; 256]) {
    let mut m = 0;
    ntt_layer::<128, 1>(w, &mut m);
}
pub fn layer16(w: &mut [u32; 256]) {
    let mut m = 7;
    ntt_layer::<16, 8>(w, &mut m);
}
pub fn layer4(w: &mut [u32; 256]) {
    let mut m = 31;
    ntt_layer::<4, 32>(w, &mut m);
}

/// The pitfall: a `target_feature` wrapper around the crate's un-annotated `ntt` only gets AVX2 code if LLVM happens to
/// inline `ntt` (and `ntt_layer`, `mul`, ...) into it.
#[target_feature(enable = "avx2")]
pub fn ntt_in_tf_wrapper(w: &[u32; 256]) -> [u32; 256] {
    crate::ntt::ntt(w)
}

/// Single layer for the micro-benchmark; `M0` is the value of `m` before the layer.
#[inline(always)]
pub fn layer<const LEN: usize, const ITERATIONS: usize, const M0: usize>(w: &mut [u32; 256]) {
    let mut m = M0;
    ntt_layer::<LEN, ITERATIONS>(w, &mut m);
}
