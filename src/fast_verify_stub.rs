//! TEMPORARY STAND-IN, delete at integration. NOT PROVED. NOT THE FINAL CODE.
//!
//! Stream W2 (the shipping path) needs a 4-way verify body to wire the dispatch against, but the proved one
//! (`verify::verify_internal_x4`, stream W1) does not exist yet. This file provides the same two signatures so that
//! the wiring in `fast_verify.rs` compiles, the tests run and the benchmarks have something to measure:
//!
//! * `verify_internal_x4::<K, L, X>`: the per-set `verify::verify_internal` with ExpandA replaced by a 4-way sampler
//!   over `keccak4::keccak_f1600_x4::<X>`. A copy of the scalar body (`verify.rs`) with one call changed.
//! * `prepare_vk_x4::<K, L, X>`: the same for `verify::prepare_vk` (`api::verifying_key_*`).
//!
//! Both are exact (they return what the scalar functions return, tested by `tests/fast_verify.rs`), but the sampler is
//! a plain, unoptimized 4-way SHAKE128 rejection sampler (byte-wise parse), not spike A's AVX2 parse, so benchmark
//! numbers taken with this stub understate what the final code will reach.
//!
//! Integration: change the one `use crate::fast_verify_stub::{...}` line in `fast_verify.rs` to
//! `use crate::verify::{...}`, remove `mod fast_verify_stub` from `lib.rs`, and delete this file.
//!
//! Inlining contract the real implementation must keep (the stub does): everything generic over `Lanes4` between the
//! `#[target_feature(enable = "avx2")]` wrapper in `fast_verify.rs` and the intrinsics must be `#[inline(always)]`
//! (under `feature = "avx2"`, not miri, x86_64), as `keccak_f1600_x4` is. A callee that is not inlined is compiled
//! without AVX2 and calls the intrinsics out of line, which is correct but several times slower than scalar.
//! `scripts/check-avx2-inlining.sh` checks for this.

use crate::encode::{pk_decode, sig_decode, w1_encode};
use crate::field::Q;
use crate::keccak::Shake;
use crate::keccak4::{Lanes4, keccak_f1600_x4};
use crate::ntt::{matrix_vector_ntt, multiply_ntt, ntt, ntt_inverse, ntt_vec, sub_poly};
use crate::params::{Params, pk_len, sig_len};
use crate::rounding::{poly_use_hint, vec_infinity_norm};
use crate::sampling::sample_in_ball;
use crate::verify::{PreparedVk, prefix_eq};

/// ExpandA with four SHAKE128 streams at a time. Entry `idx = r * L + s` of the matrix is sampled from
/// `rho || s || r`, exactly as `sampling::rej_ntt_poly` does; the last group repeats entry `base` in its unused lanes.
#[inline(always)]
fn expand_a_x4_into<const K: usize, const L: usize, X: Lanes4>(rho: &[u8; 32], a: &mut [[[u32; 256]; L]; K]) {
    let total = K * L;
    let mut base = 0;
    while base < total {
        let mut st = [[0u64; 4]; 25];
        let mut i = 0;
        while i < 4 {
            let idx = if base + i < total { base + i } else { base };
            let (r, s) = (idx / L, idx % L);
            let mut k = 0;
            while k < 4 {
                let mut w = [0u8; 8];
                w.copy_from_slice(&rho[8 * k..8 * k + 8]);
                st[k][i] = u64::from_le_bytes(w);
                k += 1;
            }
            // bytes 32, 33: the nonce; byte 34: SHAKE domain separation 0x1F; byte 167 (rate - 1): 0x80.
            st[4][i] = (s as u64) | ((r as u64) << 8) | (0x1Fu64 << 16);
            st[20][i] = 0x80u64 << 56;
            i += 1;
        }
        let mut cnt = [0usize; 4];
        let mut lanes = 4;
        if total - base < 4 {
            lanes = total - base;
        }
        loop {
            keccak_f1600_x4::<X>(&mut st);
            let mut all_done = true;
            let mut i = 0;
            while i < lanes {
                if cnt[i] < 256 {
                    let idx = base + i;
                    let (r, s) = (idx / L, idx % L);
                    let mut t = 0;
                    while t < 56 && cnt[i] < 256 {
                        // Triple t is bytes 3t, 3t+1, 3t+2 of the 168-byte block (little-endian lanes).
                        let b = |j: usize| (st[j / 8][i] >> (8 * (j % 8))) as u32 & 0xFF;
                        let z = ((b(3 * t + 2) & 127) << 16) | (b(3 * t + 1) << 8) | b(3 * t);
                        if z < Q {
                            a[r][s][cnt[i]] = z;
                            cnt[i] += 1;
                        }
                        t += 1;
                    }
                    if cnt[i] < 256 {
                        all_done = false;
                    }
                }
                i += 1;
            }
            if all_done {
                break;
            }
        }
        base += 4;
    }
}

fn scale_vec_by_2d<const N: usize>(t1: &[[u32; 256]; N]) -> [[u32; 256]; N] {
    let mut out = [[0u32; 256]; N];
    let mut i = 0;
    while i < N {
        let mut j = 0;
        while j < 256 {
            out[i][j] = t1[i][j] << 13;
            j += 1;
        }
        i += 1;
    }
    out
}

fn hash_pk(pk: &[u8]) -> [u8; 64] {
    let mut tr = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(pk);
    hash.finalize();
    hash.squeeze(&mut tr);
    tr
}

#[inline(never)]
fn prepare_vk_x4_into<const K: usize, const L: usize, X: Lanes4>(pk: &[u8], out: &mut PreparedVk<K, L>) {
    let (rho, t1) = pk_decode::<K>(pk);
    expand_a_x4_into::<K, L, X>(&rho, &mut out.a_hat);
    out.tr = hash_pk(pk);
    out.t1_2d_hat = ntt_vec(&scale_vec_by_2d(&t1));
}

/// `verify::prepare_vk` with the 4-way ExpandA. Precondition: `pk.len() == 32 + 320 * K`.
#[inline(never)]
pub(crate) fn prepare_vk_x4<const K: usize, const L: usize, X: Lanes4>(pk: &[u8]) -> PreparedVk<K, L> {
    let (rho, t1) = pk_decode::<K>(pk);
    let mut a_hat = [[[0u32; 256]; L]; K];
    expand_a_x4_into::<K, L, X>(&rho, &mut a_hat);
    let tr = hash_pk(pk);
    let t1_2d_hat = ntt_vec(&scale_vec_by_2d(&t1));
    PreparedVk { a_hat, t1_2d_hat, tr }
}

fn hash_mu(tr: &[u8; 64], m_prefix: &[u8], m: &[u8]) -> [u8; 64] {
    let mut mu = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(tr);
    hash.absorb(m_prefix);
    hash.absorb(m);
    hash.finalize();
    hash.squeeze(&mut mu);
    mu
}

#[allow(clippy::too_many_arguments)]
fn verify_decoded<const K: usize, const L: usize>(
    p: &Params,
    vk: &PreparedVk<K, L>,
    m_prefix: &[u8],
    m: &[u8],
    c_tilde: &[u8; 64],
    z: &[[u32; 256]; L],
    h: &[[bool; 256]; K],
) -> bool {
    let mu = hash_mu(&vk.tr, m_prefix, m);
    let c = sample_in_ball(p, &c_tilde[..p.c_tilde_len]);
    let az_hat = matrix_vector_ntt::<K, L>(&vk.a_hat, &ntt_vec(z));
    let c_hat = ntt(&c);
    let mut w1 = [[0u32; 256]; K];
    let mut i = 0;
    while i < K {
        let ct1_hat = multiply_ntt(&c_hat, &vk.t1_2d_hat[i]);
        let w_approx = ntt_inverse(&sub_poly(&az_hat[i], &ct1_hat));
        w1[i] = poly_use_hint(p, &h[i], &w_approx);
        i += 1;
    }
    let mut w1_enc = [0u8; 8 * 192];
    w1_encode(p, &w1, &mut w1_enc);
    let mut c_tilde_prime = [0u8; 64];
    let mut hash = Shake::shake256();
    hash.absorb(&mu);
    hash.absorb(&w1_enc[..K * 32 * p.w1_bits]);
    hash.finalize();
    hash.squeeze(&mut c_tilde_prime[..p.c_tilde_len]);
    let norm_ok = vec_infinity_norm(z) < p.gamma1 - p.beta;
    let hash_ok = prefix_eq(c_tilde, &c_tilde_prime, p.c_tilde_len);
    norm_ok && hash_ok
}

/// `verify::verify_internal` with the 4-way ExpandA. Same preconditions and results.
#[inline(always)]
pub(crate) fn verify_internal_x4<const K: usize, const L: usize, X: Lanes4>(
    p: &Params,
    pk: &[u8],
    m_prefix: &[u8],
    m: &[u8],
    sig: &[u8],
) -> bool {
    if pk.len() != pk_len(p) || sig.len() != sig_len(p) {
        return false;
    }
    let (c_tilde, z, h) = match sig_decode::<K, L>(p, sig) {
        Some(parts) => parts,
        None => return false,
    };
    let mut vk = PreparedVk::<K, L>::zeroed();
    prepare_vk_x4_into::<K, L, X>(pk, &mut vk);
    verify_decoded::<K, L>(p, &vk, m_prefix, m, &c_tilde, &z, &h)
}
