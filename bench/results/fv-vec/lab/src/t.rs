//! Single-pattern probes: does SLP vectorize this tiny shape?
type V = [u64; 4];
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_xor(a: &V, b: &V, o: &mut V) { for i in 0..4 { o[i] = a[i] ^ b[i]; } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_andnot(a: &V, b: &V, o: &mut V) { for i in 0..4 { o[i] = !a[i] & b[i]; } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_rot(a: &V, o: &mut V) { for i in 0..4 { o[i] = a[i].rotate_left(44); } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_rot_split(a: &V, o: &mut V) { for i in 0..4 { o[i] = (a[i] << 44) | (a[i] >> 20); } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_xor5(a: &V, b: &V, c: &V, d: &V, e: &V, o: &mut V) { for i in 0..4 { o[i] = a[i] ^ b[i] ^ c[i] ^ d[i] ^ e[i]; } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_xor_rot(a: &V, b: &V, o: &mut V) { for i in 0..4 { o[i] = (a[i] ^ b[i]).rotate_left(44); } }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn t_two(a: &V, b: &V, o: &mut V, p: &mut V) { for i in 0..4 { let x = a[i] ^ b[i]; o[i] = x.rotate_left(44); p[i] = x ^ (!b[i] & a[i]); } }

use crate::keccak4::{Lanes4, Shim4 as L};
type St = [[u64; 4]; 25];
/// theta C only
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn p_c(src: &St, c: &mut [[u64; 4]; 5]) {
    for x in 0..5 { c[x] = L::xor(L::xor(L::xor(L::xor(src[x], src[x + 5]), src[x + 10]), src[x + 15]), src[x + 20]); }
}
/// theta D from C
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn p_d(c: &[[u64; 4]; 5], d: &mut [[u64; 4]; 5]) {
    for x in 0..5 { d[x] = L::xor(c[(x + 4) % 5], L::rotl::<1, 63>(c[(x + 1) % 5])); }
}
/// one output row (yp = 0): b's from src and d, chi, store
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn p_row(src: &St, d: &[[u64; 4]; 5], dst: &mut St) {
    let b0_0 = L::xor(src[0], d[0]);
    let b0_1 = L::rotl::<44, 20>(L::xor(src[6], d[1]));
    let b0_2 = L::rotl::<43, 21>(L::xor(src[12], d[2]));
    let b0_3 = L::rotl::<21, 43>(L::xor(src[18], d[3]));
    let b0_4 = L::rotl::<14, 50>(L::xor(src[24], d[4]));
    dst[0] = L::xor(L::xor(b0_0, L::andnot(b0_1, b0_2)), L::splat(0x8000000080008008));
    dst[1] = L::xor(b0_1, L::andnot(b0_2, b0_3));
    dst[2] = L::xor(b0_2, L::andnot(b0_3, b0_4));
    dst[3] = L::xor(b0_3, L::andnot(b0_4, b0_0));
    dst[4] = L::xor(b0_4, L::andnot(b0_0, b0_1));
}
/// row without rotations
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn p_row_norot(src: &St, d: &[[u64; 4]; 5], dst: &mut St) {
    let b0_0 = L::xor(src[0], d[0]);
    let b0_1 = L::xor(src[6], d[1]);
    let b0_2 = L::xor(src[12], d[2]);
    let b0_3 = L::xor(src[18], d[3]);
    let b0_4 = L::xor(src[24], d[4]);
    dst[0] = L::xor(L::xor(b0_0, L::andnot(b0_1, b0_2)), L::splat(0x8000000080008008));
    dst[1] = L::xor(b0_1, L::andnot(b0_2, b0_3));
    dst[2] = L::xor(b0_2, L::andnot(b0_3, b0_4));
    dst[3] = L::xor(b0_3, L::andnot(b0_4, b0_0));
    dst[4] = L::xor(b0_4, L::andnot(b0_0, b0_1));
}
/// row with the splat dropped
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn p_row_nosplat(src: &St, d: &[[u64; 4]; 5], dst: &mut St) {
    let b0_0 = L::xor(src[0], d[0]);
    let b0_1 = L::rotl::<44, 20>(L::xor(src[6], d[1]));
    let b0_2 = L::rotl::<43, 21>(L::xor(src[12], d[2]));
    let b0_3 = L::rotl::<21, 43>(L::xor(src[18], d[3]));
    let b0_4 = L::rotl::<14, 50>(L::xor(src[24], d[4]));
    dst[0] = L::xor(b0_0, L::andnot(b0_1, b0_2));
    dst[1] = L::xor(b0_1, L::andnot(b0_2, b0_3));
    dst[2] = L::xor(b0_2, L::andnot(b0_3, b0_4));
    dst[3] = L::xor(b0_3, L::andnot(b0_4, b0_0));
    dst[4] = L::xor(b0_4, L::andnot(b0_0, b0_1));
}

#[inline(always)]
fn cd(src: &St) -> ([[u64; 4]; 5], [[u64; 4]; 5]) {
    let mut c = [[0u64; 4]; 5];
    for x in 0..5 { c[x] = L::xor(L::xor(L::xor(L::xor(src[x], src[x + 5]), src[x + 10]), src[x + 15]), src[x + 20]); }
    let mut d = [[0u64; 4]; 5];
    for x in 0..5 { d[x] = L::xor(c[(x + 4) % 5], L::rotl::<1, 63>(c[(x + 1) % 5])); }
    (c, d)
}
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn q_theta(src: &St, d: &mut [[u64; 4]; 5]) { *d = cd(src).1; }
#[target_feature(enable = "avx2")] #[inline(never)]
pub fn q_theta_row(src: &St, dst: &mut St) {
    let d = cd(src).1;
    let b0_0 = L::xor(src[0], d[0]);
    let b0_1 = L::rotl::<44, 20>(L::xor(src[6], d[1]));
    let b0_2 = L::rotl::<43, 21>(L::xor(src[12], d[2]));
    let b0_3 = L::rotl::<21, 43>(L::xor(src[18], d[3]));
    let b0_4 = L::rotl::<14, 50>(L::xor(src[24], d[4]));
    dst[0] = L::xor(L::xor(b0_0, L::andnot(b0_1, b0_2)), L::splat(0x8000000080008008));
    dst[1] = L::xor(b0_1, L::andnot(b0_2, b0_3));
    dst[2] = L::xor(b0_2, L::andnot(b0_3, b0_4));
    dst[3] = L::xor(b0_3, L::andnot(b0_4, b0_0));
    dst[4] = L::xor(b0_4, L::andnot(b0_0, b0_1));
}
