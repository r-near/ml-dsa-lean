//! Phase 0 prototype: 4-way Keccak-f[1600] in lane-interleaved layout, written as plain loops (no intrinsics).
//! `keccak_f1600` is a verbatim copy of the crate's scalar permutation; `keccak_f1600_x4` runs 4 states at once with
//! every round step written as a loop over the 4 lanes.

const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
    0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
    0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

const RHO: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

fn rotl(x: u64, n: u32) -> u64 {
    if n == 0 { x } else { (x << n) | (x >> (64 - n)) }
}

/// Verbatim copy of the crate's scalar Keccak-f[1600].
pub fn keccak_f1600(a: &mut [u64; 25]) {
    let mut round = 0;
    while round < 24 {
        let mut c = [0u64; 5];
        let mut x = 0;
        while x < 5 {
            c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let d = c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
            let mut y = 0;
            while y < 5 {
                a[x + 5 * y] ^= d;
                y += 1;
            }
            x += 1;
        }
        let mut b = [0u64; 25];
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(a[x + 5 * y], RHO[x + 5 * y]);
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
                y += 1;
            }
            x += 1;
        }
        a[0] ^= RC[round];
        round += 1;
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Variant 1: each scalar step becomes the same step with an innermost loop over the 4 lanes.

#[inline(always)]
fn rotl4(x: &[u64; 4], n: u32) -> [u64; 4] {
    let mut r = [0u64; 4];
    let mut l = 0;
    while l < 4 {
        r[l] = rotl(x[l], n);
        l += 1;
    }
    r
}

#[inline(always)]
pub fn body_v1(a: &mut [[u64; 4]; 25]) {
    let mut round = 0;
    while round < 24 {
        let mut c = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let r1 = rotl4(&c[(x + 1) % 5], 1);
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] ^= c[(x + 4) % 5][l] ^ r1[l];
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut b = [[0u64; 4]; 25];
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl4(&a[x + 5 * y], RHO[x + 5 * y]);
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] =
                        b[x + 5 * y][l] ^ (!b[(x + 1) % 5 + 5 * y][l] & b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}

// Variant 2: no helper returning arrays; every step is a pair of loops with the lane loop innermost, theta computes D
// in the lane loop (so the rotate by 1 is part of the vectorized expression).
#[inline(always)]
pub fn body_v2(a: &mut [[u64; 4]; 25]) {
    let mut round = 0;
    while round < 24 {
        let mut c = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut d = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                d[x][l] = c[(x + 4) % 5][l] ^ rotl(c[(x + 1) % 5][l], 1);
                l += 1;
            }
            x += 1;
        }
        let mut b = [[0u64; 4]; 25];
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    b[y + 5 * ((2 * x + 3 * y) % 5)][l] = rotl(a[x + 5 * y][l] ^ d[x][l], RHO[x + 5 * y]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] =
                        b[x + 5 * y][l] ^ (!b[(x + 1) % 5 + 5 * y][l] & b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}

#[inline(never)]
pub fn x4_v2_default(a: &mut [[u64; 4]; 25]) {
    body_v2(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v2_avx2(a: &mut [[u64; 4]; 25]) {
    body_v2(a)
}

#[inline(never)]
pub fn x4_v1_default(a: &mut [[u64; 4]; 25]) {
    body_v1(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v1_avx2(a: &mut [[u64; 4]; 25]) {
    body_v1(a)
}

// Variant 3 (generated by a script, not kept): fully unrolled round, state in 25 locals of type [u64; 4], rotate
// amounts are const generics. The upper bound for what portable code can reach.
type V = [u64; 4];
#[inline(always)]
fn xr(a: V, b: V) -> V {
    let mut r = [0u64; 4];
    let mut l = 0;
    while l < 4 {
        r[l] = a[l] ^ b[l];
        l += 1;
    }
    r
}
#[inline(always)]
fn rl<const M: u8, const N: u32>(a: V) -> V {
    let mut r = [0u64; 4];
    let mut l = 0;
    while l < 4 {
        r[l] = if N == 0 {
            a[l]
        } else if M == 0 {
            (a[l] << N) | (a[l] >> (64 - N))
        } else if M == 1 {
            (a[l] << N) ^ (a[l] >> (64 - N))
        } else {
            (a[l] << N).wrapping_add(a[l] >> (64 - N))
        };
        l += 1;
    }
    r
}
#[inline(always)]
fn chi(a: V, b: V, c: V) -> V {
    let mut r = [0u64; 4];
    let mut l = 0;
    while l < 4 {
        r[l] = a[l] ^ (!b[l] & c[l]);
        l += 1;
    }
    r
}
#[inline(always)]
fn iota(a: V, k: u64) -> V {
    let mut r = a;
    let mut l = 0;
    while l < 4 {
        r[l] ^= k;
        l += 1;
    }
    r
}

#[inline(always)]
pub fn body_v3<const M: u8>(st: &mut [[u64; 4]; 25]) {
    let mut a0 = st[0];
    let mut a1 = st[1];
    let mut a2 = st[2];
    let mut a3 = st[3];
    let mut a4 = st[4];
    let mut a5 = st[5];
    let mut a6 = st[6];
    let mut a7 = st[7];
    let mut a8 = st[8];
    let mut a9 = st[9];
    let mut a10 = st[10];
    let mut a11 = st[11];
    let mut a12 = st[12];
    let mut a13 = st[13];
    let mut a14 = st[14];
    let mut a15 = st[15];
    let mut a16 = st[16];
    let mut a17 = st[17];
    let mut a18 = st[18];
    let mut a19 = st[19];
    let mut a20 = st[20];
    let mut a21 = st[21];
    let mut a22 = st[22];
    let mut a23 = st[23];
    let mut a24 = st[24];
    let mut round = 0;
    while round < 24 {
        let c0 = xr(xr(xr(a0, a5), xr(a10, a15)), a20);
        let c1 = xr(xr(xr(a1, a6), xr(a11, a16)), a21);
        let c2 = xr(xr(xr(a2, a7), xr(a12, a17)), a22);
        let c3 = xr(xr(xr(a3, a8), xr(a13, a18)), a23);
        let c4 = xr(xr(xr(a4, a9), xr(a14, a19)), a24);
        let d0 = xr(c4, rl::<M, 1>(c1));
        let d1 = xr(c0, rl::<M, 1>(c2));
        let d2 = xr(c1, rl::<M, 1>(c3));
        let d3 = xr(c2, rl::<M, 1>(c4));
        let d4 = xr(c3, rl::<M, 1>(c0));
        let b0 = rl::<M, 0>(xr(a0, d0));
        let b16 = rl::<M, 36>(xr(a5, d0));
        let b7 = rl::<M, 3>(xr(a10, d0));
        let b23 = rl::<M, 41>(xr(a15, d0));
        let b14 = rl::<M, 18>(xr(a20, d0));
        let b10 = rl::<M, 1>(xr(a1, d1));
        let b1 = rl::<M, 44>(xr(a6, d1));
        let b17 = rl::<M, 10>(xr(a11, d1));
        let b8 = rl::<M, 45>(xr(a16, d1));
        let b24 = rl::<M, 2>(xr(a21, d1));
        let b20 = rl::<M, 62>(xr(a2, d2));
        let b11 = rl::<M, 6>(xr(a7, d2));
        let b2 = rl::<M, 43>(xr(a12, d2));
        let b18 = rl::<M, 15>(xr(a17, d2));
        let b9 = rl::<M, 61>(xr(a22, d2));
        let b5 = rl::<M, 28>(xr(a3, d3));
        let b21 = rl::<M, 55>(xr(a8, d3));
        let b12 = rl::<M, 25>(xr(a13, d3));
        let b3 = rl::<M, 21>(xr(a18, d3));
        let b19 = rl::<M, 56>(xr(a23, d3));
        let b15 = rl::<M, 27>(xr(a4, d4));
        let b6 = rl::<M, 20>(xr(a9, d4));
        let b22 = rl::<M, 39>(xr(a14, d4));
        let b13 = rl::<M, 8>(xr(a19, d4));
        let b4 = rl::<M, 14>(xr(a24, d4));
        a0 = iota(chi(b0, b1, b2), RC[round]);
        a1 = chi(b1, b2, b3);
        a2 = chi(b2, b3, b4);
        a3 = chi(b3, b4, b0);
        a4 = chi(b4, b0, b1);
        a5 = chi(b5, b6, b7);
        a6 = chi(b6, b7, b8);
        a7 = chi(b7, b8, b9);
        a8 = chi(b8, b9, b5);
        a9 = chi(b9, b5, b6);
        a10 = chi(b10, b11, b12);
        a11 = chi(b11, b12, b13);
        a12 = chi(b12, b13, b14);
        a13 = chi(b13, b14, b10);
        a14 = chi(b14, b10, b11);
        a15 = chi(b15, b16, b17);
        a16 = chi(b16, b17, b18);
        a17 = chi(b17, b18, b19);
        a18 = chi(b18, b19, b15);
        a19 = chi(b19, b15, b16);
        a20 = chi(b20, b21, b22);
        a21 = chi(b21, b22, b23);
        a22 = chi(b22, b23, b24);
        a23 = chi(b23, b24, b20);
        a24 = chi(b24, b20, b21);
        round += 1;
    }
    st[0] = a0;
    st[1] = a1;
    st[2] = a2;
    st[3] = a3;
    st[4] = a4;
    st[5] = a5;
    st[6] = a6;
    st[7] = a7;
    st[8] = a8;
    st[9] = a9;
    st[10] = a10;
    st[11] = a11;
    st[12] = a12;
    st[13] = a13;
    st[14] = a14;
    st[15] = a15;
    st[16] = a16;
    st[17] = a17;
    st[18] = a18;
    st[19] = a19;
    st[20] = a20;
    st[21] = a21;
    st[22] = a22;
    st[23] = a23;
    st[24] = a24;
}

#[inline(never)]
pub fn x4_v3or_default(a: &mut [[u64; 4]; 25]) {
    body_v3::<0>(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v3or_avx2(a: &mut [[u64; 4]; 25]) {
    body_v3::<0>(a)
}

#[inline(never)]
pub fn x4_v3xor_default(a: &mut [[u64; 4]; 25]) {
    body_v3::<1>(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v3xor_avx2(a: &mut [[u64; 4]; 25]) {
    body_v3::<1>(a)
}

#[inline(never)]
pub fn x4_v3add_default(a: &mut [[u64; 4]; 25]) {
    body_v3::<2>(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v3add_avx2(a: &mut [[u64; 4]; 25]) {
    body_v3::<2>(a)
}

// Variants 4 and 5: the step intermediates live in a caller-provided scratch (so they stay in memory and every step
// ends in stores, which are the seeds the SLP vectorizer starts from). v4 keeps the loop form of v2; v5 is fully
// unrolled with constant indices and rotate amounts (generated).
pub struct Scratch {
    c: [[u64; 4]; 5],
    d: [[u64; 4]; 5],
    b: [[u64; 4]; 25],
    rho: [u32; 25],
    one: [u32; 5],
}
impl Scratch {
    pub fn new() -> Scratch {
        Scratch { c: [[0; 4]; 5], d: [[0; 4]; 5], b: [[0; 4]; 25], rho: RHO, one: [1; 5] }
    }
}

#[inline(always)]
pub fn body_v4(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    let mut round = 0;
    while round < 24 {
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                s.c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                s.d[x][l] = s.c[(x + 4) % 5][l] ^ rotl(s.c[(x + 1) % 5][l], 1);
                l += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    s.b[y + 5 * ((2 * x + 3 * y) % 5)][l] = rotl(a[x + 5 * y][l] ^ s.d[x][l], RHO[x + 5 * y]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] = s.b[x + 5 * y][l]
                        ^ (!s.b[(x + 1) % 5 + 5 * y][l] & s.b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}

#[inline(always)]
fn rot<const N: u32>(x: u64) -> u64 {
    if N == 0 { x } else { (x << N) | (x >> (64 - N)) }
}

#[inline(always)]
pub fn body_v5(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    let mut round = 0;
    while round < 24 {
        let mut l = 0;
        while l < 4 {
            s.c[0][l] = a[0][l] ^ a[5][l] ^ a[10][l] ^ a[15][l] ^ a[20][l];
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.c[1][l] = a[1][l] ^ a[6][l] ^ a[11][l] ^ a[16][l] ^ a[21][l];
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.c[2][l] = a[2][l] ^ a[7][l] ^ a[12][l] ^ a[17][l] ^ a[22][l];
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.c[3][l] = a[3][l] ^ a[8][l] ^ a[13][l] ^ a[18][l] ^ a[23][l];
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.c[4][l] = a[4][l] ^ a[9][l] ^ a[14][l] ^ a[19][l] ^ a[24][l];
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.d[0][l] = s.c[4][l] ^ rot::<1>(s.c[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.d[1][l] = s.c[0][l] ^ rot::<1>(s.c[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.d[2][l] = s.c[1][l] ^ rot::<1>(s.c[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.d[3][l] = s.c[2][l] ^ rot::<1>(s.c[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.d[4][l] = s.c[3][l] ^ rot::<1>(s.c[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[0][l] = rot::<0>(a[0][l] ^ s.d[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[16][l] = rot::<36>(a[5][l] ^ s.d[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[7][l] = rot::<3>(a[10][l] ^ s.d[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[23][l] = rot::<41>(a[15][l] ^ s.d[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[14][l] = rot::<18>(a[20][l] ^ s.d[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[10][l] = rot::<1>(a[1][l] ^ s.d[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[1][l] = rot::<44>(a[6][l] ^ s.d[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[17][l] = rot::<10>(a[11][l] ^ s.d[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[8][l] = rot::<45>(a[16][l] ^ s.d[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[24][l] = rot::<2>(a[21][l] ^ s.d[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[20][l] = rot::<62>(a[2][l] ^ s.d[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[11][l] = rot::<6>(a[7][l] ^ s.d[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[2][l] = rot::<43>(a[12][l] ^ s.d[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[18][l] = rot::<15>(a[17][l] ^ s.d[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[9][l] = rot::<61>(a[22][l] ^ s.d[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[5][l] = rot::<28>(a[3][l] ^ s.d[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[21][l] = rot::<55>(a[8][l] ^ s.d[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[12][l] = rot::<25>(a[13][l] ^ s.d[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[3][l] = rot::<21>(a[18][l] ^ s.d[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[19][l] = rot::<56>(a[23][l] ^ s.d[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[15][l] = rot::<27>(a[4][l] ^ s.d[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[6][l] = rot::<20>(a[9][l] ^ s.d[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[22][l] = rot::<39>(a[14][l] ^ s.d[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[13][l] = rot::<8>(a[19][l] ^ s.d[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            s.b[4][l] = rot::<14>(a[24][l] ^ s.d[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] = s.b[0][l] ^ (!s.b[1][l] & s.b[2][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[1][l] = s.b[1][l] ^ (!s.b[2][l] & s.b[3][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[2][l] = s.b[2][l] ^ (!s.b[3][l] & s.b[4][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[3][l] = s.b[3][l] ^ (!s.b[4][l] & s.b[0][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[4][l] = s.b[4][l] ^ (!s.b[0][l] & s.b[1][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[5][l] = s.b[5][l] ^ (!s.b[6][l] & s.b[7][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[6][l] = s.b[6][l] ^ (!s.b[7][l] & s.b[8][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[7][l] = s.b[7][l] ^ (!s.b[8][l] & s.b[9][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[8][l] = s.b[8][l] ^ (!s.b[9][l] & s.b[5][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[9][l] = s.b[9][l] ^ (!s.b[5][l] & s.b[6][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[10][l] = s.b[10][l] ^ (!s.b[11][l] & s.b[12][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[11][l] = s.b[11][l] ^ (!s.b[12][l] & s.b[13][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[12][l] = s.b[12][l] ^ (!s.b[13][l] & s.b[14][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[13][l] = s.b[13][l] ^ (!s.b[14][l] & s.b[10][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[14][l] = s.b[14][l] ^ (!s.b[10][l] & s.b[11][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[15][l] = s.b[15][l] ^ (!s.b[16][l] & s.b[17][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[16][l] = s.b[16][l] ^ (!s.b[17][l] & s.b[18][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[17][l] = s.b[17][l] ^ (!s.b[18][l] & s.b[19][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[18][l] = s.b[18][l] ^ (!s.b[19][l] & s.b[15][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[19][l] = s.b[19][l] ^ (!s.b[15][l] & s.b[16][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[20][l] = s.b[20][l] ^ (!s.b[21][l] & s.b[22][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[21][l] = s.b[21][l] ^ (!s.b[22][l] & s.b[23][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[22][l] = s.b[22][l] ^ (!s.b[23][l] & s.b[24][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[23][l] = s.b[23][l] ^ (!s.b[24][l] & s.b[20][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[24][l] = s.b[24][l] ^ (!s.b[20][l] & s.b[21][l]);
            l += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}

#[inline(never)]
pub fn x4_v4_default(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v4(a, s)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v4_avx2(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v4(a, s)
}

#[inline(never)]
pub fn x4_v5_default(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v5(a, s)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v5_avx2(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v5(a, s)
}

// Variant 6: every step is its own non-inlined function (so each SLP tree is tiny and isolated), the state moves
// through memory between steps. The rho/pi step is unrolled with constant rotate amounts.
#[inline(never)]
fn s6_theta_c(a: &[[u64; 4]; 25], c: &mut [[u64; 4]; 5]) {
    let mut x = 0;
    while x < 5 {
        let mut l = 0;
        while l < 4 {
            c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
            l += 1;
        }
        x += 1;
    }
}

#[inline(never)]
fn s6_theta_d(c: &[[u64; 4]; 5], d: &mut [[u64; 4]; 5]) {
    let mut x = 0;
    while x < 5 {
        let mut l = 0;
        while l < 4 {
            d[x][l] = c[(x + 4) % 5][l] ^ rotl(c[(x + 1) % 5][l], 1);
            l += 1;
        }
        x += 1;
    }
}

#[inline(never)]
fn s6_rho_pi(a: &[[u64; 4]; 25], d: &[[u64; 4]; 5], b: &mut [[u64; 4]; 25]) {
    let mut l = 0;
    while l < 4 {
        b[0][l] = rot::<0>(a[0][l] ^ d[0][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[16][l] = rot::<36>(a[5][l] ^ d[0][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[7][l] = rot::<3>(a[10][l] ^ d[0][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[23][l] = rot::<41>(a[15][l] ^ d[0][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[14][l] = rot::<18>(a[20][l] ^ d[0][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[10][l] = rot::<1>(a[1][l] ^ d[1][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[1][l] = rot::<44>(a[6][l] ^ d[1][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[17][l] = rot::<10>(a[11][l] ^ d[1][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[8][l] = rot::<45>(a[16][l] ^ d[1][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[24][l] = rot::<2>(a[21][l] ^ d[1][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[20][l] = rot::<62>(a[2][l] ^ d[2][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[11][l] = rot::<6>(a[7][l] ^ d[2][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[2][l] = rot::<43>(a[12][l] ^ d[2][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[18][l] = rot::<15>(a[17][l] ^ d[2][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[9][l] = rot::<61>(a[22][l] ^ d[2][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[5][l] = rot::<28>(a[3][l] ^ d[3][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[21][l] = rot::<55>(a[8][l] ^ d[3][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[12][l] = rot::<25>(a[13][l] ^ d[3][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[3][l] = rot::<21>(a[18][l] ^ d[3][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[19][l] = rot::<56>(a[23][l] ^ d[3][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[15][l] = rot::<27>(a[4][l] ^ d[4][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[6][l] = rot::<20>(a[9][l] ^ d[4][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[22][l] = rot::<39>(a[14][l] ^ d[4][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[13][l] = rot::<8>(a[19][l] ^ d[4][l]);
        l += 1;
    }
    let mut l = 0;
    while l < 4 {
        b[4][l] = rot::<14>(a[24][l] ^ d[4][l]);
        l += 1;
    }
}

#[inline(never)]
fn s6_chi_iota(b: &[[u64; 4]; 25], a: &mut [[u64; 4]; 25], rc: u64) {
    let mut x = 0;
    while x < 5 {
        let mut y = 0;
        while y < 5 {
            let mut l = 0;
            while l < 4 {
                a[x + 5 * y][l] = b[x + 5 * y][l] ^ (!b[(x + 1) % 5 + 5 * y][l] & b[(x + 2) % 5 + 5 * y][l]);
                l += 1;
            }
            y += 1;
        }
        x += 1;
    }
    let mut l = 0;
    while l < 4 {
        a[0][l] ^= rc;
        l += 1;
    }
}

#[inline(never)]
pub fn x4_v6_default(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    let mut round = 0;
    while round < 24 {
        s6_theta_c(a, &mut s.c);
        s6_theta_d(&s.c, &mut s.d);
        s6_rho_pi(a, &s.d, &mut s.b);
        s6_chi_iota(&s.b, a, RC[round]);
        round += 1;
    }
}

// Variant 7: v4 with the rotate amounts read from the (opaque) scratch, so they are loop-invariant variables
// instead of constants (the SLP cost of a variable-amount rotate is lower than that of a constant one).
#[inline(always)]
pub fn body_v7(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    let mut round = 0;
    while round < 24 {
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                s.c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let n = s.one[x];
            let mut l = 0;
            while l < 4 {
                s.d[x][l] = s.c[(x + 4) % 5][l] ^ rotl(s.c[(x + 1) % 5][l], n);
                l += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let n = s.rho[x + 5 * y];
                let mut l = 0;
                while l < 4 {
                    s.b[y + 5 * ((2 * x + 3 * y) % 5)][l] = rotl(a[x + 5 * y][l] ^ s.d[x][l], n);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] = s.b[x + 5 * y][l]
                        ^ (!s.b[(x + 1) % 5 + 5 * y][l] & s.b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}

#[inline(never)]
pub fn x4_v7_default(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v7(a, s)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v7_avx2(a: &mut [[u64; 4]; 25], s: &mut Scratch) {
    body_v7(a, s)
}

// Variant 8 (reference only, NOT the approach under test): hand-written AVX2 intrinsics, same step structure.
#[cfg(target_arch = "x86_64")]
pub mod intr {
    use super::RC;
    use core::arch::x86_64::*;

    #[target_feature(enable = "avx2")]
    #[inline]
    fn r<const N: i32, const M: i32>(x: __m256i) -> __m256i {
        _mm256_or_si256(_mm256_slli_epi64::<N>(x), _mm256_srli_epi64::<M>(x))
    }

    /// # Safety
    /// The CPU must support AVX2.
    #[target_feature(enable = "avx2")]
    pub unsafe fn keccak_f1600_x4_intrinsics(st: &mut [[u64; 4]; 25]) {
        // SAFETY: AVX2 is enabled for this function; the loads and stores are in bounds and unaligned-safe.
        unsafe {
            let mut a0 = _mm256_loadu_si256(st[0].as_ptr() as *const __m256i);
            let mut a1 = _mm256_loadu_si256(st[1].as_ptr() as *const __m256i);
            let mut a2 = _mm256_loadu_si256(st[2].as_ptr() as *const __m256i);
            let mut a3 = _mm256_loadu_si256(st[3].as_ptr() as *const __m256i);
            let mut a4 = _mm256_loadu_si256(st[4].as_ptr() as *const __m256i);
            let mut a5 = _mm256_loadu_si256(st[5].as_ptr() as *const __m256i);
            let mut a6 = _mm256_loadu_si256(st[6].as_ptr() as *const __m256i);
            let mut a7 = _mm256_loadu_si256(st[7].as_ptr() as *const __m256i);
            let mut a8 = _mm256_loadu_si256(st[8].as_ptr() as *const __m256i);
            let mut a9 = _mm256_loadu_si256(st[9].as_ptr() as *const __m256i);
            let mut a10 = _mm256_loadu_si256(st[10].as_ptr() as *const __m256i);
            let mut a11 = _mm256_loadu_si256(st[11].as_ptr() as *const __m256i);
            let mut a12 = _mm256_loadu_si256(st[12].as_ptr() as *const __m256i);
            let mut a13 = _mm256_loadu_si256(st[13].as_ptr() as *const __m256i);
            let mut a14 = _mm256_loadu_si256(st[14].as_ptr() as *const __m256i);
            let mut a15 = _mm256_loadu_si256(st[15].as_ptr() as *const __m256i);
            let mut a16 = _mm256_loadu_si256(st[16].as_ptr() as *const __m256i);
            let mut a17 = _mm256_loadu_si256(st[17].as_ptr() as *const __m256i);
            let mut a18 = _mm256_loadu_si256(st[18].as_ptr() as *const __m256i);
            let mut a19 = _mm256_loadu_si256(st[19].as_ptr() as *const __m256i);
            let mut a20 = _mm256_loadu_si256(st[20].as_ptr() as *const __m256i);
            let mut a21 = _mm256_loadu_si256(st[21].as_ptr() as *const __m256i);
            let mut a22 = _mm256_loadu_si256(st[22].as_ptr() as *const __m256i);
            let mut a23 = _mm256_loadu_si256(st[23].as_ptr() as *const __m256i);
            let mut a24 = _mm256_loadu_si256(st[24].as_ptr() as *const __m256i);
            let mut round = 0;
            while round < 24 {
                let c0 = _mm256_xor_si256(_mm256_xor_si256(_mm256_xor_si256(a0, a5), _mm256_xor_si256(a10, a15)), a20);
                let c1 = _mm256_xor_si256(_mm256_xor_si256(_mm256_xor_si256(a1, a6), _mm256_xor_si256(a11, a16)), a21);
                let c2 = _mm256_xor_si256(_mm256_xor_si256(_mm256_xor_si256(a2, a7), _mm256_xor_si256(a12, a17)), a22);
                let c3 = _mm256_xor_si256(_mm256_xor_si256(_mm256_xor_si256(a3, a8), _mm256_xor_si256(a13, a18)), a23);
                let c4 = _mm256_xor_si256(_mm256_xor_si256(_mm256_xor_si256(a4, a9), _mm256_xor_si256(a14, a19)), a24);
                let d0 = _mm256_xor_si256(c4, r::<1, 63>(c1));
                let d1 = _mm256_xor_si256(c0, r::<1, 63>(c2));
                let d2 = _mm256_xor_si256(c1, r::<1, 63>(c3));
                let d3 = _mm256_xor_si256(c2, r::<1, 63>(c4));
                let d4 = _mm256_xor_si256(c3, r::<1, 63>(c0));
                let b0 = _mm256_xor_si256(a0, d0);
                let b16 = r::<36, 28>(_mm256_xor_si256(a5, d0));
                let b7 = r::<3, 61>(_mm256_xor_si256(a10, d0));
                let b23 = r::<41, 23>(_mm256_xor_si256(a15, d0));
                let b14 = r::<18, 46>(_mm256_xor_si256(a20, d0));
                let b10 = r::<1, 63>(_mm256_xor_si256(a1, d1));
                let b1 = r::<44, 20>(_mm256_xor_si256(a6, d1));
                let b17 = r::<10, 54>(_mm256_xor_si256(a11, d1));
                let b8 = r::<45, 19>(_mm256_xor_si256(a16, d1));
                let b24 = r::<2, 62>(_mm256_xor_si256(a21, d1));
                let b20 = r::<62, 2>(_mm256_xor_si256(a2, d2));
                let b11 = r::<6, 58>(_mm256_xor_si256(a7, d2));
                let b2 = r::<43, 21>(_mm256_xor_si256(a12, d2));
                let b18 = r::<15, 49>(_mm256_xor_si256(a17, d2));
                let b9 = r::<61, 3>(_mm256_xor_si256(a22, d2));
                let b5 = r::<28, 36>(_mm256_xor_si256(a3, d3));
                let b21 = r::<55, 9>(_mm256_xor_si256(a8, d3));
                let b12 = r::<25, 39>(_mm256_xor_si256(a13, d3));
                let b3 = r::<21, 43>(_mm256_xor_si256(a18, d3));
                let b19 = r::<56, 8>(_mm256_xor_si256(a23, d3));
                let b15 = r::<27, 37>(_mm256_xor_si256(a4, d4));
                let b6 = r::<20, 44>(_mm256_xor_si256(a9, d4));
                let b22 = r::<39, 25>(_mm256_xor_si256(a14, d4));
                let b13 = r::<8, 56>(_mm256_xor_si256(a19, d4));
                let b4 = r::<14, 50>(_mm256_xor_si256(a24, d4));
                a0 = _mm256_xor_si256(b0, _mm256_andnot_si256(b1, b2));
                a1 = _mm256_xor_si256(b1, _mm256_andnot_si256(b2, b3));
                a2 = _mm256_xor_si256(b2, _mm256_andnot_si256(b3, b4));
                a3 = _mm256_xor_si256(b3, _mm256_andnot_si256(b4, b0));
                a4 = _mm256_xor_si256(b4, _mm256_andnot_si256(b0, b1));
                a5 = _mm256_xor_si256(b5, _mm256_andnot_si256(b6, b7));
                a6 = _mm256_xor_si256(b6, _mm256_andnot_si256(b7, b8));
                a7 = _mm256_xor_si256(b7, _mm256_andnot_si256(b8, b9));
                a8 = _mm256_xor_si256(b8, _mm256_andnot_si256(b9, b5));
                a9 = _mm256_xor_si256(b9, _mm256_andnot_si256(b5, b6));
                a10 = _mm256_xor_si256(b10, _mm256_andnot_si256(b11, b12));
                a11 = _mm256_xor_si256(b11, _mm256_andnot_si256(b12, b13));
                a12 = _mm256_xor_si256(b12, _mm256_andnot_si256(b13, b14));
                a13 = _mm256_xor_si256(b13, _mm256_andnot_si256(b14, b10));
                a14 = _mm256_xor_si256(b14, _mm256_andnot_si256(b10, b11));
                a15 = _mm256_xor_si256(b15, _mm256_andnot_si256(b16, b17));
                a16 = _mm256_xor_si256(b16, _mm256_andnot_si256(b17, b18));
                a17 = _mm256_xor_si256(b17, _mm256_andnot_si256(b18, b19));
                a18 = _mm256_xor_si256(b18, _mm256_andnot_si256(b19, b15));
                a19 = _mm256_xor_si256(b19, _mm256_andnot_si256(b15, b16));
                a20 = _mm256_xor_si256(b20, _mm256_andnot_si256(b21, b22));
                a21 = _mm256_xor_si256(b21, _mm256_andnot_si256(b22, b23));
                a22 = _mm256_xor_si256(b22, _mm256_andnot_si256(b23, b24));
                a23 = _mm256_xor_si256(b23, _mm256_andnot_si256(b24, b20));
                a24 = _mm256_xor_si256(b24, _mm256_andnot_si256(b20, b21));
                a0 = _mm256_xor_si256(a0, _mm256_set1_epi64x(RC[round] as i64));
                round += 1;
            }
            _mm256_storeu_si256(st[0].as_mut_ptr() as *mut __m256i, a0);
            _mm256_storeu_si256(st[1].as_mut_ptr() as *mut __m256i, a1);
            _mm256_storeu_si256(st[2].as_mut_ptr() as *mut __m256i, a2);
            _mm256_storeu_si256(st[3].as_mut_ptr() as *mut __m256i, a3);
            _mm256_storeu_si256(st[4].as_mut_ptr() as *mut __m256i, a4);
            _mm256_storeu_si256(st[5].as_mut_ptr() as *mut __m256i, a5);
            _mm256_storeu_si256(st[6].as_mut_ptr() as *mut __m256i, a6);
            _mm256_storeu_si256(st[7].as_mut_ptr() as *mut __m256i, a7);
            _mm256_storeu_si256(st[8].as_mut_ptr() as *mut __m256i, a8);
            _mm256_storeu_si256(st[9].as_mut_ptr() as *mut __m256i, a9);
            _mm256_storeu_si256(st[10].as_mut_ptr() as *mut __m256i, a10);
            _mm256_storeu_si256(st[11].as_mut_ptr() as *mut __m256i, a11);
            _mm256_storeu_si256(st[12].as_mut_ptr() as *mut __m256i, a12);
            _mm256_storeu_si256(st[13].as_mut_ptr() as *mut __m256i, a13);
            _mm256_storeu_si256(st[14].as_mut_ptr() as *mut __m256i, a14);
            _mm256_storeu_si256(st[15].as_mut_ptr() as *mut __m256i, a15);
            _mm256_storeu_si256(st[16].as_mut_ptr() as *mut __m256i, a16);
            _mm256_storeu_si256(st[17].as_mut_ptr() as *mut __m256i, a17);
            _mm256_storeu_si256(st[18].as_mut_ptr() as *mut __m256i, a18);
            _mm256_storeu_si256(st[19].as_mut_ptr() as *mut __m256i, a19);
            _mm256_storeu_si256(st[20].as_mut_ptr() as *mut __m256i, a20);
            _mm256_storeu_si256(st[21].as_mut_ptr() as *mut __m256i, a21);
            _mm256_storeu_si256(st[22].as_mut_ptr() as *mut __m256i, a22);
            _mm256_storeu_si256(st[23].as_mut_ptr() as *mut __m256i, a23);
            _mm256_storeu_si256(st[24].as_mut_ptr() as *mut __m256i, a24);
        }
    }
}

#[inline(always)]
fn rotm(x: u64, n: u32) -> u64 {
    (x << n) | (x >> ((64 - n) & 63))
}

// Variant 2a: v2 with a branch-free rotate. Variant 2c: also D fused into the rho/pi expression.
#[inline(always)]
pub fn body_v2a(a: &mut [[u64; 4]; 25]) {
    let mut round = 0;
    while round < 24 {
        let mut c = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut d = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                d[x][l] = c[(x + 4) % 5][l] ^ rotm(c[(x + 1) % 5][l], 1);
                l += 1;
            }
            x += 1;
        }
        let mut b = [[0u64; 4]; 25];
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    b[y + 5 * ((2 * x + 3 * y) % 5)][l] = rotm(a[x + 5 * y][l] ^ d[x][l], RHO[x + 5 * y]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] =
                        b[x + 5 * y][l] ^ (!b[(x + 1) % 5 + 5 * y][l] & b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}


#[inline(always)]
pub fn body_v2c(a: &mut [[u64; 4]; 25]) {
    let mut round = 0;
    while round < 24 {
        let mut c = [[0u64; 4]; 5];
        let mut x = 0;
        while x < 5 {
            let mut l = 0;
            while l < 4 {
                c[x][l] = a[x][l] ^ a[x + 5][l] ^ a[x + 10][l] ^ a[x + 15][l] ^ a[x + 20][l];
                l += 1;
            }
            x += 1;
        }
        let mut b = [[0u64; 4]; 25];
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    b[y + 5 * ((2 * x + 3 * y) % 5)][l] = rotm(a[x + 5 * y][l] ^ c[(x + 4) % 5][l] ^ rotm(c[(x + 1) % 5][l], 1), RHO[x + 5 * y]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                let mut l = 0;
                while l < 4 {
                    a[x + 5 * y][l] =
                        b[x + 5 * y][l] ^ (!b[(x + 1) % 5 + 5 * y][l] & b[(x + 2) % 5 + 5 * y][l]);
                    l += 1;
                }
                y += 1;
            }
            x += 1;
        }
        let mut l = 0;
        while l < 4 {
            a[0][l] ^= RC[round];
            l += 1;
        }
        round += 1;
    }
}


#[inline(never)]
pub fn x4_v2a_default(a: &mut [[u64; 4]; 25]) {
    body_v2a(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v2a_avx2(a: &mut [[u64; 4]; 25]) {
    body_v2a(a)
}

#[inline(never)]
pub fn x4_v2c_default(a: &mut [[u64; 4]; 25]) {
    body_v2c(a)
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn x4_v2c_avx2(a: &mut [[u64; 4]; 25]) {
    body_v2c(a)
}

/// 4 independent scalar permutations (what the crate does today).
#[inline(never)]
pub fn scalar4(a: &mut [[u64; 25]; 4]) {
    keccak_f1600(&mut a[0]);
    keccak_f1600(&mut a[1]);
    keccak_f1600(&mut a[2]);
    keccak_f1600(&mut a[3]);
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
pub fn scalar4_avx2(a: &mut [[u64; 25]; 4]) {
    keccak_f1600(&mut a[0]);
    keccak_f1600(&mut a[1]);
    keccak_f1600(&mut a[2]);
    keccak_f1600(&mut a[3]);
}
