//! The variants. Naming: `<id>` is exported as `pub fn <id>(s: &mut [[u64;4];25])`, avx2-enabled, never inlined.
#[allow(unused_imports)]
use crate::keccak4::{Lanes4, Shim4, keccak_f1600_x4};

/// Current crate code, Shim4 instance.
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn shim(s: &mut [[u64; 4]; 25]) {
    keccak_f1600_x4::<Shim4>(s)
}

/// Current crate code, Avx2 intrinsics instance.
#[cfg(feature = "avx2")]
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2(s: &mut [[u64; 4]; 25]) {
    keccak_f1600_x4::<crate::keccak4::avx2::Avx2>(s)
}

/// 4 scalar permutations.
#[inline(never)]
pub fn scalar4(s: &mut [[u64; 4]; 25]) {
    let mut st = [[0u64; 25]; 4];
    for k in 0..25 {
        for i in 0..4 {
            st[i][k] = s[k][i];
        }
    }
    for i in 0..4 {
        crate::keccak::keccak_f1600(&mut st[i]);
    }
    for k in 0..25 {
        for i in 0..4 {
            s[k][i] = st[i][k];
        }
    }
}

use crate::keccak4::round;
use crate::keccak::RC;

type St = [[u64; 4]; 25];

/// `<name>`: the crate skeleton over lane instance `$l`; `<name>_noinl`: same but one round per out-of-line call
/// (so the stores to `dst` are real stores and SLP gets store seeds).
macro_rules! variant {
    ($name:ident, $noinl:ident, $l:ty) => {
        #[target_feature(enable = "avx2")]
        #[inline(never)]
        pub fn $name(s: &mut St) {
            keccak_f1600_x4::<$l>(s)
        }
        #[target_feature(enable = "avx2")]
        #[inline(never)]
        pub fn $noinl(s: &mut St) {
            #[target_feature(enable = "avx2")]
            #[inline(never)]
            fn rd(src: &St, dst: &mut St, rc: u64) {
                round::<$l>(src, dst, rc)
            }
            let mut t = *s;
            let mut r = 0;
            while r < 24 {
                rd(s, &mut t, RC[r]);
                rd(&t, s, RC[r + 1]);
                r += 2;
            }
        }
    };
}
variant!(shim_x, noinl, Shim4);
variant!(rotl_x, rotl_noinl, crate::lanes::LRotl);
variant!(xor_x, xor_noinl, crate::lanes::LXor);
variant!(add_x, add_noinl, crate::lanes::LAdd);
variant!(norot_x, norot_noinl, crate::lanes::LNoRot);
variant!(nod_x, nod_noinl, crate::lanes::LNoD);
variant!(norho_x, norho_noinl, crate::lanes::LNoRho);

mod gs {
    include!("gen_scalar.rs");
}

/// Rounds outer, states inner; per state: load 25 lanes, one scalar round, store (loop-vectorizer shape).
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn lv_copy(s: &mut St) {
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 {
            let mut a = [0u64; 25];
            let mut k = 0;
            while k < 25 {
                a[k] = s[k][i];
                k += 1;
            }
            let mut o = [0u64; 25];
            gs::rs(&a, &mut o, RC[r]);
            let mut k = 0;
            while k < 25 {
                s[k][i] = o[k];
                k += 1;
            }
            i += 1;
        }
        r += 1;
    }
}

/// Same with `for` loops.
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn lv_for(s: &mut St) {
    for r in 0..24 {
        for i in 0..4 {
            let mut a = [0u64; 25];
            for k in 0..25 {
                a[k] = s[k][i];
            }
            let mut o = [0u64; 25];
            gs::rs(&a, &mut o, RC[r]);
            for k in 0..25 {
                s[k][i] = o[k];
            }
        }
    }
}

/// Two rounds per state iteration (ping-pong a -> o -> a).
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn lv2(s: &mut St) {
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 {
            let mut a = [0u64; 25];
            let mut k = 0;
            while k < 25 {
                a[k] = s[k][i];
                k += 1;
            }
            let mut o = [0u64; 25];
            gs::rs(&a, &mut o, RC[r]);
            gs::rs(&o, &mut a, RC[r + 1]);
            let mut k = 0;
            while k < 25 {
                s[k][i] = a[k];
                k += 1;
            }
            i += 1;
        }
        r += 2;
    }
}

/// Four rounds per state iteration.
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn lv4(s: &mut St) {
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 {
            let mut a = [0u64; 25];
            let mut k = 0;
            while k < 25 {
                a[k] = s[k][i];
                k += 1;
            }
            let mut o = [0u64; 25];
            gs::rs(&a, &mut o, RC[r]);
            gs::rs(&o, &mut a, RC[r + 1]);
            gs::rs(&a, &mut o, RC[r + 2]);
            gs::rs(&o, &mut a, RC[r + 3]);
            let mut k = 0;
            while k < 25 {
                s[k][i] = a[k];
                k += 1;
            }
            i += 1;
        }
        r += 4;
    }
}

fn rotl_c(x: u64, n: u32) -> u64 {
    if n == 0 { x } else { (x << n) | (x >> (64 - n)) }
}
/// The loop body of the crate's `keccak_f1600`, as a function of one round constant (verbatim, `while` loops).
#[inline(always)]
pub fn round_loops(a: &mut [u64; 25], rc: u64) {
    let rho = &crate::keccak::RHO;
    let mut c = [0u64; 5];
    let mut x = 0;
    while x < 5 {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        x += 1;
    }
    let mut x = 0;
    while x < 5 {
        let d = c[(x + 4) % 5] ^ rotl_c(c[(x + 1) % 5], 1);
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
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl_c(a[x + 5 * y], rho[x + 5 * y]);
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
    a[0] ^= rc;
}

macro_rules! lv_loops {
    ($name:ident, $step:expr) => {
        #[target_feature(enable = "avx2")]
        #[inline(never)]
        pub fn $name(s: &mut St) {
            let mut r = 0;
            while r < 24 {
                let mut i = 0;
                while i < 4 {
                    let mut a = [0u64; 25];
                    let mut k = 0;
                    while k < 25 {
                        a[k] = s[k][i];
                        k += 1;
                    }
                    let mut j = 0;
                    while j < $step {
                        round_loops(&mut a, RC[r + j]);
                        j += 1;
                    }
                    let mut k = 0;
                    while k < 25 {
                        s[k][i] = a[k];
                        k += 1;
                    }
                    i += 1;
                }
                r += $step;
            }
        }
    };
}
lv_loops!(lvl1, 1);
lv_loops!(lvl2, 2);

/// Two explicit calls of the crate's loop-form round per state iteration (no inner `while j`).
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn lvl2b(s: &mut St) {
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 {
            let mut a = [0u64; 25];
            let mut k = 0;
            while k < 25 {
                a[k] = s[k][i];
                k += 1;
            }
            round_loops(&mut a, RC[r]);
            round_loops(&mut a, RC[r + 1]);
            let mut k = 0;
            while k < 25 {
                s[k][i] = a[k];
                k += 1;
            }
            i += 1;
        }
        r += 2;
    }
}

mod lane {
    include!("lane.rs");
}
macro_rules! lv_direct {
    ($name:ident, $f:ident, $n:expr) => {
        #[target_feature(enable = "avx2")]
        #[inline(never)]
        pub fn $name(s: &mut St) {
            let mut r = 0;
            while r < 24 {
                let mut i = 0;
                while i < 4 {
                    let mut rc = [0u64; $n];
                    let mut j = 0;
                    while j < $n {
                        rc[j] = RC[r + j];
                        j += 1;
                    }
                    lane::$f(s, i, rc);
                    i += 1;
                }
                r += $n;
            }
        }
    };
}
lv_direct!(ld1, lane_rounds_1, 1);
lv_direct!(ld2, lane_rounds_2, 2);
lv_direct!(ld4, lane_rounds_4, 4);

// ---- hypothesis 3: separate elementwise passes over memory-resident arrays (loop / SLP shape) ----
const PI_DST: [usize; 25] = {
    // b[y + 5*((2x+3y)%5)] = rot(a[x+5y]) : destination of source lane k = x + 5y
    let mut t = [0usize; 25];
    let mut x = 0;
    while x < 5 {
        let mut y = 0;
        while y < 5 {
            t[x + 5 * y] = y + 5 * ((2 * x + 3 * y) % 5);
            y += 1;
        }
        x += 1;
    }
    t
};
#[inline(always)]
fn round_pass(src: &St, dst: &mut St, rc: u64) {
    let mut c = [[0u64; 4]; 5];
    for x in 0..5 {
        for i in 0..4 {
            c[x][i] = src[x][i] ^ src[x + 5][i] ^ src[x + 10][i] ^ src[x + 15][i] ^ src[x + 20][i];
        }
    }
    let mut d = [[0u64; 4]; 5];
    for x in 0..5 {
        for i in 0..4 {
            d[x][i] = c[(x + 4) % 5][i] ^ c[(x + 1) % 5][i].rotate_left(1);
        }
    }
    let mut b = [[0u64; 4]; 25];
    for k in 0..25 {
        for i in 0..4 {
            b[PI_DST[k]][i] = (src[k][i] ^ d[k % 5][i]).rotate_left(crate::keccak::RHO[k]);
        }
    }
    for k in 0..25 {
        for i in 0..4 {
            dst[k][i] = b[k][i] ^ (!b[(k % 5 + 1) % 5 + 5 * (k / 5)][i] & b[(k % 5 + 2) % 5 + 5 * (k / 5)][i]);
        }
    }
    for i in 0..4 {
        dst[0][i] ^= rc;
    }
}
#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn passes(s: &mut St) {
    let mut t = *s;
    let mut r = 0;
    while r < 24 {
        round_pass(s, &mut t, RC[r]);
        round_pass(&t, s, RC[r + 1]);
        r += 2;
    }
}
