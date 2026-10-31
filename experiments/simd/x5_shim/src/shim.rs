//! Rust models ("shims") of 19 AVX2 operations, in the style of SymCrypt's `src/verify/intrinsics/x86_64/avx2.rs`:
//! a 256-bit register is eight u32 lanes (lane 0 = lowest dword), each operation is a plain loop transcribed from the
//! Intel intrinsics guide pseudocode, and nothing here uses `core::arch`. The kernel (`kernel.rs`) is written against
//! these names; a second module (`real.rs`) binds the same names to the real intrinsics.
//!
//! Immediate operands are const generics (as in `core::arch`). Everything is `#[inline(always)]` so that a kernel
//! compiled under `#[target_feature(enable = "avx2")]` gets them inlined.

pub type M256 = [u32; 8];

#[inline(always)]
pub fn set1_epi32(x: u32) -> M256 {
    [x; 8]
}

#[inline(always)]
pub fn setr_epi32(e0: u32, e1: u32, e2: u32, e3: u32, e4: u32, e5: u32, e6: u32, e7: u32) -> M256 {
    [e0, e1, e2, e3, e4, e5, e6, e7]
}

#[inline(always)]
pub fn add_epi32(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = a[i].wrapping_add(b[i]);
        i += 1;
    }
    r
}

#[inline(always)]
pub fn sub_epi32(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = a[i].wrapping_sub(b[i]);
        i += 1;
    }
    r
}

#[inline(always)]
pub fn mullo_epi32(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = a[i].wrapping_mul(b[i]);
        i += 1;
    }
    r
}

/// Signed 32 x 32 -> 64 multiply of the even dwords (0, 2, 4, 6); result qword k is the product of dwords 2k.
#[inline(always)]
pub fn mul_epi32(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let p = (a[2 * k] as i32 as i64) * (b[2 * k] as i32 as i64);
        r[2 * k] = p as u32;
        r[2 * k + 1] = (p >> 32) as u32;
        k += 1;
    }
    r
}

#[inline(always)]
pub fn and_si256(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = a[i] & b[i];
        i += 1;
    }
    r
}

/// Logical right shift of each qword by `IMM` bits (zero when `IMM > 63`).
#[inline(always)]
pub fn srli_epi64<const IMM: i32>(a: M256) -> M256 {
    let mut r = [0u32; 8];
    if IMM >= 0 && IMM < 64 {
        let mut k = 0;
        while k < 4 {
            let q = (a[2 * k] as u64) | ((a[2 * k + 1] as u64) << 32);
            let s = q >> (IMM as u32);
            r[2 * k] = s as u32;
            r[2 * k + 1] = (s >> 32) as u32;
            k += 1;
        }
    }
    r
}

/// Arithmetic right shift of each dword by `IMM` bits (sign fill when `IMM > 31`).
#[inline(always)]
pub fn srai_epi32<const IMM: i32>(a: M256) -> M256 {
    let mut r = [0u32; 8];
    let sh = if IMM >= 0 && IMM < 32 { IMM as u32 } else { 31 };
    let mut i = 0;
    while i < 8 {
        r[i] = ((a[i] as i32) >> sh) as u32;
        i += 1;
    }
    r
}

/// Signed compare greater-than: all ones where a > b.
#[inline(always)]
pub fn cmpgt_epi32(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = if (a[i] as i32) > (b[i] as i32) { 0xFFFF_FFFF } else { 0 };
        i += 1;
    }
    r
}

/// Within each 128-bit half, dword i of the result is dword `(MASK >> 2i) & 3` of the same half of `a`.
#[inline(always)]
pub fn shuffle_epi32<const MASK: i32>(a: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut h = 0;
    while h < 2 {
        let mut i = 0;
        while i < 4 {
            let sel = ((MASK >> (2 * i)) & 3) as usize;
            r[4 * h + i] = a[4 * h + sel];
            i += 1;
        }
        h += 1;
    }
    r
}

/// Qword j of the result is qword `(IMM >> 2j) & 3` of `a` (crosses the 128-bit halves).
#[inline(always)]
pub fn permute4x64_epi64<const IMM: i32>(a: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut j = 0;
    while j < 4 {
        let sel = ((IMM >> (2 * j)) & 3) as usize;
        r[2 * j] = a[2 * sel];
        r[2 * j + 1] = a[2 * sel + 1];
        j += 1;
    }
    r
}

/// Dword i of the result comes from `b` if bit i of `IMM` is set, else from `a`.
#[inline(always)]
pub fn blend_epi32<const IMM: i32>(a: M256, b: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = if (IMM >> i) & 1 == 1 { b[i] } else { a[i] };
        i += 1;
    }
    r
}

/// Dword i of the result is dword `idx[i] & 7` of `a` (crosses the 128-bit halves).
#[inline(always)]
pub fn permutevar8x32_epi32(a: M256, idx: M256) -> M256 {
    let mut r = [0u32; 8];
    let mut i = 0;
    while i < 8 {
        r[i] = a[(idx[i] & 7) as usize];
        i += 1;
    }
    r
}

/// Interleave the low qword of each 128-bit half of `a` and `b`.
#[inline(always)]
pub fn unpacklo_epi64(a: M256, b: M256) -> M256 {
    [a[0], a[1], b[0], b[1], a[4], a[5], b[4], b[5]]
}

/// Interleave the high qword of each 128-bit half of `a` and `b`.
#[inline(always)]
pub fn unpackhi_epi64(a: M256, b: M256) -> M256 {
    [a[2], a[3], b[2], b[3], a[6], a[7], b[6], b[7]]
}

#[inline(always)]
fn half(a: M256, b: M256, sel: i32) -> [u32; 4] {
    if (sel & 8) != 0 {
        return [0; 4];
    }
    let src = if (sel & 2) != 0 { b } else { a };
    let o = if (sel & 1) != 0 { 4 } else { 0 };
    [src[o], src[o + 1], src[o + 2], src[o + 3]]
}

/// Low half from `IMM & 0xF`, high half from `(IMM >> 4) & 0xF`: 0 = a.lo, 1 = a.hi, 2 = b.lo, 3 = b.hi, bit 3 = zero.
#[inline(always)]
pub fn permute2x128_si256<const IMM: i32>(a: M256, b: M256) -> M256 {
    let lo = half(a, b, IMM & 0xF);
    let hi = half(a, b, (IMM >> 4) & 0xF);
    [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
}

/// Load eight lanes from `mem[at..at + 8]` (the model of `_mm256_loadu_si256` on a slice-backed polynomial).
#[inline(always)]
pub fn loadu_si256(mem: &[u32; 256], at: usize) -> M256 {
    [mem[at], mem[at + 1], mem[at + 2], mem[at + 3], mem[at + 4], mem[at + 5], mem[at + 6], mem[at + 7]]
}

/// Store eight lanes to `mem[at..at + 8]` (the model of `_mm256_storeu_si256`).
#[inline(always)]
pub fn storeu_si256(mem: &mut [u32; 256], at: usize, v: M256) {
    mem[at] = v[0];
    mem[at + 1] = v[1];
    mem[at + 2] = v[2];
    mem[at + 3] = v[3];
    mem[at + 4] = v[4];
    mem[at + 5] = v[5];
    mem[at + 6] = v[6];
    mem[at + 7] = v[7];
}
