//! Lab for plain-Rust 4-way Keccak variants. Every variant is a `#[target_feature(enable = "avx2")]` function
//! `fn(&mut [[u64; 4]; 25])` so that asm and timing can be compared; none of this is part of the crate.
#![allow(clippy::all, dead_code, unsafe_code)]

pub mod keccak {
    pub const RC: [u64; 24] = [
        0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
        0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
        0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
        0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
        0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
    ];
    pub const RHO: [u32; 25] = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14];
    fn rotl(x: u64, n: u32) -> u64 {
        if n == 0 { x } else { (x << n) | (x >> (64 - n)) }
    }
    /// Reference scalar permutation (same algorithm as the crate's).
    pub fn keccak_f1600(a: &mut [u64; 25]) {
        for r in 0..24 {
            let mut c = [0u64; 5];
            for x in 0..5 {
                c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
            }
            for x in 0..5 {
                let d = c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
                for y in 0..5 {
                    a[x + 5 * y] ^= d;
                }
            }
            let mut b = [0u64; 25];
            for x in 0..5 {
                for y in 0..5 {
                    b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(a[x + 5 * y], RHO[x + 5 * y]);
                }
            }
            for y in 0..5 {
                for x in 0..5 {
                    a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
                }
            }
            a[0] ^= RC[r];
        }
    }
}

pub mod keccak4 {
    include!(concat!(env!("OUT_DIR"), "/k4.rs"));
}

pub mod lanes;
pub mod v;
pub mod t;
pub mod rows;
