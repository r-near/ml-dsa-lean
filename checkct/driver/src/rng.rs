// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright (c) 2024-2026 RustCrypto Developers
// Adapted from the constant-time harness in RustCrypto's ml-dsa crate (github.com/RustCrypto/signatures, ml-dsa/checkct,
// rev a3690c4, licensed Apache-2.0 OR MIT): the same hook pair (`__checkct_private_rand`,
// `__checkct_public_rand`) without the rand_core impls, which this dependency-free crate does not need.

//! Secret and public value sources for BINSEC. `__checkct_private_rand` and `__checkct_public_rand` are
//! the hook symbols the generated BINSEC scripts replace (private reads are marked secret). Same contract
//! as the RustCrypto checkct driver; the rand_core trait impls are dropped because this crate has no
//! dependencies.
#![allow(dead_code)]

#[unsafe(no_mangle)]
#[inline(never)]
pub fn __checkct_private_rand() -> u8 {
    unsafe { core::ptr::read_volatile(0xcafe as *const u8) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn __checkct_public_rand() -> u8 {
    unsafe { core::ptr::read_volatile(0xf00d as *const u8) }
}

pub struct PrivateRng;
pub struct PublicRng;

macro_rules! impl_rng {
    ($rng:ident, $rand:ident) => {
        impl $rng {
            pub fn next_u32(&mut self) -> u32 {
                u32::from_be_bytes([$rand(), $rand(), $rand(), $rand()])
            }
            pub fn next_u64(&mut self) -> u64 {
                ((self.next_u32() as u64) << 32) | (self.next_u32() as u64)
            }
            pub fn fill_bytes(&mut self, dest: &mut [u8]) {
                let mut i = 0;
                while i < dest.len() {
                    dest[i] = $rand();
                    i += 1;
                }
            }
        }
    };
}
impl_rng!(PrivateRng, __checkct_private_rand);
impl_rng!(PublicRng, __checkct_public_rand);
