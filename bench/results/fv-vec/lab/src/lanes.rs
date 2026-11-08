//! Alternative `Lanes4` instances over `[u64; 4]`, to probe what LLVM's SLP cost model dislikes.
use crate::keccak4::Lanes4;

macro_rules! lanes {
    ($name:ident, $rot:expr) => {
        pub struct $name;
        impl Lanes4 for $name {
            #[inline(always)]
            fn xor(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
                [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]]
            }
            #[inline(always)]
            fn andnot(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
                [!a[0] & b[0], !a[1] & b[1], !a[2] & b[2], !a[3] & b[3]]
            }
            #[inline(always)]
            fn rotl<const L: u32, const R: u32>(a: [u64; 4]) -> [u64; 4] {
                let f: fn(u64, u32, u32) -> u64 = $rot;
                [f(a[0], L, R), f(a[1], L, R), f(a[2], L, R), f(a[3], L, R)]
            }
            #[inline(always)]
            fn splat(x: u64) -> [u64; 4] {
                [x, x, x, x]
            }
        }
    };
}
// closures with `#[inline(always)]` semantic are fine here: they are inlined as plain fns
lanes!(LRotl, |x, l, _r| x.rotate_left(l));
lanes!(LXor, |x, l, r| (x << l) ^ (x >> r));
lanes!(LAdd, |x, l, r| (x << l).wrapping_add(x >> r));
lanes!(LNoRot, |x, _l, _r| x); // PROBE ONLY: wrong results

macro_rules! lanes_c {
    ($name:ident, |$l:ident| $keep:expr) => {
        pub struct $name;
        impl Lanes4 for $name {
            #[inline(always)]
            fn xor(a: [u64; 4], b: [u64; 4]) -> [u64; 4] { [a[0] ^ b[0], a[1] ^ b[1], a[2] ^ b[2], a[3] ^ b[3]] }
            #[inline(always)]
            fn andnot(a: [u64; 4], b: [u64; 4]) -> [u64; 4] { [!a[0] & b[0], !a[1] & b[1], !a[2] & b[2], !a[3] & b[3]] }
            #[inline(always)]
            fn rotl<const L: u32, const R: u32>(a: [u64; 4]) -> [u64; 4] {
                let $l = L;
                if $keep { [a[0].rotate_left(L), a[1].rotate_left(L), a[2].rotate_left(L), a[3].rotate_left(L)] } else { a }
            }
            #[inline(always)]
            fn splat(x: u64) -> [u64; 4] { [x, x, x, x] }
        }
    };
}
lanes_c!(LNoD, |l| l != 1);      // PROBE: theta's rotate-by-1 dropped
lanes_c!(LNoRho, |l| l == 1);    // PROBE: rho's rotates dropped
lanes_c!(LOnly8, |l| l == 8 || l == 56 || l == 1); // PROBE
