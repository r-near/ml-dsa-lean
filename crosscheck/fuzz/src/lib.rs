//! Shared fuzz-target code: input cursor, the base pool of valid (pk, m, ctx, sig) tuples and edit regions.
//!
//! Inputs are plain bytes with explicit flag bytes so that single-byte mutations stay meaningful; reading past
//! the end yields zeros, so every byte string is a valid input.
use std::sync::OnceLock;
use xc::oracle::{self, Imp};
use xc::Set;

pub use xc::cases::region_range as sig_region_range;

pub struct Cur<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cur<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Cur { data, pos: 0 }
    }
    pub fn u8(&mut self) -> u8 {
        let b = self.data.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        b
    }
    pub fn u16(&mut self) -> u16 {
        let lo = self.u8() as u16;
        lo | (self.u8() as u16) << 8
    }
    pub fn take(&mut self, n: usize) -> Vec<u8> {
        let mut v = vec![0u8; n];
        let start = self.pos.min(self.data.len());
        let end = (self.pos + n).min(self.data.len());
        v[..end - start].copy_from_slice(&self.data[start..end]);
        self.pos += n;
        v
    }
    pub fn blob(&mut self, cap: usize) -> Vec<u8> {
        let n = (self.u16() as usize).min(cap);
        self.take(n)
    }
    pub fn rest(&mut self) -> Vec<u8> {
        let start = self.pos.min(self.data.len());
        self.pos = self.data.len();
        self.data[start..].to_vec()
    }
}

/// The implementations to compare, fixed once per process.
pub fn imps() -> &'static [Imp] {
    static I: OnceLock<Vec<Imp>> = OnceLock::new();
    I.get_or_init(oracle::available)
}

pub fn pattern(n: usize, salt: u8) -> Vec<u8> {
    (0..n).map(|i| (i as u8).wrapping_mul(7).wrapping_add(salt)).collect()
}

pub struct Base {
    pub pk: Vec<u8>,
    pub msg: Vec<u8>,
    pub ctx: Vec<u8>,
    pub sig: Vec<u8>,
}

pub const POOL_SIZE: usize = 8;
const POOL_CTX_LEN: [usize; POOL_SIZE] = [0, 1, 255, 7, 0, 255, 32, 0];
const POOL_MSG_LEN: [usize; POOL_SIZE] = [0, 1, 33, 136, 300, 0, 5, 137];

/// Valid tuples per parameter set: keys from fixed seeds, signed by our crate (hedged for odd entries) and checked
/// once against every other implementation, so a broken pool cannot make the targets vacuous.
pub fn pool(set: Set) -> &'static [Base] {
    static P: [OnceLock<Vec<Base>>; 3] = [OnceLock::new(), OnceLock::new(), OnceLock::new()];
    P[set.idx()].get_or_init(|| {
        (0..POOL_SIZE)
            .map(|i| {
                let xi: [u8; 32] = std::array::from_fn(|j| (j as u8).wrapping_mul(31).wrapping_add(i as u8 * 17 + set.idx() as u8));
                let (pk, sk) = Imp::Ours.keygen(set, &xi);
                let msg = pattern(POOL_MSG_LEN[i], 3 * i as u8);
                let ctx = pattern(POOL_CTX_LEN[i], 5 * i as u8);
                let rnd: [u8; 32] = if i % 2 == 1 { std::array::from_fn(|j| (j + i) as u8) } else { [0; 32] };
                let sig = Imp::Ours.sign(set, &sk, &msg, &ctx, &rnd).sig().cloned().expect("pool: sign failed");
                for &imp in imps() {
                    assert!(imp.verify(set, &pk, &msg, &ctx, &sig).ok, "pool: {} rejects our signature", imp.name());
                }
                Base { pk, msg, ctx, sig }
            })
            .collect()
    })
}

/// Which byte range an edit region addresses, for a buffer of `len` bytes. Regions 0-4 address the signature (c̃, z,
/// hint positions, hint counts, anywhere), 5-6 the public key (ρ, t1), 7 anything.
pub fn region_range(set: Set, region: u8, len: usize) -> (usize, usize) {
    use xc::cases::Region;
    let (lo, hi) = match region % 8 {
        0 => sig_region_range(set, Region::CTilde),
        1 => sig_region_range(set, Region::Z),
        2 => sig_region_range(set, Region::HintPositions),
        3 => sig_region_range(set, Region::HintCounts),
        4 => sig_region_range(set, Region::Anywhere),
        5 => (0, 32),
        6 => (32, set.pk_len()),
        _ => (0, len),
    };
    let hi = hi.min(len);
    (lo.min(hi), hi)
}
