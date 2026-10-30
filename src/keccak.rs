//! Keccak-f[1600] and the SHAKE128/SHAKE256 sponge (FIPS 202), in-crate and in plain loops.
//! FIPS 204 §3.7: H = SHAKE256, G = SHAKE128, used through Init/Absorb/Squeeze.

const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// ρ offsets indexed by x + 5y.
const RHO: [u32; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

fn rotl(x: u64, n: u32) -> u64 {
    if n == 0 { x } else { (x << n) | (x >> (64 - n)) }
}

/// Keccak-f[1600] on lanes A[x + 5y].
pub fn keccak_f1600(a: &mut [u64; 25]) {
    let mut round = 0;
    while round < 24 {
        // θ
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
        // ρ and π
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
        // χ
        let mut x = 0;
        while x < 5 {
            let mut y = 0;
            while y < 5 {
                a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
                y += 1;
            }
            x += 1;
        }
        // ι
        a[0] ^= RC[round];
        round += 1;
    }
}

/// A SHAKE sponge with rate `rate` bytes (168 for SHAKE128, 136 for SHAKE256).
pub struct Shake {
    state: [u64; 25],
    pos: usize,
    rate: usize,
}

impl Shake {
    pub fn shake128() -> Shake {
        Shake {
            state: [0; 25],
            pos: 0,
            rate: 168,
        }
    }
    pub fn shake256() -> Shake {
        Shake {
            state: [0; 25],
            pos: 0,
            rate: 136,
        }
    }

    fn xor_byte(&mut self, i: usize, b: u8) {
        self.state[i / 8] ^= (b as u64) << (8 * (i % 8));
    }

    pub fn absorb(&mut self, data: &[u8]) {
        let mut i = 0;
        while i < data.len() {
            self.xor_byte(self.pos, data[i]);
            self.pos += 1;
            if self.pos == self.rate {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
            i += 1;
        }
    }

    /// Pad (SHAKE domain 1111, then pad10*1) and switch to squeezing.
    pub fn finalize(&mut self) {
        self.xor_byte(self.pos, 0x1F);
        self.xor_byte(self.rate - 1, 0x80);
        keccak_f1600(&mut self.state);
        self.pos = 0;
    }

    pub fn squeeze(&mut self, out: &mut [u8]) {
        let mut i = 0;
        while i < out.len() {
            if self.pos == self.rate {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
            out[i] = (self.state[self.pos / 8] >> (8 * (self.pos % 8))) as u8;
            self.pos += 1;
            i += 1;
        }
    }
}
