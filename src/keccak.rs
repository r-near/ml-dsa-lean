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

/// Little-endian lane `data[i..i + 8]`. Requires `data.len() - i >= 8`.
fn load_lane(data: &[u8], i: usize) -> u64 {
    (data[i] as u64)
        | ((data[i + 1] as u64) << 8usize)
        | ((data[i + 2] as u64) << 16usize)
        | ((data[i + 3] as u64) << 24usize)
        | ((data[i + 4] as u64) << 32usize)
        | ((data[i + 5] as u64) << 40usize)
        | ((data[i + 6] as u64) << 48usize)
        | ((data[i + 7] as u64) << 56usize)
}

/// Writes the lane `x` little-endian to `out[i..i + 8]`. Requires `out.len() - i >= 8`.
fn store_lane(out: &mut [u8], i: usize, x: u64) {
    out[i] = x as u8;
    out[i + 1] = (x >> 8usize) as u8;
    out[i + 2] = (x >> 16usize) as u8;
    out[i + 3] = (x >> 24usize) as u8;
    out[i + 4] = (x >> 32usize) as u8;
    out[i + 5] = (x >> 40usize) as u8;
    out[i + 6] = (x >> 48usize) as u8;
    out[i + 7] = (x >> 56usize) as u8;
}

/// A SHAKE sponge with rate `rate` bytes (168 for SHAKE128, 136 for SHAKE256).
///
/// Absorb and squeeze move whole 8-byte lanes whenever the position is lane aligned, a whole lane still fits in the
/// current block and at least 8 bytes of input (output) remain; otherwise they move one byte. The choice depends
/// only on `pos`, `rate` and the public lengths, never on the data.
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

    /// Whether a whole lane can be moved now: `remaining >= 8` bytes are left, the position is lane aligned and a
    /// lane still fits in the current block. Depends only on `pos`, `rate` and the public length.
    fn lane_fits(&self, remaining: usize) -> bool {
        remaining >= 8 && self.pos % 8 == 0 && self.rate - self.pos >= 8
    }

    /// Permutes and restarts the block once it is full. Absorbing calls it after each step, squeezing before each
    /// read, so the permutation after the last byte of a block is lazy when squeezing.
    fn wrap(&mut self) {
        if self.pos == self.rate {
            keccak_f1600(&mut self.state);
            self.pos = 0;
        }
    }

    fn xor_lane(&mut self, i: usize, x: u64) {
        self.state[i] ^= x;
    }

    pub fn absorb(&mut self, data: &[u8]) {
        let mut i = 0;
        while i < data.len() {
            if self.lane_fits(data.len() - i) {
                let x = load_lane(data, i);
                self.xor_lane(self.pos / 8, x);
                self.pos += 8;
                i += 8;
            } else {
                self.xor_byte(self.pos, data[i]);
                self.pos += 1;
                i += 1;
            }
            self.wrap();
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
            self.wrap();
            if self.lane_fits(out.len() - i) {
                store_lane(out, i, self.state[self.pos / 8]);
                self.pos += 8;
                i += 8;
            } else {
                out[i] = (self.state[self.pos / 8] >> (8 * (self.pos % 8))) as u8;
                self.pos += 1;
                i += 1;
            }
        }
    }
}
