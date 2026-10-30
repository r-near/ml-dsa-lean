//! The three parameter sets and the sizes the harness needs.

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Set {
    S44,
    S65,
    S87,
}

pub const ALL_SETS: [Set; 3] = [Set::S44, Set::S65, Set::S87];

impl Set {
    pub fn level(self) -> i32 {
        match self {
            Set::S44 => 44,
            Set::S65 => 65,
            Set::S87 => 87,
        }
    }
    pub fn from_level(l: u32) -> Option<Set> {
        match l {
            44 => Some(Set::S44),
            65 => Some(Set::S65),
            87 => Some(Set::S87),
            _ => None,
        }
    }
    pub fn from_byte(b: u8) -> Set {
        ALL_SETS[(b % 3) as usize]
    }
    pub fn idx(self) -> usize {
        match self {
            Set::S44 => 0,
            Set::S65 => 1,
            Set::S87 => 2,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Set::S44 => "ML-DSA-44",
            Set::S65 => "ML-DSA-65",
            Set::S87 => "ML-DSA-87",
        }
    }
    pub fn pk_len(self) -> usize {
        match self {
            Set::S44 => 1312,
            Set::S65 => 1952,
            Set::S87 => 2592,
        }
    }
    pub fn sk_len(self) -> usize {
        match self {
            Set::S44 => 2560,
            Set::S65 => 4032,
            Set::S87 => 4896,
        }
    }
    pub fn sig_len(self) -> usize {
        match self {
            Set::S44 => 2420,
            Set::S65 => 3309,
            Set::S87 => 4627,
        }
    }
    /// Length of the commitment hash c̃ at the start of a signature.
    pub fn c_tilde_len(self) -> usize {
        match self {
            Set::S44 => 32,
            Set::S65 => 48,
            Set::S87 => 64,
        }
    }
    /// ω, the maximum number of ones in the hint.
    pub fn omega(self) -> usize {
        match self {
            Set::S44 => 80,
            Set::S65 => 55,
            Set::S87 => 75,
        }
    }
    pub fn k(self) -> usize {
        match self {
            Set::S44 => 4,
            Set::S65 => 6,
            Set::S87 => 8,
        }
    }
    pub fn l(self) -> usize {
        match self {
            Set::S44 => 4,
            Set::S65 => 5,
            Set::S87 => 7,
        }
    }
    pub fn eta(self) -> usize {
        match self {
            Set::S44 => 2,
            Set::S65 => 4,
            Set::S87 => 2,
        }
    }
    /// Signature layout: c̃ | z | hint (ω positions, then K cumulative counts).
    pub fn hint_start(self) -> usize {
        self.sig_len() - self.omega() - self.k()
    }
    pub fn counts_start(self) -> usize {
        self.sig_len() - self.k()
    }
    /// Bytes of one packed s1 or s2 polynomial in the secret key (3 bits per coefficient for η = 2, 4 for η = 4).
    pub fn eta_poly_bytes(self) -> usize {
        if self.eta() == 2 { 96 } else { 128 }
    }
    /// Offsets in sk = ρ(32) ‖ K(32) ‖ tr(64) ‖ s1 ‖ s2 ‖ t0.
    pub fn sk_s1_start(self) -> usize {
        128
    }
    pub fn sk_s2_start(self) -> usize {
        128 + self.l() * self.eta_poly_bytes()
    }
    pub fn sk_t0_start(self) -> usize {
        self.sk_s2_start() + self.k() * self.eta_poly_bytes()
    }
}
