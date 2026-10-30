//! FIPS 204 Table 1, plus derived constants. `K`/`L` are const generics on every vector function;
//! a `Params` value carries the scalar parameters.

#[derive(Clone, Copy)]
pub struct Params {
    pub k: usize,
    pub l: usize,
    pub eta: u32,
    /// bitlen(2·η): 3 or 4
    pub eta_bits: usize,
    pub tau: usize,
    pub beta: u32,
    pub gamma1: u32,
    /// 1 + bitlen(γ1 − 1): 18 or 20
    pub gamma1_bits: usize,
    pub gamma2: u32,
    /// bitlen((q − 1)/(2γ2) − 1): 6 or 4
    pub w1_bits: usize,
    pub omega: usize,
    /// λ/4 bytes
    pub c_tilde_len: usize,
    /// Barrett constants for reduction modulo 2γ2 (shift = 2·(⌊log2 2γ2⌋+1), mult = ⌊2^shift / 2γ2⌋)
    pub two_gamma2_shift: u32,
    pub two_gamma2_mult: u64,
    /// ⌈2^48 / 2γ2⌉ for constant-time division
    pub two_gamma2_div_mult: u64,
}

pub const ML_DSA_44: Params = Params {
    k: 4,
    l: 4,
    eta: 2,
    eta_bits: 3,
    tau: 39,
    beta: 78,
    gamma1: 1 << 17,
    gamma1_bits: 18,
    gamma2: 95_232,
    w1_bits: 6,
    omega: 80,
    c_tilde_len: 32,
    two_gamma2_shift: 36,
    two_gamma2_mult: 360_800,
    two_gamma2_div_mult: 1_477_838_210,
};
pub const ML_DSA_65: Params = Params {
    k: 6,
    l: 5,
    eta: 4,
    eta_bits: 4,
    tau: 49,
    beta: 196,
    gamma1: 1 << 19,
    gamma1_bits: 20,
    gamma2: 261_888,
    w1_bits: 4,
    omega: 55,
    c_tilde_len: 48,
    two_gamma2_shift: 38,
    two_gamma2_mult: 524_800,
    two_gamma2_div_mult: 537_395_713,
};
pub const ML_DSA_87: Params = Params {
    k: 8,
    l: 7,
    eta: 2,
    eta_bits: 3,
    tau: 60,
    beta: 120,
    gamma1: 1 << 19,
    gamma1_bits: 20,
    gamma2: 261_888,
    w1_bits: 4,
    omega: 75,
    c_tilde_len: 64,
    two_gamma2_shift: 38,
    two_gamma2_mult: 524_800,
    two_gamma2_div_mult: 537_395_713,
};

pub const fn pk_len(p: &Params) -> usize {
    32 + 320 * p.k
}
pub const fn sk_len(p: &Params) -> usize {
    128 + 32 * ((p.k + p.l) * p.eta_bits + 13 * p.k)
}
pub const fn sig_len(p: &Params) -> usize {
    p.c_tilde_len + p.l * 32 * p.gamma1_bits + p.omega + p.k
}
