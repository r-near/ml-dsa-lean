//! Thin public wrapper: fixed-size byte arrays per parameter set, delegating to the core.
//!
//! Planned (phase 1, wave 3): Algorithm 1 ML-DSA.KeyGen, Algorithm 2 ML-DSA.Sign and Algorithm 3
//! ML-DSA.Verify per parameter set. The external API builds the M′ prefix 0 ‖ |ctx| ‖ ctx in a stack
//! buffer (rejecting |ctx| > 255) and passes it with M to the `_internal` functions.

use crate::params::{ML_DSA_44, ML_DSA_65, ML_DSA_87};
use crate::sign::sign_internal;

pub fn sign_internal_44(sk: &[u8; 2560], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 2420]> {
    let mut sig = [0u8; 2420];
    if sign_internal::<4, 4>(&ML_DSA_44, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}
pub fn sign_internal_65(sk: &[u8; 4032], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 3309]> {
    let mut sig = [0u8; 3309];
    if sign_internal::<6, 5>(&ML_DSA_65, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}
pub fn sign_internal_87(sk: &[u8; 4896], m_prime: &[u8], rnd: &[u8; 32]) -> Option<[u8; 4627]> {
    let mut sig = [0u8; 4627];
    if sign_internal::<8, 7>(&ML_DSA_87, sk, &[], m_prime, rnd, &mut sig) {
        Some(sig)
    } else {
        None
    }
}
