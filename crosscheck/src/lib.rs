//! Cross-implementation differential testing for `ml-dsa-lean`.
//!
//! Oracles (see `oracle::Imp`): our crate through its public `api`, RustCrypto `ml-dsa`, libcrux-ml-dsa (portable
//! and AVX2) and mldsa-native (portable C and AVX2). `cases` produces seeded random cases and mutations,
//! `check` runs a case through every available implementation and reports disagreements.
pub mod check;
pub mod cases;
pub mod mldsa_native;
pub mod oracle;
pub mod set;
pub mod undefined;

pub use set::Set;
