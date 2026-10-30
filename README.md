# ml-dsa-verified

A proof-first ML-DSA (FIPS 204) implementation in Rust, written so that it extracts cleanly to Lean (Charon/Aeneas) and can carry one end-to-end proof:

- KeyGen = FIPS 204 Algorithms 1/6
- Sign = Algorithms 2/7
- Verify = Algorithms 3/8
- stretch goal: Verify(pk, M, Sign(sk, M)) accepts for honestly generated keys

The code shape is one Rust function per FIPS 204 algorithm, with plain `while` loops over native arrays, no iterator chains or closures in the core, no operator-trait impls, and Keccak in-crate. It starts from a skeleton derived from RustCrypto's `ml-dsa` (MIT or Apache-2.0, see `LICENSE-*`), which is also used as the differential-test oracle.

Status: in progress, see `STATUS.md`. Nothing is proved yet.

`docs/` holds the design (`FORK-DESIGN.md`), the extraction survey of upstream master `a3690c4` (`SURVEY.md`) and the blocker list (`BLOCKERS.md`). They were written inside a larger verification campaign, so relative paths in them point outside this repo.

Not audited. Not for production use.
