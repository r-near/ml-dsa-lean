# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- With the `avx2` feature on x86_64, `verify_NN` and `verifying_key_NN` check the CPU at run time and use a 4-way body (4-way
  Keccak-f[1600], SHAKE128 and ExpandA) on a CPU with AVX2. Lean proves the body equal to the scalar verify on every input for its
  plain-Rust instance; the AVX2 lane operations it runs on are tested equal to that instance, not proved
  (`docs/assurance.md` section 1.9, `docs/limitations.md`). ML-DSA-65 verify takes 54.0 µs with it against 103.8 µs scalar under
  nearcore's flags with rustc 1.99.1 (`bench/results/2026-11-07-p3.md`); 43.1 µs with the verify-only arithmetic below
  (`bench/results/2026-11-07-p4.md`).
- Lean theorems for the 4-way verify (`lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt`), gated by
  `scripts/lean-check.sh`; `scripts/check-avx2-inlining.sh` and `bench/fast-verify.sh`.

### Changed

- Verify uses `poly_use_hint_pub` and `bit_unpack_pub`, plain-arithmetic versions of UseHint and the unpacking of `t1` and `z`,
  proved equal to the specification (5 more names in `lean/headline-theorems.txt`, 412 in all). The scalar verify is faster too.
- The `avx2` CPU check moved to `src/cpu.rs`, shared by the NTT and verify dispatch.
- Verify uses verify-only arithmetic on its public data (`src/verify_arith.rs`, `rounding::vec_norm_lt_pub`,
  `encode::bit_pack_pub`): a lazy-reduction NTT and NTT⁻¹, one fused multiply-accumulate row for Â ∘ NTT(z) − NTT(c) ∘
  NTT(t₁·2^d), a norm check without constant-time masks and a fixed-width w1Encode, each proved equal to the specification
  (`Proofs/NTTPub.lean`, `Proofs/VerifyArith.lean`; `lean/fast-verify-theorems.txt`). Signing and key generation are unchanged.
  ML-DSA-65 verify with the `avx2` feature takes 43.1 µs (was 54.0) and 88.2 µs without it (was 103.8), under nearcore's flags
  with rustc 1.99.1; ML-DSA-44 26.7 (was 35.5) and ML-DSA-87 64.9 µs (was 84.0). `tests/verify_arith.rs` compares each new function with
  its shared counterpart.

## [0.1.0] - 2026-11-06

Initial release.

- Formally verified ML-DSA-44/65/87 key generation, signing and verification, proved in Lean to never panic and to match FIPS 204.
