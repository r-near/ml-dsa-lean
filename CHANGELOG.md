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
- With the `avx2` feature on x86_64, the prepared-key verify (`verify_prepared_NN`, `verify_internal_prepared_NN`) is also
  compiled with AVX2: a second `#[target_feature(enable = "avx2")]` wrapper (`verify_prepared_avx2`) around the same proved
  scalar function, reached after the same CPU check. No intrinsic, no new `unsafe` beyond the call into the wrapper, and no
  Lean statement or proof changed. ML-DSA-65 prepared-key verify takes 11.3 µs (was 14.9; ML-DSA-44 9.7, was 12.3;
  ML-DSA-87 15.3, was 20.3); one-shot verify and `verifying_key_NN` are unchanged (`bench/results/2026-11-07-p5.md`).
  `scripts/check-avx2-inlining.sh` now also requires ymm code inside each `verify_prepared_avx2` instantiation.
- With the `avx2` feature, the verify wrappers (`verify_internal_avx2`, `verify_prepared_avx2`, `prepare_vk_avx2`) realign their
  stack frames to 32 bytes (`align_frame` in `src/fast_verify/dispatch.rs`: a `#[repr(align(32))]` local passed to `black_box`),
  and `prepare_vk_avx2` builds the key in place instead of returning a 57 KB value. Before this, one-shot verify and
  `verifying_key_NN` were up to 7, 13 and 24 µs slower than their median (ML-DSA-44, 65, 87) at about one stack offset in seven:
  LLVM spilled the 4-way Keccak's vectors to 16-byte-aligned slots, and a slot straddling a 4 KiB page makes each access a page
  split. After it, the largest of 257 stack offsets is 1.02 to 1.03 times the median in every set and operation (rustc 1.99.1).
  ML-DSA-65 one-shot verify takes 41.8 µs (rustc 1.99.1) and 41.9 µs (1.95.0), at every offset (it was 42.4 at a fast offset),
  and `verifying_key_87` 51.8 µs (was 53.5); the prepared-key verify is unchanged. No Lean statement or proof changed; the source
  changes are in the dispatch glue only (`bench/results/2026-11-07-p6.md`, `docs/assurance.md` section 1.9).
- With the `avx2` feature, the one-shot verify and `verifying_key_NN` compute `tr = H(pk, 64)` in the fourth lane of the first
  groups of the 4-way ExpandA (three ExpandA entries per group, the SHAKE256 absorb of the key in the spare lane; what the lane
  does not reach is finished with the scalar permutation) instead of with the scalar permutation after ExpandA. Plain Rust inside
  the existing `Lanes4` surface; the dispatch wrappers are unchanged and nothing Sign or KeyGen calls changed. Lean proves it
  equal to ExpandA followed by `hash_pk` as `RustM` values for every key and all three parameter sets, for any group schedule
  (`Proofs.expand_a_tr_into_x4_eq`; `prepare_vk_x4_eq` keeps its statement; 28 more names in `lean/fast-verify-theorems.txt`, 79 in
  all). ML-DSA-65 one-shot verify takes 38.5 µs (rustc 1.99.1; 41.8 before) and 38.7 µs (1.95.0), ML-DSA-44 26.1 (was 26.5) and
  ML-DSA-87 60.8 µs (was 64.6); `verifying_key_65` 28.5 µs (was 32.2). The prepared-key verify is unchanged
  (`bench/results/2026-11-07-p7.md`, `docs/assurance.md` section 1.9). `tests/fast_verify_tr.rs` compares it with the scalar functions.
- The checkct driver includes the real `src/fast_verify.rs` instead of a hand-copied list of its re-exports.
- `bench/fast-verify.sh` ends with a stack-offset scan (`bench/stackscan.sh`; `bench/ab.sh` has a `PAD` knob and `scan` subcommands)
  that fails when any stack offset makes verify, `verifying_key` or the prepared-key verify more than 1.15 times slower than the
  median. `scripts/check-avx2-inlining.sh` now also requires that each verify wrapper realigns its frame.

## [0.1.0] - 2026-11-06

Initial release.

- Formally verified ML-DSA-44/65/87 key generation, signing and verification, proved in Lean to never panic and to match FIPS 204.
