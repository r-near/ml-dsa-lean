# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

This section is the net change since 0.1.0. The branch went through a run-time AVX2 dispatch for verify on the way (rounds 1 to 11 of
`docs/assurance.md`, section 0); the last round removed it, so none of it ships.

### Added

- `verify_NN`, `verify_internal_NN` and `verifying_key_NN` run a 4-way body (4-way Keccak-f[1600], SHAKE128 and ExpandA, with `tr = H(pk, 64)` in the spare
  fourth lane of the first groups) in every build. It is plain Rust, proved equal to the scalar verify on every input, divergence included, in Lean
  (`docs/assurance.md` section 1.9, `lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt`); nothing selects it at run time and nothing is
  `cfg`'d: the public functions call it directly. One-shot verify for ML-DSA-44 / 65 / 87 takes 38.6 / 57.9 / 96.2 µs under nearcore's current flags (no AVX2) against
  52.5 / 88.4 / 152.6 µs for the scalar functions, and 26.1 / 38.4 / 60.7 µs with `-C target-feature=+avx,+avx2` added (AMD EPYC 9B14, rustc 1.99.1;
  `bench/results/2026-11-09-p12.md`). **The AVX2 numbers need AVX2 target features at compile time**; a binary built that way runs only on a CPU with AVX2.
- Verify-only arithmetic on public data (`src/verify_arith.rs`, `rounding::poly_use_hint_pub`, `rounding::vec_norm_lt_pub`, `encode::bit_unpack_pub`,
  `encode::bit_pack_pub`): a lazy-reduction NTT and NTT⁻¹, one fused multiply-accumulate row for Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁·2^d), UseHint and the unpacking of
  t1 and z in plain arithmetic, a norm check without constant-time masks and a fixed-width w1Encode, each proved equal to the specification
  (`Proofs/NTTPub.lean`, `Proofs/VerifyArith.lean`; 5 more names in `lean/headline-theorems.txt`, 412 in all). Signing and key generation are unchanged by it.
  `tests/verify_arith.rs` compares each function with its shared counterpart.
- Lean theorems for the 4-way verify: 6 names in `lean/keccak4-theorems.txt` and 79 in `lean/fast-verify-theorems.txt`, gated by `scripts/lean-check.sh`. The 4-way Keccak
  has no trait, no lane operation and no intrinsic: `keccak_f1600_x4` is a loop over four states around a straight-line scalar round, which LLVM vectorizes
  (256-bit with AVX2 target features, 128-bit without).
- Gates: `scripts/check-feature-independence.sh` extracts the crate twice, as it is and with `-C target-feature=+avx,+avx2`, and requires `lean/Impl` to be
  byte-identical (the whitelist is empty; it cannot pass vacuously: a probe crate shows that the second extraction really had the target feature, and the recorded
  flags must differ); a census of every `cfg` site in `src/` (`scripts/cfg_inventory.py`, token-aware, covering `cfg_if!`, `env!`, `include!`,
  `is_*_feature_detected!`, `#[path]`, `macro_rules!` and build scripts) against `scripts/cfg-inventory.txt`; a walk of the Lean environment from the verify entry points
  (`scripts/reachable-defs.sh`); `scripts/check-no-decls.sh` (no `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` or `extern` in `lean/Impl`,
  `lean/Spec` or `lean/Proofs`, with a self-test); a check of the theorem counts in the README; `scripts/ci-selftest.sh`; and `checkct/compare_code.py` rejects empty
  or truncated disassemblies. `scripts/check-avx2-inlining.sh` and `bench/fast-verify.sh` check performance only (256-bit permutation code, 32-byte aligned verify frames, a
  stack-offset scan `bench/stackscan.sh`).
- `verify_core` computes w′1 and its encoding in a `#[repr(align(32))]` `VerifyScratch` that it owns, which gives the functions that inline it a 32-byte aligned stack
  frame from an object the proved code uses (no code exists only in the compiled build).
- Extraction no longer leaves unreferenced `axiom` declarations in `lean/Impl/FunsExternal.lean` (`scripts/extract_hash.py` `clean_external`, with a self-test).

### Changed

- **The crate has no `unsafe` and detects nothing at run time.** `#![forbid(unsafe_code)]` holds in every configuration, `src/cpu.rs` and the NTT's AVX2 dispatch
  (`#[target_feature]` copies and a cached CPUID check, the `avx2` feature of 0.1.0) are gone, and `src/api.rs` has no token-passing call lines. The Cargo feature `avx2`
  stays as a deprecated no-op so that `features = ["avx2"]` still resolves; to get AVX2 code build with `-C target-feature=+avx2` or `-C target-cpu=x86-64-v3`.
  The residual of the proofs for verify is the base shared with 0.1.0 (the spec transcription, Charon/Aeneas, rustc/LLVM, the Lean kernel and the hardware): the CPU
  detection and its assumption, the 15 call lines and the 3 `unsafe` calls no longer exist.
- **Cost for users of the 0.1.0 `avx2` feature** (`bench/results/2026-11-09-p12.md`): with nearcore's flags and no AVX2 target features, Sign is 14 to 17 % slower
  (ML-DSA-65 hedged 342.9 → 402.6 µs) and KeyGen 2 to 6 % slower (ML-DSA-65 140.2 → 145.7 µs), because the AVX2 copy of the NTT is gone. With `+avx2` target features
  there is no difference beyond noise (-1.9 % to +1.1 %). Users who did not enable the feature see no change in Sign or KeyGen speed.
- The one-shot verify and `verifying_key_NN` use more stack: `verify_NN` 64 / 90 / 132 KB (was 45 / 71 / 111) and `verifying_key_NN` 50 / 74 / 111 KB (was 35 / 58 / 35);
  the ML-DSA-87 `verifying_key` figure includes a second copy of the key that the compiler does not elide (`bench/results/2026-11-09-p12.md`).
- The checkct driver includes the real `src/api.rs`; its `avx2` feature and the `dispatch` BINSEC profiles are gone.

## [0.1.0] - 2026-11-06

Initial release.

- Formally verified ML-DSA-44/65/87 key generation, signing and verification, proved in Lean to never panic and to match FIPS 204.
