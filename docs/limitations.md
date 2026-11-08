# Scope and limitations

The README states the result in one line. This page is exactly what that line covers and what it doesn't. The complete
version, with the exact theorem statements, the trusted base and the evidence for every claim, is
[assurance.md](assurance.md). nearcore, which the constant-time notes below use as a build profile, is only an
integration target studied here ([nearcore-integration.md](nearcore-integration.md); no affiliation).

## What the proof says

For every parameter set and every value of the argument types of `api::keygen_NN`, `api::sign_NN`, `api::verify_NN`,
their `_internal` variants and `api::pk_from_sk_NN`, and with no unproved premises, the extracted Rust code:

- never fails in the Aeneas model (no panic, arithmetic overflow or out-of-bounds access), and
- returns exactly what the Lean transcription of FIPS 204 returns, whenever either returns a result. The Rust can diverge
  exactly when the specification's rejection samplers never terminate on that input, which the proofs characterize but do not
  rule out. `sign_NN` returns `None` exactly for a context longer than 255 bytes or when the specification's bounded
  attempt loop (κ + ℓ ≤ 2¹⁶) is exhausted.

This is partial correctness plus absence of panics. For honestly generated keys, a separate theorem shows that Verify
accepts what Sign produces (its premises are named in [assurance.md](assurance.md)). The prepared-key functions are proved
equal to the one-shot ones. The theorems are checked with only the standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). `scripts/witness-check.sh` kernel-checks instances showing the premises are satisfiable, for one ML-DSA-44
input.

## What the proof does not say

- **It is about the Rust source as modeled by Aeneas.** Stack exhaustion, out-of-memory, rustc and LLVM, and the instruction
  set are trusted.
- **Extraction runs with `--cfg miri`**, so the proved code is the source with its `cfg(miri)` variants: the `black_box`
  barriers (`field::opaque_u32` and the RISC-V mask barrier) are the identity there, and the AVX2 dispatch is absent. Those
  are not in the proved code ([assurance.md](assurance.md) section 2).
- **The specification is trusted.** `lean/Spec` is our transcription of FIPS 204; the standard itself is not formalized. It
  has been cross-checked against test vectors and against ocaml-pq's independent transcription (proved equal in `xspec/`,
  with the qualifiers in [assurance.md](assurance.md) section 1.8: their Sign loop stops after 821 attempts, their key import
  rejects inconsistent keys that FIPS 204 accepts, and some directions assume their rejection samplers terminate).
- **The `zeroize` feature is outside the proof.**
- **The `avx2` feature is proved only modulo a tested link.** Without it, the code that ships is exactly the extracted code
  and the crate has `forbid(unsafe_code)`. With it on x86_64, `verify_NN` and `verifying_key_NN` check the CPU at run time and
  use a 4-way body (4-way Keccak-f[1600], SHAKE128 and ExpandA, with `tr = H(pk, 64)` hashed in a spare lane). Lean proves that body equal to the scalar verify on every
  input, divergence included, for its plain-Rust instance `Shim4` only (`lean/fast-verify-theorems.txt`,
  [assurance.md](assurance.md) section 1.9). The shipped AVX2 build runs the same body over intrinsic lane operations
  (`Avx2`), which are tested equal to `Shim4`, not proved (`tests/keccak4_avx2.rs`). So that build is proved modulo the tested
  equivalence of the AVX2 lane operations to the proved shim. Also outside the proof:
  - the dispatch glue (`src/fast_verify/dispatch.rs`) and the CPU and OS detection (`src/cpu.rs`);
  - rustc and LLVM compiling the `#[target_feature(enable = "avx2")]` clone of the body, which the proof does not see (a
    missed inlining would change only speed, and `scripts/check-avx2-inlining.sh` checks for that);
  - the AVX2 copy of the NTT, which is tested against the portable copy (`tests/dispatch.rs`), not proved.

  These make up the crate's only `unsafe`. A lane operation that differs from the shim on an input the tests missed, or a
  compiler error in the AVX2 clone, would let the AVX2 verdict differ from the proved one; the tests are evidence against
  that, not a proof.
- **HashML-DSA and external μ are not implemented.**
- **Constant time is not proved.** It is checked on compiled code with BINSEC (next section).
- **Not audited by any third party, not FIPS-validated, and not a certified module.**

## Constant time

BINSEC checks compiled probes of every secret-touching step of KeyGen and Sign (listed in `../checkct/README.md`), on x86_64
(several build profiles), thumbv7em, riscv32imac and AArch64 without NEON. No unexpected leak is open; three real ones were
found and fixed. The limits:

- Verify, including the AVX2 fast verify, handles only public data (public key, message, signature), so it has no probes and
  needs none. Sign and KeyGen do not call the 4-way body or the verify-only `poly_use_hint_pub` and `bit_unpack_pub`. The
  full sweep predates the fast verify and was not rerun on this tree (Sign and KeyGen code is unchanged since it). The harness
  (`../checkct/driver`) builds on this tree for every target and profile, and a small BINSEC run reproduced the sweep's verdicts
  for the probes it covered (assurance.md section 4).
- The whole KeyGen, Sign and `pk_from_sk` functions have no verdict, and the glue between steps is covered by code reading
  only. ExpandS is covered only through its per-nibble helper; its sampler loop branches on its public accept/reject
  outcome.
- BINSEC 0.11.3 cannot lift AVX/VEX instructions. Under nearcore's exact release build (`nearcore-exact`, where `+fma`
  implies AVX), 49 of 113 probes and both Sign censuses have no verdict (61 secure / 3 expected insecure / 0 unexpected /
  51 unknown, including the NTT, `hint_step`, `response`, `compute_t`, `prepare_sk` and `signing_key`). The same flags with
  the vectorizers off get a verdict for every probe, but that is a different binary. The AVX2 copy has no verdict either.
- AArch64 builds with NEON, and therefore macOS and Apple Silicon builds, have no BINSEC coverage.
- Some probes on other targets (riscv32imac `prepare_sk_*`, AArch64 `prepare_sk_*` and `signing_key_*`) and the whole-Sign
  censuses have no verdict.

Per-target counts: [assurance.md](assurance.md) section 4 and `../checkct/README.md`.

## Testing

Tests are evidence, not proofs.

- **Differential tests** against RustCrypto `ml-dsa`, `aws-lc-rs` (0 verdict differences in about 3.2M verify comparisons;
  empty context only), libcrux-ml-dsa and mldsa-native (`../crosscheck/`).
- **AVX2 fast verify** (needs a CPU with AVX2): the AVX2 lane operations, rotations and whole permutations against `Shim4`
  and the scalar permutation (`../tests/keccak4_avx2.rs`); the dispatched and AVX2 verify against the scalar verify on ACVP,
  Wycheproof and random inputs through every API path (`../tests/fast_verify.rs`).
- **Test vectors:** NIST ACVP (keyGen, sigGen, sigVer; the preHash and external-μ cases are skipped) and Wycheproof.
- **Fuzzing:** differential fuzz targets against RustCrypto (`../fuzz/`) and the other implementations.

## Known limitations

The full list is [assurance.md](assurance.md) section 7.

- **`zeroize`:** stack-residue wiping holds for optimized builds (release). The stack-residue scans fail at opt-level 0, except
  `signing_key_*`, and `keygen_44`/`keygen_65` fail at opt-level 1 on Linux (Z-1, open). Sign wipes the mask y and the other
  per-attempt secrets on every exit of an attempt (`src/api.rs` module docs). Not wiped by design: moves of returned
  structs, the signature (z, c̃, h of the accepted attempt), one copy of K and t0 in KeyGen, and anything skipped by a panic
  or `mem::forget`.
- **Malformed secret keys:** expanded secret keys with out-of-range coefficients are accepted by `sign_NN`, as FIPS 204
  specifies. Use `sk_is_well_formed_NN` (or `pk_from_sk_NN`) on untrusted keys (E-4).
- **`internals` feature:** the crate-private internals it exposes are meant for tests and can panic on wrong-length slices.
- **Stack use** is measured, not proved: Sign needs up to about 240 KB for ML-DSA-87 (`../tools/stack/README.md`).
- **Secret keys** are the 2560/4032/4896-byte expanded encoding, not the 32-byte seed.
