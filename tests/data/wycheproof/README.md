# Wycheproof ML-DSA vectors (vendored, unmodified)

- Source: https://github.com/C2SP/wycheproof, directory `testvectors_v1/` (the nine `mldsa_{44,65,87}_{verify,sign_seed,sign_noseed}_test.json`
  files). Usage notes for these files: `doc/mldsa.md` in that repository.
- Commit: `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9` (commit date 2026-10-23), fetched 2026-10-30 with
  `git clone --depth 1 --filter=blob:none --sparse` and `git sparse-checkout set testvectors_v1`.
- License: Apache-2.0 (full text in `LICENSE-APACHE-WYCHEPROOF`, copied from the repository root).
- Each file is the upstream JSON, byte for byte, compressed with `gzip -9 -n`. SHA-256 of the uncompressed upstream files:

```
82191a3caf22c00a2c0686ca7e29dbf45b91b6d1c361bdd5687fb228d423d442  mldsa_44_sign_noseed_test.json
cc12df1c6c7dd5591195151ed2ae98708bf5de2df24bb06dc00b031f7c60b8cd  mldsa_44_sign_seed_test.json
f70759c95146ff3057ae9708438f6e8d25ba822e3af11d2e87bb20d9a9c39d0e  mldsa_44_verify_test.json
a83aa58a50bad259d34e0ad626e7eacd095ee7ae80d9717c4cbe1c765edd7223  mldsa_65_sign_noseed_test.json
e26b2bb9ab8d45ed570ba6828c7e40b6fa3e1545bb8bc2c449c77531760133e0  mldsa_65_sign_seed_test.json
1ca235f61928421a173a171780beb00264ae9155dc33c52a11e1766cc7979034  mldsa_65_verify_test.json
911e90bfc5a40e1ebed21580c079bb5e7233e6bd87a35fa285af5870ecfb79ad  mldsa_87_sign_noseed_test.json
6e801c2916fee64e71cd845928513726cdbfe688ef41be4544e472e4d8742c8e  mldsa_87_sign_seed_test.json
54adffe10f6dad7941ffd97f77ad4e5c85cb3a54d44cf5ce1c95cb1757b9ba14  mldsa_87_verify_test.json
```

## File kinds

- `*_verify_test.json`: groups with a `publicKey` (some deliberately 1 byte short or long) and tests `{msg, ctx?, sig, result, flags}`.
  Flags include `InvalidHintsEncoding`, `InfinityNormViolation`, `IncorrectSignatureLength`, `IncorrectPublicKeyLength`,
  `InvalidContext` (context longer than 255 bytes), `ZeroPublicKey`, `BoundaryCondition`, `ManySteps`, `ModifiedSignature`.
- `*_sign_seed_test.json`: groups with a 32-byte `privateSeed` (plus a few with a wrong-length seed) and tests
  `{msg?, ctx?, mu?, rnd?, sig, result, flags}`. `rnd` absent means deterministic (32 zero bytes).
- `*_sign_noseed_test.json`: the same with the expanded `privateKey` (skEncode bytes), including wrong-length keys and keys
  with out-of-range s1/s2 coefficients (`InvalidPrivateKey`).
- Tests flagged `Internal` carry only `mu` (the NIST M' values were not provided as message and context), so they can only
  be run through an external-mu signing interface, which this crate does not offer. The harnesses count them as skipped.

## Use

- Rust: `tests/wycheproof.rs` (`cargo test --release --test wycheproof -- --nocapture`).
- Lean specification: `scripts/gen-lean-wycheproof.py` generates `lean/SpecTests/WycheproofData.lean`, evaluated by
  `lean/SpecTests/Wycheproof.lean` (`lake build spec-wycheproof`).
