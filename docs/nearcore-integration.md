# nearcore integration notes

Notes from an outside reader of nearcore at cd5a94457 (2026-11-03), read-only; nothing in nearcore was built or run, and
the notes may be out of date or wrong for later commits. File:line cites are repo-relative paths into that tree. This
document lists facts and options; the decisions are nearcore's. `ml-dsa-lean` is an independent personal project, not
affiliated with or endorsed by NEAR, and nearcore is only an example of a consumer. Our side: `src/api.rs`,
`tools/stack/README.md`, `docs/assurance.md`.

## 0. Starting point: nearcore already ships ML-DSA-65

nearcore at this commit has ML-DSA-65 (FIPS 204) accepted in transactions and as access keys since protocol version
85, plus an `ml_dsa_verify` host function behind a config gate, all backed by `aws-lc-rs` 1.18.2
(`docs/architecture/how/post_quantum_signatures.md` lines 8–35; `Cargo.toml:143`, `Cargo.lock` for the version). ML-DSA-44
and ML-DSA-87 are not present. So this crate is not a first ML-DSA integration but a candidate alternative backend
for the existing ML-DSA-65 paths, and a possible source of 44/87 if nearcore ever wants them. Verification of the
existing 65 paths is consensus-critical: every node must return the same verdict for every (key, message, signature),
including malformed ones. The nearcore doc states the message is passed with an empty context string
(`post_quantum_signatures.md` §7), which is `ctx = &[]` in our `api`. Our crate's evidence that its Verify equals
the Lean transcription of FIPS 204's Verify on every input on which either returns (the transcription is trusted, not
the standard itself) is in `docs/assurance.md` §1.1; the verdict differential against aws-lc-rs 1.18.2
(`tests/awslc_diff.rs`, `docs/assurance.md` §5) found 0 differences in about 3.2M verify comparisons, incl. malformed
inputs, with ctx = "" as nearcore uses it. It is a test, not a proof about aws-lc. The §1.1 statement is about the portable
build; with the opt-in `avx2` feature, verify runs a 4-way body that is proved equal to the scalar one for a plain-Rust model
of its Keccak lane operations and tested equal for the AVX2 ones (`docs/assurance.md` §1.9), which matters for a
consensus-critical verdict (§4, §5 item 6).

## 1. Key and signature representation today

`core/crypto/src/signature.rs`:

| Item | Where | ML-DSA-65 detail |
|---|---|---|
| `KeyType { ED25519 = 0, SECP256K1 = 1, MLDSA65 = 2 }` | :39–43; `TryFrom<u8>` :81–92; strings `"ml-dsa-65"` :62, :75 | the only ML-DSA variant |
| Sizes | :20–31 | pk 1952, sk (raw) 4032, sig 3309, seed 32, handle 32 |
| `PublicKey::MLDSA65(MlDsa65PublicKey(Box<[u8; 1952]>))` | enum :248–255, `len()` :262–271 | boxed so the enum stays small (:149–151) |
| Borsh `PublicKey` | :398–425: 1-byte tag (`KeyTag`, :352) then raw bytes; tag 2 = full ML-DSA-65 key | 1 + 1952 bytes; tag 3 is rejected here (:422–425) |
| `PublicKeyHandle::MlDsa65(32-byte SHA3-256)` | :515–523, hash derivation :164–172 | the trie stores the hash, not the key (`trie_id_len` :326–337); domain tag `near:ml-dsa-65-pubkey-hash:v1` (`hash_domain.rs:9,15`) |
| `Signature::MLDSA65(MlDsa65Signature(Box<[u8; 3309]>))` | enum :1024–1028 | borsh = 1-byte `KeyType` (2) then 3309 bytes (:1131–1149, :1151–1180) |
| `SecretKey::MLDSA65(Box<[u8; 4032]>)` | :735–739; sign :783–794 | raw FIPS 204 private key; validated by `PqdsaKeyPair::from_raw_private_key` at parse (:898) |
| serde / `Display` / `FromStr` | `"ml-dsa-65:<bs58>"` for keys and signatures (:387, :1181–) | JSON is a string, borsh is binary |

Byte sizes for all three sets (FIPS 204 Table 2; ours are the `[u8; N]` types in `src/api.rs`):

| Set | pk | sk (expanded) | signature | borsh `PublicKey` (tag + pk) | borsh `Signature` (tag + sig) |
|---|---|---|---|---|---|
| ML-DSA-44 | 1312 | 2560 | 2420 | 1313 | 2421 |
| ML-DSA-65 | 1952 | 4032 | 3309 | 1953 | 3310 |
| ML-DSA-87 | 2592 | 4896 | 4627 | 2593 | 4628 |

**Where 44/87 would plug in** (if nearcore wanted them; each is a protocol decision): a new `KeyType` and `KeyTag` value
and string (:39, :81, :352, :62/:75), new variants in `PublicKey`, `PublicKeyHandle`, `Signature` and `SecretKey`
(each match is exhaustive by design, :49–53), new length constants, a hash domain tag per set (`hash_domain.rs`), the
`Signature::verify` arm (:1108–1111), `PublicKeyBuffer::new` for host-function key decoding
(`runtime/near-vm-runner/src/logic/logic.rs:172–`), `trie_id_len`, the `ProtocolSchema` hash cascade
(`post_quantum_signatures.md` Caveat 8), gas parameters, Rosetta and test utilities. The existing doc records that
borsh tags are permanent once a network accepts them (Caveat 1). For ML-DSA-65 alone, using this crate changes only the
function bodies: `Signature::verify` (:1108–1111, now `UnparsedPublicKey::new(&ML_DSA_65, pk).verify(data, sig)`),
`SecretKey::sign` (:783–794), `SecretKey::public_key` (:798–818) and seed derivation (`ml_dsa_65_secret_from_seed`, :844).
Our equivalents: `verify_65(&pk, m, &[], &sig)`, `sign_65(&sk, m, &[], &rnd)`, `keygen_65(&xi)`, all taking the boxed arrays by
reference without copying (`src/api.rs:287–307`, `:278–283`). `sign_65` takes `rnd` explicitly (32 random bytes or 32
zero bytes), which aws-lc-rs's `sign` hides, so deterministic-versus-hedged behavior must be chosen. One caveat for
`from_raw_private_key`-style validation: `sign_65` does not validate the key; `sk_is_well_formed_65` and `pk_from_sk_65`
are the optional checks (`docs/assurance.md` §1.5).

## 2. Where signatures are verified

All of these call `Signature::verify(data, &PublicKey) -> bool` (`signature.rs:1069`), so a backend swap behind that
function reaches every site. Validator keys are ed25519-only today (`is_valid_staking_key`,
`core/crypto/src/key_conversion.rs:6–12`; `post_quantum_signatures.md` §8), so block, chunk, approval and endorsement
verification never sees ML-DSA at this commit; the sites are listed because they would if validator keys changed.

| Site | Location |
|---|---|
| Transaction signature, on admission | `core/primitives/src/transaction.rs:339–343` (`ValidatedTransaction::new`); `validate_transaction` `runtime/runtime/src/verifier.rs:112–119`; run in parallel on rayon in `runtime/runtime/src/lib.rs:1999–2025`; `verify_transaction_signature` tries a list of keys, `transaction.rs:1208–1215` |
| Delegate actions (inner signer) | `core/primitives/src/action/delegate.rs:89`, `:213`; `runtime/runtime/src/actions.rs:453` |
| Block header | `core/primitives/src/block_header.rs:1740–1742`; `chain/chain/src/signature_verification.rs:78–85` |
| Chunk header | `chain/chain/src/signature_verification.rs:35–75` |
| Block approvals (one message, up to one signature per validator) | `chain/chain/src/approval_verification.rs`: the two verify calls are at `:33` and `:71`; each loop verifies the same `message_to_sign` against each approver's key |
| Chunk endorsements | `core/primitives/src/stateless_validation/chunk_endorsement.rs:88–97`, `:133–134` (V2 verifies two signatures); `core/primitives/src/spice/chunk_endorsement.rs:97`, `:178` |
| Partial witnesses, contract distribution | `stateless_validation/partial_witness.rs:73`, `:185`; `stateless_validation/contract_distribution.rs`: 8 `.verify(` call sites, at `:139`, `:210`, `:332`, `:459`, `:806`, `:879`, `:946`, `:1005` (the `verify_signature` wrappers at `:113`, `:138`, `:300`, `:413`, `:765` dispatch to them) |
| Generic validator signature | `chain/epoch-manager/src/adapter.rs:787–796` |
| Network (account data), on a rayon pool | `chain/network/src/accounts_data/mod.rs:235–300` via `chain/network/src/concurrency/rayon.rs:10–17` |
| Host functions | `ed25519_verify` `runtime/near-vm-runner/src/logic/host.rs:2028–`; `ml_dsa_verify` `:2261–2321` (65 only: `MlDsa65Signature`, `MlDsa65PublicKey`, length check, then `Signature::verify` at :2320) |

**Gas pattern of the host functions** (`host.rs:2259–2260`): `input_cost(sig) + input_cost(msg) + input_cost(pk) + base +
byte · message_len`. Parameters (`core/parameters/res/runtime_configs/parameters.yaml`): `ed25519_verify` base
210,000,000,000 and 9,000,000 per message byte (:215–216); `ml_dsa_verify` base 540,000,000,000 and 11,000,000 per
message byte (:220–221, "derived from measurements relative to ed25519"). The host function is gated by
`ml_dsa_verify_host_fn` (`parameters.yaml:350`, enabled in `87.yaml:14`, import list `imports.rs:162`).
Transaction-level ML-DSA-65 verification is charged at conversion as `ml_dsa_65_verification_cost` = 100 Ggas per
signature, including each `Delegate` action's inner signer (`parameters.yaml:404`, `core/primitives/src/fees.rs:624–668`;
rationale and the per-signature wording in `post_quantum_signatures.md` §6, which cites
mean ≈ 80 µs on aws-lc and says pricing must cover the worst observed case, Caveat 4). These costs were calibrated for aws-lc.
Changing backend changes the measured time (section 6 has our numbers, with aws-lc-rs measured in the same runs, but on
hardware that is not the machine behind the ≈ 80 µs figure), so the gas calibration would need re-measuring on one machine;
this is a nearcore decision.

## 3. Stack: nearcore's threads against our measured worst case

Our figures (`tools/stack/README.md`, release, x86_64, bytes below the caller's frame; ML-DSA-44 / 65 / 87):

| Call | KB |
|---|---|
| `verify_*` (one-shot) | 50 / 76 / 115 |
| `verify_prepared_*` | 34 / 45 / 59 |
| `verifying_key_*` (plus 20.5 / 36.9 / 65.6 KB key object in the caller's frame) | 31 / 52 / 26 |
| `sign_*` | 116 / 168 / 240 |
| `keygen_*` | 64 / 98 / 143 |
| debug (opt-level 0, with debug assertions; `cargo test` without `--release`) | see the next table |

Dev profile (opt-level 0), x86_64 painted, bytes, from the dev-profile column of the `tools/stack/README.md` results
table (release in parentheses; the ratio is not uniform, from 1.3 times for `sign_87` to 8.7 times for `verifying_key_87`):

| Call | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---|---|---|---|
| `verify_*` | 73,824 (49,576) | 103,008 (75,688) | 169,480 (115,112) |
| `sign_*` | 163,728 (115,704) | 228,480 (167,816) | 317,648 (239,784) |
| `keygen_*` | 93,440 (64,184) | 143,072 (98,040) | 221,856 (142,616) |
| `verifying_key_*` | 79,008 (31,112) | 133,280 (51,592) | 225,440 (25,976) |
| `signing_key_*` | 179,176 (59,960) | 286,696 (98,872) | 474,688 (164,424) |
| `verify_prepared_*` | 53,264 (34,216) | 66,064 (45,480) | 83,984 (58,792) |
| `sign_prepared_*` | 134,768 (73,384) | 180,064 (100,920) | 236,464 (133,976) |

The key constructors also place the returned key object in the caller's frame (20.5 / 36.9 / 65.6 KB for
`verifying_key_*`, 28.8 / 48.2 / 81.0 KB for `signing_key_*`). The largest dev-profile figure is `signing_key_87`,
about 475 KB below the caller's frame plus the 81 KB result slot.

Thread stacks found in nearcore (a grep for `stack_size`, `RUST_MIN_STACK` and thread builders over the whole tree
found only the two entries marked explicit; no `actix` appears in `Cargo.toml`):

| Thread | Stack | Where |
|---|---|---|
| rayon global pool (explicit) | 8 MiB | `neard/src/main.rs:58–60`; parallel transaction validation (:1999–2025 above) and `RayonAsyncComputationSpawner` (`core/async/src/futures.rs:171–176`) run on it unless a local pool is installed there (not checked) |
| compiler-daemon workers (explicit) | 8 MiB default (`DEFAULT_THREAD_STACK_SIZE_BYTES`), configurable: the parent passes `thread_stack_size_bytes` to the child in `COMPILER_DAEMON_STACK_SIZE_ENV` (`protocol.rs:10`, `parent.rs:94`, `:118`, `child.rs:94`) | `runtime/near-vm-runner/src/compiler_daemon/mod.rs:52`, `child.rs:47–49` (wasm compilation, not signatures) |
| Chunk-application workers (`apply_chunks_spawner`, `chain/chain/src/chain.rs:303`, `:461`; it was not traced whether the VM, and so `ml_dsa_verify`, runs on exactly these threads) | no `stack_size` call, so the std default (2 MiB, or `RUST_MIN_STACK`) | `ApplyChunksSpawner::Default` is `ThreadPool` (`core/async/src/thread_pool.rs:414–432`), whose workers on unix come from `thread_priority::ThreadBuilder` with name, policy and priority only (`:223–239`; the `std::thread::Builder` at :242–252 is the non-unix branch) |
| `StdThreadAsyncComputationSpawner` | std default | `core/async/src/futures.rs:155–160` |
| Actor runtimes: one tokio worker each | tokio default (2 MiB), no `thread_stack_size` | `core/async/src/tokio/runtime_handle.rs:117–120`, `core/async/src/tokio/futures.rs:12–15`, `neard/src/cli.rs:577–580` |
| Main thread | OS default (not set by nearcore) | |

Against a 2 MiB stack: Verify 65 uses 3.6%, Verify 87 5.5%, Sign 87 11.4% (240 KB; `tools/stack/README.md` "Notes for
nearcore" gives 11%). A 64 KB (65,536 B) stack fits none of Sign, KeyGen 65/87 or Verify 65/87; `keygen_44` (64,184 B)
fits with about 1.3 KB to spare, before any frame above the call, and Verify 44 (49,576 B) with about 16 KB. What is not measured: the frames
already on the stack when verification starts. For `ml_dsa_verify` those include the VM's own frames (wasmtime sets
`max_wasm_stack(1 GiB)` and relies on instrumented stack metering, `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:193`;
`max_stack_height` is 262,144, `parameters.yaml:303`) and async state machines, none of which this repository measured
(`tools/stack/README.md` says the same for a VM). If any call site runs on a thread with a reduced stack, the one-shot
`verify_*` frame is the large one; `verify_prepared_*` is about half.

## 4. Build configuration

- `[profile.release]`: `overflow-checks = true`, `panic = 'abort'`, `lto = "fat"`, `codegen-units = 1`
  (`Cargo.toml:388–392`). `dev-release` inherits it with `lto = false`, `codegen-units = 16`, `debug-assertions = true`
  (:395–399). Under the Aeneas model arithmetic overflow is a `fail`, and the `_exact` theorems say the extracted code never
  fails (`docs/assurance.md` §1.1), but the compiled code under overflow checks is only tested empirically:
  `scripts/ci.sh` steps `nearcore-test`, `nearcore-test-avx2` and `nearcore-test-zeroize` run the test suite (ACVP,
  Wycheproof, the differentials; the last one `tests/zeroize.rs` with the `zeroize` feature) with nearcore's release
  settings and its x86_64 rustflags, on 1.95.0, and `nearcore-build` checks that `-C overflow-checks=on` is on the crate's
  rustc line and that `target_feature="sse4.2"`, `"bmi2"`, `"lzcnt"` and `"movbe"` are in rustc's cfg. Both passed on a Linux machine on 2026-11-03,
  with and without the `avx2` feature. The step prints cargo's unit graph first: every unit is `opt=3 lto=fat cgu=1
  overflow_checks=True`; the library build unit is `panic=abort`, the test units are `panic=unwind` because cargo ignores
  `panic = "abort"` for test targets (so the tests exercise overflow checks, not the abort path). A passing run is an empirical
  check on those inputs, not a proof that no overflow can occur in the compiled code.
- Dev and test builds: `[profile.dev]` is `panic = 'abort'` (`Cargo.toml:385–386`). Per-package overrides give seven named
  crates `opt-level = 3` (`:408–421`) and **every other non-workspace dependency `opt-level = 1`** via
  `[profile.dev.package."*"]` (`:422–423`); cargo's `"*"` override does not apply to workspace members. `dev-release` is
  release without LTO (:395–399). So there are two cases for this crate in a dev or test build:
  1. As a registry or git dependency (a non-workspace package), it builds at `opt-level = 1`.
  2. Vendored as a workspace member (a path crate under the root `Cargo.toml` `members`, `:22`), the `"*"` override does
     not apply and it builds at the dev default, `opt-level = 0`. That is where the `zeroize` stack-residue scans fail
     and where the stacks are largest (the dev-profile table in section 3).

  Our stack figures are measured for release and for opt-level 0, not for 1. The `zeroize` feature's stack-residue tests
  (`tests/zeroize.rs`: 24 scan tests, eight per parameter set) pass in release (24 of 24) and at opt-level 0 fail for 21 of
  the 24 (everything except `signing_key_*`), finding copies of secrets in dead stack frames (Z-1 in `docs/assurance.md` §7).
  Run with `CARGO_PROFILE_DEV_OPT_LEVEL=1` (the whole crate and test at opt-level 1, which approximates case 1) 26 of the 28 tests
  of the file passed on a Linux x86_64 machine (`keygen_44` and `keygen_65` fail) and all 28 on an aarch64 macOS machine. `scripts/ci.sh` runs the 3 scans
  that pass at opt-level 0 in `test-zeroize` and all 24 in release (`test-zeroize-release`, and `nearcore-test-zeroize` under
  nearcore's profile). So the wipe behavior documented in `src/api.rs` should be read as a property of optimized builds on
  the measured toolchain; drop and the explicit wipes (`signing_key_*` drop, `Shake::wipe`, the decoded-key wipes) are not
  affected, which the `signing_key_drop_wipes` and `shake_wipe_zeroes_the_sponge` tests check, and they pass at opt-level 0
  and in release. A nearcore test run in its dev profile would not show the stack-residue results.
- x86_64 target features: `+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq`, plus
  `-Cforce-unwind-tables=y` (`.cargo/config.toml:9`; the profiling config adds frame pointers). **There is no `avx` or `avx2`**
  in that list. Our NTT is vectorized by LLVM only with AVX2, and the 4-way Keccak of the fast verify is an AVX2 kernel, so
  nearcore's build as it stands gets the `scalar` rows of section 6 (and of the benchmark table in `docs/assurance.md` §5). To get
  the AVX2 rows without changing nearcore's target features, nearcore would enable our opt-in `avx2` cargo feature: it checks
  the CPU at run time (a cached CPUID/XGETBV check) and dispatches the NTT, `verify_NN` and `verifying_key_NN` to AVX2 code, and
  runs the scalar code on a CPU without AVX2. The alternative, `-C target-cpu=x86-64-v3`, makes the binary require AVX2 and, for
  verify, was not reliably faster than the feature (section 6). Either is nearcore's decision. What the feature costs in
  assurance: the crate then has `unsafe` (the dispatch and the AVX2 lane operations), and the verify it runs is proved modulo
  the tested equivalence of the AVX2 lane operations to the proved plain-Rust model, with the dispatch glue, the CPU detection and
  the compiler's output for the AVX2 clone outside the proof (`docs/assurance.md` §1.9, §3, FV-1 in §7). Because the
  dispatch depends on the CPU, two validators with and without AVX2 would run different code for the same transaction; the two
  are tested equal (`tests/fast_verify.rs`: ACVP, Wycheproof and random inputs), not proved equal. `scripts/ci.sh` runs the
  tests with the feature under nearcore's flags (`nearcore-test-avx2`) and checks that the AVX2 body is compiled with AVX2
  (`avx2-inlining`). The CT results for the `nearcore` profile do not cover nearcore's exact build (`docs/assurance.md` §4).
- Toolchain: `rust-toolchain.toml:12` pins 1.95.0 with a comment not to bump past 1.87-era wasm behavior for contract
  developers (:6–10); workspace `rust-version = "1.95.0"`, edition 2024 (`Cargo.toml:4–5`). Our `rust-version` is 1.86
  (needed for safe `#[target_feature]`, `Cargo.toml` comment), edition 2024. `scripts/ci.sh` builds on 1.86.0 and on 1.95.0.
- Linting policy: nearcore's workspace `[lints.clippy]` denies correctness, suspicious and perf (`Cargo.toml:95–99`); nothing
  there forbids `unsafe`. Our crate has no `unsafe` unless `avx2` is on.
- `deny.toml`: licenses allow only MIT, Apache-2.0 and Apache-2.0 WITH LLVM-exception; `unknown-git = "deny"`;
  `multiple-versions = "deny"`. Our crate is `MIT OR Apache-2.0`, has no non-optional dependencies, and its optional one
  is `zeroize` (already in nearcore's lockfile; version compatibility not checked). The RustCrypto git dependency in our
  `[dev-dependencies]` is used only by our tests and is not part of a downstream's graph; `deny.toml` in this repo checks
  that graph (`scripts/ci.sh`, step `deny`).
- **wasm32:** nearcore does not appear to need this crate on wasm32. Contracts are separate crates (for example
  `runtime/near-test-contracts/test-contract-rs/Cargo.toml` depends on `base64` and `serde_json`, not `near-crypto`) and
  verify signatures through the host functions; `near-crypto` itself pulls in `aws-lc-rs` and `secp256k1`. The toolchain file installs the
  `wasm32-unknown-unknown` target (`rust-toolchain.toml:14`) for contract builds. Our crate is `no_std` and builds for wasm32
  (`scripts/ci.sh` steps `wasm32`, `wasm32-zeroize`, 1.95.0, `wasm32-unknown-unknown`, library only; both passed on 2026-11-03), so an in-contract verifier is possible, with the
  shadow-stack caveat in `tools/stack/README.md` (Verify 87 about 115 KB against rust-lld's 1 MiB default).

## 5. Public API and semver

`src/lib.rs` makes only `pub mod api` public; the other modules are public only under the `internals` feature, which is for
tests and fuzzing and is turned on by the crate's self dev-dependency (`Cargo.toml:29–37`). `Cargo.toml` has
`version = "0.1.0"` and `license = "MIT OR Apache-2.0"`.

Public surface of `api` (39 functions and 6 types, the same per set NN ∈ {44, 65, 87}; `src/api.rs`):

| Function | Signature shape |
|---|---|
| `keygen_NN(xi: &[u8; 32])` | `([u8; PK], [u8; SK])` |
| `sign_NN(sk, m: &[u8], ctx: &[u8], rnd: &[u8; 32])` | `Option<[u8; SIG]>` (`None`: `ctx.len() > 255` or κ budget exhausted) |
| `verify_NN(pk, m, ctx, sig)` | `bool` |
| `sign_internal_NN(sk, m_prime, rnd)`, `verify_internal_NN(pk, m_prime, sig)` | FIPS 204 Algorithms 7/8, M′ supplied by the caller |
| `verifying_key_NN(pk)`, `verify_prepared_NN(vk, m, ctx, sig)`, `verify_internal_prepared_NN` | `VerifyingKeyNN` (`Clone`; 20,544 / 36,928 / 65,600 B; private field) |
| `signing_key_NN(sk)`, `sign_prepared_NN(ssk, m, ctx, rnd)`, `sign_internal_prepared_NN` | `SigningKeyNN` (not `Clone`; 28,768 / 48,224 / 80,992 B; wipes on drop with `zeroize`) |
| `sk_is_well_formed_NN(sk)`, `pk_from_sk_NN(sk)` | `bool`, `Option<[u8; PK]>`; optional checks, not FIPS steps |

Cargo features: `zeroize` (optional dependency), `avx2` (x86_64 only), `internals` (not a supported surface).

What would need to stabilize, as options rather than recommendations:

1. **Version and metadata.** `0.1.0` promises nothing. Vendoring as a path or git dependency avoids publishing; publishing
   needs the `repository` field (a TODO placeholder in `Cargo.toml`) and a decision on the crate name.
2. **Naming and types.** The API is 3 × 13 free functions with literal array sizes in signatures and no exported length
   constants; options are to export `PK_LEN`/`SK_LEN`/`SIG_LEN` per set, to add newtypes, or to keep the arrays
   (they let near-crypto pass its `Box<[u8; N]>` contents by reference).
3. **Errors.** `sign_*` returns `Option` with two failure causes (|ctx| > 255, κ budget) folded into `None`; Verify returns `bool`.
   A typed error would be a breaking change later, so decide before 1.0.
4. **`*_internal_*` functions.** They expose M′ (Algorithms 7/8) and are not part of FIPS 204's external interface; they are
   `pub` for the Lean theorems and tests. Options: keep, or move behind a feature.
5. **Prepared-key types.** `VerifyingKeyNN` is `Clone` with a private field and size in the tens of KB (meant to be boxed);
   `SigningKeyNN` is deliberately not `Clone`. Whether these are public API or an implementation detail of a cache is open.
6. **Feature semantics.** `avx2` dispatches the NTT, `verify_NN` and `verifying_key_NN` at run time on a cached CPUID check and
   contains the only `unsafe`; its verify is proved equal to the scalar verify only modulo the tested equivalence of the AVX2 lane
   operations to the proved model (`docs/assurance.md` §1.9); `zeroize` changes `Drop` behavior; Cargo
   unifies features across a dependency graph, so enabling `internals` anywhere in the graph exposes panicking internals (E-1 in `docs/assurance.md` §7).
7. **Behavior contracts.** Verify returns `false` for malformed hint encodings and `ctx.len() > 255` (it equals the verdict of the Lean
   transcription of FIPS 204's Verify on every input on which either returns, `docs/assurance.md` §1.1); the possible non-termination of ExpandA/SampleInBall on adversarial input (probability
   negligible but not zero) is documented in `Divergence.lean`, not by a timeout. Sign can return `None`.
8. **MSRV.** 1.86 today; the policy for raising it is not written down.

## 6. Verify time, and the prepared verifying-key cache: the options and their numbers

**One-shot verify.** Measured with nearcore's `[profile.release]` settings and its x86_64 target features, on rustc 1.95.0
(nearcore's pinned toolchain), median of 15 rounds, one pinned core of an otherwise idle AMD EPYC 9B14 (Zen 4) virtual machine,
2026-11-07 (`bench/fast-verify.sh`; the setup, the rustc 1.99.1 numbers and the other implementations are in
`docs/assurance.md` §5 and `bench/results/2026-11-07-p3.md`). "Without the feature" is the proved scalar verify, which is what
nearcore's flags give today; "with `avx2`" is the opt-in feature (section 4).

| Verify, µs, rustc 1.95.0 | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---|---|---|---|
| this crate, without the `avx2` feature | 62.0 | 103.3 | 179.4 |
| this crate, with the `avx2` feature | 34.2 | 55.4 | 83.3 |
| aws-lc-rs 1.18.2 (the backend nearcore ships) | 22.7 | 36.5 | 56.5 |
| mldsa-native 2.0.0, AVX2 | 21.0 | 34.3 | 53.2 |

For ML-DSA-65, the only set nearcore has: 103.3 µs without the feature (2.8 times aws-lc-rs on this machine), 55.4 µs with it
(1.5 times). These were measured on one machine, not on the hardware behind nearcore's ≈ 80 µs aws-lc figure (§2), so they say
which backend is faster on this machine, not what the gas calibration should be. aws-lc-rs verifies faster than this crate in
every row. The same runs, in the columns used by the table in `docs/assurance.md` §5, give ML-DSA-65 verify of 103.8 and 54.0 µs
on rustc 1.99.1.

**Prepared key.** `verifying_key_NN(pk)` computes Â = ExpandA(ρ), NTT(t1·2^d) and tr once; `verify_prepared_NN` returns exactly what
`verify_NN` returns for that key (proved: `verify_prepared_NN_eq`, `docs/assurance.md` §1.4). Same runs:

| rustc 1.95.0, µs | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |
|---|---|---|---|
| `verifying_key_NN`, without / with `avx2` | 41.7 / 23.0 | 75.6 / 33.7 | 135.2 / 54.9 |
| `verify_prepared_NN`, without / with `avx2` | 20.5 / 17.0 | 27.9 / 22.1 | 40.9 / 33.0 |

`verify_prepared_NN` runs no ExpandA, so it is not dispatched to the 4-way body; its gain from the feature is the NTT dispatch.
A prepared-key verify (ML-DSA-65: 27.9 µs without the feature, 22.1 µs with it) is faster than aws-lc-rs's uncached verify
(36.5 µs), which matters only if nearcore holds prepared keys: the aws-lc-rs figure is `UnparsedPublicKey::new(..).verify(..)` on every call,
as nearcore calls it.
Building the key and verifying costs about what a one-shot verify costs (ML-DSA-65 with `avx2`: 33.7 + 22.1 = 55.8 µs against
55.4 µs).

Where a cache could apply in nearcore: any place the same public key verifies many signatures. Approval verification
runs one message over many validators' keys each block (`approval_verification.rs:33`, `:71`), but those keys are ed25519 today;
transactions from one ML-DSA account reuse its access key, but nearcore has the full 1952-byte key only on the wire, and the
trie holds only the 32-byte handle, which can serve as the cache key (`signature.rs:164–172`, hashing cost of one SHA3-256 over
the key). The cost side: a key object is 36,928 bytes (65) or 65,600 (87), so a cache must be bounded: an attacker
presenting many distinct keys makes each verification build a key (about the cost of one one-shot verify plus the memory churn),
never cheaper than not caching. Options: (a) no cache, one-shot `verify_65` only; (b) a bounded LRU keyed by the key handle;
(c) a per-epoch table for validator keys if those ever become ML-DSA. The hit rate on real traffic is unmeasured.

## 7. Things to check before any decision

- The differential of this crate against `aws-lc-rs` ML-DSA-65 Verify on valid, mutated and random inputs exists
  (`tests/awslc_diff.rs`, `docs/assurance.md` §5); rerun it against whichever aws-lc-rs version a deployment pins, since the
  verdict is consensus-critical.
- Re-measure verify time and the two gas parameters on one machine for both backends, including the worst-case signature
  shape nearcore's own benches probe (`core/crypto/benches/ml_dsa_worst_case.rs`); our numbers (section 6) used the benchmark
  inputs (256 messages of 64 bytes), not worst-case shapes.
- Whether to enable the `avx2` feature, given that its verify is proved modulo a tested link (section 4), and that validators with
  and without AVX2 then run different code for the same input.
- Frames above the call on the real threads (section 3), and whether any signature check runs on a reduced stack.
- If nearcore keeps aws-lc for 65 and wants 44 or 87: aws-lc-rs 1.18.2 supports all three sets, so adding sets does not
  require this crate. (A source comment in aws-lc-rs, `src/pqdsa/signature.rs:125–126`, reads "# FIPS" / "Approved for all
  supported algorithms: ML-DSA-44, ML-DSA-65, ML-DSA-87." That is aws-lc-rs's own statement; this repository does not
  assess or endorse it.) The case for this crate is the Lean evidence in `docs/assurance.md`, its portability (`no_std`, wasm32, no C toolchain) and the
  prepared-key API.
