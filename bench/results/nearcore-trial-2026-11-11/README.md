# nearcore trial: `ml-dsa-lean` as the ML-DSA-65 backend (2026-11-11)

A local trial. Nothing here was sent to near/nearcore (no issue, PR or comment). `ml-dsa-lean` is an independent personal
project, not affiliated with or endorsed by NEAR. The question: can `ml-dsa-lean` 0.2.0 from crates.io replace `aws-lc-rs`
as nearcore's ML-DSA-65 backend, and what does that cost or break?

Scope of the proof claim that motivates the question: the crate's `verify`, `sign` and `keygen` are proved equal to a Lean
transcription of FIPS 204 (statement and trusted base: `docs/assurance.md` §1.1, `docs/limitations.md`). The transcription,
rustc/LLVM and the Aeneas extraction are trusted, not proved. This trial does not touch that claim; it measures integration.

## Bottom line

- **No technical blocker found at the function level.** The swap is one new module plus seven call-site edits in
  `core/crypto/src/signature.rs`; no change to `src/` or `lean/` of this repository was needed. nearcore builds with its own
  toolchain (1.95.0), release profile and target features. All 53 ML-DSA-named tests and the packages around them pass
  (857 of 857 selected tests on the new backend, 850 of 850 on aws-lc-rs before the swap; the 7 extra are the new differential
  tests). Keygen from a seed is byte-identical to aws-lc-rs, public keys, signatures and encodings have the same sizes and
  bytes, and 80,219 verify verdicts on mutated inputs agreed (0 differences).
- **What blocks adoption is a set of decisions, not code:**
  1. **Speed under nearcore's current flags.** One-shot verify is **1.54 times** aws-lc-rs (57.7 against 37.3 µs, best case
     of 30,000 alternating pairs on one core) because nearcore's `.cargo/config.toml` has no AVX2. With `+avx,+avx2` added it
     is **0.99 times** (37.1 against 37.3 µs). Adding AVX2 makes the binary require a CPU with AVX2; nobody ran that question
     against validator hardware.
  2. **Gas calibration.** Both host-function and transaction verify costs were calibrated on aws-lc. They would need
     re-measuring on one machine for either backend. Observation only; see "Gas".
  3. **Consensus risk of changing the verifier.** Every node must return the same verdict for every input. This trial's own
     comparison is 80k verdicts (plus the crate's earlier 3.2M, `docs/assurance.md` §5), not a soak on nearcore's
     CI or a mixed-version network.
  4. **Maturity.** 0.2.0, one maintainer, no certification of any kind (aws-lc makes its own FIPS claims; this crate makes none).
- **What does not block:** API and encoding fit, DER-SPKI/ctx handling, tests, stack (verify needs about 18 KiB more than
  aws-lc, 70 against 52 KiB), build, MSRV (1.86 against 1.95), dependency tree (+1 crate, no dependencies of its own).
- **What it does not give nearcore:** a C-toolchain-free build. `aws-lc-sys` stays in nearcore's tree through `rustls`
  (reqwest, hyper-rustls) even when `near-crypto` stops using it, and `rocksdb`, `jemalloc`, `zstd`, `lz4`, `secp256k1-sys`
  and `blst` need a C/C++ compiler anyway.

## What was run, where

| Item | Value |
|---|---|
| nearcore | `cd5a94457` (2026-11-03), clone `$NC`; `Cargo.lock` kept except +7 lines for `ml-dsa-lean` |
| Toolchain | rustc/cargo 1.95.0 (nearcore's `rust-toolchain.toml`), no overrides |
| Flags | nearcore's `.cargo/config.toml`: `-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y`, release profile (fat LTO, codegen-units 1, overflow checks, panic abort) |
| "+avx2" runs | the same list plus `,+avx,+avx2`, passed as `RUSTFLAGS` (which **replaces** the config file's flags, so the full list is repeated) |
| Machine | one Linux build VM, 30 vCPU AMD EPYC 9B14 (Zen 4, AVX2 and AVX-512), **shared with other users' jobs**: load average ranged from about 10 to 540 during the runs |
| Backends | default `aws-lc-rs` 1.18.2 (`aws-lc-sys` 0.46.0); `ml-dsa-lean` 0.2.0 from crates.io |

Because the machine was shared and often loaded, timing results use **alternating A/B calls in one process on one core** and
the **minimum and lower percentiles**, not means; the loaded-machine means and tails are kept in `raw/` but are not used for
conclusions. Absolute µs numbers are for this machine only.

## The patch (`nearcore.patch`, 679 lines, 475 added and 46 removed lines)

Apply with `git apply nearcore.patch` at `cd5a94457` (checked on a clean checkout). `probes.patch` (stack probes and the A/B
bench) applies on top of it; it is not part of the proposal.

| File | Change |
|---|---|
| `core/crypto/Cargo.toml` | optional `ml-dsa-lean = "0.2.0"`; feature `ml-dsa-lean`. `aws-lc-rs` stays a normal dependency and the default |
| `core/crypto/src/ml_dsa_backend.rs` (new) | the only file that names a signature library: `verify`, `sign`, `public_key`, `secret_from_seed`, `validate_secret`, `generate_secret`, plus `ML_DSA_65_BACKEND` ("aws-lc-rs" or "ml-dsa-lean"). The aws-lc code moved here unchanged |
| `core/crypto/src/signature.rs` | seven call sites now call the module (below); `ml_dsa_65_secret_from_keypair` removed |
| `core/crypto/src/lib.rs` | `mod ml_dsa_backend;` and the re-export of `ML_DSA_65_BACKEND` (only so tests and benches can print which backend is linked; droppable) |
| `core/crypto/tests/ml_dsa_backend_diff.rs` (new) | in-tree differential of both backends (only built with the feature, since it needs both) |
| `Cargo.lock` | one package entry and one dependency line |

Call sites in `signature.rs` (all of nearcore's ML-DSA crypto goes through them): `SecretKey::from_random`,
`SecretKey::sign`, `SecretKey::public_key`, `ml_dsa_65_secret_from_seed` (behind `ml_dsa_65_from_seed`, used by
`SecretKey::from_seed` in `test_utils.rs`), `SecretKey::from_str` (secret-key validation), `Signature::verify`.
`grep` for `aws_lc` finds no other use in the tree (outside `deny.toml` and a doc comment).

Everything else reaches ML-DSA only through `Signature::verify` or the `SecretKey` methods: transactions and delegate actions
(`ValidatedTransaction::new`, `verifier.rs`), the `ml_dsa_verify` host function (`runtime/near-vm-runner/src/logic/host.rs`,
which builds `MlDsa65Signature`/`MlDsa65PublicKey` from length-checked input and calls `Signature::verify`), block/chunk/
approval/endorsement verification (ed25519-only validator keys today, so they never see ML-DSA), the gas code
(`core/primitives/src/fees.rs`, `ml_dsa_65_verification_cost`; the parameter files; it charges and never calls crypto) and
the estimator (`MlDsaVerifyBase`, `MlDsaVerifyByte`, which run the host function inside a contract). **No wasm/no-std
constraint applies:** `near-crypto` is not built for wasm32 (it depends on C crates) and contracts use the host function.

How each semantic choice was made (each is a finding, F-5 to F-8 below):

- **Signing randomness.** aws-lc signs hedged. `ml-dsa-lean`'s `sign_65` takes `rnd`. The patch draws 32 bytes from the
  `OsRng` that `near-crypto` already uses when its `rand` feature is on, and uses 32 zero bytes (the deterministic variant of
  FIPS 204 Algorithm 2) when `rand` is off.
- **Secret-key validation at parse time** (`SecretKey::from_str`) uses `pk_from_sk_65(sk).is_some()`, not `sk_is_well_formed_65`.
- `sign_65` returns `None` (context too long, or the rejection-sampling budget is exhausted) and `pk_from_sk_65` returns
  `None` where aws-lc returned errors; both are mapped to the same `expect` panics the aws-lc code already had.
- Context string: nearcore signs and verifies with the empty context (aws-lc-rs has no context parameter); the patch passes `&[]`.

## Results

### Builds

| Check | Result |
|---|---|
| `cargo build --release --locked -p neard -p near-crypto --features near-crypto/ml-dsa-lean` | succeeds with nearcore's profile and flags (`neard` does not forward the feature, so `near-crypto` is listed as a package; forwarding through `neard`, `nearcore`, `near-primitives`, ... would be extra patch) |
| Backend really linked | `cargo tree --workspace --features near-crypto/ml-dsa-lean -e features -i ml-dsa-lean` lists `near-crypto` for the same invocation as the test run; the `ml-dsa-lean-0.2.0` source path appears in the lean `neard` binary and not in the aws one; every bench and estimator binary was checked the same way; `backend_is_lean` asserts `ML_DSA_65_BACKEND` |
| Release binary size | `neard`: 95,097,448 bytes (aws-lc-rs) against 95,220,232 (lean build, aws-lc-rs still linked as a dependency): +122,784 bytes, +0.13 % |
| Build time | not comparable: a full `neard` release build took 24:09 (aws) and 34:36 (lean) wall clock, but the box load differed by a large factor and `mbx` caches units. The one robust unit number (cargo `--timings`): the `ml-dsa-lean` library compiles in about 3.8 s |
| `clippy -D warnings` (`near-crypto`, all targets, both backends) and `rustfmt --check` | clean |
| `cargo deny`, `cargo machete` | not installed on the box, not run (licenses: `ml-dsa-lean` is MIT OR Apache-2.0, which `deny.toml` allows; it adds no second version of any crate) |

### Tests (nextest, `--cargo-profile dev-release --features test_features`, the flags of nearcore's own `Justfile` recipe)

Filter: all of `near-crypto`, `near-primitives`, `near-parameters`, `near-vm-runner`, plus any test whose name contains
`ml_dsa`, `mldsa`, `ml-dsa`, `MLDSA`, `pq_` or `post_quantum`, `combined_transactions_size_limit`, `universal_account`
(workspace build, so `test-loop-tests`, `node-runtime`, `near-client`, `near-mirror` and `near-rosetta-rpc` tests come along).
Not run: the rest of the workspace, `integration-tests` beyond the name filter, pytest/nayduck.

| Run | Result |
|---|---|
| Baseline, aws-lc-rs, unpatched checkout | 850 run, 850 passed |
| Patched, lean backend | **857 run, 857 passed** (the 7 added are `ml_dsa_backend_diff`) |
| Patched, default backend | `near-crypto` 37 of 37 passed (same count as baseline; the new test file is compiled out) |
| Patched, lean, plain `cargo test` dev profile (`near-crypto`) | 37 + 7 passed (the dev profile builds the dependency at opt-level 1) |

The 53 ML-DSA-named tests (list in the nextest output) include the unit tests, the 9 `ml_dsa_verify` host-function logic tests,
the 6 end-to-end VM tests, and the test-loop tests for access keys, gas charging and the activation boundary. The known-answer
test `test_ml_dsa_65_known_answer` pins the public key derived from the seed `kat-seed-v1`; it passes unchanged, which is
byte-identical KeyGen against the aws-lc-derived constant.
One thing the first run showed: nextest kills tests after 15 s unless their name starts with `slow_test`; the 80k-comparison
differential test is named accordingly.

### Compatibility (`core/crypto/tests/ml_dsa_backend_diff.rs`, output in `raw/differential.txt`)

| Question | Result |
|---|---|
| KeyGen from a 32-byte seed | 300 seeds (all-zero, all-0xff, 298 random): public and expanded secret keys byte-identical to `PqdsaKeyPair::from_seed` |
| Cross sign/verify | 1,200 signatures (40 keys, 10 message lengths 0 to 16 KiB, three signers: lean deterministic, lean hedged, aws-lc) accepted by both verifiers and by `Signature::verify` |
| Verify verdicts on bad input | 80,219 comparisons (bit flips in c̃, z, the hint section and the key, byte spans, fills, malformed hint encodings, random, zero and 0xff keys and signatures, wrong key, message changes), 248 of them valid: **0 differences**. This is a test, not an equivalence proof; the crate's larger run is 0 in about 3.22M comparisons against aws-lc-rs 1.18.2 (`docs/assurance.md` §5) |
| DER-SPKI public keys | aws-lc's `UnparsedPublicKey` first tries to parse a DER SubjectPublicKeyInfo, then the raw key. The ML-DSA-65 SPKI is **1,974 bytes**; aws-lc accepts it, this crate does not. nearcore only has 1,952-byte arrays (`MlDsa65PublicKey::try_from` and the host function both length-check), no 1,952-byte window of the SPKI is accepted as a different key, and a header-plus-truncated-key input is rejected by both. **Unreachable through nearcore's types**, so there is no mismatch to port |
| Context string | both empty; cross-verification above covers it |
| Lengths | identical (pk 1952, sk 4032, signature 3309, seed 32) |
| Raw secret-key acceptance (`SecretKey::from_str`) | aws-lc's `from_raw_private_key` accepts exactly the keys that are internally consistent (rho, tr, t0, s1, s2 recomputed from each other; K is free). On 5,743 inputs (single-bit flips of every region, 200 random keys, all-zero, all-0xff) `pk_from_sk_65(..).is_some()` agreed with aws-lc **in every case**; the cheaper `sk_is_well_formed_65` (range check only) accepted 4,845 of the 5,743 inputs that aws-lc rejects (every single-bit flip of rho, tr and t0, and most flips of s1 and s2), so it would be the wrong replacement |
| Error behavior | `verify` returns `false` on both for every malformed input tried (no panics); the 9+6 host-function tests (invalid lengths abort the contract, bad data returns 0) pass unchanged |
| Determinism | verify has no run-time CPU dispatch and no `unsafe` in this crate: the same compiled code gives the same verdict on every machine for one build. aws-lc's C code does not depend on Rust's target-feature flags (timings identical across the two flag sets) |
| Signing | hedged on both when `rand` is on (signatures differ per call); with `rand` off the lean backend signs deterministically (aws-lc always hedged) |

### Speed: aws-lc-rs against ml-dsa-lean, same machine

Three sources, all through nearcore's own code paths. `ratio` is lean divided by aws-lc, so 1.54 means 54 % slower.

**A. Alternating A/B, one process, one core (`probes.patch`, `core/crypto/tests/ab_bench.rs`; `raw/ab_bench.txt`).**
Each row is 30,000 alternating (aws, lean) call pairs over 64 keys. Three rounds per flag set; the ranges are over rounds.
`Signature::verify` adds only a `Box` dereference to the backend call, so the backend functions are timed directly.

| One-shot ML-DSA-65 verify (valid signature) | aws-lc-rs, µs (min / p25) | ml-dsa-lean, µs (min / p25) | ratio (min / p25) |
|---|---|---|---|
| nearcore's flags | 37.3 to 37.5 / 37.9 to 39.2 | **57.7** / 58.2 to 61.5 | **1.54 to 1.55** / 1.54 to 1.57 |
| nearcore's flags plus `+avx,+avx2` | 37.3 to 37.4 / 37.7 to 38.0 | **37.1 to 37.2** / 37.4 to 37.7 | **0.994 to 0.995** / 0.99 |

Wrong-message verify (full computation, then reject) is within 0.3 % of the valid case for both backends in every round, so
the "tampered" worst case costs the same as a valid verify. Not on the consensus path, measured the same way:

| | aws-lc-rs, µs (min) | ml-dsa-lean, µs (min), nearcore flags / +avx2 | ratio |
|---|---|---|---|
| Hedged sign | 53.6 | 164 / 148 | 3.06 / 2.75 |
| KeyGen from seed (incl. raw export) | 42.9 to 43.1 | 139 / 132 | 3.24 / 3.08 |

A malformed random signature (random 3,309 bytes) is rejected by this crate in 0.6 to 1.4 µs every time; aws-lc rejects the
fastest quarter in under 1.5 µs and has a median of about 30 µs. The cost of an attacker-chosen input is therefore bounded by the
full-verify cost on both, which is the tampered-message row.

**B. nearcore's `signatures` criterion bench** (`cargo bench -p near-crypto --bench signatures -- ml-dsa-65`, the bench
profile, seven interleaved passes per variant on the least busy core; box load 10 to 110 during these, so only the minimum is
meaningful; `raw/criterion_signatures.txt`): verify min **43.1** (aws, nearcore flags), **60.3** (lean), **38.2** (aws +avx2),
**39.4** (lean +avx2) µs; sign min 184 / 498 / 187 / 392 µs; keygen min 47 / 148 / 48 / 151 µs. The same ordering as A with
more noise (A shows 37.3 for the quiet-case aws figure).

**C. nearcore's estimator, in the VM** (`runtime-params-estimator --features required`, `--metric time --costs MlDsaVerifyBase`,
the contract `ml_dsa_verify_32b_500` that calls the host function 500 times, release builds of the estimator per backend and
flag set, nine interleaved rounds each; `raw/estimator.txt`). 1 µs is 1 Ggas in its output.

| `MlDsaVerifyBase`, µs (= Ggas) | median | min |
|---|---|---|
| aws-lc-rs, nearcore flags | 42.0 | 40.1 |
| ml-dsa-lean, nearcore flags | **62.4** | 62.1 |
| aws-lc-rs, +avx2 | 41.5 | 40.3 |
| ml-dsa-lean, +avx2 | **41.9** | 41.2 |

Medians give 1.49 (nearcore flags) and 1.01 (+avx2). The estimator marked every run `UNCERTAIN HIGH-VARIANCE` (it always does
for `--metric time`; production parameters come from the instruction-count metric). `MlDsaVerifyByte` (message hashing) came
out at a few Mgas per byte for both backends (parameter: 11 Mgas), too noisy to compare.

Other nearcore benches: `verify_distribution` and `ml_dsa_worst_case` ran for all four variants (`raw/verify_distribution_and_worst_case.txt`)
but their tails (p99.9, max) swing from 100 µs to 20 ms with the box load (one run during load 520), so no tail claim is made.
What they do show survives: lean verify time is flat in the hint weight (mean 42 to 43 µs for weights 36 to 51 with `+avx2`),
as nearcore's doc found for aws-lc.

#### Gas (observation only; no protocol change proposed)

| Parameter | Value | Reading |
|---|---|---|
| `wasm_ml_dsa_verify_base` | 540 Ggas | 12.9 times the estimator's wall-clock figure for aws-lc (42.0), 8.7 times for lean on nearcore flags (62.4), 12.9 times for lean +avx2 (41.9) |
| `ml_dsa_65_verification_cost` (transaction level) | 100 Ggas | covers "the extra over classical schemes" per nearcore's doc; the lean backend on nearcore's flags adds about 20 µs to one verify (57.7 against 37.3) |

The production parameters were derived from other measurements (`post_quantum_signatures.md` §6: mean about 80 µs on a
different CPU, plus margin), so the ratio to a wall-clock figure on this VM says how much slack exists here, not what is right.
A 1.5 times slower verify is within the 12.9 times gap on these numbers; whether that slack is meant to be spent, and how the
tail should be priced, is nearcore's call. With `+avx2` there is no slowdown to price.

### Stack (painted stack, `probes.patch`; `raw/stack_probes.txt`)

**The verify call itself** (`Signature::verify`, release with fat LTO and nearcore flags, bytes below the caller; worst of five calls):

| Call | aws-lc-rs | ml-dsa-lean |
|---|---|---|
| `Signature::verify` | 51.9 KiB | **70.3 KiB** (+18.4) |
| `SecretKey::sign` | 84.2 | 130.3 |
| `SecretKey::public_key` | 55.2 | 101.3 |
| `ml_dsa_65_from_seed` | 58.8 | 105.7 |
| `SecretKey::from_str` (validation) | 65.1 | 109.3 |
| `SecretKey::from_random` | 54.7 | 105.7 |

aws-lc's verify uses stack too (its ML-DSA allocates on the stack). Dev profile (`near-crypto` at opt-level 0, dependency at
opt-level 1): verify 47.1 against 82.3 KiB, sign 83.0 against 164.9 KiB. The crate's own figure for `verify_65` is 90 KB from a
static walk; the 70.3 here is the measured value in this build.

**Inside the VM** (the case that matters: a contract recurses, then calls the host function). Production config
(`max_stack_height` 262,144), Wasmtime with Winch, release build, painted stack, valid vector:

| Recursion depth (wasm frames) | native stack, no verify | with verify, aws-lc | with verify, ml-dsa-lean |
|---|---|---|---|
| 0 | 41.1 KiB | 79.8 | 102.3 |
| 1000 | 93.8 | 142.3 | 164.8 |
| 2000 | (not run) | 204.8 | **227.3** |
| 2500 and more | aborted by the VM before the call | aborted | aborted |

About 54 to 64 bytes of native stack per wasm frame; the VM aborts the contract (`HostError(MemoryAccessViolation)`; the
limit that trips was not traced) between 2,000 and 2,500 frames of this shape, at about 237 KiB of native stack used by the
contract. The call adds about 39 KiB (aws-lc) or 61 KiB (lean) at the point of the call.
Against nearcore's thread stacks (`docs/nearcore-integration.md` §3): the rayon pool that validates transactions has 8 MiB
(`neard/src/main.rs`), chunk-application and other pools use the std default of 2 MiB. The deepest case measured here,
227 KiB, is 11 % of 2 MiB. **Not measured:** the frames above the VM entry (runtime, async state) on those threads, and
contracts that use more native stack per accounted wasm frame than this simple recursion. So: verify fits with a wide margin on
every thread nearcore uses, with these two gaps open.

### Dependencies, MSRV, toolchain

| | |
|---|---|
| New crates in the tree | 1 (`ml-dsa-lean` 0.2.0, MIT OR Apache-2.0, **no dependencies** with default features; `near-crypto` goes from 121 to 122 `cargo tree` lines) |
| `aws-lc-rs` / `aws-lc-sys` | still in the tree: needed by `rustls` 0.23 (via `reqwest` 0.12/0.13, `hyper-rustls`, `rustls-platform-verifier`) independent of `near-crypto`, and kept as the default backend. Making `aws-lc-rs` optional would only help if every other user also left |
| C/C++ toolchain | still required (aws-lc-sys, rocksdb, jemalloc, zstd, lz4, secp256k1-sys, blst, ...) |
| MSRV | ml-dsa-lean 1.86; nearcore pins 1.95.0: no issue |
| `unstable` feature | `post_quantum_signatures.md` Caveat 3 notes that aws-lc-rs's ML-DSA API sits behind the `unstable` cargo feature; this crate's API is stable-channel 0.x semver |
| wasm | not applicable to nearcore (above); the crate itself builds `no_std` for wasm32 (`docs/nearcore-integration.md` §4) |

## Findings

1. **F-1, small surface.** One file (`core/crypto/src/signature.rs`) names the library; seven call sites. The patch's source
   change is 100 new lines (`ml_dsa_backend.rs`) plus 13 added and 46 removed in `signature.rs`, plus a 351-line test.
2. **F-2, feature shape.** `ml-dsa-lean` is a non-default additive feature, `aws-lc-rs` stays a normal dependency, so the
   default build is unchanged (37 of 37 tests). Cargo features unify across the workspace: building any binary with the
   feature on, anywhere, switches the backend for the whole binary. `neard` does not forward the feature (listed as a package
   in the build command above).
3. **F-3, all ML-DSA tests pass** on the new backend without edits (857 of 857 selected), including the host-function and
   test-loop tests; clippy and rustfmt clean.
4. **F-4, no encoding mismatch.** Same lengths, empty context, byte-identical KeyGen, cross-verifying signatures, DER-SPKI
   unreachable, no verdict difference in 80,219 mutated inputs.
5. **F-5, secret-key validation: use `pk_from_sk_65`.** It matches aws-lc's accept/reject on all 5,743 inputs tried;
   `sk_is_well_formed_65` is weaker and would accept keys aws-lc rejects.
6. **F-6, signing needs a randomness decision.** aws-lc hides `rnd`. The patch hedges when `near-crypto`'s `rand` feature is
   on and signs deterministically when it is off, a difference from aws-lc that nobody chose. `sign` can also panic through
   `expect` (context too long cannot happen here; rejection-sampling budget exhaustion has negligible probability). ML-DSA signing is not
   on the consensus path (validator keys are ed25519); it is used by tools, tests and wallets.
7. **F-7, secret hygiene not evaluated.** nearcore keeps the raw 4,032-byte key in a `Box` with no wipe either way. This crate's
   `zeroize` feature was not enabled or tested; without it, secret intermediates can remain
   in dead stack frames of `sign` and `from_seed`.
8. **F-8, verify is 1.54 times slower under nearcore's current flags and equal with AVX2.** The cause is the 4-way Keccak:
   128-bit code without AVX2, 256-bit with it. The source is the same proved code in both. Choosing between "accept
   the slowdown", "raise the CPU floor to AVX2" and "stay on aws-lc" needs validator hardware data this trial does not have.
9. **F-9, gas parameters were calibrated on aws-lc.** Slack on this machine is large against a wall-clock estimate
   (table above), but the derivation is not reproducible from the repository, and the tail was not measured (box load).
10. **F-10, the rejection path differs.** Garbage-shaped signatures are rejected in about 1 µs here and in 1 to 30 µs by aws-lc.
    Pricing must use the full-verify (tampered) cost, which is the same for both and flat in the hint weight.
11. **F-11, stack: +18 KiB for verify, about 61 KiB in the VM at the call**, 227 KiB at the deepest accepted contract
    recursion measured. Fits 2 MiB and 8 MiB threads with a wide margin; two gaps listed above.
12. **F-12, no build-environment gain.** The C toolchain and `aws-lc-sys` remain (see Dependencies); the binary grows 0.13 %; nothing
    measurable in build time. The benefit case is the proof and the pure-Rust verifier, not the build.
13. **F-13, nearcore's CI tests run without its target-feature list.** The `Justfile` runs `RUSTFLAGS="-D warnings" cargo nextest`,
    and `RUSTFLAGS` replaces the `.cargo/config.toml` flags, so tests are built for baseline x86-64 while release binaries get
    the feature list. Relevant here because the verify speed and the generated code depend on those flags; it applies equally
    to aws-lc (whose C code ignores them). This trial ran its nextest without `RUSTFLAGS`, so with nearcore's config flags.
14. **F-14, crate changes: none required.** Nice to have, not needed: exported length constants (`PK_LEN`, `SK_LEN`,
    `SIG_LEN`) so `near-crypto` need not repeat them, and a documented statement about `pk_from_sk_*` being the
    right parse-time check for stored keys.

## Limits of this trial

- One CPU model (Zen 4) on a shared, often heavily loaded VM; absolute numbers are not nearcore's validator hardware.
  Ratios from the minimum and low percentiles of alternating calls are the reliable output; tails are not.
- Only the paths above were exercised; no `neard` node was run, no mainnet traffic replayed, no mixed-version network.
- Frames above the host-function call in a real chunk-application thread were not measured.
- The differential is a test (80k here, 3.2M in the crate's own suite), not a proof about aws-lc.
- Build times are not comparable (load, `mbx` cache).

## Reproduce

`$NC` is a clone of `https://github.com/near/nearcore` at `cd5a94457`; run on a machine with nearcore's prerequisites
(clang, cmake, protoc). Plain `cargo` throughout; the target directory is left at its default.

```sh
cd $NC && git apply /path/to/nearcore.patch                    # the proposal
# builds
cargo build --release --locked -p neard -p near-crypto --features near-crypto/ml-dsa-lean
# tests (nearcore's own recipe flags; FILTER is the expression in the Tests section)
cargo nextest run --locked --workspace --cargo-profile dev-release --features test_features \
  --features near-crypto/ml-dsa-lean --no-fail-fast --ignore-default-filter -E "$FILTER"
cargo clippy --locked -p near-crypto --all-targets --features ml-dsa-lean -- -D warnings
# differential (both libraries linked in one binary)
cargo test --release --locked -p near-crypto --features ml-dsa-lean --test ml_dsa_backend_diff -- --nocapture --test-threads=1
# criterion (nearcore's bench); build once per variant and copy the binaries out, then alternate them on one pinned core
NC_TF="+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq"
cargo bench --locked -p near-crypto [--features ml-dsa-lean] --bench signatures --no-run                        # nearcore flags
RUSTFLAGS="-Ctarget-feature=$NC_TF,+avx,+avx2 -Cforce-unwind-tables=y" cargo bench --locked ...                  # +avx2
# estimator (per backend and flag set)
cargo build --release --locked -p runtime-params-estimator --features required [-p near-crypto --features near-crypto/ml-dsa-lean]
estimator --metric time --iters 10 --warmup-iters 3 --accounts-num 2000 --additional-accounts-num 2000 --costs MlDsaVerifyBase,MlDsaVerifyByte
# probes (stack and A/B timing)
git apply /path/to/probes.patch
cargo test --release --locked -p near-crypto [--features ml-dsa-lean] --test stack_probe -- --nocapture
cargo test --release --locked -p near-vm-runner -p near-crypto [--features near-crypto/ml-dsa-lean] --lib -- ml_dsa_stack_probe --nocapture
cargo test --release --locked -p near-crypto --features ml-dsa-lean --test ab_bench -- --ignored --nocapture   # run with taskset on a quiet core
```

Files here: `nearcore.patch`, `probes.patch`, `raw/` (unedited outputs: differential, A/B bench, criterion, estimator,
distribution benches, stack probes). Baseline test list and counts are in the Tests section.
