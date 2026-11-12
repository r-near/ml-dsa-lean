# Assurance case

The current state of the evidence for `ml-dsa-lean`: what is proved, what the proofs trust, what is only tested and how
strongly, what is not covered, and the command that reproduces each claim. The round-by-round log, the dated gate tables, the
audit-finding tables and the detailed reference sections are in [assurance-history.md](assurance-history.md), cited here as
"history §N" (its section numbers and round names are the ones this page used to have).

**Scope.** `ml-dsa-lean` is a `no_std` Rust implementation of ML-DSA (FIPS 204). For every public `api` function and all three
parameter sets (ML-DSA-44, 65, 87), Lean theorems say that the Rust, as extracted by Charon/Aeneas, never fails in the Aeneas
model and agrees with a Lean transcription of FIPS 204 whenever either returns a result, under the trusted base of section 3.
Tests, differentials, fuzzing and constant-time checks are evidence of a different, weaker kind; the page says for each what it
covers. **Nothing here is a FIPS validation or certification: ACVP vectors are test vectors, not a CMVP validation, and the crate
has none. No third party has audited the crate, its spec or its proofs.**

**Vocabulary.** "Proved" means a Lean theorem that passes the axiom gate (`scripts/check-axioms.sh`: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`). "Checked" means a tool or test found no counterexample on the inputs it covered.
"Spec" is `lean/Spec`, our transcription of FIPS 204 (Algorithms 1–3 and 6–48) and FIPS 202 (SHAKE). "Rust" is the code extracted
into `lean/Impl` and modeled there (`RustM` = `ok`, `fail` or `div`).

## 1. What is proved

| List | Names | Holds | Checked by |
|---|---|---|---|
| `lean/headline-theorems.txt` | 412 | the API theorems of 1.1 to 1.4 and the arithmetic, codec, sampler and Keccak/SHAKE lemmas under them | `scripts/lean-check.sh` |
| `lean/keccak4-theorems.txt` | 6 | the 4-way Keccak-f[1600] equals four scalar permutations | `scripts/lean-check.sh` |
| `lean/fast-verify-theorems.txt` | 79 | the 4-way SHAKE128 sampler, ExpandA and Verify body against their scalar counterparts (1.5) | `scripts/lean-check.sh` |
| `lean/witness-theorems.txt` | 146 | non-vacuity witnesses for the premises (1.6) | `scripts/witness-check.sh` |
| `xspec/headline-theorems.txt` | 144 | `lean/Spec` equals an independent transcription (1.7); a separate Lean project | `scripts/xspec/check-axioms.sh` |

The README states 412 and 85 (79 + 6); `scripts/check-readme-counts.py` fails if they drift from the lists. By name, the 412 include
30 `*_exact` (18 for the one-shot functions, 12 for prepared keys), 37 `*_div_iff`, 37 `*_partial`, 40 containing `prepared`, 38
containing `correct`, 33 `Corr.*` and 32 SkWellFormed or PkFromSk names (a name can be in several rows); the rest are leaf and step
specifications (history §1.6 maps modules to content).

**1.1 The `*_exact` theorems.** For NN ∈ {44, 65, 87}, every value of the argument types and no unproved premise, `verify_NN`,
`verify_internal_NN`, `keygen_NN`, `sign_NN`, `sign_internal_NN` and `pk_from_sk_NN` each have a three-part theorem: (a) the Rust never
returns `fail` (no panic, overflow or out-of-bounds access in the Aeneas model); (b) if it returns `ok r`, the spec returns the
matching result at some fuel; (c) if the spec returns a result at any fuel, the Rust returns it as `ok`. The result is the verdict
for Verify, the key pair for KeyGen, the signature for Sign and the optional public key for `pk_from_sk`. The API takes fixed-size
arrays, so a wrong length cannot occur. `sign_NN` returns `none` exactly when |ctx| > 255 or the spec's `Exhausted` holds (all κ
attempts rejected; the Rust's cap κ + ℓ ≤ 2¹⁶ is the spec's `kappaBudget`). "Fuel" makes the FIPS rejection-sampling loops total in
the spec; the Rust loops are unbounded. The older theorems that carry premises (`keygen_internal_spec`, `sign_internal_spec_some`,
...) name them: `RejTerm` (the samplers receive enough accepted samples; probabilistic, not provable), the κ budget, and `Params.Std`
(the standard parameter sets; kernel-checked for 44/65/87). Files: `lean/Proofs/Partial{API,KeyGen,Sign}.lean`, `PkFromSk.lean`.

**1.2 Divergence.** `Proofs/Divergence.lean` (`rustM_div_iff`, `*_div_iff`): the Rust returns `div` exactly when the spec returns no
result at any fuel and none of its defined rejections applies, that is, when one of FIPS 204's unbounded rejection samplers (ExpandA;
ExpandS in KeyGen; SampleInBall) would never terminate on that input. Sign's defined rejections are |ctx| > 255 and `Exhausted`: on
those inputs both the spec and the Rust return `none`, which is a result, not divergence (`sign_NN_div_iff`,
`sign_internal_NN_div_iff`). **This is not a termination proof**; termination is probabilistic. Sign's κ loop is bounded, so Sign
diverges only through a sampler.

**1.3 Honest keys.** `Proofs/Correctness.lean`: `correct_44`, `correct_65`, `correct_87` (`keygen_NN`, then `sign_NN`, then
`verify_NN` returns true), with premises `StdParams` and that KeyGen and Sign return `some` at the same fuel (`RejTerm`, the κ budget).

**1.4 Prepared keys and optional checks.** The four prepared-key calls (`verify_prepared_NN`, `sign_prepared_NN` and their `_internal`
variants) equal the one-shot calls as computations, failure and divergence included, and have the three-part theorem of 1.1, for a
key `vk` with `verifying_key_NN pk = ok vk` (or `signing_key_NN sk = ok ssk`); that covers every key a caller can hold, because the key
structs have private fields. The `Drop` wipe is not in the model. `sk_is_well_formed_NN` and `pk_from_sk_NN` are optional checks,
not FIPS steps, and are proved too; `sign_NN` follows FIPS 204 Algorithm 25 literally and calls neither (E-4, section 6).

**1.5 The 4-way verify, which runs in every build.** `api::verify_NN`, `verify_internal_NN` and `verifying_key_NN` call a 4-way
body directly: a plain safe-Rust 4-way Keccak-f[1600] (`src/keccak4.rs`), a 4-way SHAKE128 RejNTTPoly and ExpandA (with
`tr = H(pk, 64)` in the spare fourth lane of the first groups), and verify-only arithmetic on public data (`src/verify_arith.rs`).
What is proved: the permutation equals four scalar permutations (no premise); the 4-way sampler and the verify-only functions have
spec statements under input preconditions (canonical coefficients, norm bounds; history §1.9 lists them); and `expand_a_x4`,
`expand_a_tr_into_x4`, `prepare_vk_x4` and `verify_internal_x4` equal the scalar `expand_a`, `prepare_vk` and `verify_internal` as
`RustM` values, divergence included, under `Params.Std`. The `*_exact` statements are therefore about the function that runs. The
crate has no run-time dispatch, no CPU detection, no `unsafe` and no `#[target_feature]` function (`#![forbid(unsafe_code)]` in every
configuration); the Cargo feature `avx2` is a deprecated no-op. The extraction does not depend on the target features: it is done
twice, as is and with `-C target-feature=+avx,+avx2`, and `lean/Impl` must be byte-identical (`scripts/check-feature-independence.sh`,
empty whitelist). That LLVM vectorizes the permutation is a performance property, not a premise. Details: history §1.9.

**1.6 Witnesses.** `Params.Std` is kernel-checked for 44/65/87. For ML-DSA-44, ξ = 0..31, rnd = 0³², M = [0], ctx = [] and the
default fuel, the hypotheses of `correct_44` hold on a kernel-checked instance with `api.verify_44 = ok true`
(`Proofs.TopWitnessCorrect.correct_44_nonvacuous`). **One parameter set and one input only**; `Exhausted` has no witness. The check
needs about 46 GB and 47 minutes cold, so it runs manually or weekly (`.github/workflows/lean.yml`), not on pull requests.

**1.7 The spec against an independent transcription.** `xspec/` vendors `lean/Spec` byte-identically and proves it equal to
ocaml-pq's Lean transcription (142 equivalence theorems and 2 kernel known-answer tests; standard axioms only). Qualifiers: their Sign
loop stops after 821 attempts and ours after the κ budget; their key import also rejects keys with inconsistent tr/t0, which FIPS 204
and our spec accept; some directions assume their samplers terminate (history §1.8 has the full list). It is only as independent as
their FIPS 202 transcription is of ours, and it is a proof about specs, not the Rust.

**1.8 What ties the proofs to the shipped source.** The proofs are about `lean/Impl`, the extraction of `src/`. On every push and pull
request `scripts/ci.sh` checks the digest of the extraction inputs (`src/`, `Cargo.toml` with the version zeroed,
`scripts/extract-roots.txt`, the tool pins) against `lean/Impl/extract-report.json`, and the `lean` job of `ci.yml` (free
`ubuntu-latest` runner; `ci-ok` needs it) re-extracts into an empty directory, requires `diff -r` against `lean/Impl`, and runs
`scripts/lean-check.sh` (full build, axiom gates, a scan of the Lean environment for `axiom`, `opaque`, `sorry`, `implemented_by`,
`extern` and `native_decide`, reachability of every verify function, cfg inventory, README counts, feature independence). These catch
accidental drift and tampering inside generated or cached files; they cannot stop someone who can change the workflows or scripts in a
commit (that is covered by review of `.github/` and `scripts/`).

## 2. Pins

Lean v4.31.0; Charon nightly-2026.09.02, Aeneas build-183e4f0, cargo-hax 0.4.2, elan v4.2.4 and Rust nightly-2026-08-18 for extraction
(`scripts/setup-tools.sh` checks recorded SHA-256 values); MSRV 1.86. Charon runs without `--monomorphize` (no external axioms) and
extraction with `--cfg miri`. Out of scope by decision: HashML-DSA (Algorithms 4/5) and external μ. History §0 has the reasons, §8 the
code-shape rules the extraction imposes, and §9 the map from each module to the FIPS 204 algorithms.

## 3. The trusted base

Every proved result assumes items 1 to 4, and the hardware that runs the binary.

1. **Spec fidelity**: `lean/Spec` against FIPS 204/202. Evidence: three internal reviews against the FIPS PDFs (the notes of the third
   are not committed), ACVP and Wycheproof, a component differential against VCVio (1,345,635 in-precondition cases, 0 mismatches) and
   1.7. None of it proves that the spec is the standard.
2. **Charon/Aeneas**, with the pins of section 2. Extraction runs with `--cfg miri`, so the proved code is the source with its
   `cfg(miri)` variants: `field::opaque_u32` and the RISC-V `black_box` barriers are the identity there (CT-1, CT-2; none is on a verify
   path). Nothing else differs: no `unsafe`, no CPU detection, no `cfg` that selects code by CPU feature. Evidence: the extracted code,
   compiled and run against the native Rust, agrees on 345,360 cases (Keccak, field, NTT, rounding, samplers, codecs and the full API,
   including 225 ACVP-derived cases), and 4 injected bugs were all detected (`scripts/impl-eval.sh`).
3. **rustc and LLVM** compile the source faithfully for the target features of the build (the default, nearcore's flags, or
   `-C target-feature=+avx2`; the proofs are about the Rust text, which is the same under all of them). The theorems are about source
   semantics, not object code. The compiled code differs from the proved code by the barriers of item 2, and `black_box` is trusted to
   be the identity on values.
4. **The Lean kernel**, with `propext`, `Classical.choice` and `Quot.sound`.

A build with AVX2 target features needs a CPU with AVX2; that is a deployment requirement and no theorem depends on it. The `zeroize`
feature and the `Drop` wipes are outside the proof.

## 4. What is tested, and how strongly

None of this is proof. "Differential" means two implementations agreed on the same inputs. Counts are recorded runs (history §5).

| Evidence | Result, and its limit |
|---|---|
| ACVP (NIST, vendored subset; `tests/acvp.rs`) | Rust: keyGen 75/75, sigGen 60/60, sigVer 30/30; the preHash and external-μ groups (the other half) are skipped because those are not implemented. Lean spec: 63/63 (`spec-acvp`) |
| Wycheproof (C2SP; `tests/wycheproof.rs`) | Rust: 1063 pass, 0 fail, 6 known (E-4), 69 skipped (external-μ only). Lean spec: 928/928 agree |
| RustCrypto `ml-dsa` (git a3690c4), the oracle | pk and sk match on 30 seeds per set; Sign matches on 25 cases per set; Verify agrees on 1,260 cases per set; randomized runs; the public API on 72 cases including \|ctx\| = 0, 255, 256 |
| aws-lc-rs 1.18.2, the backend nearcore calls for ML-DSA-65 (`tests/awslc_diff.rs`) | 0 verdict differences in about 3.22M verify comparisons (bit flips, splices, wrong lengths, hint encodings, edge keys, forged z, cross-signing); KeyGen byte-identical from 15,000 seeds. aws-lc signs hedged and has no ctx parameter, so signatures are cross-verified, not compared, and only ctx = "" is compared. 4 of 5 injected verifier weaknesses detected. Tied to that version; not an equivalence proof |
| libcrux-ml-dsa 0.0.11, mldsa-native v2.0.0, RustCrypto (`crosscheck/`) | 0 disagreements, 0 crashes: 1.05M keygens and 1.5M signatures byte-identical; 15.4M verify cases; 3.66M `verify_xdiff` and 195k `sign_xdiff` fuzz executions |
| Differential fuzzing against RustCrypto (`fuzz/`) | about 50 minutes per target, 0 crashes, 0 disagreements (`verify_diff` 12.1M executions, `sign_diff` 787k, `decode_roundtrip` 1.1M). A removed `count > ω` check was not found in 180 s; the κ-exhaustion path was never reached. CI runs each target for 60 s |
| Extracted Lean against native Rust (`scripts/impl-eval.sh`) | 345,360 cases, 100% agreement, 4 injected bugs detected (section 3, item 2) |
| Proof mutation testing | 29 semantic mutants of `src`: each breaks the Lean build at the spec theorem of the mutated function. `cargo test` missed 5; regression tests now kill four. **The harness is not committed; this cannot be re-run** |
| 4-way verify against the scalar functions (`tests/keccak4_long.rs`, `fast_verify*.rs`, `verify_arith.rs`) | more than 150,000 whole permutation states; ACVP sigVer, Wycheproof and random valid, corrupted and wrong-length inputs, all sets; run in the default build and with `-C target-feature=+avx2`. Tests the compilation of the proved source (section 3, item 3); not part of the proof |
| zeroize (`tests/zeroize.rs`) | stack scans below `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and single Sign attempts for residue of secrets. Release builds pass 28 of 28 on the recorded x86_64 Linux and aarch64 macOS machines;
opt-level 0 and opt-level 1 do not (Z-1) |
| Rust CI (`scripts/ci.sh`) | default, `zeroize` and AVX2-target-feature runs; thumbv7em; wasm32; MSRV 1.86; nearcore's release profile on 1.95.0; `cargo deny`; macOS arm64 default and release-zeroize suites. Last green on GitHub at `d28ede8` (2026-11-11), `lean` job included |

The harnesses were not themselves reviewed; their sensitivity was checked by planting bugs, as the rows say. Performance is a
measurement on one machine (AMD EPYC 9B14, one pinned core, rustc 1.99.1; history §5), not a claim: one-shot verify for ML-DSA-44 / 65 /
87 takes 38.6 / 57.9 / 96.2 µs under nearcore's current flags (no AVX2) against 52.5 / 88.4 / 152.6 µs for the scalar functions, and
26.1 / 38.4 / 60.7 µs with `+avx,+avx2` added, which needs AVX2 target features at compile time. This page does not claim that
nearcore's feature floor guarantees AVX2.

### 4.1 Constant time (BINSEC)

Checked with BINSEC (relational symbolic execution) on compiled probes, **not proved in Lean**. "Secure" means BINSEC explored the probe
to completion and found no secret-dependent branch, memory address or division operand for all secret values. The lifter, the solver and
"instructions take operand-independent time" are trusted; hardware timing (variable latency, speculation, power) is outside the model.
Verify handles only public data, so it has no probes; the property matters for KeyGen and Sign.

The latest full sweep is at tree 1d8b5c5; `src/` has changed since only in comments. Its probes are the secret-touching steps of KeyGen
and Sign (`checkct/README.md`) on x86_64 (`default`, `nearcore`, `nearcore-novec`, `nearcore-exact`, `nearcore-exact-novec`, and
`ZEROIZE=1` builds), thumbv7em, riscv32imac and AArch64 without NEON. Secure / expected insecure: 109/5 of 114 probes on x86_64
`default`, 108/5 of 113 on `nearcore`, `nearcore-novec` and `nearcore-exact-novec`, 110/4 of 114 on thumbv7em; riscv32imac 101/6 with 7
`unknown`; AArch64 100/3 with 13 `unknown` (116 probes, two of them censuses). **No entrypoint probe ended `insecure` unexpectedly or
`error`.** The expected-insecure probes are the rejection samplers (they branch on their public accept test) and the positive
controls. Limits:

- **Whole Sign has no constant-time verdict.** The whole-Sign censuses report only the public `sample_in_ball` accept branch, are cut at
  the NTT under nearcore's exact build, or ended `error` after being killed at the 160 GB memory cap (thumbv7em, riscv32imac, one x86_64
  profile). Sign is covered by its secret-touching pieces, and the glue between steps by code reading only.
- **`unknown` is no verdict.** Under `nearcore-exact` (nearcore's release profile for the crate in isolation, rustc 1.95.0; not nearcore's
  binary) 49 of 113 probes are `unknown`: 48 are cut at AVX/VEX instructions that BINSEC 0.11.3 cannot lift (T-9), and one
(`prepare_sk_1x1_65`) is an unresolved pending-path stall with no instruction cut. So there is no verdict for the NTT,
  `hint_step` and `response` in that build, and the `-novec` result is about a different binary. In builds with AVX2 target features, and in
  AArch64 builds with NEON, the probes that contain vector code cannot be lifted (so macOS and Apple Silicon builds have no coverage). A
  few riscv32imac and AArch64 probes are solver stalls.
- ExpandS is covered only through its per-nibble helper. Verdicts hold for the builds measured; the sweep binaries are built without
  `zeroize`, and a separate `ZEROIZE=1` x86_64 run gave the same verdicts.

Three real leaks were found and fixed (CT-1, CT-2, CT-3). The sweep tables, reruns and stop sites: history §4 and `checkct/README.md`.

## 5. What is not covered

- **Object code.** The theorems are about source semantics; rustc/LLVM output is trusted (section 3, item 3). Every Rust line reachable
  from the verify entry points is in an extracted function (`scripts/reachable-defs.sh`); its compilation is not proved.
- **Stack exhaustion and out-of-memory** are not modeled. Worst-case stack is measured (`tools/stack/`; release, x86_64; ML-DSA-44 / 65 /
  87, KB): Sign 99 / 140 / 209, Verify 64 / 90 / 132, KeyGen 64 / 98 / 143; `verifying_key_*` 50 / 74 / 111, `signing_key_*` 59 / 98 /
  164, `verify_prepared_*` 31 / 38 / 50, plus the 20.5–81 KB key object in the caller's frame. The 4-way verify uses more stack than the
  scalar one did.
- **That the spec returns a result.** Only the ML-DSA-44 instance of 1.6 has a witness. **Termination** is probabilistic (1.2).
- **Crate-private internals** exposed by the `internals` feature can panic (E-1); without it the public surface is `api` only and every
  `api` function has a theorem. Cargo unifies features, so enabling `internals` anywhere in a dependency graph exposes them.
- **The `zeroize` feature** (wiping, `Drop`) is outside the proof; stack-residue claims hold for the recorded release builds only, not at opt-level 0 or 1 (Z-1).
- **Randomness** is the caller's (`keygen_NN` takes ξ, `sign_NN` takes `rnd`). **HashML-DSA and external μ** are out of scope.
- **Constant time** for whole Sign, for verify, and for builds with AVX2 target features or NEON (4.1).
- **No third-party audit, no FIPS or CMVP validation.**

## 6. Known issues and fixed findings

| ID | Status | What |
|---|---|---|
| E-4 | open, accepted | Out-of-range secret keys are accepted: six Wycheproof sign vectors (two per set) use an expanded secret key with an s1 or s2 coefficient outside [−η, η] and expect signing to fail. This crate and the Lean spec both sign with them (FIPS 204 Algorithm 25 allows such coefficients "if input is malformed"; Section 7.2 says skDecode should run only on trusted input); RustCrypto panics. A hardening gap for callers who load untrusted expanded keys; `api::sk_is_well_formed_NN` is a separate proved check |
| E-1 | open | `sign_internal` and `keygen_internal` panic on wrong-length slices, and `verify_internal` on a `Params` inconsistent with its `K`/`L`. Reachable only with the `internals` feature |
| Z-1 | open | At opt-level 0, 21 of the 24 stack-residue scans in `tests/zeroize.rs` find copies of secrets in dead stack frames (`signing_key` passes for all sets); at dev opt-level 1, `keygen_44` and `keygen_65` fail on the recorded x86_64 Linux machine (26 of 28; 28 of 28 on aarch64 macOS); in release, 28 of 28 tests pass on the recorded x86_64 Linux and aarch64 macOS machines |
| T-8, T-9 | tool limits | A BINSEC probe killed at the container's memory cap shows only `error` (presumed out of memory unless the kernel log shows no kill); BINSEC 0.11.3 cannot lift AVX/VEX instructions, and overflow-check guards on secret values stalled it |
| CT-1 | fixed | riscv32imac: the mask-select idiom was turned back into branches on secret data; fixed with a RISC-V-only `black_box` barrier (identity under `cfg(miri)`) |
| CT-2 | fixed | x86_64: LLVM turned the `diff == q − 1` select in `rounding::decompose` into a branch; fixed by `field::opaque_u32` (about 2–3% in Sign) |
| CT-3 | fixed | `sk_is_well_formed` branched on the sign of secret coefficients (an overflow-check guard); only that optional check and `pk_from_sk_*` were affected, not Sign |
| E-2, E-3, FV-1 | resolved | E-2: upstream's `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β (FIPS 204 Algorithm 8 does, Algorithm 27 does not); the verdict is the same. E-3: the rejection loops have no provable bound; resolved by partial correctness plus panic-freedom. FV-1: the earlier AVX2 run-time dispatch was proved at source level only; round 12 removed it (1.5) |

History §6 and §7 have the full text, T-1 to T-6, and the cost figures; the audit findings of each round are in history §0.

## 7. Reproduce each claim

Paths are relative to the repository root; [reproduce.md](reproduce.md) has the tool pins, resource figures and what cannot be re-run.

| Claim | Command |
|---|---|
| 1.1–1.5: all headline, keccak4 and fast-verify theorems on standard axioms; no declared `axiom`/`opaque`/`sorry`/`native_decide`; reachability; feature independence | `bash scripts/lean-check.sh` (ends with `LEAN CHECK OK`) |
| 1.6: the witnesses (about 46 GB) | `bash scripts/witness-check.sh` |
| 1.8: `lean/Impl` is the extraction of `src/` | `python3 -I scripts/extract_hash.py check`; `python3 scripts/extract.py --out DIR` on an empty `DIR`, then `diff -r lean/Impl DIR` |
| 1.5: the extraction is the same under AVX2 target features; the 4-way permutation is 256-bit code with them (performance only) | `bash scripts/check-feature-independence.sh`; `bash scripts/check-avx2-inlining.sh` |
| 1.7: spec against ocaml-pq | `scripts/xspec/check-axioms.sh` and `scripts/xspec/run-diff.sh all` (after `scripts/xspec/setup.sh`, `build.sh`) |
| 3, item 1: spec against VCVio, ACVP and Wycheproof | `scripts/diff-vcvio/run.sh all` (after `setup-vcvio.sh`); in `lean/`, `lake build spec-acvp && .lake/build/bin/spec-acvp`; `python3 -I scripts/gen-lean-wycheproof.py`, then in `lean/` `lake build spec-wycheproof && .lake/build/bin/spec-wycheproof` |
| 3, item 2: extracted Lean against native Rust | `scripts/impl-eval.sh lean`, `scripts/impl-eval.sh rs`, `scripts/impl-eval.sh compare` |
| 4: ACVP, Wycheproof, RustCrypto and aws-lc-rs differentials; 4-way verify tests | `cargo test --release` (a debug `cargo test` divides the bulk aws-lc-rs differential counts by 100 unless `AWSLC_DIFF_FULL=1`, so it is smoke coverage only; the full differential alone: `cargo test --release --test awslc_diff -- --nocapture`); on an AVX2 machine also `RUSTFLAGS="-C target-feature=+avx2" ML_DSA_REQUIRE_AVX2=1 cargo test` |
| 4: libcrux and mldsa-native differentials; fuzzing | `crosscheck/README.md` ("How to run"); in `fuzz/`, `cargo +nightly fuzz run verify_diff` (also `sign_diff`, `decode_roundtrip`) |
| 4: the whole Rust check list (MSRV, thumbv7em, wasm32, nearcore profile, 60 s fuzz smoke, `cargo deny`) | `bash scripts/ci.sh --strict --lean` (every step must pass) |
| 4.1: constant time | `checkct/README.md`; reproduce.md section 3 (`checkct/run-select.sh` per target and profile; Linux and Docker) |
| 5: stack | `bash tools/stack/run.sh` (`tools/stack/README.md`); `bash bench/stackquick.sh` for the verify rows |
| 4: performance | `bash bench/compare.sh LABEL [CPU]` (keygen, sign), `SETS=44,65,87 bash bench/fast-verify.sh LABEL [CPU]` (verify; the default is set 65 only) |

## 8. Related work, and wording

The related-work survey (Apple corecrypto, Microsoft SymCrypt, ocaml-pq, libcrux-ml-dsa, mldsa-native, Formosa Crypto; 2026-10-30, not
re-run since) is in history §10. Where those projects prove things this crate does not, for example object-code properties, they go
further. Wording that stays inside the evidence (history §12 has the full text): the extracted Rust for every `api` function is proved,
with no unproved premise, to never fail (in the Aeneas model: stack exhaustion and out-of-memory are not modeled, and the Rust can diverge
exactly when a rejection sampler of the spec never terminates, with Sign's defined rejections excepted, 1.2) and to agree with the Lean transcription of FIPS 204 whenever either returns,
with the trusted base of section 3. **Not supported:** "formally verified" without that scope; "first" or "only"; "FIPS validated" or
"FIPS certified"; "production-ready" or "audited"; "no assumptions"; "constant time" for whole Sign, for verify or for builds with AVX2
target features; any statement about aws-lc equivalence beyond the differential of section 4; that the compiled AVX2 code is proved equal
to the portable build's; that nearcore's feature floor guarantees AVX2.
