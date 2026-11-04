# Check it yourself

Everything claimed in the [README](../README.md) and [assurance.md](assurance.md) can be re-run from this repository. This page
gives the commands. All paths are relative to the repository root. The scripts were written and run on x86_64 Linux; the
Lean steps also run elsewhere that Lean and Lake run, but only Linux is tested here. Nothing below needs network access to
anything but package registries and the tool download pages named in the scripts.

Resource figures are what the recorded runs used. They are rough guides, not guarantees.

## 1. The Rust crate

```sh
cargo test                      # default features: unit tests, KATs, ACVP, Wycheproof, differential tests against RustCrypto
cargo test --features zeroize   # at opt-level 0 the stack-residue scans fail (Z-1 in assurance.md); use --release
cargo test --release --features zeroize
cargo test --features avx2
```

MSRV is Rust 1.86 (`cargo +1.86.0 build`). The crate is `no_std`, has no dependencies without the `zeroize` feature, and
needs no C compiler. The dev-dependencies (RustCrypto `ml-dsa` at git rev a3690c4 as the test oracle, aws-lc-rs for one
differential) are fetched by Cargo.

`bash scripts/ci.sh` runs the whole Rust check list on a Linux x86_64 machine with rustup: tests for default, `zeroize`
and `avx2`; thumbv7em and wasm32 builds; MSRV 1.86; a build and tests under the settings of a downstream release profile
(toolchain 1.95.0, fat LTO, overflow checks); the aws-lc-rs differential; a 60-second smoke run of each fuzz target; and
`cargo deny`. It installs missing toolchains and targets with rustup, and `cargo-deny` into `~/.cache/ml-dsa-lean-ci`
(`CI_TOOLS` overrides that). It needs `cargo-fuzz` and a nightly toolchain for the fuzz steps and reports a SKIP if they are
missing; `--strict` turns a SKIP into a failure. Run `bash scripts/ci.sh --help` for options such as `--only`. A cold run
takes tens of minutes. Last recorded result: all 17 steps passed (assurance.md, section 0).

The longer differentials, fuzzing and benchmarks:

- `crosscheck/README.md`: libcrux-ml-dsa, mldsa-native (vendored C) and RustCrypto, including fuzz targets.
- `fuzz/`: `cargo +nightly fuzz run verify_diff` (also `sign_diff`, `decode_roundtrip`).
- `bench/`: `bash bench/build.sh`, then `bash bench/run.sh` and `bash bench/compare.sh` (see the header of each script).
- `tools/stack/README.md`: measuring worst-case stack use.

## 2. The Lean proofs

### Toolchain pins

| Tool | Version | Where it is pinned |
|---|---|---|
| Lean | `leanprover/lean4:v4.31.0` | `lean/lean-toolchain` |
| Aeneas Lean library, Mathlib | the revisions in `lean/lake-manifest.json` | fetched by Lake |
| Charon | nightly-2026.09.02 | `scripts/setup-tools.sh`, `scripts/extract.py` |
| Aeneas | build-183e4f0 | `scripts/setup-tools.sh`, `scripts/extract.py` |
| Rust for extraction | nightly-2026-08-18, with rustc-dev, llvm-tools, rust-src and miri | `scripts/setup-tools.sh` |
| cargo-hax (installs the two tools) | 0.4.2 | `scripts/setup-tools.sh` |

Lean is installed with [elan](https://github.com/leanprover/elan): `curl -fsSL
https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain
leanprover/lean4:v4.31.0`. The scripts expect `~/.elan/bin` to hold `lake`. You only need the extraction tools (Charon,
Aeneas, the nightly) for step 2.2; steps 2.1 and 2.3 need Lean alone, because `lean/Impl` is committed.

### 2.1 Check the proofs: `scripts/lean-check.sh`

```sh
bash scripts/lean-check.sh
```

This builds the Lake package `MlDsaLean` in `lean/` (`lake build`: the spec, the extracted code and every proof module), fails
on a nonzero Lake exit, on any `error:` or `declaration uses 'sorry'` in the full log, and then runs
`scripts/check-axioms.sh`. The axiom check prints the axioms of every extracted definition and of every name in
`lean/headline-theorems.txt` and fails if any is not one of `propext`, `Classical.choice`, `Quot.sound`. A `sorry` would
show up as `sorryAx` and `native_decide` as an extra axiom, so both fail the check. Success ends with
`LEAN CHECK OK` and the declaration count (770 at the recorded run). Pass module names to build less, for example
`bash scripts/lean-check.sh Proofs.PartialAPI`. Dependencies (Mathlib and Aeneas) are fetched with `lake exe cache get`
where possible and compiled otherwise, so the first run is much slower than later ones. `LEAN_PACKAGES_SEED` can point at a
directory of already built Lake packages (same Aeneas revision) to seed `lean/.lake/packages`. The Lean build log is kept in
`lean/.lake/check-build.log`.

To read the statements the gate covers, start with the `*_exact` theorems: `lean/Proofs/PartialAPI.lean` (Verify),
`PartialKeyGen.lean`, `PartialSign.lean` and `PkFromSk.lean` (names in assurance.md, section 1.1). The specification they refer to is
`lean/Spec/`.

### 2.2 Re-extract the Rust and diff `lean/Impl`

```sh
bash scripts/setup-tools.sh          # once; installs the pinned tools under ~/hax-tools (set ML_DSA_TOOLS to move them)
python3 scripts/extract.py           # runs Charon and Aeneas on src/ (with --cfg miri), writes lean/Impl
git diff --stat lean/Impl            # empty if the committed Lean code is the extraction of the committed Rust
```

`scripts/setup-tools.sh` needs `rustup`, `curl`, `zstd` and an x86_64 Linux machine. `scripts/extract.py` exits nonzero on
any gate failure (an Aeneas error or warning, a local opaque function, a referenced external axiom, an `api` function missing
from `scripts/extract-roots.txt`) and writes into `lean/Impl` only on success. `lean/Impl/extract-report.json` records the
SHA-256 of `src/`, so a changed `src/` with an unchanged `Impl` shows up there. `bash scripts/extract-and-build.sh`
runs extraction, `lake build` and the axiom check in one go.

### 2.3 The witness check: `scripts/witness-check.sh`

```sh
bash scripts/witness-check.sh
```

This builds `Proofs.TopWitnessCorrect`, which the default build does not import, and checks the 146 names in
`lean/witness-theorems.txt` for standard axioms only. The kernel evaluations are the cost: about 47 minutes cold and about 46
GB peak memory across modules in the recorded run (about 24 GB for the largest declaration). It ends with
`WITNESS CHECK OK: Proofs.TopWitnessCorrect`. If the kernel is killed (exit 137), the machine ran out of memory; rerun on a
larger one.

### 2.4 Cross-checks of the specification

- `scripts/xspec/check-axioms.sh` (after `scripts/xspec/setup.sh` and `scripts/xspec/build.sh`; Lean and Mathlib v4.34.0
  in a separate project; dependencies go under `~/xspec-work`, `XSPEC_WORK` overrides): the proof that `lean/Spec` equals ocaml-pq's transcription. See `xspec/README.md`.
- `scripts/xspec/run-diff.sh all` and `scripts/diff-vcvio/run.sh all`: executable differentials against ocaml-pq and
  VCVio. Both fetch the other project; read the header of each script.
- `scripts/impl-eval.sh lean`, `scripts/impl-eval.sh rs`, `scripts/impl-eval.sh compare`: run the extracted Lean and the
  native Rust on the same inputs and compare.
- Spec against ACVP: in `lean/`, `lake build spec-acvp && .lake/build/bin/spec-acvp`.

## 3. Constant-time checks (BINSEC)

These need Linux and Docker. The image builds BINSEC and the Rust toolchains (about 10 minutes):

```sh
docker build -t ct-binsec checkct
bash checkct/run.sh 2>&1 | tee ct.log
```

`checkct/README.md` explains the other scripts (`run-select.sh` for selected probes and the long sweeps, profiles for the
AVX2 dispatch and for a downstream release build, split probes for AArch64 and riscv32imac), the memory the large probes
need (some need more than 100 GB; a probe killed at the memory cap shows only `error`, and `journalctl -k -g 'Killed
process'` tells you whether the kernel killed it), the recorded verdicts and what they do and do not show. Tools for
mapping a leak address to a source line are listed there too. A static scan of the AVX2 code, which BINSEC cannot lift, is
`checkct/scan-avx2.sh`.

## 4. Test vectors

- ACVP: `cargo test --test acvp`; the vendored subset and its source are described in `tests/data/acvp/README.md`.
- Wycheproof: `cargo test --test wycheproof`; see `tests/data/wycheproof/README.md`.

## 5. What a pass means

A passing `lean-check.sh` establishes the theorems in assurance.md, section 1, under the trusted base in section 2 (the Lean
transcription of FIPS 204, the Charon/Aeneas translation, rustc and LLVM, the Lean kernel). A clean `extract.py` diff says
the Lean code is the extraction of the committed Rust. The tests, differentials, fuzzers and BINSEC runs are evidence of a
different kind (no counterexample found), and assurance.md says for each what it covers. None of this is a third-party audit
or a certification.
