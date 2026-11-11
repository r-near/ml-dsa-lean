# Check it yourself

Nearly everything claimed in the [README](../README.md) and [assurance.md](assurance.md) can be re-run from this repository.
This page gives the commands. What cannot be re-run from here:

- The proof mutation testing (29 mutants of `src`, assurance.md section 5): the harness that generated and ran the mutants is
  not committed. Only the regression tests it led to (`tests/mutants.rs`, the `prefix_eq` unit test in `src/verify.rs`) are.
- The notes of the third internal review of `lean/Spec` against the FIPS PDFs (assurance.md, section 1.8): they are not committed.
  The Lean tests, the VCVio differential and the other cross-checks it relied on can be re-run (section 2.4).
- Earlier logs and notes. The raw results of the latest constant-time sweep (`checkct/results/sweep-1a72d9e/`), of the one before it
  (`sweep-15b4ce2/`, the baseline of the comparison in `checkct/README.md`) and the
  `nearcore-exact` stage logs that assurance.md cites are kept. The raw logs of older sweeps (for example e9a1c74, whose results
  fill the cells marked "not rerun"), the progress trackers, the benchmark baseline notes and the experiment directories
  were deleted before release, so statements that only they supported can be re-measured but not re-read.
- Machine-dependent figures: benchmark numbers, stack-use measurements and BINSEC memory use depend on the machine.

All paths are relative to the repository root. The scripts were written and run on x86_64 Linux; the
Lean steps also run elsewhere that Lean and Lake run, but only Linux is tested here. Nothing below needs network access to
anything but package registries and the tool download pages named in the scripts.

Resource figures are what the recorded runs used. They are rough guides, not guarantees.

## 1. The Rust crate

```sh
cargo test                      # default features: unit tests, KATs, ACVP, Wycheproof, differential tests against RustCrypto
cargo test --features zeroize   # at opt-level 0 the stack-residue scans fail (Z-1 in assurance.md); use --release
cargo test --release --features zeroize
cargo test --features avx2                                    # the feature is a deprecated no-op
RUSTFLAGS="-C target-feature=+avx2" ML_DSA_REQUIRE_AVX2=1 cargo test   # on an AVX2 machine; see below
bash scripts/check-avx2-inlining.sh                           # x86_64 Linux; see below
```

Verify always runs the 4-way code; what LLVM makes of it depends on the target features of the build (SSE2 by default, 256-bit code with `-C target-feature=+avx2`), and
nothing is chosen at run time. The tests that compare the 4-way code with the scalar functions (`tests/keccak4.rs`, `tests/keccak4_long.rs`, `tests/fast_verify.rs`,
`tests/fast_verify_x4.rs`, `tests/fast_verify_tr.rs`) are meant to be run in both configurations: as they are, and with `RUSTFLAGS="-C target-feature=+avx2"` on an
AVX2 machine (`scripts/ci.sh` step `test-avx2` does both, and also runs the suite with `--features avx2`, the no-op). Without AVX2 target features they still run and
pass; `ML_DSA_REQUIRE_AVX2=1` turns "this build has no AVX2 target feature" from a printed note into a failure (`scripts/ci.sh` sets it for its AVX2 step). They are `cfg`'d out of nothing, so they also run
on an aarch64 Mac, where they test the NEON compilation. `scripts/check-avx2-inlining.sh` builds the library in release under nearcore's target features plus `+avx,+avx2`, emits
assembly, and fails unless the 4-way permutation is 256-bit vector code and the functions that own a `PreparedVk` or a `VerifyScratch` realign their stack frames to 32 bytes
(these are performance properties: a miss would still be correct, but several times slower).
`EXTRA_RF="-Ctarget-feature=+avx,+avx2" bash bench/stackscan.sh build NAME && OPS=verify,vk,prepared bash bench/stackscan.sh check CPU NAME` scans 257 stack offsets
(`STACK SCAN OK` when the largest is within 1.15 of the median; without `EXTRA_RF` it scans the 128-bit build).
`bash bench/scanboth.sh CPU NAME` builds and scans both variants (nearcore's flags and the same plus `+avx,+avx2`); `bash bench/stackquick.sh` prints the painted and static stack of `verify_NN`, `verifying_key_NN` and `verify_prepared_NN` (x86_64 and thumbv7em, default profile and fat LTO) on the build box; `bash bench/emu/run.sh` counts the instructions of the scalar and 4-way verify on Cortex-M4 and riscv32imac under the Unicorn emulator (docker; instruction counts, not cycles).
The Lean theorems behind the 4-way verify (`lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt`) are checked by
`scripts/lean-check.sh` (section 2.1).

MSRV is Rust 1.86 (`cargo +1.86.0 build`). The crate itself is `no_std`, has no dependencies without the `zeroize` feature, and
needs no C compiler. `cargo test` does need one, because the dev-dependency `aws-lc-rs` builds `aws-lc-sys` (C) for the
aws-lc differential; `crosscheck/` and `bench/` also compile mldsa-native's C and assembly (gcc was 13.3 in the recorded runs).
The dev-dependencies (RustCrypto `ml-dsa` at git rev a3690c4 as the test oracle, aws-lc-rs) are fetched by Cargo.

`bash scripts/ci.sh` runs the whole Rust check list on a Linux x86_64 machine with rustup: tests for default, `zeroize`
and `avx2` (the no-op feature, and AVX2 target features); thumbv7em and wasm32 builds; MSRV 1.86; a build and tests under the settings of a downstream release profile
(toolchain 1.95.0, fat LTO, overflow checks); the aws-lc-rs differential; a 60-second smoke run of each fuzz target; and
`cargo deny`. It installs missing toolchains and targets with rustup, and `cargo-deny` into `$HOME/.cache/ml-dsa-lean-ci/tools`
(`CI_TOOLS` overrides that). It needs `cargo-fuzz` and a nightly toolchain for the fuzz steps and reports a SKIP if they are
missing; `--strict` turns a SKIP into a failure. Run `bash scripts/ci.sh --help` for options such as `--only`. A cold run
takes tens of minutes. It also runs checks that need no Rust or Lean: `extract-hash` (the digests of the extraction inputs and of
`lean/Impl` against `lean/Impl/extract-report.json`, section 2.2), `axiom-gate-selftest` (`scripts/check-axioms.sh` must fail on a missing
or empty list), `no-decls-text` (the text half of `scripts/check-no-decls.sh`), `cfg-inventory` (`scripts/cfg_inventory.py`: every
`#[cfg(..)]`, `#[cfg_attr(..)]`, `cfg!`, `cfg_if!`, `env!`, `include!`, `is_*_feature_detected!` and `#[path]` site in `src/`, and any build
script, against the justified whitelist `scripts/cfg-inventory.txt`; a new or changed site fails until it is listed with a reason, and so
does a scan that finds no site), `readme-counts` (`scripts/check-readme-counts.py`: the theorem counts the README
states against `lean/*-theorems.txt`) and `ci-selftest` (`scripts/ci-selftest.sh`: the `--only lean` path of `ci.sh` and `lean-check.sh`
against stub gates, so the feature-independence check cannot be skipped silently; and `checkct/compare_code.py --self-test`). With `--lean` it also runs `feature-independence` (`scripts/check-feature-independence.sh`, section 2.2).
Last recorded result: see assurance.md, section 0.

The longer differentials, fuzzing and benchmarks:

- `crosscheck/README.md`: libcrux-ml-dsa, mldsa-native (vendored C) and RustCrypto, including fuzz targets.
- `fuzz/`: `cargo +nightly fuzz run verify_diff` (also `sign_diff`, `decode_roundtrip`).
- `bench/` (Linux x86_64; `run.sh` and `compare.sh` pin with `taskset`, and the numbers are only comparable on an otherwise idle
  machine): `bash bench/build.sh OUTDIR` builds the variants; `bash bench/run.sh OUTDIR CPU RESULTDIR [variant ...]` runs them
  pinned to one CPU (the first argument is the directory `build.sh` wrote to); `bash bench/compare.sh LABEL [CPU]` builds and
  runs the default / `avx2` (the no-op feature) / `x86-64-v3` comparison of Sign and KeyGen behind the older table in assurance.md section 5 (output under
  `$ML_DSA_SCRATCH/ntt-bench-LABEL`, which defaults to `${XDG_CACHE_HOME:-~/.cache}/ml-dsa-lean/scratch`). See the header of each script.
  `bash bench/fast-verify.sh LABEL [CPU]` is the verify benchmark behind the verify table in assurance.md section 5 and
  `bench/results/2026-11-07-p3.md`: it builds three variants (labeled `scalar`, `avx2`, `v3`; nearcore's flags, plus `+avx,+avx2`, and `-C target-cpu=x86-64-v3`) under nearcore's profile and target
  features (`SETS=44,65,87` for all sets; `TOOLCHAIN=1.95.0` for nearcore's compiler; `ROUNDS`, `HT_OFFSET` and
  `ML_DSA_SCRATCH` as described in its header) and runs them next to aws-lc-rs and mldsa-native AVX2, pinned to an idle core.
  `bench/ab.sh` is the interleaved A/B runner behind the per-change savings in that results file and the tables of `bench/results/2026-11-09-p12.md` (`EXTRA_RF` adds target features to a build).
  `bench/stackscan.sh build|run|check` scans the process environment padding (every 64 bytes by default, 16 with `STEP=16`, up to
  4 KiB, ASLR off) for verify, `verifying_key` and the prepared-key verify of a build (with `EXTRA_RF`, one with AVX2 target features) and fails when any padding is more
  than `LIMIT` (1.15) times the median; `bench/fast-verify.sh` runs it at the end (`STACKSCAN=0` skips it), and `bench/ab.sh`
  takes `PAD=<bytes>` and has `scan-build`/`scan` subcommands. `bench/results/2026-11-07-p6.md` is the stack-offset write-up.
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

`scripts/setup-tools.sh` installs Lean with [elan](https://github.com/leanprover/elan) (release v4.2.4, downloaded from its
GitHub release and checked against a SHA-256 recorded in the script) and the toolchain `leanprover/lean4:v4.31.0`. The scripts
expect `~/.elan/bin` to hold `lake`. You only need the extraction tools (Charon,
Aeneas, the nightly) for step 2.2; steps 2.1 and 2.3 need Lean alone, because `lean/Impl` is committed.

### 2.1 Check the proofs: `scripts/lean-check.sh`

```sh
bash scripts/lean-check.sh
```

This builds the Lake package `MlDsaLean` in `lean/` (`lake build`: the spec, the extracted code and every proof module), fails
on a nonzero Lake exit, on any `error:` or `declaration uses 'sorry'` in the full log, and then runs
`scripts/check-axioms.sh`. The axiom check prints the axioms of every extracted definition and of every name in
`lean/headline-theorems.txt` and fails if any is not one of `propext`, `Classical.choice`, `Quot.sound`. `lean-check.sh` then runs
the same gate over `lean/keccak4-theorems.txt` and `lean/fast-verify-theorems.txt` (the 4-way Keccak, sampler, ExpandA and verify
theorems, assurance.md section 1.9; `scripts/check-axioms.sh --list FILE --no-impl` runs one list). A `sorry` would
show up as `sorryAx` and `native_decide` as an extra axiom, so both fail the check. That gate looks only at the dependencies of the names it is given, so `lean-check.sh` also runs `scripts/check-no-decls.sh`, which fails on any `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` or `extern` declared anywhere in `lean/Impl`, `lean/Spec` or `lean/Proofs` (a scan of the source text and a walk over the Lean environment's constants of those modules), and `scripts/check-no-decls.sh --self-test`, which injects each of them into an `Impl` module and requires the scan to report it. `witness-check.sh` repeats the scan with the `TopWitness` modules built (`--all-built`). The axiom gate prints the declaration count
on its `defs/theorems to check:` and `checked:` lines (the count depends on the tree; assurance.md section 0 has the recorded one); success ends with `LEAN CHECK OK` and does not
repeat it. Pass module names to build less, for example
`bash scripts/lean-check.sh Proofs.PartialAPI`. Dependencies (Mathlib and Aeneas) are fetched with `lake exe cache get`
where possible and compiled otherwise, so the first run is much slower than later ones. `LEAN_PACKAGES_SEED` can point at a
directory of already built Lake packages (same Aeneas revision) to seed `lean/.lake/packages`. The Lean build log is kept in
`lean/.lake/check-build.log`. `LEAN_BUILD_TIMEOUT` (seconds, default 7200) bounds the `lake build`; it ends a hung build and is not a gate.

GitHub runs this script on every pull request and every push to `main` (`.github/workflows/ci.yml`, job `lean`, on the free `ubuntu-latest`
runner; `ci-ok` needs it, so it is a required check). The job does what sections 2.1 and 2.2 describe, in this order: `scripts/setup-tools.sh`,
`python3 -I scripts/extract_hash.py check`, `scripts/extract.py` into an empty directory with `diff -r` against `lean/Impl`, then
`scripts/lean-check.sh`. It sets `LEAN_NUM_THREADS=2` and deletes preinstalled software (dotnet, Android, GHC, CodeQL, Boost) to make room
on the 14 GB disk. A cold run took 1596 s for the build with `LEAN_NUM_THREADS=2` (peak 12.7 GB) in a container with the runner's limits
(16 GB, 4 cores); one thread took 2048 s (9.1 GB). On a machine with less than about 16 GB of RAM set `LEAN_NUM_THREADS=1`.

To read the statements the gate covers, start with the `*_exact` theorems: `lean/Proofs/PartialAPI.lean` (Verify),
`PartialKeyGen.lean`, `PartialSign.lean` and `PkFromSk.lean` (names in assurance.md, section 1.1). The specification they refer to is
`lean/Spec/`.

### 2.2 Re-extract the Rust and diff `lean/Impl`

To check that the committed `lean/Impl` is the extraction of the committed `src/` (extract into a new empty directory, never
into the tree you are checking):

```sh
bash scripts/setup-tools.sh                 # once; installs the pinned tools under ~/hax-tools (set ML_DSA_TOOLS to move them)
python3 -I scripts/extract_hash.py check    # no symlinks or stray files in lean/Impl, hashes as recorded in extract-report.json
out="$(mktemp -d)" && python3 scripts/extract.py --out "$out"   # runs Charon and Aeneas on src/ (with --cfg miri)
diff -r lean/Impl "$out"                    # no output: every file, including extract-report.json, is identical
```

To regenerate `lean/Impl` after changing `src/`, run `python3 scripts/extract.py` (it refuses an output directory that holds
symlinks or files it does not write), then `python3 -I scripts/extract_hash.py check`, and commit `lean/Impl`.

The extraction runs with `--cfg miri` and no cargo feature, and the crate has no cargo feature that changes what is extracted. To check that the target features of a build
do not change the extracted code, run `bash scripts/check-feature-independence.sh`: it extracts a second time with `-C target-feature=+avx,+avx2` (still `--cfg miri`; the rustflags are
recorded in each `extract-report.json`) and compares the generated Lean with `lean/Impl`. The whitelist of differences in `scripts/feature_independence.py` is empty, so any difference fails. The gate cannot pass
vacuously: it fails if both extractions recorded the same rustflags, and a probe crate (`scripts/fi-probe`, whose one function is `cfg!(target_feature = "avx2")`) must extract to `true` under the second flags and `false` under
the first, which shows that the flag reached rustc. `python3 -I scripts/cfg_inventory.py` is the Rust-side census of every `cfg` site (and the other compile-time selectors, and any build
script) in `src/` against `scripts/cfg-inventory.txt`. `scripts/lean-check.sh` runs the feature-independence check itself unless
`scripts/ci.sh` passes `ML_DSA_FEATURE_INDEPENDENCE_DONE=1`, which it does only after its own `feature-independence` step passed in the
same invocation; a run with module arguments (`scripts/lean-check.sh Proofs.X`) prints `LEAN CHECK OK (PARTIAL ...)` and is not the done-gate.

`scripts/setup-tools.sh` needs `rustup`, `curl`, `zstd`, `sha256sum` and an x86_64 Linux machine. It downloads cargo-hax and
elan from tagged releases and checks recorded SHA-256 values. On every run it checks the installed cargo-hax binary and the
whole Aeneas and Charon tool directories (cargo-hax runs the executables that `hax-metadata.toml` in them names, so every file
counts, and the execute bit) against recorded digests, reinstalling if they differ, and runs each tool. `scripts/extract.py` exits nonzero on
any gate failure (an Aeneas error or warning, a local opaque function, a referenced external axiom, an `api` function missing
from `scripts/extract-roots.txt`) and writes into `lean/Impl` only on success. Aeneas declares an `axiom` for every external function it knows a name pattern for, used or not (four, `core.iter.range.Step.*.default`, for this crate); extraction removes them (`extract_hash.clean_external`) and the files in `lean/Impl` and the hashes in the report are those of the cleaned text. `lean/Impl/extract-report.json` records a
digest of the extraction inputs (every file under `src/` with its name, `Cargo.toml` without `[dev-dependencies]` and with its package `version` replaced by `0.0.0`, the roots and
the tool pins) and the SHA-256 of each file in `lean/Impl`; `bash scripts/ci.sh --only extract-hash` compares them with the
tree (no tools needed) and rejects symlinks, so a changed input or a hand-edited or added file in `lean/Impl` without a new
extraction fails it. Someone who edits `lean/Impl` and the report together passes that check; the `lean` job of `.github/workflows/ci.yml`
extracts into a new empty directory and compares every file with `lean/Impl` (`diff -r`), which fails on that too. The commands above
do the same by hand. Extraction runs the verified cargo-hax by absolute path (not `cargo hax`, which would pick up a
`$CARGO_HOME/bin/cargo-hax`), on a crate staged in a fresh temporary directory, with a fixed list of environment variables and a
fresh `CARGO_HOME`; the fast check also rejects a build script, `env!`/`include!`-style macros in `src/`, a root `.cargo`
directory or toolchain file, and file names with control characters, since those would change the shipped build or the
manifests without changing the extraction. What is not isolated is listed in the header of `scripts/extract.py` (PATH, HOME,
RUSTUP_HOME). `bash scripts/extract-and-build.sh` runs extraction, the check, `lake build` and the axiom check in one go; it
leaves `extract-report.json` alone and writes its build and axiom results to `lean/.lake/pipeline-result.json`.

### 2.3 The witness check: `scripts/witness-check.sh`

```sh
bash scripts/witness-check.sh
```

This builds `Proofs.TopWitnessCorrect`, which the default build does not import, and checks the 146 names in
`lean/witness-theorems.txt` for standard axioms only. The kernel evaluations are the cost: about 47 minutes cold and about 46
GB peak memory across modules in the recorded run (about 24 GB for the largest declaration). It ends with
`WITNESS CHECK OK: Proofs.TopWitnessCorrect`. If the kernel is killed (exit 137), the machine ran out of memory; rerun on a
larger one. This script does not run on pull requests: it is manual or weekly (`.github/workflows/lean.yml`, on the runner named by the
repository variable `LEAN_HEAVY_RUNNER`), because it needs a large runner.

### 2.4 Cross-checks of the specification

- `scripts/xspec/check-axioms.sh` (after `scripts/xspec/setup.sh` and `scripts/xspec/build.sh`; Lean and Mathlib v4.34.0
  in a separate project; dependencies go under `~/xspec-work`, `XSPEC_WORK` overrides): the proof that `lean/Spec` equals ocaml-pq's transcription. See `xspec/README.md`.
- `scripts/xspec/run-diff.sh all`: executable differential against ocaml-pq (after `scripts/xspec/setup.sh` and
  `scripts/xspec/build.sh`).
- `bash scripts/diff-vcvio/setup-vcvio.sh` once (clones and builds VCVio, the other project), then
  `bash scripts/diff-vcvio/run.sh all`: executable differential against VCVio's `MLDSA.Concrete`. Read the header of each script.
- `scripts/impl-eval.sh lean`, `scripts/impl-eval.sh rs`, `scripts/impl-eval.sh compare`: run the extracted Lean and the
  native Rust on the same inputs and compare.
- Spec against ACVP: in `lean/`, `lake build spec-acvp && .lake/build/bin/spec-acvp`.
- Spec against Wycheproof: the Lean test data is generated and not committed (`lean/SpecTests/WycheproofData.lean` is
  gitignored), so generate it first: `python3 -I scripts/gen-lean-wycheproof.py`, then in `lean/`
  `lake build spec-wycheproof && .lake/build/bin/spec-wycheproof` (it ends with `928/928 cases agree`: 631 verify, 236 sign and 61 keyGen checks over the three parameter sets, and
  prints that the 6 `InvalidPrivateKey` vectors are signed by the spec; the run is slow, so start it in the background).

## 3. Constant-time checks (BINSEC)

These need Linux and Docker. The sweep of round 13 (`checkct/results/sweep-1d8b5c5/`, assurance.md section 4, "Round 13 BINSEC sweep") is the current one. The
harness (`checkct/driver`, which includes the `src/` files by `#[path]`) builds on this tree. `bash checkct/compare-code.sh build NAME` and `compare A B` compare the driver's machine code between two checkouts; `checkct/sweep-post.sh CELL` and `checkct/sweep-compare.py OLD NEW` turn a cell's log into its files and compare two cells. The image builds BINSEC and the Rust toolchains (about 10 minutes):

```sh
docker build -t ct-binsec checkct
```

The recorded sweep (`checkct/results/sweep-1a72d9e/`) was not produced with `checkct/run.sh`: `run.sh` starts one BINSEC job per
CPU, which does not fit in a 64 GB container. It used `checkct/run-select.sh` with `ONLY=.`, one container per target and
profile (the settings are in `checkct/README.md`, "Full sweep at 1a72d9e"). For example, the x86_64 default profile:

```sh
ONLY=. EXCLUDE=census_sign TARGETS=x86_64-unknown-linux-gnu JOBS=4 TIMEOUT=3600 CT_MEMORY=32g \
  NAME=ct-x86-default bash checkct/run-select.sh 2>&1 | tee sweep-x86-default.log
```

For other profiles set `PROFILE=nearcore`, `nearcore-novec`, `avx2`, `nearcore-avx2`, `nearcore-exact` or
`nearcore-exact-novec` (the `nearcore-exact*` profiles are x86_64 only and used `TIMEOUT=600`, `JOBS=8`, `CT_MEMORY=8g`); for thumbv7em and riscv32imac
change `TARGETS`; AArch64 is `NONEON=1 ONLY=. EXCLUDE=census_sign TIMEOUT=3600 JOBS=4 CT_MEMORY=32g bash checkct/aarch64.sh`. The two whole-Sign censuses ran
separately, one container each, because they need far more memory (`ONLY=census_sign JOBS=1 TIMEOUT=3600 CT_MEMORY=110g`, or
`120g`; several do not finish even then). Memory guidance: about 32 GB per container with `JOBS=4` for the sweep probes (the earlier sweep used 64 GB with `JOBS=8`; 16 jobs
in 64 GB got large probes killed); a probe killed at the cap shows only `error`, so check `journalctl -k -g 'Killed process'`;
the sweep ran up to eight containers at once on one machine, so budget the host memory for the sum of the caps. Stopping a
script does not stop its container (`docker kill NAME`). A quick check of a few probes is
`ONLY='ct_select|field_mul' TIMEOUT=900 bash checkct/run-select.sh`; `checkct/run.sh` is the same thing for every probe but needs
`JOBS` set to fit your memory.

`checkct/README.md` explains the other scripts (`run-select.sh` for selected probes and the long sweeps, profiles for the
AVX2 target features and for a downstream release build, split probes for AArch64 and riscv32imac), the memory the large probes
need (some need more than 100 GB; a probe killed at the memory cap shows only `error`, and `journalctl -k -g 'Killed
process'` tells you whether the kernel killed it), the recorded verdicts and what they do and do not show. Tools for
mapping a leak address to a source line are listed there too. BINSEC cannot lift AVX/VEX code, so the profiles that use it (`avx2`, `nearcore-avx2`, and `nearcore-exact`, where `+fma` brings AVX) have no verdict for the
probes that contain vector code; the old static scan of the dispatched AVX2 NTT (`checkct/scan-avx2.sh`) is gone with the dispatch.

## 4. Test vectors

- ACVP: `cargo test --test acvp`; the vendored subset and its source are described in `tests/data/acvp/README.md`.
- Wycheproof: `cargo test --test wycheproof`; see `tests/data/wycheproof/README.md`.

## 5. What a pass means

A passing `lean-check.sh` establishes the theorems in assurance.md, section 1, under the trusted base in section 2 (the Lean
transcription of FIPS 204, the Charon/Aeneas translation, rustc and LLVM, the Lean kernel). A clean `extract.py` diff says
the Lean code is the extraction of the committed Rust. The tests, differentials, fuzzers and BINSEC runs are evidence of a
different kind (no counterexample found), and assurance.md says for each what it covers. None of this is a third-party audit
or a certification.
