# checkct: binary-level constant-time checks (BINSEC)

Port of the RustCrypto `ml-dsa/checkct` harness (signatures repo, rev a3690c4) to this crate. The driver
`#[path]`-includes the crate sources unchanged (`params`, `field`, `rounding`, `ntt`, `keccak`, `keccak4`, `encode`, `sampling`,
`keygen`, `sign`, `verify`, `verify_arith`, `api`; the
crate is `no_std` with no dependencies, so no shims are needed), marks every probe input secret through the `__checkct_private_rand` hook, and lets BINSEC (via `cargo-checkct`) symbolically
execute the compiled release binary, flagging any secret-dependent branch, memory access, or division operand.

This directory is its own workspace (`[workspace]` in `checkct/Cargo.toml`). It is not a member of the main
crate's workspace and the main `Cargo.toml` needed no `exclude`. `src/` is not edited.

> **Reading `error` results.** BINSEC killed at a container's memory cap shows only `error` in the job log. Every `error`
> in the tables below is presumed to be an out-of-memory kill, with no verdict, unless the kernel log
> (`journalctl -k -g 'Killed process'`) shows no kill in its run window. No entrypoint probe of the sweep at 1a72d9e ended `error`;
> its one recorded `error` (a census) and the discarded attempts that ended `error` were each matched to a kernel OOM kill
> (`results/sweep-1a72d9e/oom-kills.txt`).

> **Round 12 (the dispatch is gone).** The sweep tables below are for the tree of 1a72d9e and the profiles it had, including `dispatch` and
> `nearcore-dispatch`, which no longer exist. Removing the NTT dispatch changed the compiled NTT callers of Sign and KeyGen in the default build
> (`results/smoke-p12/compare-code.txt`), so the verdicts of this tree are in `results/smoke-p12/`: the NTT probes (`select-ntt-default.log`: 81 of
> 84 cells `secure`, the rest the whole-Sign census) and the smoke of eight probes on three targets (`smoke-default.log`, `verdicts.tsv`, against round 10's counts).
> `docs/assurance-history.md` section 4, "Round 12", reads them.

> **Round 13 (the sweep of this tree).** `src/ntt.rs` has its safe `dispatch` wrapper module again (no choice inside), and the driver of the default release profile is
> identical to fv-p11's in every function on riscv32imac, thumbv7em and x86_64 (234, 239, 234; `compare-code.sh compare p11 p13f`). The full sweep was rerun on the tree of 1d8b5c5
> (the `src/` of the final tree; later commits change documents only): every profile of the "Profiles" table except the removed dispatch ones, on x86_64 (`default`, `nearcore`,
> `nearcore-novec`, `nearcore-exact`, `nearcore-exact-novec`, the `ZEROIZE=1` builds of `default` and `nearcore-exact-novec`, and the NTT probes of `avx2` and `nearcore-avx2`),
> thumbv7em, riscv32imac and AArch64 `NONEON=1`, plus the whole-Sign censuses that finished. The per-cell files (`*.verdicts.tsv`, `*.summary.txt` with the SHA-256 of each analyzed
> ELF and script, `*.header.txt`, `*.unknowns.txt`, `driver-sha256.txt`, the compared verdicts) are in `results/sweep-1d8b5c5/`; `docs/assurance-history.md` section 4, "Round 13", reads them. `sweep-compare.py`
> compares two verdict files probe by probe and `sweep-post.sh` produces a cell's files from its log.

## Running

Linux only (BINSEC), via Docker:

    docker build -t ct-binsec checkct                           # once, and again after Dockerfile changes; ~10 min
    bash checkct/run.sh 2>&1 | tee ct.log

Scripts (all start from the repository root; stopping a script does not stop its container, so use `docker kill $NAME` too):

| script | purpose | environment |
|---|---|---|
| `run.sh` | all probes, all three targets (`cargo-checkct run --all-leaks`); `JOBS` defaults to every CPU, which does not fit a 64 GB container, so the full sweeps use `run-select.sh` with `ONLY=.` instead | `TIMEOUT` (900 s per probe), `JOBS`, `OUT` (copies the three `<target>.driver` binaries), `NAME`, `PROFILE=nearcore` |
| `run-select.sh` | only probes matching a regex, long timeouts; builds with `cargo-checkct`, then calls `binsec` directly. Streams a `done <target> <probe> <status>` line per probe and ends with a `Summary:` block like `run.sh` | `ONLY` (regex), `EXCLUDE` (regex), `TARGETS`, `TIMEOUT` (7200), `JOBS` (4), `OUT`, `NAME`, `PROFILE`, `TRACE=1` (last executed instruction per probe), `EXPERIMENTS=1` (the `exp_*` probes), `CT_TOOLCHAIN` (nearcore-exact; default 1.95.0), `ZEROIZE=1` (builds the driver with the crate's `zeroize` feature, x86_64 profiles without dispatch; no other run builds that code) |
| `unknowns.py BIN LOG...` | maps every leak address, every cut path (`uninterpreted "KO"`) and every `TRACE` last instruction of a `Summary:` block to function, source line and instruction (GNU `objdump`; `leaks.sh` needs `llvm-objdump`). `python3 -I checkct/unknowns.py DIR/x86_64-unknown-linux-gnu.driver LOG` | |
| `verdicts-tsv.py LOG [UNKNOWNS_TXT]` | regenerates the per-probe `*.verdicts.tsv` of a sweep from the `Summary:` block of its log (with the `unknowns.py` output, the leak and cut sites of x86_64 rows are added) | |
| `leak-context.sh BIN ADDR...` | disassembly around an address with source lines (`BEFORE`, `AFTER` bytes) | |
| `probe-now.sh CONTAINER PROBE [T] [binsec args]` | reruns one probe inside a running `run-select.sh` container for a few seconds with the full BINSEC log (diagnosis of a sweep in flight; not for verdicts) | |
| `leaks.sh LOG BINDIR` | maps every leaking instruction address of a `Summary:` block to `file:line` and the instruction (`llvm-objdump -d -l` on the `OUT` binaries) | `OBJDUMP` as third argument |
| `aarch64.sh` | experiment: AArch64 (see below); `cargo-checkct` does not support the target, so it builds the driver for `aarch64-unknown-linux-gnu` in the container and writes the BINSEC scripts itself | `ONLY`, `TIMEOUT`, `JOBS`, `NAME`, `OUT`, `NONEON=1` |
| `split-run.sh [round2]` | the split probes of `driver/src/split.rs` on AArch64 (`NONEON=1`) and riscv32imac, two containers in parallel, exit status nonzero if either fails (see "Split probes") | `TIMEOUT` (3600), `JOBS` (2 per container), `AONLY`, `RONLY` |
| `select-ntt.sh [mode]` | the NTT and field-product probes and the KeyGen/Sign pieces built on them, through `run-select.sh`; `mode` is `default`, `avx2` or `nearcore-avx2` (see "Profiles") | `TIMEOUT` (3600), `JOBS`, `OUT`, `NAME`; the 2nd and 3rd arguments replace the probe regex and the target list |

`PROFILE=nearcore` builds with `opt-level = 3`, `lto = "fat"`, `codegen-units = 1`, `panic = "abort"` (through
`CARGO_PROFILE_RELEASE_*`). It approximates nearcore's release build but does not match it: nearcore (checked at
nearcore cd5a94457, 2026-11-03) also sets `overflow-checks = true`, builds x86_64 with
`-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq` and
`-Cforce-unwind-tables=y`, and uses Rust 1.95.0. The `nearcore` results below are for this approximation only; the
profile that takes all of those settings is `nearcore-exact`
(section "`nearcore-exact`" below; x86_64 only, `run-select.sh`). The default is the checkct workspace profile (release plus debug info, `panic = "abort"`,
16 codegen units). BINSEC's `-sse-timeout` is only checked between paths, so a probe stuck in a long solver query
can run well past `TIMEOUT`.

### Profiles

The crate has no run-time AVX2 dispatch and no `avx2` code selection any more (round 12): the driver has no `avx2` feature, `src/cpu.rs` and `fast_verify` are gone from it, and each profile is one
compilation of the same sources. A build that wants AVX2 code gets it from target features.

| `PROFILE` | driver build |
|---|---|
| (unset) | the checkct workspace profile (release plus debug info, `panic = "abort"`, 16 codegen units) |
| `nearcore`, `nearcore-novec` | opt-level 3, fat LTO, one codegen unit, `panic = "abort"`; `nearcore-novec` adds `-C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false` |
| `avx2`, `nearcore-avx2` | the default profile (`nearcore-avx2`: the `nearcore` settings) with `-C target-feature=+avx2`; BINSEC cannot lift the VEX code, so probes that reach vector code end `unknown` |
| `nearcore-exact` | nearcore's `[profile.release]` incl. `overflow-checks` (driver package), nearcore's x86_64 target features, rustc 1.95.0 |
| `nearcore-exact-novec` | `nearcore-exact` plus `-C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false` (x86_64 only) |

An unknown `PROFILE` is rejected. The profiles `dispatch`, `nearcore-dispatch` and `nearcore-exact-dispatch` of earlier rounds built the driver with the `avx2` Cargo feature and pre-set the dispatch cache
(`static AVX2: AtomicU8`, anchored on the symbol `driver::cpu::AVX2`) to "no AVX2" in every x86_64 BINSEC script; they, the anchor and `scan-avx2.sh` are removed. The sweep tables below that name them record
results for the trees at 1a72d9e and before, where those profiles existed, and are history.

`select-ntt.sh` alone is the default build; `select-ntt.sh avx2` and `select-ntt.sh nearcore-avx2` build with `+avx2` (x86_64 only).

Toolchain (every profile except `nearcore-exact*`, which use 1.95.0, see below): `nightly-2026-10-06` with `rust-src` (`checkct/rust-toolchain.toml`), `-Zbuild-std=core,panic_abort` with
`compiler-builtins-mem` (`.cargo/config.toml`, copied from upstream). BINSEC 0.11.3, unisim_archisec 0.0.14,
cargo-checkct @ 85271e5. Checks: `control-flow,memory-access,dividend,divisor`. Building only (no BINSEC) works
anywhere with the toolchain: `cd checkct && cargo build --release -p driver --target x86_64-unknown-linux-gnu`.

Scratch space: scripts that keep driver binaries or logs (`select-ntt.sh`, `run-prepared.sh`, `prepared-leaks.sh`, `at.sh`,
`scan-avx2.sh`) put them under `$ML_DSA_SCRATCH`, which defaults to `${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch`.

`checkct_macros/src/lib.rs`, `checkct_macros/Cargo.toml`, `rust-toolchain.toml` and `.cargo/config.toml` are copied from upstream
(RustCrypto `ml-dsa/checkct` at rev a3690c4, Apache-2.0 OR MIT; each carries an SPDX line and a note on its origin), as
`cargo-checkct init` generates them (`rust-toolchain.toml` without the "autogenerated" marker line). `driver/src/rng.rs`,
`driver/src/main.rs` and `driver/src/signing.rs` are adapted from the files of the same name in that upstream harness (each carries the
same SPDX line and an origin note): `rng.rs` is the same hook pair without the `rand_core` impls, `main.rs` includes this crate's
modules instead of upstream's, and `signing.rs` probes this crate's `sign::response` and `sign::hint_step`. The other driver files
(`probes.rs`, `extra.rs`, `prepared.rs`, `split.rs`, `experiments.rs`) are this project's.

## Full sweep at 1a72d9e (November 5–6, 2026, UTC)

The results at 1a72d9e (the current ones are `results/sweep-1d8b5c5/`, see the Round 13 note above). `src/` at 1a72d9e: the tree after the merge of the change to Sign. The per-attempt intermediates of
`sign::attempt` live in caller-owned buffers (`response_into`, `hint_step_into`; `response` and `hint_step` are those functions on
fresh buffers) that the `zeroize` feature wipes on every path (`wipe_attempt`); secret keys are decoded in place
(`sk_decode_into`, `unpack_signed_into`, `prepare_sk_into` with `ntt_vec_into`, `ntt_inverse_in_place`,
`scalar_vector_ntt_inverse_into` and `matrix_vector_ntt_into`) instead of being returned by value; and the rejection loop's guard is
`sign::more_attempts`. `expand_s` in `sampling.rs` now returns through a local that `zeroize` wipes, and `field.rs` changed in
comments only. No probed function changed its name or signature, so no probe was added or edited: the by-value functions the probes
call (`sign::response`, `sign::hint_step`, `encode::sk_decode`, `ntt::scalar_vector_ntt_inverse`, `ntt::matrix_vector_ntt`,
`sign::prepare_sk`) are thin wrappers over the new `_into` functions and `api::signing_key_NN` calls `prepare_sk_into`, so the
secret-touching code of the default build is what the probes already analyze (see "Not covered" for what that leaves out). The driver sources are those of c63f632
except for SPDX and origin comments; `run-select.sh` is as of a29e06e (the new `ZEROIZE=1` option). Raw per-probe results, with every
leak and stop address mapped to function, source line and instruction by `unknowns.py`, are in `checkct/results/sweep-1a72d9e/`
(`<target>-<profile>.verdicts.tsv`, `.unknowns.txt`/`.summary.txt`, `.header.txt` with the toolchain and flags the run printed). The
previous full sweep, at 15b4ce2 (the tree after ae6023c, which put `wrapping_*` arithmetic into `field.rs`, `rounding.rs` and `encode.rs`
so that no overflow-check guard is left on a secret value, CT-3 in `docs/assurance.md`), is in `checkct/results/sweep-15b4ce2/`; every
comparison below is probe by probe against its TSVs.

Method: `run-select.sh` (AArch64: `aarch64.sh` with `NONEON=1`), `ONLY=.`, one container per target and profile,
`EXCLUDE=census_sign` (the censuses ran separately, below). The x86_64 checkct-profile, `nearcore`, `dispatch` and
`nearcore-dispatch` runs, thumbv7em, riscv32imac and AArch64: `TIMEOUT=3600`, `JOBS=4`, 32 GB cap per container. The three
`nearcore-exact*` runs: `TIMEOUT=600`, `JOBS=8`, 8 GB cap (a first pass with a 20 GB cap kept no driver binaries, which `unknowns.py`
needs, and was rerun with `OUT` set; the rerun is the recorded one). Up to eight containers ran at the same time on one Linux machine
whose containers share a 165 GiB memory limit. The x86_64 profiles other than `nearcore-exact*` use `nightly-2026-10-06` (LLVM 23.1.3),
`nearcore-exact*` use rustc 1.95.0 (LLVM 22.1.2); the `.comment` check passed in every x86_64 run (`x86_64-*.header.txt`); the
thumbv7em, riscv32imac and AArch64 headers do not record it. The machine is a preemptible cloud instance and was terminated once in the
first hours: the three slowest probes of the x86_64 default run (`rej_bounded_poly_eta2/4`, `control_prepared_branch_44`) were lost and
rerun alone (`JOBS=3`, 16 GB, 3600 s) on a byte-identical driver binary, and `x86_64-default.*` merges the two logs; a thumbv7em pass and
a traced riscv32imac pass that were running were lost and rerun in full. A first thumbv7em pass was also discarded after its cap was
lowered while it ran (killed probes, `oom-kills.txt`). None of the discarded runs enters the tables.

**Count basis.** A run has 114 entrypoints without the censuses on the x86_64 default and `dispatch` builds, thumbv7em, riscv32imac
and AArch64 (85 non-split and 29 split), and 113 on x86_64 `nearcore`, `nearcore-dispatch` and `nearcore-exact*` (28 split, with
`split_vec_power2round_4` folded into `vec_power2round_44` by LTO); the AArch64 run has 116 rows with the two censuses. Against 15b4ce2,
`split_vec_power2round_4` is a new entrypoint in the x86_64 default, thumbv7em and AArch64 builds (`secure` in all three). The
"87-probe basis" column is the 85 non-split entrypoints plus the two censuses; the split probes have their own column. Which field
probe survives LTO as its own entrypoint differs by profile (the default TSVs list `field_mul` and not `field_add`, the `nearcore-exact*`
TSVs the reverse); the count of 85 holds in both.

Columns: secure / expected insecure / unexpected insecure / unknown / no verdict (OOM). In brackets, the 15b4ce2 value where it
differs.

| target / profile | 87-probe basis | split probes |
|---|---|---|
| x86_64, default | 80 / 6 / 0 / 0 / 1 (prepared census not rerun) | 29 / 0 / 0 / 0 / 0 [28 / 0 / 0 / 0 / 0] |
| x86_64, `nearcore` | 80 / 7 / 0 / 0 / 0 | 28 / 0 / 0 / 0 / 0 |
| x86_64, `dispatch` | 80 / 6 / 0 / 0 / 1 (prepared census not rerun) | 29 / 0 / 0 / 0 / 0 |
| x86_64, `nearcore-dispatch` | 80 / 6 / 0 / 0 / 1 (prepared census not rerun) | 28 / 0 / 0 / 0 / 0 |
| thumbv7em, default | 81 / 4 / 0 / 0 / 2 (censuses not rerun) | 29 / 0 / 0 / 0 / 0 [28 / 0 / 0 / 0 / 0] |
| riscv32imac, default | 75 / 6 / 0 / 5 / 1 [78 / 6 / 0 / 2 / 1] (censuses not rerun) | 26 / 0 / 0 / 3 / 0 [23 / 0 / 0 / 6 / 0] |
| AArch64 `NONEON=1` | 73 / 3 / 0 / 11 / 0 | 27 / 0 / 0 / 2 / 0 [26 / 0 / 0 / 2 / 0] |

Not on the 87-probe basis, all probes of the run (113 entrypoints plus the two censuses):

| x86_64 profile | secure / expected insecure / unexpected insecure / unknown / no verdict |
|---|---|
| `nearcore-exact` | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-dispatch` | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-novec` | 108 / 6 / 0 / 0 / 1 [108 / 7 / 0 / 0 / 0] |

Reading the first table: the "expected insecure" cells are `rej_bounded_poly_eta2/4`, the positive controls (`control_early_exit_44`,
`control_prepared_branch_44`, `control_prepared_index_44`; on thumbv7em only the first and the third, the branch control is the invalid
`secure` one; on riscv32imac also the standalone `ct_lt_mask`) and, on x86_64, the censuses that ran, which report only the public
`sampling.rs:35` leak (then 1 pending path) (below). Every probe of the first table has a verdict except the unknown and OOM cells shown,
and each `secure` row has 0 pending paths and all checks passing. **No unexpected `insecure` result on any target or profile; no new
leak.**

Against the previous full sweep (15b4ce2), **no verdict changed on x86_64 (all seven profiles), thumbv7em or AArch64**, probe for
probe, and every leak and cut path of those runs is at the same mnemonic, source line and function as before; only the addresses and
the visited-instruction and check counts moved with the code (they differ for 46 to 88 of the probes of each run). On riscv32imac seven
verdicts changed: `prepare_sk_{44,65,87}` went from `secure` to `unknown` (a solver stall, below), `control_prepared_branch_44` from
`unknown` to `insecure` (the expected result for a positive control, found within the sweep's 3600 s this time), and
`split_prepare_sk_65_col`, `split_prepare_sk_65_row` and `split_prepare_sk_87_6x1` from `unknown` to `secure`. The one loss of
evidence is the riscv32imac `prepare_sk_*` rows.

Every non-secure probe of the sweep that is not an `nearcore-exact*` unknown:

| probe | where | result | reason |
|---|---|---|---|
| `rej_bounded_poly_eta2/4` | every row above | insecure, expected | sampler accept test, public outcome (`sampling.rs:129`, `:132`) |
| `control_early_exit_44` | every row above | insecure, expected | positive control, `extra.rs:221` (8 leaks on x86_64) |
| `control_prepared_branch_44` | x86_64 (all profiles but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac | insecure, expected | positive control, `prepared.rs:76` |
| `control_prepared_index_44` | x86_64 (all but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac, thumbv7em | insecure, expected | positive control, `prepared.rs:96` |
| `control_prepared_branch_44` | thumbv7em | secure, invalid control | branch lowered to a select |
| `control_prepared_{branch,index}_44` | AArch64 | unknown | built on `prepare_sk_44`, which does not finish (uncontrolled `prepare_sk` rows) |
| `control_prepared_{branch,index}_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown | cut path in `prepare_sk`'s NTT (`vinsertps`) before the control site; the `prepare_sk_*` rows there are uncontrolled |
| `ct_lt_mask` | riscv32imac | insecure, documented | standalone probe, in-crate callers are secure |
| `vec_power2round_87`, `split_vec_power2round_{5,6,7}` | riscv32imac | unknown | 1 pending path, no leak (unchanged, solver capacity) |
| `prepare_sk_{44,65,87}` | riscv32imac | unknown | new; 1 pending path, no leak, stuck at a store in `ntt_body_mut`; below |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `split_prepare_sk_87_{7x1,col}`, the two censuses | AArch64 | unknown | 1 pending path stuck in one solver query (unchanged, U-42) |

Censuses (`census_sign_internal_44`, `census_sign_prepared_44`; `checkct/results/sweep-1a72d9e/x86_64-censuses.txt`), x86_64,
`JOBS=1`, `TIMEOUT=3600`, one container per profile and census. A census proves nothing (the rejection samplers of Sign are public-outcome
branches); the aim is to catch an obvious leak. The cap was 110 GB for the `default`, `nearcore`, `dispatch`, `nearcore-dispatch` and
`nearcore-exact-novec` runs and 12 GB for `nearcore-exact*` (they are cut within 2 s). Earlier attempts killed by the 165 GiB limit that
all containers share, or by a 64 GB cap, were discarded and rerun (`oom-kills.txt`):

| profile | `census_sign_internal_44` | `census_sign_prepared_44` |
|---|---|---|
| default | insecure: one leak, `sampling.rs:35` (`sample_in_ball` accept test, public outcome) at 0x242548; 1 pending path, 2,874,206 instructions, 205,381 of 205,382 control-flow checks passed | not rerun: no verdict at 15b4ce2 (OOM, killed at 110 GB and alone at 120 GB) |
| `nearcore` | insecure: `sampling.rs:35` only (0x20e2bb); 2,845,144 instructions | insecure: `sampling.rs:35` only; 1,535,058 instructions |
| `dispatch` | insecure: `sampling.rs:35` only (0x25ba78); 2,867,291 instructions | not rerun: no verdict at 15b4ce2 (OOM at 120 GB) |
| `nearcore-dispatch` | insecure: `sampling.rs:35` only (0x20dceb); 2,838,100 instructions | not rerun: OOM above 120 GB on an earlier tree |
| `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 726,934 instructions, 0 pending paths; no `sampling.rs:35` leak reached | unknown: cut at the same instruction after 82,072 / 82,076 instructions |
| `nearcore-exact-novec` | insecure: `sampling.rs:35` only (0x20d32a); 1 pending path, 2,825,690 instructions, 228,827 of 228,828 control-flow checks passed | **no verdict, OOM**: killed at the 110 GB cap (binsec at 115.1 GB RSS) and again alone at 150 GB (157.0 GB RSS); it was `insecure` (public leak only) at 15b4ce2, in 120 GB |

So the whole of Sign gets no better than "the only leak found is the public `sample_in_ball` accept test" where the census runs (the
internal census of five x86_64 profiles, the prepared census of `nearcore`); under nearcore's exact build it is still cut at the NTT.
The prepared census of `nearcore-exact-novec` changed from a verdict to no verdict: it needs more memory on this tree than on the
previous one (more than 150 GB, against less than 120 GB); the code shape changed, and the census is not evidence either way.

### `nearcore-exact` and `nearcore-exact-dispatch` at 1a72d9e

Both profiles give the same verdict for every probe (113 entrypoints, 600 s per probe), and each probe has the verdict it had at
15b4ce2: 61 secure, 3 expected insecure (`rej_bounded_poly_eta2/4` at `sampling.rs:129`/`:132`, and the positive control
`control_early_exit_44` at `extra.rs:221`), 0 unexpected insecure, 49 unknown. The six `sk_is_well_formed` probes that were
`insecure` on the tree before 15b4ce2 (CT-3 in `docs/assurance.md`) are `secure`.

At 15b4ce2, against the sweep before it, 6 probes had gone from `insecure` to `secure`
(`sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}`: 51,583 / 76,740 / 97,281 and 65,893 / 82,034 / 97,281
instructions, 12,707 / 18,908 / 24,020 and 17,671 / 20,744 / 24,020 control-flow checks, 0 pending paths) and 16 from `unknown` to
`secure` (`sk_decode_*`, `sk_encode_*`, `expand_mask_*`, `barrett_reduce`, `vec_power2round_87`,
`split_vec_power2round_{5,6,7,8_hi,8_lo}`; they had been stuck at an overflow-check guard in `field.rs`, and the guards are gone);
`field_add` was a new entrypoint (secure) then. At 1a72d9e nothing moved in either direction: the same 61 are `secure` and the same
49 `unknown`, at the same instructions (below).

**What `unknown` means here.** "0 pending paths, no leak among the checks that passed, one path cut at an instruction BINSEC
cannot lift" (`[sse:error] Cut path 0 (uninterpreted "KO")`; the 600 s limit is not reached: 0.08 to 1.4 s per probe; every cut line
and status time in `sweep-1a72d9e/x86_64-nearcore-exact.cut-paths.txt`) for 48 of the 49, and a solver stall for one:

| unliftable instruction | where | probes |
|---|---|---|
| `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `ntt.rs:111` (`ntt_layer::<8, 16>`, forward NTT layer), `0x221610` | 31: `ntt`, `ntt_vec_44`, `compute_t_*` (4), `prepare_sk_*` (3), `prepare_sk_1x1_44`, `signing_key_*` (3), `control_prepared_{branch,index}_44`, and the `split_*` NTT, `compute_t` and `prepare_sk` pieces (16) |
| `vblendvps` with `xmm` operands | vectorized `small_reduce` (the `wrapping_sub(Q & mask)` select, `field.rs:25`) right after `mont_reduce` (`field.rs:76`) in the pointwise product; objdump labels every one of these addresses `<u32>::wrapping_sub`, `uint_macros.rs:2494`, and the enclosing frames were checked for `0x207771` (`hint_step_44`, `response_44`) only | 16: `matrix_vector_ntt_*` (4), `scalar_vector_ntt_inverse_1`, `multiply_ntt`, `hint_step_*` (5), `response_*` (5) |
| `vblendps $0xf0,%ymm7,%ymm13,%ymm6` | `ntt.rs:131` (`ntt_inverse_layer::<4, 32>`, inverse NTT layer), `0x222619`: a 256-bit (`ymm`) blend | 1: `ntt_inverse` |

All three are VEX encodings (`vinsertps`, `vblendvps`, `vblendps`); BINSEC 0.11.3 does not lift them, the same limit as `vtestps` in
the experiments (upstream U-44). Under nearcore's target features (`+fma` implies AVX) LLVM emits them for the vectorized loops.
Unknown rows are not findings: they are probes about which BINSEC says nothing for nearcore's exact build, and the two censuses
are in the same state (cut at `vinsertps` after 726,927 and 82,072 instructions; `x86_64-censuses.txt`).
Per probe (steps = executed instructions when the path was cut, `nearcore-exact`; the last column is the address in
`nearcore-exact-dispatch`, which cuts at the same mnemonic for every probe; nine `vblendvps` rows have other register operands
there, in `sweep-1a72d9e/x86_64-nearcore-exact-dispatch.unknowns.txt`):

| probe | steps | stop address | instruction | address in `-dispatch` |
|---|---|---|---|---|
| `compute_t_1x1` | 25971 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `compute_t_44` | 192485 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `compute_t_65` | 328115 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `compute_t_87` | 568425 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `matrix_vector_ntt_1x1` | 15301 | `0x22b593` | `vblendvps %xmm7,%xmm14,%xmm5,%xmm7` | `0x23372a` |
| `matrix_vector_ntt_44` | 159965 | `0x2063c0` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x232310` |
| `matrix_vector_ntt_65` | 281169 | `0x206c90` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x232730` |
| `matrix_vector_ntt_87` | 507044 | `0x22aa10` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x232b50` |
| `ntt_vec_44` | 33301 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `scalar_vector_ntt_inverse_1` | 15147 | `0x22e1de` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x2366ce` |
| `control_prepared_branch_44` | 82051 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `control_prepared_index_44` | 82072 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `prepare_sk_1x1_44` | 40725 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `prepare_sk_1x1_65` | 49510 | (1 pending path, see text) | | |
| `prepare_sk_44` | 82052 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `prepare_sk_65` | 127096 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `prepare_sk_87` | 164978 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `signing_key_44` | 82052 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `signing_key_65` | 127100 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `signing_key_87` | 164982 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `multiply_ntt` | 14376 | `0x24080d` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x247c9d` |
| `ntt` | 11066 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `ntt_inverse` | 10153 | `0x222619` | `vblendps $0xf0,%ymm7,%ymm13,%ymm6` | `0x2203a9` |
| `hint_step_1_44` | 22232 | `0x21db8a` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x21e9aa` |
| `hint_step_1_65` | 22232 | `0x21db8a` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x21e9aa` |
| `hint_step_44` | 67667 | `0x207771` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x20a151` |
| `hint_step_65` | 97619 | `0x207e31` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x2065d0` |
| `hint_step_87` | 127595 | `0x208831` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x207360` |
| `response_1x1_44` | 36821 | `0x21d0ab` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x21dd8a` |
| `response_1x1_65` | 36821 | `0x21d0ab` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x21dd8a` |
| `response_44` | 127938 | `0x207771` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x208582` |
| `response_65` | 172055 | `0x245e0f` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x24d2de` |
| `response_87` | 231851 | `0x246f2f` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x24e6fe` |
| `split_compute_t_44_2x2` | 65559 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `split_compute_t_44_col` | 72714 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `split_compute_t_44_row` | 72716 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x22be00` |
| `split_ntt_vec_into_1` | 11066 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_ntt_vec_into_7` | 55334 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_ntt_vec_into_8` | 62680 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_44_col` | 84515 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_44_row` | 51241 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_65_col` | 132346 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_65_row` | 66274 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_2x1` | 67880 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_4x1` | 99117 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_6x1` | 135284 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_7x1` | 139585 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_col` | 154339 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |
| `split_prepare_sk_87_row` | 78606 | `0x221610` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225890` |

The 49th unknown, `prepare_sk_1x1_65`, is not a cut path: 1 pending path at the 600 s limit (49,510 instructions) and at a 3600 s
rerun with `TRACE=1` (`x86_64-nearcore-exact.prepare_sk_1x1_65-trace-3600s.txt`: 49,510 again, last step 49,529: `0x22006e movdqu
%xmm6,0x3c0(%rdi)` in `ntt_body_mut`, +0x112e), 13,214 control-flow checks passed, no leak. A solver stall, not a VEX cut; same in
`nearcore-exact-dispatch` at 600 s (49,514 instructions). (At 15b4ce2: 50,277 instructions, last step 50,296 at the same kind of store.)
It is `secure` in `nearcore-exact-novec` (below). 


### `nearcore-exact-novec`: the same flags with the loop and SLP vectorizers off

New profile (`run-select.sh`, `PROFILE=nearcore-exact-novec`, c63f632): `nearcore-exact` plus `-C llvm-args=-vectorize-loops=false
-C llvm-args=-vectorize-slp=false` (what `nearcore-novec` does for the older profile). Overflow checks, nearcore's target features
(`+fma`, so AVX is on) and rustc 1.95.0 are unchanged (`x86_64-nearcore-exact-novec.header.txt`). 113 probes, 600 s each:
**108 secure, 5 expected insecure, 0 unexpected insecure, 0 unknown** (the same, probe for probe, at 15b4ce2 and 1a72d9e; also with
the crate's `zeroize` feature on, `x86_64-nearcore-exact-novec-zeroize.*`): no cut path and no timeout. The five insecure are
`rej_bounded_poly_eta2/4`, `control_early_exit_44` and, now that the NTT is analyzable, both prepared positive controls
`control_prepared_branch_44` (`prepared.rs:76`) and `control_prepared_index_44` (`prepared.rs:96`). So every one of the 49 probes that
is `unknown` under `nearcore-exact` (the NTT, `hint_step`, `response`, `prepare_sk`, `signing_key`, `compute_t` family and the
splits) has a verdict with the vectorizers off (47 `secure`, and the two prepared controls `insecure` as intended), including
`prepare_sk_1x1_65` (`secure`), and the `prepare_sk_*` rows are controlled there
(under `nearcore-exact*` the two prepared controls are cut in `prepare_sk`'s NTT before the control site, so the `prepare_sk_*`
rows of those profiles are uncontrolled as well as unknown). What this is: evidence about a build that is not nearcore's, since
nearcore leaves the vectorizers on. It shows that the scalar code, with nearcore's overflow checks and target features, has no
secret-dependent branch, address or division operand in these probes; it does not cover the vectorized NTT and product code that
nearcore's compiler actually emits.

### thumbv7em, riscv32imac, AArch64 without NEON

- **thumbv7em** (default profile, 114 probes, 3600 s): 110 secure, 4 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_index_44`), 0 unknown. `control_prepared_branch_44` is `secure` here, an invalid
  control (the branch is lowered to a select). The two censuses were not rerun (OOM at 120 GB, below).
- **riscv32imac** (default profile, 114 probes, 3600 s): 101 secure, 6 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_branch_44`, `control_prepared_index_44`, and the standalone `ct_lt_mask`: one
  control-flow leak, 0x04100e in this run), 7 unknown: `vec_power2round_87` (177,574 instructions, 1 pending path) and
  `split_vec_power2round_{5,6,7}` (unchanged), and `prepare_sk_{44,65,87}` (new, below). `control_prepared_branch_44` is
  `insecure` in the sweep run itself this time (it was `unknown` at 3600 s at 15b4ce2 and `insecure` only in a rerun alone, so the
  result depends on exploration order). The three `split_prepare_sk_*` pieces that were `unknown` at 15b4ce2
  (`split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1`) are `secure`.

  **`prepare_sk_{44,65,87}` went from `secure` to `unknown`.** At 15b4ce2 they visited 2,350,080 / 4,160,737 / 7,342,811
  instructions and passed all 136,950 / 230,741 / 378,811 control-flow checks. Now each ends with 1 pending path and no leak after
  447,444 / 427,074 / 698,393 instructions (53,928 / 71,526 / 102,327 control-flow checks passed). With `TRACE=1` at 600 s
  (`sweep-1a72d9e/riscv32imac.rerun-trace-600s.txt`, `JOBS=3`) and again at 7200 s for `prepare_sk_{44,65}` (`riscv32imac.rerun-trace-7200s.txt`,
  `JOBS=2`) the visited-instruction counts are exactly those of the sweep run, so neither contention nor the timeout is the cause:
  one solver query never returns. The last executed instruction is a store in `ntt_body_mut`: `0x0497de sw t6,-8(a6)` (+0xb94) for
  `prepare_sk_44`, `0x049704 sw s1,0(a7)` (+0xaba) for `prepare_sk_65` and `prepare_sk_87`; the second is the instruction (same
  offset in `ntt_body_mut`) at which the three `split_prepare_sk_*` probes stalled at 15b4ce2 (then at `0x045e28`). A control
  (`riscv32imac.control-15b4ce2.txt`): the same driver built against `src/` of 15b4ce2 gives `prepare_sk_44` `secure` with exactly the
  old counts (2,350,080 instructions, 136,950 control-flow and 771,273 memory-access checks), so the change is in `src/`, not in the
  harness, the toolchain or the machine. What in `src/` moves the stall is not pinned down (`prepare_sk_into` and `sk_decode_into` changed, and the compiler lays out
  `ntt_body_mut` and its callers differently); the stall is at the same kind of store as before and has moved from the
  `split_prepare_sk_*` wrappers to the full-size `prepare_sk_*`. Coverage is not reduced: the
  public constructors `signing_key_{44,65,87}` (`prepare_sk_into` on a fresh key, 2,267,295 / 4,026,939 / 7,130,496 instructions) are
  `secure` at full size, so are `prepare_sk_1x1_{44,65}` and all riscv split pieces except the three capacity probes, which now
  include the three `split_prepare_sk_*` probes above. No leak was found.
- **AArch64 without NEON** (`aarch64.sh`, 116 probes with the two censuses, 3600 s): 100 secure, 3 expected insecure
  (`rej_bounded_poly_eta2/4`, `control_early_exit_44`), 13 unknown: `compute_t_44`, `prepare_sk_{44,65,87}`,
  `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44`, `control_prepared_{branch,index}_44`, and the two
  split pieces `split_prepare_sk_87_{7x1,col}`. All are the same solver stall: one pending path, with the visited-instruction count identical at 300, 600, 3600 and 7200 s in the earlier runs (this sweep ran 3600 s), so one solver query never returns (a BINSEC limitation, not a verdict). All 29 split
  probes ran (27 secure, 2 unknown).
- Every `secure` row of the thumbv7em, riscv32imac and AArch64 runs has 0 pending paths and all of its (nonzero) control-flow and
  memory-access checks passing (`*.verdicts.tsv`); the x86_64 rows too.
- `NONEON` code is not what an AArch64 production build runs (NEON is on), and BINSEC cannot lift the vectorized code of that
  build (`umax`/`umin` on `.4s` vectors, U-40). The scalar result shows that the source-level structure is constant time with the
  AArch64 select lowering (`csel`), not that the NEON code is. `aarch64.sh` is not a supported `cargo-checkct` target: it builds
  the driver for `aarch64-unknown-linux-gnu` itself (release, same profile, static relocation, `rust-lld`) and generates the BINSEC
  scripts with the `cargo-checkct` template adapted to AArch64 (return address in `x30`, `halt at` the panic hook and the sentinel
  return address).

### Not rerun, and why

These were not rerun at 1a72d9e (about an hour each, and the result at the same cap would not be a verdict: the earlier runs needed
more than 120 GB, and the machine's containers share 165 GiB); their results are those of the last sweep that ran them (e9a1c74 for the
first four, 15b4ce2 for the x86_64 default and `dispatch` prepared censuses). `src/` changed again, so a different outcome is possible,
but nothing points to one; the `nearcore-exact-novec` prepared census, which fitted in 120 GB before and no longer fits in 150 GB, shows
that this can go either way.

- thumbv7em `census_sign_internal_44`, `census_sign_prepared_44`, riscv32imac `census_sign_prepared_44` and x86_64 `default`, `dispatch`
  and `nearcore-dispatch` `census_sign_prepared_44`: out of memory at the 120 GB cap.
- riscv32imac `census_sign_internal_44`: 4 pending paths at 3600 s and 7200 s.
- Static-AVX2 profiles `avx2` and `nearcore-avx2` (`select-ntt.sh avx2`): not part of the sweep tables.

### OOM ledger

No entrypoint probe of the sweep ended `error`. The only recorded `error` is `census_sign_prepared_44` under `nearcore-exact-novec`:
a kernel OOM kill at the 110 GB cap (binsec at 115.1 GB RSS) and another, alone, at a 150 GB cap (157.0 GB RSS), both matched to a
kernel log entry (`journalctl -k -g 'Killed process'`; `sweep-1a72d9e/oom-kills.txt`). Seven more kills belong to discarded runs
(a thumbv7em pass whose cap was lowered while it ran, two census containers killed by the shared 165 GiB limit, two prepared censuses
at a 64 GB cap); each was rerun and none enters the tables. A census killed alone at 150 GB is recorded as "needs more than 150 GB" and
the cap is not raised again.

Other deviations from the method above:

- Up to eight containers ran at once in the first hours (`JOBS=4` and 32 GB each for the 3600 s runs, `JOBS=8` and 8 GB each for
  `nearcore-exact*`), 7200 s reruns used `JOBS=2`, and the censuses ran one at a time at the end. Where contention could matter (the
  riscv32imac `prepare_sk_*` stall), a rerun alone gave the same instruction counts.
- `cargo-checkct`'s build pass runs every probe with `-sse-timeout 1`, which BINSEC checks only between paths: in the census
  containers it held one container for a long time on a single probe before the real run started. No verdict depends on it.
- The machine was terminated once (see the method paragraph above); the discarded and lost runs are listed there.

## The `nearcore-exact` profiles: settings and method

The older `nearcore` profile approximates nearcore's release build. `nearcore-exact` and `nearcore-exact-dispatch` take their
settings from nearcore itself (read-only clone at commit cd5a94457, 2026-11-03). `nearcore-exact-dispatch` is `nearcore-exact` plus the
crate's `avx2` feature with the dispatch cache pre-set, exactly as `nearcore-dispatch` does. x86_64 only; the other targets are not
part of nearcore's x86_64 flags and were not rerun.

| setting | value | source (nearcore cd5a94457) |
|---|---|---|
| `overflow-checks` | `true` | `Cargo.toml:389` (`[profile.release]`, lines 388-392) |
| `panic` | `abort` | `Cargo.toml:390` |
| `lto` | `"fat"` | `Cargo.toml:391` |
| `codegen-units` | `1` | `Cargo.toml:392` |
| `opt-level`, `debug-assertions` | not set: release defaults 3 and off | `Cargo.toml:388-392` (no other `[profile.release]` override) |
| x86_64 `target-feature` | `+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq` (no AVX2) | `.cargo/config.toml:9` (`[target.'cfg(target_arch = "x86_64")']`) |
| `force-unwind-tables` | `y` | `.cargo/config.toml:6` and `:9` |
| toolchain | Rust 1.95.0 | `rust-toolchain.toml:12` |

How `run-select.sh` builds it: `CARGO_PROFILE_RELEASE_{OPT_LEVEL=3,LTO=fat,CODEGEN_UNITS=1,PANIC=abort,DEBUG_ASSERTIONS=false}`,
and the x86_64 flags through `CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS` (cargo-checkct drops `RUSTFLAGS`; the per-target
variable replaces the x86_64 rustflags of `checkct/.cargo/config.toml`, so its three linker flags are repeated, as in
`nearcore-novec`). The log of every run prints the flags, the toolchain file, the driver package override and the
compiler read back from the driver's `.comment` section; the run aborts if that is not rustc 1.95.0.

Three things differ from "the same settings with the checkct workspace":

1. **Overflow checks apply to the `driver` package only.** `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true` also reaches the
   `-Zbuild-std` crates (`cargo build -v` shows `overflow-checks=on` for `core`, `compiler_builtins`, `panic_abort`), whereas
   nearcore links the prebuilt `core`, whose own MIR has no overflow checks. The run appends
   `[profile.release.package.driver] overflow-checks = true` to its working copy of `checkct/.cargo/config.toml` instead;
   `-v` then shows `-C overflow-checks=on` on the `driver` command line and none on `core`. The driver includes the crate
   sources as modules (and the harness), so exactly the crate and the probes are checked, as nearcore checks the crate.
2. **`+fma` enables AVX.** `rustc --print cfg` with nearcore's feature list shows `target_feature="avx"`; without the list
   it does not. LLVM therefore emits VEX-encoded SSE (`vpminud`, `vtestps`, `vpor`, ...) and 256-bit `vmovups`/`vandps`/
   `vzeroupper` for copies and zeroing. The driver of that earlier sweep contains 695 `vmovups`, 160 `vandps`, 158 `vzeroupper`,
   41 `vxorps` and about 70 other VEX instructions. In the earlier staged sweep of this profile (112 probes per profile, before the `wrapping_*` changes of ae6023c;
   `results/nearcore-exact.stage1-600s.txt`), the one instruction confirmed unliftable by BINSEC 0.11.3 was `vtestps` (cut path,
   "uninterpreted KO", experiment `exp_sk_wf_wrapadd_44`, `results/experiments-*.txt`), and no probe of that sweep had a cut path.
   That does not hold at 15b4ce2 or at 1a72d9e: 48 of the 113 probes are cut paths at `vinsertps`, `vblendvps` or `vblendps` (tables above), so
   the other VEX forms are not lifted either.
3. **The harness had to change.** `probes.rs` `secret_elem()` computed `x - Q` for every `x` (the select picks afterwards).
   With overflow checks that subtraction is a branch on the secret `x < Q`, in the harness itself: every probe built on
   `secret_elem` (the first attempt: `field_small_reduce`) reported two control-flow leaks at `probes.rs:12`. It is now
   `x.wrapping_sub(Q)`, which is the same machine code without overflow checks (the other profiles are unaffected).
   `secret_elem` is the only harness arithmetic on secrets that can overflow.

### Toolchain

| | checkct pin | nearcore |
|---|---|---|
| toolchain | `nightly-2026-10-06` (`checkct/rust-toolchain.toml`) | `1.95.0` (`rust-toolchain.toml:12`) |
| `rustc -vV` | `rustc 1.101.0-nightly (ea137335b 2026-10-05)`, commit ea137335b78829b4514bf1b4c16302f74fab8581, **LLVM 23.1.3**, host x86_64-unknown-linux-gnu | `rustc 1.95.0 (59807616e 2026-04-14)`, commit 59807616e1fa2540724bfbac14d7976d7e4a3860, **LLVM 22.1.2**, host x86_64-unknown-linux-gnu |
| driver `.comment` | `rustc version 1.101.0-nightly (ea137335b 2026-10-05)`, `Linker: LLD 23.1.3` | `rustc version 1.95.0 (59807616e 2026-04-14)`, `Linker: LLD 22.1.2` |

The driver is `#![no_std] #![no_main]` with `panic = "abort"` and links with `rust-lld` and no libc, so it needs
`-Zbuild-std=core,panic_abort` with `compiler-builtins-mem` (`memcpy`, `memset`, `memcmp` come from `compiler_builtins`).
Build-std is required: a 1.95.0 build without it (prebuilt `core`) fails at link time with `undefined symbol: memcpy` and
`undefined symbol: memset` (checked in the image with nearcore's flags). Stable 1.95.0 takes build-std with
`RUSTC_BOOTSTRAP=1`, which unlocks unstable flags and does not change code generation.
**The `nearcore-exact*` drivers are therefore built with rustc 1.95.0, LLVM 22.1.2** (installed in the image by
`checkct/Dockerfile`, selected through the working copy's `rust-toolchain.toml`: `RUSTUP_TOOLCHAIN` does not work because
cargo-checkct removes it from its cargo's environment, `cargo-checkct/src/run.rs:263`; the first nearcore-exact drivers
were silently built with the nightly that way, which the `.comment` check now rules out). `CT_TOOLCHAIN=nightly-2026-10-06`
builds the same flags with the nightly. A nightly build of the same flags gave the same `sk_is_well_formed_44` verdict
(insecure, same two branches); no other probe was compared across the two LLVM versions.

Remaining differences from nearcore's binary (limitations): `core` is built from source with nearcore's target features and
opt-level 3 and without overflow checks, while nearcore links the prebuilt `core` (generic and `#[inline]` code from `core`
is instantiated in the driver in both cases, so it matches; non-inline `core` functions are compiled with SSE4.2/AVX here and for
baseline x86-64 there); `memcpy`/`memset` are `compiler_builtins`', nearcore's are glibc's; only the crate is probed,
not nearcore's callers, so inlining contexts differ (CT-2 in `docs/assurance.md` shows that it matters); the driver is a static,
non-PIE `no_std` binary.

Sweep method: `run-select.sh`, x86_64 only, `ONLY=.` minus the two censuses, one container per profile, 64 GB cap, `TIMEOUT=600`.
With overflow checks left on secret values, the NTT-family probes stalled for the whole timeout, so the earlier sweep of this
profile was staged (600 s, then a traced 300 s pass over the `unknown`s to find the instruction BINSEC stopped at, then 3600 s
for a few). The sweeps at 15b4ce2 and 1a72d9e need no stages: an `unknown` is a cut path within seconds. `TRACE=1` records the last executed
instruction of every probe.

### What this does and does not show

- `nearcore-exact` is a better approximation of nearcore's x86_64 release build than `nearcore`, not the binary: the crate is
  probed in isolation (inlining context), `core` is built from source (above), `memcpy` is `compiler_builtins`', and the
  allocator, `std` and nearcore's callers are absent.
- At 15b4ce2 and again at 1a72d9e: 61 secure, 3 expected insecure, 49 unknown (and the two censuses, also unknown). Everything on the NTT, on
  `hint_step` and `response`, and on `prepare_sk`/`signing_key` has **no verdict under `nearcore-exact`**: BINSEC 0.11.3 cannot lift
  the VEX instructions LLVM emits under `+fma`. That is a loss of evidence for the nearcore build, not a leak. With the vectorizers
  off (`nearcore-exact-novec`) all of these are `secure`, which is evidence about a different binary.
- Overflow checks can introduce secret-dependent branches (CT-3 in `docs/assurance.md`: the `&&` in the old `poly_in_eta`), and a
  guard on a secret value can stall BINSEC. Source that keeps overflow-check guards on secret values should be probed again under
  `nearcore-exact`.
- The panic paths themselves are not analyzed: a reachable panic is outside this tool's questions (abort on a malformed input is a
  robustness property, covered by the Lean panic-freedom statements, not here).

## Known no-verdict probes (skip unless something changed)

These probes are already known to end with no verdict. Don't rerun them unless one of these changed: the code
under test (`src/` or the probe), the per-probe timeout, the memory cap, or how the probe is split. A rerun that
changes nothing costs hours and gives the same result (about 1.6 h went to such reruns on 2026-11-01). Each entry
says what was tried. When an entry gets a verdict, move it out of this list.

| probe | target / profile | outcome | already tried |
|---|---|---|---|
| `vec_power2round_87` (full size) | riscv32imac default | unknown, 1 pending path | 1 h and 2 h on the previous tree, 1 h at 15b4ce2 (190,098 instructions) and at 1a72d9e (177,574 instructions), still 1 pending path. Covered by the split windows `split_vec_power2round_8_*` (secure) |
| `split_vec_power2round_7` | riscv32imac | unknown, 1 pending path | 1 h, again 1 h at 15b4ce2 and 1a72d9e, 2 h alone at 1d8b5c5 (212,780 instructions); capacity probing only, the 8-wide windows cover the loop. `split_vec_power2round_{5,6}` are `secure` at 2 h (7200 s, 20 GB, alone, at 1d8b5c5; `unknown` at 1 h) |
| `census_sign_internal_44` | riscv32imac default | unknown, 4 pending paths | 1 h and 2 h on the previous tree |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44` | AArch64 `NONEON=1` | unknown: one pending path stuck in one solver query (instruction count identical at 300, 600, 3600 and 7200 s; upstream log U-42) | 1 h and 2 h on the previous tree, 1 h again at 15b4ce2 and at 1a72d9e (same probes, `control_prepared_*` too). Pieces covered by split probes, except the K = 8 glue of `prepare_sk_87` / `signing_key_87` |
| `split_prepare_sk_87_7x1`, `split_prepare_sk_87_8x1` | AArch64 `NONEON=1` | unknown, same stall | 1 h (round 2 of `split-run.sh`), again 1 h at 15b4ce2 and 1a72d9e (`split_prepare_sk_87_col` is the `_8x1` probe) |
| `census_sign_internal_44`, `census_sign_prepared_44` | thumbv7em default | OOM: needs more than 160 GB, no verdict (a control-flow leak at `sample_in_ball`, `sampling.rs:36`, was reported after 38.8 s and 53.0 s before the kill) | 64 GB and 120 GB caps, then 160 GB alone at 1d8b5c5 (killed at `anon-rss` 167.4 GB). Don't raise the cap again; a split would be needed |
| `census_sign_prepared_44` | riscv32imac default | OOM: needs more than 160 GB, no verdict | 64 GB and 120 GB caps, then 160 GB alone at 1d8b5c5 (killed at `anon-rss` 167.4 GB, no leak reported before the kill) |
| `census_sign_prepared_44` | x86_64 `nearcore-dispatch`, `dispatch` (profiles removed in round 12) | OOM: needs more than 120 GB, no verdict | history; x86_64 default has a verdict at 1d8b5c5 (`insecure`, public leak only, 160 GB) |
| `census_sign_prepared_44` | x86_64 `nearcore-exact-novec` | OOM: needs more than 160 GB, no verdict (`insecure`, public leak only, at 15b4ce2 in 120 GB) | 110 GB cap, then alone at 150 GB (killed at 115.1 and 157.0 GB RSS) at 1a72d9e, then alone at 160 GB at 1d8b5c5 (killed at `anon-rss` 167.4 GB). Don't raise the cap again |
| `control_prepared_branch_44` | thumbv7em | `secure`: the control is invalid there (branch lowered to a select) | every run; expected |
| `control_prepared_branch_44`, `control_prepared_index_44` | AArch64 `NONEON=1` | no verdict | 1 h and 2 h |
| 49 probes: `ntt`, `ntt_inverse`, `multiply_ntt`, `ntt_vec_44`, `compute_t_*`, `matrix_vector_ntt_*`, `scalar_vector_ntt_inverse_1`, `prepare_sk_*`, `signing_key_*`, `prepare_sk_1x1_*`, `control_prepared_*`, `hint_step_*`, `response_*`, 16 `split_*` (list in "`nearcore-exact` and `nearcore-exact-dispatch` at 1a72d9e") | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: 48 are cut paths at VEX instructions BINSEC 0.11.3 cannot lift (`vinsertps`, `vblendvps`, `vblendps ymm`), 0 pending paths, stopped in 0.08 to 1.4 s; `prepare_sk_1x1_65` is a solver stall (1 pending path) | 600 s for all, 3600 s with `TRACE=1` for `prepare_sk_1x1_65`. A longer timeout cannot help a cut path. What helps: a build without the vectorizers (`PROFILE=nearcore-exact-novec`: 47 `secure`, the two prepared controls `insecure`) or a BINSEC that lifts VEX (U-44) |
| `census_sign_internal_44`, `census_sign_prepared_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 82,072 instructions (`nearcore-exact`) | `JOBS=1`, 3600 s at 15b4ce2 (110 GB) and at 1a72d9e (12 GB; cut within 2 s). `nearcore-exact-novec` has a result for the internal census: `insecure`, only the public `sampling.rs:35` leak |
| `prepare_sk_{44,65,87}` | riscv32imac default | unknown, 1 pending path, stuck at `0x0497de sw t6,-8(a6)` (`_44`) / `0x049704 sw s1,0(a7)` (`_65`, `_87`) in `ntt_body_mut` (new at 1a72d9e; `secure` at 15b4ce2) | 3600 s (sweep), 600 s with `TRACE=1`, 7200 s with `TRACE=1` and `JOBS=2` (`_44`, `_65`): the same instruction counts every time; the same driver on the `src/` of 15b4ce2 is `secure`. Covered by `signing_key_{44,65,87}`, `prepare_sk_1x1_*` and the split pieces, which are `secure` |

## Probes

113 or 114 entrypoints without the censuses (85 non-split probes and 28 or 29 split pieces, by profile), built for x86_64-unknown-linux-gnu, thumbv7em-none-eabihf, riscv32imac-unknown-none-elf and (with `aarch64.sh`) AArch64.

Primitives (`probes.rs` and `signing.rs`):

- field/mask: `field_small_reduce`, `barrett_reduce`, `field_add`, `field_sub`, `field_neg`, `field_mul`,
  `ct_lt_mask`, `ct_select` (mask taken from a secret bit); `field_mul_shoup`, `field_mul_mont` and `field_mont_reduce`
  (the Shoup/Montgomery products; `field_add` is merged into `field_small_reduce` in some builds).
- rounding: `power2round`, `decompose`/`high_bits`/`low_bits`/`make_hint` (`_44` for gamma2 = (q-1)/88 and
  `_65_87` for (q-1)/32), `infinity_norm`, `vec_infinity_norm` (4 polynomials).
- `ntt`, `ntt_inverse`, `multiply_ntt` on secret polynomials; `keccak_f1600` with a secret state.
- encode: `bit_pack_{3,4,13,18,20}` (inputs masked to c bits), `sk_encode_{44,65,87}` (secret key, s1, s2, t0;
  public rho and tr), `sk_decode_{44,65,87}` on a secret sk.
- `signing.rs`: `response_{44,65,87}` (z = y + cs1, cs2, r0 = LowBits(w - cs2), both vector norms) and
  `hint_step_{44,65,87}` (ct0, MakeHint(-ct0, w - cs2 + ct0), hamming weight, ct0 norm). c-hat is public.
  These call the production `sign::response` and `sign::hint_step`; the norms are taken on the returned vectors, as
  `attempt` does before its rejection `if`s.

KeyGen, Sign, well-formedness and controls (`extra.rs`, plus four in `signing.rs`):

| area | probes | what is analyzed |
|---|---|---|
| well-formedness of a secret key | `sk_is_well_formed_{44,65,87}` (the public `api::sk_is_well_formed_NN`), `encode_sk_is_well_formed_{44,65,87}` (the `encode::` function it wraps) | secret sk bytes in, bool out. Includes the eta-range checks of s1, s2 and the t0 range. |
| KeyGen | `keygen_seed_hash` (H(xi, k, l) to rho, rho', K), `coeff_from_half_byte_eta{2,4}` (the `% 15` / `% 9` of ExpandS), `rej_bounded_poly_eta{2,4}` (ExpandS rejection sampler), `matrix_vector_ntt_{1x1,44,65,87}` (A-hat * NTT(s1)), `ntt_vec_44` (NTT of s1), `scalar_vector_ntt_inverse_1`, `compute_t_{1x1,44,65,87}` (t = NTT^-1(A-hat s1-hat) + s2), `poly_power2round`, `vec_power2round_{44,87}` | the secret-touching steps of KeyGen: ExpandS, NTT of s1, t, Power2Round. skEncode is `sk_encode_*` from the earlier set. |
| Sign | `sk_decode_*` and `sk_is_well_formed_*` (skDecode), `sign_rho_pp_hash` (rho'' = H(K, rnd, mu)), `expand_mask_{44,65,87}` (ExpandMask: bit-unpack of the secret y), `response_1x1_{44,65}`, `hint_step_1_{44,65}` (one-polynomial splits of `response` and `hint_step`) | skDecode, mask generation, and the two secret-dependent halves of `attempt` |
| whole-function | `census_sign_internal_44` | the complete `api::sign_internal_44`, with a concrete well-formed secret key whose K, s1, s2, t0 are replaced by secret bytes. Not expected to be "secure", see below. |
| positive control | `control_early_exit_44` | a deliberate early exit on a secret bit-unpacked value. Must be `insecure`; it shows the method flags a leak in the same context as the real probes. |

Coverage of the secret paths:

- KeyGen: seed hash (`keygen_seed_hash`), ExpandS (`coeff_from_half_byte_*`, `rej_bounded_poly_*`), NTT of s1
  (`ntt_vec_44`, `ntt`), t computation (`compute_t_*`, `matrix_vector_ntt_*`, `scalar_vector_ntt_inverse_1`),
  Power2Round (`power2round`, `poly_power2round`, `vec_power2round_*`), skEncode (`sk_encode_*`, `bit_pack_*`).
  The Keccak permutation is `keccak_f1600`; the sponge wrappers around it are straight-line.
- Sign: skDecode (`sk_decode_*`, `sk_is_well_formed_*`), rho'' hash, ExpandMask, NTT/NTT^-1 (`ntt*`), `response`, `hint_step`.
- Not probed on purpose: the accept/reject branching of ExpandA (`z < q`) and SampleInBall (public outcome, inputs
  public or hash outputs), and the two rejection `if`s of `attempt`.

### Prepared signing key (`prepared.rs`, 11 probes)

`api::signing_key_NN` computes the secret-key half of Sign once (`sign::prepare_sk`: skDecode, three NTTs, ExpandA).
Secret = the secret key bytes K (32..64) and the packed s1, s2, t0 (128..); rho (0..32) and tr (64..128) are fixed
public constants (`black_box`ed, so ExpandA stays concrete but is not folded away; `prepare_sk` does not check
consistency, so they need not come from a real key). Making rho secret would only report ExpandA's rejection test, a
public-outcome branch. m, ctx and rnd are public in the census.

| probes | what is analyzed |
|---|---|
| `prepare_sk_{44,65,87}` | `sign::prepare_sk::<K, L>` |
| `signing_key_{44,65,87}` | `api::signing_key_NN` end to end (a wrapper: identical instruction counts and check counts to `prepare_sk_NN` on x86_64 and thumbv7em) |
| `prepare_sk_1x1_{44,65}` | one-polynomial split (K = L = 1) of `prepare_sk`, for the eta = 2 / eta = 4 sets, for riscv32imac where the full-size 44 and 87 probes do not finish |
| `census_sign_prepared_44` | `signing_key_44` then `sign_prepared_44`; the mirror of `census_sign_internal_44`. There is no per-attempt probe of `sign_prepared_internal` to mirror: `attempt` is private to `sign.rs`, and its secret halves are the unchanged `response_*` and `hint_step_*`. |
| `control_prepared_branch_44`, `control_prepared_index_44` | positive controls: `prepare_sk_44`, then a branch on a bit of ŝ1, resp. a table lookup indexed by a byte of ŝ1. Must be `insecure` |

Run the prepared-key probes with `bash checkct/run-prepared.sh '<regex>' '<targets>' <timeout> [<memory>]` or
`checkct/prepared-leaks.sh` (same arguments; also maps leak addresses to source lines).

The `prepare_sk_*` verdicts are not vacuous: 0 pending paths, and for example `prepare_sk_87` on x86_64 (checkct profile, 1a72d9e) visits 3,044,242
instructions with 214,281 control-flow and 1,054,289 memory-access checks passing. `control_prepared_branch_44` is `secure` on thumbv7em because
the compiler turns `if bit {1} else {2}` into a conditional select; it is a valid control only where it reports `insecure`. The
index control cannot be compiled away and is `insecure` on all three default targets.

Expected-insecure probes. `rej_bounded_poly_eta{2,4}` leak by design: the loop branches on whether a sampled
nibble is accepted, and which positions are rejected is public (it only changes how many XOF bytes are consumed).
`census_sign_internal_44` finds the same kind of branch (a rejection sampler) first. These are not constant-time
bugs; they show what BINSEC cannot distinguish (secret data versus public outcome of a secret-derived value), which
is why the check for "no secret-dependent branch" is done per step.

## Split probes (`driver/src/split.rs`, `split-run.sh`)

Some full-size probes have no verdict: BINSEC stops with one pending path stuck in one solver query (the same instruction count at
3600 s and 7200 s), no leak found. The split probes cover the same code in smaller pieces, so that every piece has a completed
verdict. They are in `driver/src/split.rs`; run them with `bash checkct/split-run.sh`, which starts the AArch64 container
(`NONEON=1`, `aarch64.sh`) and the riscv32imac container (`run-select.sh`) side by side, each with 2 BINSEC jobs, 3600 s per probe,
and exits nonzero if either fails. A probe name starts with `split_`. Per-probe verdicts of the latest sweep are in
`checkct/results/sweep-1a72d9e/*.verdicts.tsv`.

**How a split covers the original.** Every split probe calls the same functions as the probe it splits (the
production `sign::prepare_sk` and `ntt::ntt_vec_into`; the driver's own copies of `keygen::compute_t` and
`keygen::vec_power2round`, which are private in the crate, copied from `extra.rs` unchanged), with the same inputs
secret or public as the original, and only the const-generic loop bounds (`K`, `L`) or the iteration window of a loop
differ. In each of these functions the loops index with public counters, iteration `i` reads and writes only element
`i` of its output, and nothing flows between iterations except through the accumulators that the pieces keep
(`w[i]` over `j`). A shape with `K = 1` and the full `L` therefore runs every `L`-loop body (and the
per-row tail once), and a shape with the full `K` and `L = 1` runs every `K`-loop body. Limits of the argument: it is a
statement about the source, and each shape is its own monomorphization, so the machine code of the full-size instance
(unrolling, inlining) is not what the pieces analyze; this is the same argument the existing `*_1x1_*` probes rest on.
A piece that is `unknown` covers nothing.

| original (no verdict) | target | pieces (all `secure` unless noted) | what they cover |
|---|---|---|---|
| `compute_t_44` | AArch64 | `split_compute_t_44_row` (K=1, L=4), `split_compute_t_44_col` (K=4, L=1), `split_compute_t_44_2x2`; with the existing `compute_t_1x1` (secure) | `ntt_vec::<4>`, the four-term row accumulation of `matrix_vector_ntt`, `ntt_inverse` and `add_poly` of one row (row); the four row iterations (col) |
| `prepare_sk_44`, `prepare_sk_65`, `signing_key_44`, `signing_key_65` | AArch64 (riscv32imac too) | `split_prepare_sk_{44,65}_row` (K=1, L full), `split_prepare_sk_{44,65}_col` (K full, L=1); with the existing `prepare_sk_1x1_{44,65}` | skDecode of s1 and the in-place NTT of ŝ1 (row); skDecode of s2, t0 and their NTTs (col); ExpandA on the public rho for 1×L and K×1 |
| `prepare_sk_87`, `signing_key_87` | AArch64 | `split_prepare_sk_87_row` (1×7), `_2x1`, `_4x1`, `_6x1`; stages `split_ntt_vec_into_7` (ŝ1), `split_ntt_vec_into_8` (ŝ2 and t̂0), `split_ntt_vec_into_1`; the existing `sk_decode_87` (secure on AArch64, full size). **`_7x1` and `_8x1` (`split_prepare_sk_87_col`) are `unknown`**: one pending path each, 1 pending path after 3600 s, no leak | K=8 does not fit in one query, K=6 does. The K=8 loops of skDecode (s2, t0) are the existing `sk_decode_87`, the K=8 loop of the in-place NTT is `split_ntt_vec_into_8`; ExpandA is on the public rho. What no probe has run in one piece is the glue between those stages (copies of K and tr, the zeroing in `ntt_vec_into`), which `_6x1` and `_row` do run |
| `vec_power2round_87` | riscv32imac | `split_vec_power2round_{1,2,3}` (K = 1 to 3), the windows `_8_lo` (i in 0..4), `_8_hi` (4..8) and `_8_q0..q3` (pairs 0..2, 2..4, 4..6, 6..8) of the K=8 loop over the same eight secret polynomials. `_5`, `_6`, `_7` are `unknown` (capacity probing, not cover). `split_vec_power2round_4` is `secure` where it is its own entrypoint (riscv32imac and, at 1a72d9e, the x86_64 default and `dispatch`, thumbv7em and AArch64 builds); at 15b4ce2 the compiler had folded it into the identical `vec_power2round_44` (K = 4, secure in the sweep) outside riscv32imac and `dispatch`, and it is folded again in the `nearcore*` builds | the windows run the identical K=8 instance and partition its iterations, so their union is the whole loop (the loop's trip count is public); `_8_lo`/`_8_hi` are the halves, `_q0..q3` the pairs |
| `prepare_sk_44`, `prepare_sk_87`, `signing_key_44`, `signing_key_87` | riscv32imac (`prepare_sk_{44,65,87}` are `unknown` at 1a72d9e, see the riscv32imac bullet above) | `split_prepare_sk_{44,65,87}_{row,col}`, `split_prepare_sk_87_{2,4,6,7}x1` (all `secure` at 1a72d9e) | cover the stages of the full-size probes that stall |

`signing_key_NN` is `sign::prepare_sk_into` on a zeroed key object plus a `mem::replace` of that object (`api.rs`): the
same instruction and check counts as `prepare_sk_NN` on x86_64 and thumbv7em, so the `prepare_sk` pieces are its pieces. In the sweep above the riscv32imac `signing_key_*` rows are `secure` at full size and the `prepare_sk_*` rows are
`unknown` (a solver stall, see the riscv32imac bullet), so the riscv32imac `prepare_sk` splits are the cover for those three.

Reading the results: no split piece found a leak, and every piece that completed is `secure`. The `unknown` rows are
the same solver stall as the originals (1 pending path, "timeout has left (at least) 1 pending paths", no leak among
the checks that passed), reproduced at smaller sizes: AArch64 `prepare_sk` with K = 7 and 8 (not K <= 6), riscv32imac
`vec_power2round` with K >= 5. For `prepare_sk_87` and `signing_key_87` on AArch64 the cover is therefore by stages
(skDecode, the in-place NTTs, ExpandA on the public rho) plus the K <= 6 and L = 7 whole-function shapes, not by
a smaller instantiation that includes the K = 8 glue; claim it at that strength. The AArch64 build is the scalar
(`NONEON=1`) one, as in the sweep. The pieces were compiled into one driver with the full set of probes.

## Not covered

- Only the listed steps, on the target/opt-level above (release, debug info) and the nearcore-like profile for the
  rows reported there. Other compilers, versions, opt-levels and inlining contexts can differ, as the x86_64
  `decompose` edge select (CT-2 in `docs/assurance.md`) shows: a function that is branch-free in isolation can acquire a branch once inlined into a
  caller. Re-run after toolchain bumps. Release builds of downstream crates (a different codegen-units count, PGO,
  `-C target-cpu=native`) are not covered.
- `sign::attempt` and `sign_internal` as a whole are not proven: the rejection samplers and the two rejection `if`s
  of `attempt` are public-outcome branches that BINSEC cannot tell from leaks, so the check is by parts (the secret
  steps above) plus the code reading that the glue between them has no secret branch. The same holds for the whole
  KeyGen and `pk_from_sk`: there is no whole-function probe of either, only of their secret-touching steps.
- The Sign change swept at 1a72d9e is covered through its callers, not by probes of its own: `response_into`, `hint_step_into`,
  `sk_decode_into`, `unpack_signed_into`, `prepare_sk_into`, `scalar_vector_ntt_inverse_into`, `matrix_vector_ntt_into`,
  `ntt_vec_into` and the in-place NTTs run inside the probes that call their by-value wrappers (`response_*`, `hint_step_*`,
  `sk_decode_*`, `prepare_sk_*`, `signing_key_*`, `matrix_vector_ntt_*`, `scalar_vector_ntt_inverse_1`, `compute_t_*`). What no probe
  contains: the two direct calls in the `zeroize` build of `attempt` (`ntt_inverse_in_place` on `w[i]`, `ntt_in_place` on ĉ;
  the functions are the ones probed through `scalar_vector_ntt_inverse_into` and `ntt_vec_into`), `wipe_attempt`, and `more_attempts`
  and `attempt_at` (public counter κ only; `attempt_at` exists only under the `internals` feature, which the driver does not enable).
  A whole-attempt probe would show the public rejection branches as leaks, like the censuses.
- The binaries of the sweep are built without the crate's `zeroize` feature (the default). `ZEROIZE=1` (`run-select.sh`, x86_64
  profiles without dispatch) builds the driver with it. At 1a72d9e that was run for the checkct profile and for
  `nearcore-exact-novec` (`results/sweep-1a72d9e/x86_64-default-zeroize.*`, `x86_64-nearcore-exact-novec-zeroize.*`): every probe has
  the verdict it has without the feature (109 secure and 5 expected insecure; 108 and 5), with different instruction counts for 70 and
  57 probes. That covers the `zeroize` code shape of the probed functions on those two profiles only. The `zeroize` build of the
  other profiles and targets and of the censuses was not run, and the wipe loops in `attempt` and `wipe_attempt` are in no probe.
- Shake absorb/squeeze with a secret input is covered through `keccak_f1600` and the hash probes
  (`keygen_seed_hash`, `sign_rho_pp_hash`, `expand_mask_*`) only for the parameter sets listed; verify (public data) and
  `use_hint` are not probed; zeroization is outside this tool.
- BINSEC checks the absence of secret-dependent control flow/memory/division operands, not absence of data-dependent
  instruction timing (e.g. variable-latency multiplies on some cores; the `multiplication` check is experimental and
  not enabled).
