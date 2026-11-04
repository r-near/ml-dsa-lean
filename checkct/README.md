# checkct: binary-level constant-time checks (BINSEC)

Port of the RustCrypto `ml-dsa/checkct` harness (signatures repo, rev a3690c4) to this crate. The driver
`#[path]`-includes the crate sources unchanged (`params`, `field`, `rounding`, `ntt`, `keccak`, `encode`, `sampling`,
`keygen`, `sign`, `verify`, `api`; the crate is `no_std` with no dependencies, so no shims are needed), marks every
probe input secret through the `__checkct_private_rand` hook, and lets BINSEC (via `cargo-checkct`) symbolically
execute the compiled release binary, flagging any secret-dependent branch, memory access, or division operand.

This directory is its own workspace (`[workspace]` in `checkct/Cargo.toml`). It is not a member of the main
crate's workspace and the main `Cargo.toml` needed no `exclude`. `src/` is not edited.

> **Reading `error` results.** BINSEC killed at a container's memory cap shows only `error` in the job log. Every `error`
> in the tables below is presumed to be an out-of-memory kill, with no verdict, unless the kernel log
> (`journalctl -k -g 'Killed process'`) shows no kill in its run window. The sweep at 15b4ce2 matched each of its three
> `error` results to a kernel OOM kill (`results/sweep-15b4ce2/oom-kills.txt`).

## Running

Linux only (BINSEC), via Docker:

    docker build -t ct-binsec checkct                           # once, and again after Dockerfile changes; ~10 min
    bash checkct/run.sh 2>&1 | tee ct.log

Scripts (all start from the repository root; stopping a script does not stop its container, so use `docker kill $NAME` too):

| script | purpose | environment |
|---|---|---|
| `run.sh` | all probes, all three targets (`cargo-checkct run --all-leaks`); `JOBS` defaults to every CPU, which does not fit a 64 GB container, so the full sweeps use `run-select.sh` with `ONLY=.` instead | `TIMEOUT` (900 s per probe), `JOBS`, `OUT` (copies the three `<target>.driver` binaries), `NAME`, `PROFILE=nearcore` |
| `run-select.sh` | only probes matching a regex, long timeouts; builds with `cargo-checkct`, then calls `binsec` directly. Streams a `done <target> <probe> <status>` line per probe and ends with a `Summary:` block like `run.sh` | `ONLY` (regex), `EXCLUDE` (regex), `TARGETS`, `TIMEOUT` (7200), `JOBS` (4), `OUT`, `NAME`, `PROFILE`, `TRACE=1` (last executed instruction per probe), `EXPERIMENTS=1` (the `exp_*` probes), `CT_TOOLCHAIN` (nearcore-exact; default 1.95.0) |
| `unknowns.py BIN LOG...` | maps every leak address, every cut path (`uninterpreted "KO"`) and every `TRACE` last instruction of a `Summary:` block to function, source line and instruction (GNU `objdump`; `leaks.sh` needs `llvm-objdump`). `python3 -I checkct/unknowns.py DIR/x86_64-unknown-linux-gnu.driver LOG` | |
| `leak-context.sh BIN ADDR...` | disassembly around an address with source lines (`BEFORE`, `AFTER` bytes) | |
| `probe-now.sh CONTAINER PROBE [T] [binsec args]` | reruns one probe inside a running `run-select.sh` container for a few seconds with the full BINSEC log (diagnosis of a sweep in flight; not for verdicts) | |
| `leaks.sh LOG BINDIR` | maps every leaking instruction address of a `Summary:` block to `file:line` and the instruction (`llvm-objdump -d -l` on the `OUT` binaries) | `OBJDUMP` as third argument |
| `aarch64.sh` | experiment: AArch64 (see below); `cargo-checkct` does not support the target, so it builds the driver for `aarch64-unknown-linux-gnu` in the container and writes the BINSEC scripts itself | `ONLY`, `TIMEOUT`, `JOBS`, `NAME`, `OUT`, `NONEON=1` |
| `split-run.sh [round2]` | the split probes of `driver/src/split.rs` on AArch64 (`NONEON=1`) and riscv32imac, two containers in parallel, exit status nonzero if either fails (see "Split probes") | `TIMEOUT` (3600), `JOBS` (2 per container), `AONLY`, `RONLY` |
| `select-ntt.sh [mode]` | the NTT and field-product probes and the KeyGen/Sign pieces built on them, through `run-select.sh`; `mode` is `default`, `dispatch`, `nearcore-dispatch`, `avx2` or `nearcore-avx2` (see "Profiles for the AVX2 dispatch") | `TIMEOUT` (3600), `JOBS`, `OUT`, `NAME`; the 2nd and 3rd arguments replace the probe regex and the target list |
| `scan-avx2.sh DIR` | static scan of the `*_avx2` functions of a dispatch driver (`DIR` is a directory name under `$ML_DSA_SCRATCH`, the `OUT` of a dispatch run); fails if there are none | |

`PROFILE=nearcore` builds with `opt-level = 3`, `lto = "fat"`, `codegen-units = 1`, `panic = "abort"` (through
`CARGO_PROFILE_RELEASE_*`). It approximates nearcore's release build but does not match it: nearcore (checked at
nearcore cd5a94457, 2026-11-03) also sets `overflow-checks = true`, builds x86_64 with
`-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq` and
`-Cforce-unwind-tables=y`, and uses Rust 1.95.0. The `nearcore` results below are for this approximation only; the
profiles that take all of those settings are `nearcore-exact` and `nearcore-exact-dispatch`
(section "`nearcore-exact` and `nearcore-exact-dispatch`" below; x86_64 only, `run-select.sh`). The default is the checkct workspace profile (release plus debug info, `panic = "abort"`,
16 codegen units). BINSEC's `-sse-timeout` is only checked between paths, so a probe stuck in a long solver query
can run well past `TIMEOUT`.

### Profiles for the AVX2 dispatch

The crate's runtime AVX2 dispatch of the NTT bodies (`src/ntt.rs`, `mod dispatch`) exists only with the opt-in cargo
feature `avx2`. The driver includes `src/` through `#[path]`, so the sources are modules of the driver crate and see
the driver's own feature: `checkct/driver/Cargo.toml` declares `avx2 = []`, off by default like the crate's. A build of
the driver without it has no dispatch (the default; what `run.sh` builds). `cargo-checkct` has no `--features` option, so
the dispatch profiles of `run-select.sh` make `avx2` a default feature in the container's working copy of that file.

| `PROFILE` | driver build | dispatch compiled | cache pre-set |
|---|---|---|---|
| (unset), `nearcore`, `nearcore-novec` | no `avx2` feature | no | none; the log says "no dispatch compiled" |
| `dispatch` | the checkct profile with the `avx2` feature | yes, on x86_64 (a no-op on the other targets) | yes |
| `nearcore-dispatch` | the nearcore settings with the `avx2` feature | as above | yes |
| `avx2`, `nearcore-avx2` | `-C target-feature=+avx2`, no feature | no: the static-AVX2 arm, one AVX2 compilation of each body | none |
| `nearcore-exact` | nearcore's `[profile.release]` incl. `overflow-checks` (driver package), nearcore's x86_64 target features, rustc 1.95.0; no `avx2` feature | no | none |
| `nearcore-exact-dispatch` | `nearcore-exact` with the `avx2` feature | yes, as `nearcore-dispatch` | yes |
| `nearcore-exact-novec` | `nearcore-exact` plus `-C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false` (x86_64 only) | no | none |

In a dispatch profile `run-select.sh` pre-sets the dispatch cache (`static AVX2: AtomicU8` in `.bss`) to 1 ("checked, no
AVX2") in every x86_64 BINSEC script, which is what `cargo-checkct`'s stubbed `cpuid` would have produced; without it
BINSEC leaves the static symbolic, enters the AVX2 arm and stops at its first VEX instruction ("uninterpreted KO",
status `unknown`). The run is loud about it:

- before any probe starts, it prints `preset <target>: PROFILE=...: dispatch compiled in, AVX2 cache static at 0x...` (or
  `no dispatch compiled ... nothing to pre-set`), and aborts with `PRESET FAILED` unless `nm` finds exactly one symbol
  `driver::ntt::dispatch::AVX2` (matched exactly, in v0 or legacy mangling with the LTO suffixes) in a dispatch profile
  and none in any other profile;
- per probe it checks that the `@[rsp, 8] :=` anchor of the generated script matched and the inserted line is there,
  and prints `done <target> <probe> <status> (AVX2 cache 0x... pre-set to 1)`; a missing anchor reports the probe as
  `error` and the script exits 1;
- an unknown `PROFILE` is rejected. `run.sh` refuses the dispatch profiles (it would not pre-set the cache); use
  `run-select.sh` or `select-ntt.sh dispatch`.

`select-ntt.sh dispatch` is `PROFILE=dispatch` on x86_64 only (the other targets build the same code as the default),
`select-ntt.sh` alone the default build. `scan-avx2.sh` needs a driver from a dispatch profile and fails if the
disassembly has no `*_avx2` function (the default build gives none). Measured at the merge of the opt-in dispatch,
x86_64, 5 probes (`ntt`, `ntt_inverse`, `multiply_ntt`, `field_mul_shoup`, `field_mul_mont`): `dispatch` and
`nearcore-dispatch` give `secure` for all five with the pre-set; the default profile gives `secure` for all five with no
dispatch compiled; with the pre-set disabled, `dispatch` gives `unknown` ("Cut path (uninterpreted KO)") for `ntt`,
`ntt_inverse` and `multiply_ntt`. `scan-avx2.sh` reports `ntt_avx2`, `ntt_inverse_avx2` and `multiply_ntt_avx2`.
The sweep at 15b4ce2 below covers every probe in both dispatch profiles.

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

## Full sweep at 15b4ce2 (November 4, 2026)

The current results. `src/` at 15b4ce2: the tree after ae6023c (merged in ddf201b), which put `wrapping_*` arithmetic into
`field.rs` (`small_reduce`, `barrett_reduce`, `add`, `sub`, `neg`, `mont_reduce`), `rounding.rs` (`reduce_mod`,
`mod_plus_minus`, `decompose`, `infinity_norm`, an `opaque_u32` on the running maximum of `vec_infinity_norm`) and
`encode.rs` (`poly_eta_bad`/`eta_block_bad` mask accumulation, one compare in `sk_is_well_formed`), so that no
overflow-check guard is left on a secret value (CT-3 in `docs/assurance.md`). The harness is c63f632. Raw per-probe results,
with every leak and stop address mapped to function, source line and instruction by `unknowns.py`, are in
`checkct/results/sweep-15b4ce2/` (`<target>-<profile>.verdicts.tsv`, `.unknowns.txt`/`.summary.txt`, `.header.txt` with the
toolchain and flags the run printed).

Method: `run-select.sh` (AArch64: `aarch64.sh` with `NONEON=1`), `ONLY=.`, one container per target and profile (64 GB
cap, `JOBS=8`), `EXCLUDE=census_sign` (the censuses ran separately, below). `TIMEOUT=3600` for the checkct-profile,
`nearcore`, `dispatch` and `nearcore-dispatch` x86_64 runs and for thumbv7em, riscv32imac and AArch64; `TIMEOUT=600` for
`nearcore-exact`, `nearcore-exact-dispatch` and `nearcore-exact-novec`. Up to ten containers ran at the same time on one
60-core Linux machine, which is why three riscv32imac probes were rerun alone (below). The x86_64 profiles other than
`nearcore-exact*` use `nightly-2026-10-06` (LLVM 23.1.3), `nearcore-exact*` use rustc 1.95.0 (LLVM 22.1.2); the `.comment`
check passed in every x86_64 run (`x86_64-*.header.txt`); the thumbv7em, riscv32imac and AArch64 headers do not record it.

**Count basis.** A run has 113 entrypoints without the censuses (114 on riscv32imac and in the `dispatch` build, where
`split_vec_power2round_4` stays its own entrypoint): 85 non-split and 28 split (29 where noted); the AArch64 run has 115 rows with
the two censuses. The "87-probe basis" column is the 85 non-split entrypoints plus the two censuses; the split probes have their own
column. Which field probe survives LTO as its own entrypoint differs by profile (the default TSVs list `field_mul` and not
`field_add`, the `nearcore-exact*` TSVs the reverse); the count of 85 holds in both.

Columns: secure / expected insecure / unexpected insecure / unknown / no verdict (OOM).

| target / profile | 87-probe basis | split probes |
|---|---|---|
| x86_64, default | 80 / 6 / 0 / 0 / 1 | 28 / 0 / 0 / 0 / 0 |
| x86_64, `nearcore` | 80 / 7 / 0 / 0 / 0 | 28 / 0 / 0 / 0 / 0 |
| x86_64, `dispatch` | 80 / 6 / 0 / 0 / 1 | 29 / 0 / 0 / 0 / 0 |
| x86_64, `nearcore-dispatch` | 80 / 6 / 0 / 0 / 1 (prepared census not rerun) | 28 / 0 / 0 / 0 / 0 |
| thumbv7em, default | 81 / 4 / 0 / 0 / 2 (censuses not rerun) | 28 / 0 / 0 / 0 / 0 |
| riscv32imac, default | 78 / 6 / 0 / 2 / 1 (censuses not rerun; counts `control_prepared_branch_44` as insecure from its 7200 s rerun, it is `unknown` in the sweep TSV, which strictly gives 78 / 5 / 0 / 3 / 1) | 23 / 0 / 0 / 6 / 0 |
| AArch64 `NONEON=1` | 73 / 3 / 0 / 11 / 0 | 26 / 0 / 0 / 2 / 0 |

Not on the 87-probe basis, all probes of the run (113 entrypoints plus the two censuses):

| x86_64 profile | secure / expected insecure / unexpected insecure / unknown / no verdict |
|---|---|
| `nearcore-exact` | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-dispatch` | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-novec` | 108 / 7 / 0 / 0 / 0 |

Reading the first table: the "expected insecure" cells are `rej_bounded_poly_eta2/4`, the positive controls (`control_early_exit_44`,
`control_prepared_branch_44`, `control_prepared_index_44`; on thumbv7em only the first and the third, the branch control is the invalid
`secure` one; on riscv32imac also the standalone `ct_lt_mask`) and, on x86_64, the censuses, which report only the public
`sampling.rs:35` leak (then 1 pending path) (below). Every probe of the first table has a verdict except the unknown and OOM cells shown, and each `secure`
row has 0 pending paths and all checks passing. **No unexpected `insecure` result on any target or profile; no new leak.**

Against the previous full sweep (e9a1c74), the changes were: the six `sk_is_well_formed` probes went from unknown or insecure to
`secure` in every x86_64 profile; 22 `nearcore-exact*` probes improved (6 `insecure` to `secure`, 16 `unknown` to `secure`) and none got worse;
the x86_64 default and `dispatch` `census_sign_prepared_44` went from `insecure` (public leak) to no verdict, killed at the
120 GB cap; and three riscv32imac `split_prepare_sk_*` probes went from `secure` to `unknown` (solver stall, below). Everything
else, on thumbv7em and AArch64 in particular, is probe-for-probe identical.

Every non-secure probe of the sweep that is not an `nearcore-exact*` unknown:

| probe | where | result | reason |
|---|---|---|---|
| `rej_bounded_poly_eta2/4` | every row above | insecure, expected | sampler accept test, public outcome (`sampling.rs:129`, `:132`) |
| `control_early_exit_44` | every row above | insecure, expected | positive control, `extra.rs:221` (8 leaks on x86_64) |
| `control_prepared_branch_44` | x86_64 (all profiles but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac (`insecure` in the 7200 s rerun, `unknown` at 3600 s in the sweep run) | insecure, expected | positive control, `prepared.rs:76` |
| `control_prepared_index_44` | x86_64 (all but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac, thumbv7em | insecure, expected | positive control, `prepared.rs:96` |
| `control_prepared_branch_44` | thumbv7em | secure, invalid control | branch lowered to a select |
| `control_prepared_{branch,index}_44` | AArch64 | unknown | built on `prepare_sk_44`, which does not finish (uncontrolled `prepare_sk` rows) |
| `control_prepared_{branch,index}_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown | cut path in `prepare_sk`'s NTT (`vinsertps`) before the control site; the `prepare_sk_*` rows there are uncontrolled |
| `ct_lt_mask` | riscv32imac | insecure, documented | standalone probe, in-crate callers are secure |
| `vec_power2round_87`, `split_vec_power2round_{5,6,7}` | riscv32imac | unknown | 1 pending path, no leak (unchanged, solver capacity) |
| `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1` | riscv32imac | unknown | new; below |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `split_prepare_sk_87_{7x1,col}`, the two censuses | AArch64 | unknown | 1 pending path stuck in one solver query (unchanged, U-42) |

Censuses (`census_sign_internal_44`, `census_sign_prepared_44`; `checkct/results/sweep-15b4ce2/x86_64-censuses.txt`), x86_64,
`JOBS=1`, `TIMEOUT=3600`, one container per profile. A census proves nothing (the rejection samplers of Sign are public-outcome
branches); the aim is to catch an obvious leak. The caps were 110 GB for the first batch (`default`, `nearcore`, `nearcore-exact`,
`nearcore-exact-dispatch`) and 120 GB, as in the earlier runs, for the later runs (`nearcore-exact-novec`, `dispatch`,
`nearcore-dispatch`, and the rerun of the default prepared census after it was killed at 110 GB):

| profile | `census_sign_internal_44` | `census_sign_prepared_44` |
|---|---|---|
| default | insecure: one leak, `sampling.rs:35` (`sample_in_ball` accept test, public outcome) at 0x237998; 1 pending path, 2,875,532 instructions, 209,729 of 209,730 control-flow checks passed | **no verdict, OOM**: killed at the 110 GB cap (binsec at 115.1 GB RSS, 11:45:09Z) and again alone at the 120 GB cap (125.6 GB RSS, 16:27:26Z). an earlier tree fit in 120 GB and was `insecure` |
| `nearcore` | insecure: `sampling.rs:35` only (0x20da3b); 2,850,363 instructions | insecure: `sampling.rs:35` only; 1,539,485 instructions |
| `dispatch` | insecure: `sampling.rs:35` only (0x24a768); 2,869,582 instructions | **no verdict, OOM** at the 120 GB cap (125.6 GB RSS, 17:42:09Z) |
| `nearcore-dispatch` | insecure: `sampling.rs:35` only (0x20d26b); 2,842,625 instructions | not rerun: OOM above 120 GB on the previous tree |
| `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 726,933 instructions, 0 pending paths; no `sampling.rs:35` leak reached | unknown: cut at the same instruction after 85,683 / 85,687 instructions |
| `nearcore-exact-novec` | insecure: `sampling.rs:35` only (0x20cd5a); 1 pending path, 2,834,212 instructions, 232,794 of 232,795 control-flow checks passed | insecure: `sampling.rs:35` only; 1,566,361 instructions |

So the whole of Sign gets no better than "the only leak found is the public `sample_in_ball` accept test" where the census runs
(four x86_64 profiles and the novec one); under nearcore's exact build it is still cut at the NTT. The census needs more memory
under `default` and `dispatch` than on the previous tree (the prepared census no longer fits in 120 GB); the code shape changed, and the
census is not evidence either way.

### `nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2

Both profiles give the same verdict for every probe (113 entrypoints, 600 s per probe):
61 secure, 3 expected insecure (`rej_bounded_poly_eta2/4` at `sampling.rs:129`/`:132`, and the positive control
`control_early_exit_44` at `extra.rs:221`), 0 unexpected insecure, 49 unknown. The six `sk_is_well_formed` probes that were
`insecure` on the previous tree (CT-3 in `docs/assurance.md`) are `secure`.

Against the previous sweep of the same profiles, 6 probes went from `insecure` to `secure`
(`sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}`: 51,583 / 76,740 / 97,281 and 65,893 / 82,034 / 97,281
instructions, 12,707 / 18,908 / 24,020 and 17,671 / 20,744 / 24,020 control-flow checks, 0 pending paths) and 16 from `unknown` to
`secure` (`sk_decode_*`, `sk_encode_*`, `expand_mask_*`, `barrett_reduce`, `vec_power2round_87`,
`split_vec_power2round_{5,6,7,8_hi,8_lo}`; they had been stuck at an overflow-check guard in `field.rs`, and the guards are gone);
`field_add` is a new entrypoint (secure). No probe went from `secure` to anything else.

**What `unknown` means here.** "0 pending paths, no leak among the checks that passed, one path cut at an instruction BINSEC
cannot lift" (`[sse:error] Cut path 0 (uninterpreted "KO")`; the 600 s limit is not reached: 0.08 to 1.7 s per probe; every cut line
and status time in `sweep-15b4ce2/x86_64-nearcore-exact.cut-paths.txt`) for 48 of the 49, and a solver stall for one:

| unliftable instruction | where | probes |
|---|---|---|
| `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `ntt.rs:111` (`ntt_layer::<8, 16>`, forward NTT layer), `0x224f10` | 31: `ntt`, `ntt_vec_44`, `compute_t_*` (4), `prepare_sk_*` (3), `prepare_sk_1x1_44`, `signing_key_*` (3), `control_prepared_{branch,index}_44`, and the `split_*` NTT, `compute_t` and `prepare_sk` pieces (16) |
| `vblendvps` with `xmm` operands | vectorized `small_reduce` (the `wrapping_sub(Q & mask)` select, `field.rs:25`) right after `mont_reduce` (`field.rs:76`) in the pointwise product; objdump labels every one of these addresses `<u32>::wrapping_sub`, `uint_macros.rs:2494`, and the enclosing frames were checked for `0x2077e1` (`hint_step_44`, `response_44`) only | 16: `matrix_vector_ntt_*` (4), `scalar_vector_ntt_inverse_1`, `multiply_ntt`, `hint_step_*` (5), `response_*` (5) |
| `vblendps $0xf0,%ymm7,%ymm13,%ymm6` | `ntt.rs:131` (`ntt_inverse_layer::<4, 32>`, inverse NTT layer), `0x21faa9`: a 256-bit (`ymm`) blend | 1: `ntt_inverse` |

All three are VEX encodings (`vinsertps`, `vblendvps`, `vblendps`); BINSEC 0.11.3 does not lift them, the same limit as `vtestps` in
the experiments (upstream U-44). Under nearcore's target features (`+fma` implies AVX) LLVM emits them for the vectorized loops.
Unknown rows are not findings: they are probes about which BINSEC says nothing for nearcore's exact build, and the two censuses
are in the same state (cut at `vinsertps` after 726,927 and 85,683 instructions; `x86_64-censuses.txt`).
Per probe (steps = executed instructions when the path was cut, `nearcore-exact`; the last column is the address in
`nearcore-exact-dispatch`, which cuts at the same mnemonic for every probe; nine `vblendvps` rows have other register operands
there, in `sweep-15b4ce2/x86_64-nearcore-exact-dispatch.unknowns.txt`):

| probe | steps | stop address | instruction | address in `-dispatch` |
|---|---|---|---|---|
| `compute_t_1x1` | 25971 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `compute_t_44` | 192481 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `compute_t_65` | 328107 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `compute_t_87` | 568425 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `matrix_vector_ntt_1x1` | 15301 | `0x22ba23` | `vblendvps %xmm7,%xmm14,%xmm5,%xmm7` | `0x2309aa` |
| `matrix_vector_ntt_44` | 159967 | `0x2063d0` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x22f550` |
| `matrix_vector_ntt_65` | 281173 | `0x206ce0` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x22f980` |
| `matrix_vector_ntt_87` | 507044 | `0x22aea0` | `vblendvps %xmm1,%xmm13,%xmm14,%xmm1` | `0x22fdb0` |
| `ntt_vec_44` | 33301 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `scalar_vector_ntt_inverse_1` | 15301 | `0x22e65a` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x23394e` |
| `control_prepared_branch_44` | 85662 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `control_prepared_index_44` | 85683 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `prepare_sk_1x1_44` | 41492 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `prepare_sk_1x1_65` | 50277 | (1 pending path, see text) | | |
| `prepare_sk_44` | 85663 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `prepare_sk_65` | 132210 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `prepare_sk_87` | 172553 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `signing_key_44` | 85663 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `signing_key_65` | 132214 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `signing_key_87` | 172557 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `multiply_ntt` | 14376 | `0x24011d` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x24446d` |
| `ntt` | 11066 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `ntt_inverse` | 10155 | `0x21faa9` | `vblendps $0xf0,%ymm7,%ymm13,%ymm6` | `0x220889` |
| `hint_step_1_44` | 22376 | `0x21e04a` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x21ed9a` |
| `hint_step_1_65` | 22376 | `0x21e04a` | `vblendvps %xmm8,%xmm5,%xmm6,%xmm8` | `0x21ed9a` |
| `hint_step_44` | 66979 | `0x2077e1` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x210fa1` |
| `hint_step_65` | 96605 | `0x207ed1` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x206540` |
| `hint_step_87` | 126261 | `0x208921` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x2072e0` |
| `response_1x1_44` | 36515 | `0x21d55b` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x21e1aa` |
| `response_1x1_65` | 36515 | `0x21d55b` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x21e1aa` |
| `response_44` | 125615 | `0x2077e1` | `vblendvps %xmm2,%xmm14,%xmm0,%xmm2` | `0x20f2e2` |
| `response_65` | 169790 | `0x2456bf` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x249a4e` |
| `response_87` | 228822 | `0x24686f` | `vblendvps %xmm2,%xmm9,%xmm0,%xmm2` | `0x24af0e` |
| `split_compute_t_44_2x2` | 65559 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `split_compute_t_44_col` | 72713 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `split_compute_t_44_row` | 72716 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x229040` |
| `split_ntt_vec_into_1` | 11066 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_ntt_vec_into_7` | 55334 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_ntt_vec_into_8` | 62680 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_44_col` | 86494 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_44_row` | 52920 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_65_col` | 135272 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_65_row` | 68255 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_2x1` | 68910 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_4x1` | 101096 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_6x1` | 138210 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_7x1` | 143318 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_col` | 157611 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |
| `split_prepare_sk_87_row` | 81189 | `0x224f10` | `vinsertps $0x68,%xmm10,%xmm14,%xmm14` | `0x225d70` |

The 49th unknown, `prepare_sk_1x1_65`, is not a cut path: 1 pending path at the 600 s limit (50,277 instructions) and at a 3600 s
rerun with `TRACE=1` (50,277 again, last step 50,296: `0x22396e movdqu %xmm6,0x3c0(%rdi)` in `ntt_body_mut`, the same
place), 13,884 control-flow checks passed, no leak. A solver stall, not a VEX cut; same in `nearcore-exact-dispatch` at 600 s.
It is `secure` in `nearcore-exact-novec` (below). 

### `nearcore-exact-novec`: the same flags with the loop and SLP vectorizers off

New profile (`run-select.sh`, `PROFILE=nearcore-exact-novec`, c63f632): `nearcore-exact` plus `-C llvm-args=-vectorize-loops=false
-C llvm-args=-vectorize-slp=false` (what `nearcore-novec` does for the older profile). Overflow checks, nearcore's target features
(`+fma`, so AVX is on) and rustc 1.95.0 are unchanged (`x86_64-nearcore-exact-novec.header.txt`). 113 probes, 600 s each:
**108 secure, 5 expected insecure, 0 unexpected insecure, 0 unknown**: no cut path and no timeout. The five insecure are
`rej_bounded_poly_eta2/4`, `control_early_exit_44` and, now that the NTT is analyzable, both prepared positive controls
`control_prepared_branch_44` (`prepared.rs:76`) and `control_prepared_index_44` (`prepared.rs:96`). So every one of the 49 probes that
is `unknown` under `nearcore-exact` (the NTT, `hint_step`, `response`, `prepare_sk`, `signing_key`, `compute_t` family and the
splits) is `secure` with the vectorizers off, including `prepare_sk_1x1_65`, and the `prepare_sk_*` rows are controlled there
(under `nearcore-exact*` the two prepared controls are cut in `prepare_sk`'s NTT before the control site, so the `prepare_sk_*`
rows of those profiles are uncontrolled as well as unknown). What this is: evidence about a build that is not nearcore's, since
nearcore leaves the vectorizers on. It shows that the scalar code, with nearcore's overflow checks and target features, has no
secret-dependent branch, address or division operand in these probes; it does not cover the vectorized NTT and product code that
nearcore's compiler actually emits.

### thumbv7em, riscv32imac, AArch64 without NEON

- **thumbv7em** (default profile, 113 probes, 3600 s): 109 secure, 4 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_index_44`), 0 unknown. `control_prepared_branch_44` is `secure` here, an invalid
  control (the branch is lowered to a select). The two censuses were not rerun (OOM at 120 GB, below).
- **riscv32imac** (default profile, 114 probes): 101 secure, 5 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_index_44`, and the standalone `ct_lt_mask`: one control-flow leak, 0x03d456 in this
  run), 8 unknown in the sweep run (`JOBS=8`, 3600 s): `vec_power2round_87` (190,098 instructions, 1 pending path) and
  `split_vec_power2round_{5,6,7}`; `control_prepared_branch_44`, which is `insecure` in a rerun alone (`JOBS=2`, 7200 s; the leak
  was found, so the result depends on exploration order); and three that are `unknown` here but were `secure` when the probes were
  added: `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1`. Rerun alone with `JOBS=2` and 7200 s
  (`sweep-15b4ce2/riscv32imac.rerun-7200s.txt`) they are `unknown` again with 1 pending path, 387,086 / 280,586 / 590,565
  instructions and 59,674 / 42,013 / 70,756 control-flow checks passed, no leak, the same counts as the sweep run, so contention was
  not the cause. With `TRACE=1` at 600 s (`riscv32imac.rerun-trace-600s.txt`) all three stop at the same instruction,
  `0x045e28 sw s1,0(a7)` in `ntt_body_mut` (+0xaba). Built from the commit that added them (d1f4da0), the same three probes are
  `secure` (`riscv32imac.control-d1f4da0.txt`: 1,431,873 / 991,518 / 1,434,718 instructions). The harness changes are irrelevant
  and `ntt_body_mut` is essentially unchanged (3 of 3136 bytes differ, apparently immediates); what changed is that the
  `split_prepare_sk_*` wrappers now inline `prepare_sk_into` (`65_col` 340 to 1296 bytes, `65_row` 216 to 854). Other pieces inlined
  the same way stayed `secure`, so the cause of the stall at the `ntt_body_mut` store is not pinned down. Coverage is not reduced:
  the full-size riscv `prepare_sk_{44,65,87}` and `signing_key_{44,65,87}` are `secure`, and the 23 other riscv split pieces and
  both one-polynomial `prepare_sk_1x1_*` are `secure`. No leak was found.
- **AArch64 without NEON** (`aarch64.sh`, 115 probes with the two censuses, 3600 s): 99 secure, 3 expected insecure
  (`rej_bounded_poly_eta2/4`, `control_early_exit_44`), 13 unknown: `compute_t_44`, `prepare_sk_{44,65,87}`,
  `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44`, `control_prepared_{branch,index}_44`, and the two
  split pieces `split_prepare_sk_87_{7x1,col}`. All are the solver stall (upstream U-42 in `docs/upstream-issues.md`). All 28 split
  probes ran (26 secure, 2 unknown).
- Every `secure` row of the thumbv7em, riscv32imac and AArch64 runs has 0 pending paths and all of its (nonzero) control-flow and
  memory-access checks passing (`*.verdicts.tsv`); the x86_64 rows too.
- `NONEON` code is not what an AArch64 production build runs (NEON is on), and BINSEC cannot lift the vectorized code of that
  build (`umax`/`umin` on `.4s` vectors, U-40). The scalar result shows that the source-level structure is constant time with the
  AArch64 select lowering (`csel`), not that the NEON code is. `aarch64.sh` is not a supported `cargo-checkct` target: it builds
  the driver for `aarch64-unknown-linux-gnu` itself (release, same profile, static relocation, `rust-lld`) and generates the BINSEC
  scripts with the `cargo-checkct` template adapted to AArch64 (return address in `x30`, `halt at` the panic hook and the sentinel
  return address).

### Not rerun, and why

These were not rerun at 15b4ce2 (about an hour each, and the result at the same cap would not be a verdict); their results are those of
the previous sweep (e9a1c74). `field.rs` changed, so a different outcome is possible, but nothing points to one; the x86_64 default and
`dispatch` prepared censuses, which fitted in 120 GB before and no longer do, show that this can go either way.

- thumbv7em `census_sign_internal_44`, `census_sign_prepared_44`, riscv32imac `census_sign_prepared_44` and x86_64
  `nearcore-dispatch` `census_sign_prepared_44`: out of memory at the 120 GB cap.
- riscv32imac `census_sign_internal_44`: 4 pending paths at 3600 s and 7200 s.
- Static-AVX2 profiles `avx2` and `nearcore-avx2` (`select-ntt.sh avx2`): not part of the sweep tables.

### OOM ledger

Every `error` of this sweep is an out-of-memory kill: three `census_sign_prepared_44` runs, each matched to a kernel log entry
(`journalctl -k -g 'Killed process'`): `default` at the 110 GB cap (binsec at 115.1 GB RSS), `default` again alone at the 120 GB
cap (125.6 GB RSS) and `dispatch` at the 120 GB cap (125.6 GB RSS). There was no other kill of any process on the machine in that
window; no probe of the 113 per profile ended `error` (`sweep-15b4ce2/oom-kills.txt`). A census killed alone at 120 GB is recorded
as "needs more than 120 GB" and the cap is not raised again.

Other deviations from the method above:

- Up to ten containers ran at once in the first hours (`JOBS=8` each, 64 GB cap each, `--cpus 24` each on 60 cores), and 7200 s
  reruns used `JOBS=2`. Where contention could matter (the three riscv32imac split probes), a rerun alone gave the same result.
- `cargo-checkct`'s build pass runs every probe with `-sse-timeout 1`, which BINSEC checks only between paths: in the census
  containers it held one container for about 110 minutes on a single probe before the real run started. No verdict depends on it.
- One census container (`nearcore-exact-novec`, started while a 98 GB `default` census was running) was stopped at 36 GB RSS with
  `docker kill` to keep the machine clear of a host-level OOM (a deliberate stop, not a kernel kill) and rerun later alone.

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
   That does not hold at 15b4ce2: 48 of the 113 probes are cut paths at `vinsertps`, `vblendvps` or `vblendps` (tables above), so
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
for a few). The sweep at 15b4ce2 needs no stages: an `unknown` is a cut path within seconds. `TRACE=1` records the last executed
instruction of every probe.

### What this does and does not show

- `nearcore-exact` is a better approximation of nearcore's x86_64 release build than `nearcore`, not the binary: the crate is
  probed in isolation (inlining context), `core` is built from source (above), `memcpy` is `compiler_builtins`', and the
  allocator, `std` and nearcore's callers are absent.
- At 15b4ce2: 61 secure, 3 expected insecure, 49 unknown (and the two censuses, also unknown). Everything on the NTT, on
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
| `vec_power2round_87` (full size) | riscv32imac default | unknown, 1 pending path | 1 h and 2 h on the previous tree, 1 h at 15b4ce2 (190,098 instructions, still 1 pending path). Covered by the split windows `split_vec_power2round_8_*` (secure) |
| `split_vec_power2round_{5,6,7}` | riscv32imac | unknown | 1 h, again 1 h at 15b4ce2 (capacity probing only; the 8-wide windows cover the loop) |
| `census_sign_internal_44` | riscv32imac default | unknown, 4 pending paths | 1 h and 2 h on the previous tree |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44` | AArch64 `NONEON=1` | unknown: one pending path stuck in one solver query (instruction count identical at 300, 600, 3600 and 7200 s; upstream log U-42) | 1 h and 2 h on the previous tree, 1 h again at 15b4ce2 (same probes, `control_prepared_*` too). Pieces covered by split probes, except the K = 8 glue of `prepare_sk_87` / `signing_key_87` |
| `split_prepare_sk_87_7x1`, `split_prepare_sk_87_8x1` | AArch64 `NONEON=1` | unknown, same stall | 1 h (round 2 of `split-run.sh`), again 1 h at 15b4ce2 (`split_prepare_sk_87_col` is the `_8x1` probe) |
| `census_sign_internal_44`, `census_sign_prepared_44` | thumbv7em default | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps (see "Reading `error` results" above). Don't raise the cap again; a split would be needed |
| `census_sign_prepared_44` | riscv32imac default; x86_64 `nearcore-dispatch`; x86_64 default and `dispatch` (since 15b4ce2) | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps; x86_64 default also at 110 GB, `dispatch` at 120 GB (15b4ce2, killed at 125.6 GB RSS). It was `insecure` on the previous tree for default and `dispatch` after a 120 GB run |
| `control_prepared_branch_44` | thumbv7em | `secure`: the control is invalid there (branch lowered to a select) | every run; expected |
| `control_prepared_branch_44`, `control_prepared_index_44` | AArch64 `NONEON=1` | no verdict | 1 h and 2 h |
| 49 probes: `ntt`, `ntt_inverse`, `multiply_ntt`, `ntt_vec_44`, `compute_t_*`, `matrix_vector_ntt_*`, `scalar_vector_ntt_inverse_1`, `prepare_sk_*`, `signing_key_*`, `prepare_sk_1x1_*`, `control_prepared_*`, `hint_step_*`, `response_*`, 16 `split_*` (list in "`nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2") | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: 48 are cut paths at VEX instructions BINSEC 0.11.3 cannot lift (`vinsertps`, `vblendvps`, `vblendps ymm`), 0 pending paths, stopped in 0.08 to 1.7 s; `prepare_sk_1x1_65` is a solver stall (1 pending path) | 600 s for all, 3600 s with `TRACE=1` for `prepare_sk_1x1_65`. A longer timeout cannot help a cut path. What helps: a build without the vectorizers (`PROFILE=nearcore-exact-novec`: all 49 `secure`) or a BINSEC that lifts VEX (U-44) |
| `census_sign_internal_44`, `census_sign_prepared_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 85,683 instructions | 110 GB, `JOBS=1`, 3600 s at 15b4ce2 (cut within 2 s). `nearcore-exact-novec` has a result: `insecure`, only the public `sampling.rs:35` leak |
| `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1` | riscv32imac default | unknown, 1 pending path, stuck at `0x045e28 sw s1,0(a7)` in `ntt_body_mut` (new at 15b4ce2; `secure` at d1f4da0) | 3600 s (sweep), 7200 s alone with `JOBS=2`, 600 s with `TRACE=1`: the same instruction counts every time. Covered by the full-size `prepare_sk_*` / `signing_key_*` rows, which are `secure` |

## Probes

113 entrypoints without the censuses, built for x86_64-unknown-linux-gnu, thumbv7em-none-eabihf, riscv32imac-unknown-none-elf and (with `aarch64.sh`) AArch64.

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

The `prepare_sk_*` verdicts are not vacuous: 0 pending paths, and for example `prepare_sk_87` on x86_64 visits 3,166,803 instructions
with 207,975 control-flow and 1,038,098 memory-access checks passing. `control_prepared_branch_44` is `secure` on thumbv7em because
the compiler turns `if bit {1} else {2}` into a conditional select; it is a valid control only where it reports `insecure`. The
index control cannot be compiled away and is `insecure` on all three default targets.

Expected-insecure probes. `rej_bounded_poly_eta{2,4}` leak by design: the loop branches on whether a sampled
nibble is accepted, and which positions are rejected is public (it only changes how many XOF bytes are consumed).
`census_sign_internal_44` finds the same kind of branch (a rejection sampler) first. These are not constant-time
bugs; they show what BINSEC cannot distinguish (secret data versus public outcome of a secret-derived value), which
is why the proof of "no secret-dependent branch" is done per step.

## Split probes (`driver/src/split.rs`, `split-run.sh`)

Some full-size probes have no verdict: BINSEC stops with one pending path stuck in one solver query (the same instruction count at
3600 s and 7200 s), no leak found. The split probes cover the same code in smaller pieces, so that every piece has a completed
verdict. They are in `driver/src/split.rs`; run them with `bash checkct/split-run.sh`, which starts the AArch64 container
(`NONEON=1`, `aarch64.sh`) and the riscv32imac container (`run-select.sh`) side by side, each with 2 BINSEC jobs, 3600 s per probe,
and exits nonzero if either fails. A probe name starts with `split_`. Per-probe verdicts of the latest sweep are in
`checkct/results/sweep-15b4ce2/*.verdicts.tsv`.

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
| `vec_power2round_87` | riscv32imac | `split_vec_power2round_{1,2,3}` (K = 1 to 3), the windows `_8_lo` (i in 0..4), `_8_hi` (4..8) and `_8_q0..q3` (pairs 0..2, 2..4, 4..6, 6..8) of the K=8 loop over the same eight secret polynomials. `_5`, `_6`, `_7` are `unknown` (capacity probing, not cover). `split_vec_power2round_4` was `secure` in the previous run of the same script (checks 26,713 control-flow); in the last run the compiler folded it into the identical `vec_power2round_44` (K = 4, secure in the sweep), so it has no entrypoint there | the windows run the identical K=8 instance and partition its iterations, so their union is the whole loop (the loop's trip count is public); `_8_lo`/`_8_hi` are the halves, `_q0..q3` the pairs |
| `prepare_sk_44`, `prepare_sk_87`, `signing_key_44`, `signing_key_87` | riscv32imac (`unknown` on an older tree, `secure` since) | `split_prepare_sk_{44,65,87}_{row,col}`, `split_prepare_sk_87_{2,4,6,7}x1` | not needed for a verdict any more; run for the table |

`signing_key_NN` is `sign::prepare_sk_into` on a zeroed key object plus a `mem::replace` of that object (`api.rs`): the
same instruction and check counts as `prepare_sk_NN` on x86_64 and thumbv7em, so the `prepare_sk` pieces are its pieces. In the sweep above every riscv32imac `prepare_sk_*` and `signing_key_*` row is already `secure` at
full size (they were `unknown` on an older tree); the riscv32imac `prepare_sk` splits are run for completeness.

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
- Shake absorb/squeeze with a secret input is covered through `keccak_f1600` and the hash probes
  (`keygen_seed_hash`, `sign_rho_pp_hash`, `expand_mask_*`) only for the parameter sets listed; verify (public data) and
  `use_hint` are not probed; zeroization is outside this tool.
- BINSEC proves absence of secret-dependent control flow/memory/division operands, not absence of data-dependent
  instruction timing (e.g. variable-latency multiplies on some cores; the `multiplication` check is experimental and
  not enabled).
