# checkct: binary-level constant-time checks (BINSEC)

Port of the RustCrypto `ml-dsa/checkct` harness (signatures repo, rev a3690c4) to this crate. The driver
`#[path]`-includes the crate sources unchanged (`params`, `field`, `rounding`, `ntt`, `keccak`, `encode`, `sampling`,
`keygen`, `sign`, `verify`, `api`; the crate is `no_std` with no dependencies, so no shims are needed), marks every
probe input secret through the `__checkct_private_rand` hook, and lets BINSEC (via `cargo-checkct`) symbolically
execute the compiled release binary, flagging any secret-dependent branch, memory access, or division operand.

This directory is its own workspace (`[workspace]` in `checkct/Cargo.toml`). It is not a member of the main
crate's workspace and the main `Cargo.toml` needed no `exclude`. `src/` is not edited.

> **Reading `error` results (2026-10-31, ISSUES.md T-8).** BINSEC killed at a container's memory cap shows only `error`
> in the job log. Every `error` in the tables below is presumed to be an out-of-memory kill, with no verdict, unless
> the kernel log (`journalctl -k -g 'Killed process'`) shows no kill in its run window. The full sweep at e9a1c74
> (below) matched every `error` of that sweep to a kernel OOM kill, and the sweep at 15b4ce2 did the same for its three; the `error`
> rows of the older-tree sections stay "presumed".

## Running

Linux only (BINSEC). On the build box, via Docker:

    docker build -t ct-binsec checkct                           # once, and again after Dockerfile changes; ~10 min
    rx submit ct4 -- 'set -o pipefail; bash checkct/run.sh 2>&1 | tee ct.log'
    rx wait ct4

Scripts (all start from the repository root; `rx kill` does not stop containers, so `docker kill $NAME` too):

| script | purpose | environment |
|---|---|---|
| `run.sh` | all probes, all three targets (`cargo-checkct run --all-leaks`); `JOBS` defaults to every CPU, which does not fit a 64 GB container, so the full sweep of e9a1c74 used `run-select.sh` with `ONLY=.` instead | `TIMEOUT` (900 s per probe), `JOBS`, `OUT` (copies the three `<target>.driver` binaries), `NAME`, `PROFILE=nearcore` |
| `run-select.sh` | only probes matching a regex, long timeouts; builds with `cargo-checkct`, then calls `binsec` directly. Streams a `done <target> <probe> <status>` line per probe and ends with a `Summary:` block like `run.sh` | `ONLY` (regex), `EXCLUDE` (regex), `TARGETS`, `TIMEOUT` (7200), `JOBS` (4), `OUT`, `NAME`, `PROFILE`, `TRACE=1` (last executed instruction per probe), `EXPERIMENTS=1` (the `exp_*` probes), `CT_TOOLCHAIN` (nearcore-exact; default 1.95.0) |
| `unknowns.py BIN LOG...` | maps every leak address, every cut path (`uninterpreted "KO"`) and every `TRACE` last instruction of a `Summary:` block to function, source line and instruction (GNU `objdump`, runs on the box host; `leaks.sh` needs `llvm-objdump`, which the host does not have). `python3 -I checkct/unknowns.py DIR/x86_64-unknown-linux-gnu.driver LOG` | |
| `leak-context.sh BIN ADDR...` | disassembly around an address with source lines (`BEFORE`, `AFTER` bytes) | |
| `probe-now.sh CONTAINER PROBE [T] [binsec args]` | reruns one probe inside a running `run-select.sh` container for a few seconds with the full BINSEC log (diagnosis of a sweep in flight; not for verdicts) | |
| `leaks.sh LOG BINDIR` | maps every leaking instruction address of a `Summary:` block to `file:line` and the instruction (`llvm-objdump -d -l` on the `OUT` binaries) | `OBJDUMP` as third argument |
| `aarch64.sh` | experiment: AArch64 (see below); `cargo-checkct` does not support the target, so it builds the driver for `aarch64-unknown-linux-gnu` in the container and writes the BINSEC scripts itself | `ONLY`, `TIMEOUT`, `JOBS`, `NAME`, `OUT`, `NONEON=1` |
| `split-run.sh [round2]` | the split probes of `driver/src/split.rs` on AArch64 (`NONEON=1`) and riscv32imac, two containers in parallel, exit status nonzero if either fails (see "Split probes") | `TIMEOUT` (3600), `JOBS` (2 per container), `AONLY`, `RONLY` |
| `select-ntt.sh [mode]` | the NTT and field-product probes and the KeyGen/Sign pieces built on them, through `run-select.sh`; `mode` is `default`, `dispatch`, `nearcore-dispatch`, `avx2` or `nearcore-avx2` (see "Profiles for the AVX2 dispatch") | `TIMEOUT` (3600), `JOBS`, `OUT`, `NAME`; the 2nd and 3rd arguments replace the probe regex and the target list |
| `scan-avx2.sh DIR` | static scan of the `*_avx2` functions of a dispatch driver (`DIR` under `~/rx/scratch`, the `OUT` of a dispatch run); fails if there are none | |

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
The full sweep at e9a1c74 below covers every probe in both dispatch profiles.

Toolchain (every profile except `nearcore-exact*`, which use 1.95.0, see below): `nightly-2026-10-06` with `rust-src` (`checkct/rust-toolchain.toml`), `-Zbuild-std=core,panic_abort` with
`compiler-builtins-mem` (`.cargo/config.toml`, copied from upstream). BINSEC 0.11.3, unisim_archisec 0.0.14,
cargo-checkct @ 85271e5. Checks: `control-flow,memory-access,dividend,divisor`. Building only (no BINSEC) works
anywhere with the toolchain: `cd checkct && cargo build --release -p driver --target x86_64-unknown-linux-gnu`.

`checkct_macros/src/lib.rs` and `.cargo/config.toml` are copied from upstream (Apache-2.0 OR MIT), as
`cargo-checkct init` generates them. `driver/src/rng.rs` is the same hook pair without the `rand_core` impls.

## Full sweep at 15b4ce2 (November 4, 2026)

The current results. `src/` at 15b4ce2: the tree after ae6023c (merged in ddf201b), which put `wrapping_*` arithmetic into
`field.rs` (`small_reduce`, `barrett_reduce`, `add`, `sub`, `neg`, `mont_reduce`), `rounding.rs` (`reduce_mod`,
`mod_plus_minus`, `decompose`, `infinity_norm`, an `opaque_u32` on the running maximum of `vec_infinity_norm`) and
`encode.rs` (`poly_eta_bad`/`eta_block_bad` mask accumulation, one compare in `sk_is_well_formed`), so that no
overflow-check guard is left on a secret value (ISSUES CT-3). The harness is c63f632, which only adds the profile
`nearcore-exact-novec` to `run-select.sh` (`nearcore-exact` plus `-C llvm-args=-vectorize-loops=false
-vectorize-slp=false`). The previous full sweep is at e9a1c74 (below). Raw per-probe results, with every
leak and stop address mapped to function, source line and instruction by `unknowns.py`, are in
`checkct/results/sweep-15b4ce2/` (`<target>-<profile>.verdicts.tsv`, `.unknowns.txt`/`.summary.txt`, `.header.txt` with the
toolchain and flags the run printed).

Method: `run-select.sh` (AArch64: `aarch64.sh` with `NONEON=1`), `ONLY=.`, one container per target and profile (64 GB
cap, `JOBS=8`), `EXCLUDE=census_sign` (the censuses ran separately, below). `TIMEOUT=3600` for the checkct-profile,
`nearcore`, `dispatch` and `nearcore-dispatch` x86_64 runs and for thumbv7em, riscv32imac and AArch64; `TIMEOUT=600` for
`nearcore-exact`, `nearcore-exact-dispatch` and `nearcore-exact-novec`, as for the e9a1c74-era `nearcore-exact` sweep. Up to
ten containers ran at the same time on the 60-core box, which is why three riscv32imac probes were rerun alone (below). The x86_64 profiles
other than `nearcore-exact*` use `nightly-2026-10-06` (LLVM 23.1.3), `nearcore-exact*` use rustc 1.95.0 (LLVM 22.1.2); the
`.comment` check passed in every run (`*.header.txt`).

**Count basis.** The e9a1c74 tables count 87 probes per target: 85 entrypoints (the `split_*` probes of `split.rs` came after those
tables and are counted separately) plus the two censuses. A run now has 113 entrypoints without the censuses
(114 on riscv32imac and in the `dispatch` build, where `split_vec_power2round_4` stays its own entrypoint): 85 non-split and 28 split
(29 where noted); the AArch64 run has 115 rows with the two censuses. The "same basis" column is the 85
non-split entrypoints plus the two censuses, which is the e9a1c74 basis and gives 87; the split probes have their own column. The
e9a1c74-era `nearcore-exact` sweep had 84 non-split entrypoints because LTO had merged `field_add`; its totals (114 with the
censuses) are not on the 87 basis, so the `nearcore-exact*` rows compare all probes.

Columns: secure / expected insecure / unexpected insecure / unknown / no verdict (OOM).

| target / profile | e9a1c74, 87 probes | 15b4ce2, same 87-probe basis | 15b4ce2, split probes |
|---|---|---|---|
| x86_64, default | 80 / 7 / 0 / 0 / 0 | 80 / 6 / 0 / 0 / 1 | 28 / 0 / 0 / 0 / 0 |
| x86_64, `nearcore` | 74 / 7 / 0 / 6 / 0 | 80 / 7 / 0 / 0 / 0 | 28 / 0 / 0 / 0 / 0 |
| x86_64, `dispatch` | 80 / 7 / 0 / 0 / 0 | 80 / 6 / 0 / 0 / 1 | 29 / 0 / 0 / 0 / 0 |
| x86_64, `nearcore-dispatch` | 74 / 6 / 0 / 6 / 1 | 80 / 6 / 0 / 0 / 1 (prepared census not rerun) | 28 / 0 / 0 / 0 / 0 |
| thumbv7em, default | 81 / 4 / 0 / 0 / 2 | 81 / 4 / 0 / 0 / 2 (censuses not rerun) | 28 / 0 / 0 / 0 / 0 |
| riscv32imac, default | 78 / 6 / 0 / 2 / 1 | 78 / 6 / 0 / 2 / 1 (censuses not rerun) | 23 / 0 / 0 / 6 / 0 |
| AArch64 `NONEON=1` | 73 / 3 / 0 / 11 / 0 | 73 / 3 / 0 / 11 / 0 | 26 / 0 / 0 / 2 / 0 |

Not on the 87 basis, all probes of the run (113 entrypoints plus the two censuses):

| x86_64 profile | e9a1c74-era tree (112 entrypoints plus the 2 censuses) | 15b4ce2 (113 plus the 2 censuses) |
|---|---|---|
| `nearcore-exact` | 38 / 3 / 6 / 67 / 0 | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-dispatch` | 38 / 3 / 6 / 67 / 0 | 61 / 3 / 0 / 51 / 0 |
| `nearcore-exact-novec` (new) | not run | 108 / 7 / 0 / 0 / 0 |

Reading the first table: the "expected insecure" cells are `rej_bounded_poly_eta2/4`, the positive controls (`control_early_exit_44`,
`control_prepared_branch_44`, `control_prepared_index_44`; on thumbv7em only the first and the third, the branch control is the invalid
`secure` one; on riscv32imac also the standalone `ct_lt_mask`) and, on x86_64, the censuses that finish `insecure` with only the public
`sampling.rs:35` leak (below). Every probe of the first table has a verdict except the unknown and OOM cells shown, and each `secure`
row has 0 pending paths and all checks passing. **No unexpected `insecure` result on any target or profile; no new leak.**

**Verdict changes against e9a1c74**, probe by probe:

- x86_64 `nearcore` and `nearcore-dispatch`: `sk_is_well_formed_{44,65,87}` and `encode_sk_is_well_formed_{44,65,87}`, `unknown`
  (SSE2 `movmskpd` cut) to `secure`. The six probes are secure in all seven x86_64 profiles, on thumbv7em, riscv32imac and
  AArch64 (`*.verdicts.tsv`).
- x86_64 `nearcore-exact`, `nearcore-exact-dispatch`: 22 probes improve (6 `insecure` to `secure`, 16 `unknown` to `secure`), none
  gets worse; see "`nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2".
- x86_64 `default` and `dispatch` `census_sign_prepared_44`: `insecure` (public leak, 1 pending path) at e9a1c74 after a 120 GB run,
  now killed at the 120 GB cap (kernel log: binsec at 125.6 GB RSS), so no verdict. A census proves nothing either way; the other
  census verdicts are unchanged.
- riscv32imac `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1`: `secure` to `unknown`
  (solver stall, below). This is the only verdict that got worse.
- Nothing else changed: thumbv7em and AArch64 are identical to e9a1c74 probe for probe (every non-secure probe is the same
  one), and riscv32imac differs only as stated. The only cut-path unknowns of the e9a1c74 sweep (SSE2 `movmskpd`) were the six
  `sk_is_well_formed` rows above.

Every non-secure probe of the sweep that is not an `nearcore-exact*` unknown:

| probe | where | result | reason |
|---|---|---|---|
| `rej_bounded_poly_eta2/4` | every row above | insecure, expected | sampler accept test, public outcome (`sampling.rs:129`, `:132`) |
| `control_early_exit_44` | every row above | insecure, expected | positive control, `extra.rs:221` (8 leaks on x86_64) |
| `control_prepared_branch_44` | x86_64 (all profiles but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac (`insecure` in the 7200 s rerun, `unknown` at 3600 s in the sweep run) | insecure, expected | positive control, `prepared.rs:76` |
| `control_prepared_index_44` | x86_64 (all but `nearcore-exact` and `nearcore-exact-dispatch`), riscv32imac, thumbv7em | insecure, expected | positive control, `prepared.rs:96` |
| `control_prepared_branch_44` | thumbv7em | secure, invalid control | branch lowered to a select, as at e9a1c74 |
| `control_prepared_{branch,index}_44` | AArch64 | unknown | built on `prepare_sk_44`, which does not finish (uncontrolled `prepare_sk` rows) |
| `control_prepared_{branch,index}_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown | cut path in `prepare_sk`'s NTT (`vinsertps`) before the control site; the `prepare_sk_*` rows there are uncontrolled |
| `ct_lt_mask` | riscv32imac | insecure, documented | standalone probe, in-crate callers are secure (as at e9a1c74) |
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
| default | insecure: one leak, `sampling.rs:35` (`sample_in_ball` accept test, public outcome) at 0x237998; 1 pending path, 2,875,532 instructions, 209,729 of 209,730 control-flow checks passed | **no verdict, OOM**: killed at the 110 GB cap (binsec at 115.1 GB RSS, 11:45:09Z) and again alone at the 120 GB cap (125.6 GB RSS, 16:27:26Z). It was `insecure` at e9a1c74 after a 120 GB run |
| `nearcore` | insecure: `sampling.rs:35` only (0x20da3b); 2,850,363 instructions | insecure: `sampling.rs:35` only; 1,539,485 instructions |
| `dispatch` | insecure: `sampling.rs:35` only (0x24a768); 2,869,582 instructions | **no verdict, OOM** at the 120 GB cap (125.6 GB RSS, 17:42:09Z); `insecure` at e9a1c74 |
| `nearcore-dispatch` | insecure: `sampling.rs:35` only (0x20d26b); 2,842,625 instructions | not rerun: OOM above 120 GB at e9a1c74 |
| `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 726,933 instructions, 0 pending paths; no `sampling.rs:35` leak reached | unknown: cut at the same instruction after 85,683 / 85,687 instructions |
| `nearcore-exact-novec` | insecure: `sampling.rs:35` only (0x20cd5a); 1 pending path, 2,834,212 instructions, 232,794 of 232,795 control-flow checks passed | insecure: `sampling.rs:35` only; 1,566,361 instructions |

So the whole of Sign gets no better than "the only leak found is the public `sample_in_ball` accept test" where the census runs
(four x86_64 profiles and the novec one); under nearcore's exact build it is still cut at the NTT. The census needs more memory
under `default` and `dispatch` than at e9a1c74 (the prepared census no longer fits in 120 GB); the code shape changed, and the
census is not evidence either way.

### `nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2

Both profiles give the same verdict for every probe (113 entrypoints, 600 s per probe):
61 secure, 3 expected insecure (`rej_bounded_poly_eta2/4` at `sampling.rs:129`/`:132`, and the positive control
`control_early_exit_44` at `extra.rs:221`), 0 unexpected insecure, 49 unknown. The six `sk_is_well_formed` probes that were
`insecure` at the e9a1c74-era tree (ISSUES CT-3) are `secure`.

**What changed against the e9a1c74-era sweep of the same profiles** (`checkct/results/nearcore-exact.stage1-600s.txt` and
`.stage3-trace-3600s.txt` against `sweep-15b4ce2/x86_64-nearcore-exact.verdicts.tsv`; the dispatch profile changes the same
probes; no probe went from `secure` to anything else):

- `insecure` to `secure` (6): `sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}` (51,583 / 76,740 / 97,281 and
  65,893 / 82,034 / 97,281 instructions, 12,707 / 18,908 / 24,020 and 17,671 / 20,744 / 24,020 control-flow checks, 0 pending paths).
- `unknown` to `secure` (16): `sk_decode_{44,65,87}`, `sk_encode_{44,65,87}`, `expand_mask_{44,65,87}`, `barrett_reduce`,
  `vec_power2round_87`, `split_vec_power2round_{5,6,7,8_hi,8_lo}`. These were stuck at an overflow-check guard in
  `field.rs`; the guards are gone.
- new entrypoint `field_add` (secure).
- the other 49 unknown probes were unknown at the e9a1c74-era tree too, but for a different reason (below).

**What `unknown` means now.** At e9a1c74 it was "timeout with 1 pending path stuck at an overflow-check guard". At 15b4ce2 it is
"0 pending paths, no leak among the checks that passed, one path cut at an instruction BINSEC cannot lift" (`[sse:error]
Cut path 0 (uninterpreted "KO")`, the 600 s limit is not reached: 0.08 to 1.7 s per probe) for 48 of the 49, and a solver stall for one:

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

### The review of `nearcore-exact` (confirmed or corrected)

| claim | measured | where |
|---|---|---|
| default x86_64: 39/39 secure | confirmed and wider: 108 secure, 5 expected insecure, 0 unknown over 113 probes | `x86_64-default.verdicts.tsv` |
| `nearcore-exact`: 6 `sk_is_well_formed` probes insecure to secure | confirmed (the three `sk_is_well_formed_NN` and the three `encode_sk_is_well_formed_NN`, both exact profiles) | `x86_64-nearcore-exact*.verdicts.tsv` |
| `sk_decode`, `sk_encode`, `expand_mask`: unknown to secure | confirmed (all nine probes; also `barrett_reduce`, `vec_power2round_87` and five `split_vec_power2round_*`) | same |
| `barrett_reduce` secure | confirmed (92 instructions, 13 control-flow checks) | same |
| 17 NTT, `hint_step` and `response` probes unknown at VEX instructions (`vinsertps`, `vblendvps`, `vblendps ymm`) | the instructions are right; the count is not: **48 probes** are cut at a VEX instruction, plus one solver stall (`prepare_sk_1x1_65`), 49 unknown in all, in each exact profile | stop table above |
| those are secure with vectorization off | confirmed: `nearcore-exact-novec` has a verdict for all 113 probes, 108 secure | `x86_64-nearcore-exact-novec.verdicts.tsv` |

### thumbv7em, riscv32imac, AArch64 without NEON

- **thumbv7em** (default profile, 113 probes, 3600 s): 109 secure, 4 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_index_44`), 0 unknown. `control_prepared_branch_44` is `secure` here, the invalid
  control of the e9a1c74 sweep (the branch is lowered to a select). The two censuses were not rerun (OOM at 120 GB, below). No
  verdict changed.
- **riscv32imac** (default profile, 114 probes): 101 secure, 5 expected insecure (`rej_bounded_poly_eta2/4`,
  `control_early_exit_44`, `control_prepared_index_44`, and the standalone `ct_lt_mask`: `insecure` as at
  e9a1c74, one control-flow leak, 0x03d456 in this run), 8 unknown in the sweep run (`JOBS=8`, 3600 s): the known `vec_power2round_87` (190,098 instructions, 1 pending path) and
  `split_vec_power2round_{5,6,7}`; `control_prepared_branch_44`, which is `insecure` in a rerun alone (`JOBS=2`, 7200 s; the
  leak was found, as in the e9a1c74 rerun, so the result depends on exploration order); and **three verdicts that are new:
  `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1` are `unknown`, and were `secure` at the tree
  that added them (d1f4da0, 120,105 / 80,137 / 122,233 control-flow checks, 0 pending paths).** This is a change, not noise: the
  three probes ran again alone with `JOBS=2` and 7200 s (`sweep-15b4ce2/riscv32imac.rerun-7200s.txt`): `unknown` again, 1 pending
  path, 387,086 / 280,586 / 590,565 instructions and 59,674 / 42,013 / 70,756 control-flow checks passed, no leak, the same counts as in
  the sweep run at 3600 s (that run shared the box with other containers; the rerun alone shows contention was not the cause).
  With `TRACE=1` at 600 s (`riscv32imac.rerun-trace-600s.txt`) all three stop at the same instruction, `0x045e28 sw s1,0(a7)` in
  `ntt_body_mut` (+0xaba). As a control the same three probes were built from d1f4da0
  (checkct harness and `src/` of that commit, same image and command, `JOBS=3`): all `secure` within the run
  (`riscv32imac.control-d1f4da0.txt`: 1,431,873 / 991,518 / 1,434,718 instructions). So the source changes between d1f4da0 and
  15b4ce2 (the wrapping arithmetic of ae6023c) changed the riscv code shape of the in-place NTT enough that BINSEC stalls on one
  solver query at a store of `ntt_body_mut` for these three pieces. Coverage is not reduced: the full-size riscv
  `prepare_sk_{44,65,87}` and `signing_key_{44,65,87}` are `secure` at 15b4ce2 (the reason the pieces were run is gone), and
  the 23 other riscv split pieces and both one-polynomial `prepare_sk_1x1_*` are `secure`. No leak was found.
- **AArch64 without NEON** (`aarch64.sh`, 115 probes with the two censuses, 3600 s): 99 secure, 3 expected insecure
  (`rej_bounded_poly_eta2/4`, `control_early_exit_44`), 13 unknown: the 11 of e9a1c74 (`compute_t_44`, `prepare_sk_{44,65,87}`,
  `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44`, `control_prepared_{branch,index}_44`) and the two
  split pieces that were already unknown (`split_prepare_sk_87_{7x1,col}`). Run as part of the sweep
  (not skipped), because the arithmetic of `field.rs` changed; none changed verdict. They are the solver stall of U-42 again.
  All 28 split probes ran (26 secure, 2 unknown).
- Every `secure` row of the thumbv7em, riscv32imac and AArch64 runs has 0 pending paths and all of its (nonzero) control-flow and
  memory-access checks passing (`*.verdicts.tsv`); the x86_64 rows too.

### Not rerun, and why

Per the known no-verdict list below, these were not rerun at 15b4ce2; their results are the e9a1c74 ones (about an hour each, and
the result at the same cap would not be a verdict). `field.rs` changed, so a different outcome is possible, but nothing points to one;
the x86_64 default and `dispatch` prepared censuses, which did fit in 120 GB at e9a1c74 and no longer do, show that this can go
either way.

- thumbv7em `census_sign_internal_44`, `census_sign_prepared_44`, riscv32imac `census_sign_prepared_44` and x86_64
  `nearcore-dispatch` `census_sign_prepared_44`: out of memory at the 120 GB cap at e9a1c74.
- riscv32imac `census_sign_internal_44`: 4 pending paths at 3600 s and 7200 s at e9a1c74.
- Static-AVX2 profiles `avx2` and `nearcore-avx2` (`select-ntt.sh avx2`): not part of the e9a1c74 sweep tables either.
- The nightly-versus-1.95.0 comparison of one probe and the rewrite experiments (`EXPERIMENTS=1`) stay as measured; no experiment
  was rerun.

### OOM ledger and the other runs of this sweep

Every `error` of this sweep is an out-of-memory kill: three `census_sign_prepared_44` runs, each matched to a kernel log entry
(`journalctl -k -g 'Killed process'`, checked at 18:43Z for the whole day since 08:50Z): 11:45:09Z (`default`, 110 GB cap, binsec at
115.1 GB RSS), 16:27:26Z (`default`, 120 GB cap, 125.6 GB RSS) and 17:42:09Z (`dispatch`, 120 GB cap, 125.6 GB RSS). There was no other
kill of any process on the box in that window; no probe of the 113 per profile ended `error`. Per README rule, a census killed alone at
120 GB is recorded as "needs more than 120 GB" and the cap was not raised again.

Other deviations from the README method, for reference:

- Up to ten containers ran at once in the first hours (`JOBS=8` each, 64 GB cap each, `--cpus 24` each on 60 cores), and 7200 s
  reruns used `JOBS=2`. Where contention could matter (the three riscv32imac split probes), a rerun alone gave the same result.
- `cargo-checkct`'s build pass runs every probe with `-sse-timeout 1`, which BINSEC checks only between paths: in the census containers
  it held one container for about 110 minutes on a single probe (the `nearcore-exact` census run, `split_prepare_sk_87_col` of the build pass)
  before the real run started. No verdict depends on it.
- One census container (`nearcore-exact-novec`, started while a 98 GB `default` census was running) was stopped at 36 GB RSS
  with `docker kill` to keep the box clear of a host-level OOM (a deliberate stop, not a kernel kill) and rerun later alone.
- `nearcore-exact-novec` (c63f632) is a profile added by this sweep; the nightly-versus-1.95.0 comparison under "Toolchain"
  was not repeated.

## `nearcore-exact` and `nearcore-exact-dispatch` (x86_64; November 3, 2026)

> **Superseded by the sweep at 15b4ce2 (above).** The tables below were measured at the e9a1c74-era tree, before the wrapping
> arithmetic of ae6023c: their `insecure` and overflow-guard `unknown` results no longer hold (`sk_is_well_formed` is `secure`; the
> unknowns are now VEX cuts). They stay as the 'before' of that sweep and for the method, which is unchanged.

The older `nearcore` profile approximates nearcore's release build. These two profiles take their settings from nearcore
itself (read-only clone at commit cd5a94457, 2026-11-03); the older profiles are unchanged because the historical
numbers above refer to them. `nearcore-exact-dispatch` is `nearcore-exact` plus the crate's `avx2` feature with the
dispatch cache pre-set, exactly as `nearcore-dispatch` does. x86_64 only; the other targets are not part of nearcore's
x86_64 flags and were not rerun.

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
   `vzeroupper` for copies and zeroing. The driver of the sweep contains 695 `vmovups`, 160 `vandps`, 158 `vzeroupper`,
   41 `vxorps` and about 70 other VEX instructions. The one instruction confirmed unliftable by BINSEC 0.11.3 in these runs is
   `vtestps` (cut path, "uninterpreted KO", experiment `exp_sk_wf_wrapadd_44`); no probe of the sweep (112 per profile) had a
   cut path, so either the other VEX forms are lifted or no explored path reaches them. This was not tested further.
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
not nearcore's callers, so inlining contexts differ (the `decompose` finding above shows that matters); the driver is a static,
non-PIE `no_std` binary.

### Method and what ran

All runs: `run-select.sh`, x86_64 only, `ONLY=.` minus the two censuses, one container per profile (`ct-ne`, `ct-ne2`),
64 GB cap. The README's 3600 s per probe at `JOBS=2` was not workable here: with overflow checks the NTT-family probes
stall for the whole timeout (two probes per hour per container, about two days for the sweep), so the sweep was done in stages:

1. **Stage 1:** all 112 probes, `TIMEOUT=600`, `JOBS=8` (a probe that is `secure` or `insecure` has a verdict at that point;
   an `unknown` can only get more time).
2. **Stage 2:** the 68 stage-1 `unknown`s again with `TRACE=1` (BINSEC `-sse-debug-level 3 -sse-loglevel debug`; the run keeps
   only the last executed instruction and the count) at `TIMEOUT=300`: *the instruction BINSEC stopped at*.
3. **Stage 3:** 14 representative `unknown`s whose instruction count was still rising between 300 s and 600 s, at `TIMEOUT=3600`,
   `JOBS=14`, with `TRACE=1`. Three of them finished `secure` (`vec_power2round_44`, `vec_infinity_norm`,
   `split_vec_power2round_3`); the others did not, and moved by a few thousand instructions in 3000 s.
4. The two censuses alone at 120 GB, `JOBS=1`, `TIMEOUT=3600` (below).

The unknown rows were not rerun at 7200 s. Post-processed summaries (not BINSEC's raw output), with every leak and stop address mapped to function, source line and
instruction by `checkct/unknowns.py`, are in `checkct/results/`.

### Results (x86_64, rustc 1.95.0, BINSEC 0.11.3)

112 probes per profile (84 non-split entrypoints and the 28 `split_*` probes of `split.rs`) plus the two censuses. No `error` result and no
OOM kill occurred in any run (below), so the "no verdict" column is empty; `unknown` is a path BINSEC could not finish
(timeout with one pending path), not an unliftable instruction (see the stop table).

| profile (x86_64) | secure | expected insecure | insecure, new | unknown | no verdict (OOM) |
|---|---|---|---|---|---|
| `nearcore-exact` | 38 | 3 | 6 | 67 | 0 |
| `nearcore-exact-dispatch` | 38 | 3 | 6 | 67 | 0 |

Verdicts per probe are identical in the two profiles for all 112 probes (stage 1, and stage 3 for the 14 reruns); only
the censuses are listed separately below. "Secure" means exactly what the README defines everywhere else; every secure row
here has 0 pending paths and a nonzero number of control-flow checks passed (`checkct/results/`).

- **secure (38):** `field_small_reduce`, `field_sub`, `field_neg`, `field_mul_shoup`, `field_mul_mont`, `field_mont_reduce`,
  `ct_lt_mask`, `ct_select`, `power2round`, `decompose_44`, `decompose_65_87`, `high_bits_*`, `low_bits_*`, `make_hint_*`,
  `infinity_norm`, `vec_infinity_norm` (3600 s), `keccak_f1600`, `bit_pack_{3,4,13,18,20}`, `keygen_seed_hash`,
  `sign_rho_pp_hash`, `coeff_from_half_byte_eta{2,4}`, `poly_power2round`, `vec_power2round_44` (3600 s),
  `split_vec_power2round_{1,2,3,8_q0..q3}` (`_3` at 3600 s). The standalone Decompose-family probes are `secure`, but CT-2
  showed up inside `hint_step`'s inlining context, and every `hint_step_*` is `unknown` in this build: the CT-2 context has no
  verdict under `nearcore-exact`.
- **expected insecure (3):** `rej_bounded_poly_eta2/4` (`sampling.rs:129`, `:132`, public accept pattern) and the positive
  control `control_early_exit_44` (`extra.rs:221`, 8 leaks), which must be and is `insecure`: the method sees a leak in this build.
  The other two positive controls (`control_prepared_branch_44`, `control_prepared_index_44`) are `unknown` (below), so the
  `prepare_sk` rows are uncontrolled.
- **insecure, new (6):** `sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}`: a real secret-dependent branch,
  analysis below.
- **unknown (67):** 65 probes plus the two censuses. All stop at an overflow-check guard in `field.rs`, below.

### Where the 67 `unknown`s stop

`unknown` here is always "timeout has left 1 pending path", no leak among the checks that passed, and the instruction BINSEC
was at (`TRACE=1`) is a conditional jump to the panic path: the overflow check of an arithmetic operation in `field.rs`
or `rounding.rs`, never an instruction the lifter rejects. Counts at 300 s and 600 s are equal or within a few thousand
instructions (a path that creeps: 4 to 20 instructions per second at most), and the 14 reruns at 3600 s moved on by about 2,000 to
19,000 instructions without finishing (three finished `secure`). So these rows are solver capacity on overflow-check guards;
they are not findings, and they are not proofs.

| stop site (source) | probes (count) | instruction pattern |
|---|---|---|
| `field.rs:39` `sub`: `a + Q - b` | 47: `sk_decode_*`, `sk_encode_*`, `prepare_sk_*`, `signing_key_*`, `expand_mask_*`, `vec_power2round_87`, all NTT-based `compute_t_*`, `ntt`, `ntt_vec_44`, the `split_*` pieces | `cmp $Q+k, %ecx; ja/jae panic` after the load of a decoded coefficient, or `lea Q(%rdx),%r8d; sub %esi,%r8d; jb panic` in `ntt_body_mut` (0x218f8d) |
| `field.rs:71` `mont_reduce`: `a + m * Q` (u64) | 15: `hint_step_*`, `response_*`, `matrix_vector_ntt_{1x1,65,87}`, `scalar_vector_ntt_inverse_1`, `multiply_ntt` | `imul $0x7fe001,%rdx,%rdx; add %rsi,%rdx; jb panic` |
| `field.rs:35` `add`; `:21` `small_reduce`; `:29` `barrett_reduce` | 1 each: `ntt_inverse`; `matrix_vector_ntt_44`; `barrett_reduce` (stops after 84 instructions: `cmp; sbb; jb`) | `add; jb panic`; `sub; jb panic`; `cmp %rcx,%rax; sbb %rdx,%rsi; jb panic` |
| `census_sign_*_44` | 2 | `sk_decode::<4,4>` `field.rs:39`, `ja` at 0x211ce7 (after 1,372,577 and 54,314 instructions) |

The guards are not reachable with canonical operands (`barrett_reduce` and `field::mul` are not even called by the crate:
`mul` is `#[allow(dead_code)]`, the NTT uses the Shoup/Montgomery products), so a stuck guard is BINSEC failing to prove a
nonlinear bound, not a panic path that exists. The SSE4.1 hint ("reductions may lower to different instructions") did not
materialize as unliftable instructions in the probes that finish: the only unliftable instruction reached anywhere is the
VEX `vtestps` of the experiment `exp_sk_wf_wrapadd_44` (which removes the overflow check from the original test); the
`sk_is_well_formed` loop, which was `movmskpd` in the `nearcore` profile, is scalar here (the overflow check blocks the
vectorization).

Per probe (stop = the last executed instruction; 300 s trace unless the stage column says 3600 s; the instruction before it is
the flag setter; `nearcore-exact-dispatch` stops at the same sites with other addresses, except `matrix_vector_ntt_44` (`field.rs:21` vs `:71`) and `prepare_sk_1x1_44` (`:35` vs `:39`), all overflow guards; `checkct/results/`):

| probe | stage | steps | stopped at | source | preceding instructions |
|---|---|---|---|---|---|
| `compute_t_1x1` | 300 s | 22173 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `compute_t_44` | 300 s | 188684 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `compute_t_65` | 300 s | 324310 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `compute_t_87` | 300 s | 564628 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `expand_mask_44` | 300 s | 35336 | `0x217af8` ja | src/field.rs:39 | `mov  0x36c(%rsp,%rax,4),%ecx; cmp  $0x81e001,%ecx` |
| `expand_mask_65` | 300 s | 38090 | `0x21bf7d` jae | src/field.rs:39 | `mov  0x3d8(%rsp,%rax,4),%ecx; cmp  $0x87e002,%ecx` |
| `expand_mask_87` | 300 s | 38336 | `0x21c7fb` ja | src/field.rs:39 | `mov  0x3dc(%rsp,%rax,4),%ecx; cmp  $0x87e001,%ecx` |
| `matrix_vector_ntt_1x1` | 300 s | 15679 | `0x20627b` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `matrix_vector_ntt_44` | 300 s | 160367 | `0x20646e` jb | src/field.rs:21 | `cmova %r13d,%edx; sub  %edx,%ecx` |
| `matrix_vector_ntt_65` | 300 s | 281585 | `0x20696b` jb | src/field.rs:71 | `imul  $0x7fe001,%rcx,%rcx; add  %rdx,%rcx` |
| `matrix_vector_ntt_87` | 300 s | 507450 | `0x206fcb` jb | src/field.rs:71 | `imul  $0x7fe001,%rcx,%rcx; add  %rdx,%rcx` |
| `ntt_vec_44` | 300 s | 29504 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `scalar_vector_ntt_inverse_1` | 300 s | 15666 | `0x2212f3` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `vec_power2round_87` | 3600 s | 88718 | `0x21ddea` jae | src/field.rs:39 | `mov  (%r14,%rax,4),%ecx; cmp  $0xff801fff,%ecx` |
| `control_prepared_branch_44` | 300 s | 35245 | `0x21196d` ja | src/field.rs:39 | `mov  0x404(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `control_prepared_index_44` | 300 s | 35392 | `0x21196d` ja | src/field.rs:39 | `mov  0x404(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `prepare_sk_1x1_44` | 3600 s | 44292 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `prepare_sk_1x1_65` | 300 s | 51820 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `prepare_sk_44` | 3600 s | 53874 | `0x211ce7` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `prepare_sk_65` | 3600 s | 71280 | `0x212cdd` jae | src/field.rs:39 | `mov  0x404(%rsp,%rax,4),%ecx; cmp  $0x7fe006,%ecx` |
| `prepare_sk_87` | 300 s | 61750 | `0x213e6a` jae | src/field.rs:39 | `mov  0x24(%rsp,%rax,4),%ecx; cmp  $0x7fe004,%ecx` |
| `signing_key_44` | 300 s | 35297 | `0x211997` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `signing_key_65` | 300 s | 52139 | `0x2129a8` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe005,%ecx` |
| `signing_key_87` | 300 s | 61763 | `0x213e94` ja | src/field.rs:39 | `mov  0x28(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `barrett_reduce` | 300 s | 84 | `0x232083` jb | src/field.rs:29 | `cmp  %rcx,%rax; sbb  %rdx,%rsi` |
| `multiply_ntt` | 300 s | 14787 | `0x22e97f` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `ntt` | 300 s | 7269 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `ntt_inverse` | 300 s | 11386 | `0x218365` jb | src/field.rs:35 | `mov  %r8d,%r9d; add  %edi,%r9d` |
| `sk_decode_44` | 3600 s | 53751 | `0x211cbd` ja | src/field.rs:39 | `mov  0x404(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `sk_decode_65` | 3600 s | 64745 | `0x212d07` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe005,%ecx` |
| `sk_decode_87` | 3600 s | 69556 | `0x213e94` ja | src/field.rs:39 | `mov  0x28(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `sk_encode_44` | 3600 s | 118458 | `0x2146cb` jae | src/field.rs:39 | `mov  -0x4(%r15,%rax,4),%ecx; cmp  $0x7fe004,%ecx` |
| `sk_encode_65` | 3600 s | 157439 | `0x23028d` ja | src/field.rs:39 | `mov  0x4ec8(%rsp,%rax,4),%ecx; cmp  $0x7fe005,%ecx` |
| `sk_encode_87` | 3600 s | 199045 | `0x231b86` ja | src/field.rs:39 | `mov  (%r12,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `hint_step_1_44` | 300 s | 23084 | `0x216c63` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `hint_step_1_65` | 300 s | 23084 | `0x216c63` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `hint_step_44` | 300 s | 67367 | `0x20719b` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `hint_step_65` | 300 s | 96974 | `0x2074fb` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `hint_step_87` | 300 s | 126894 | `0x235a4c` jb | src/field.rs:71 | `imul  $0x7fe001,%rcx,%rcx; add  %rdx,%rcx` |
| `response_1x1_44` | 300 s | 37515 | `0x216483` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `response_1x1_65` | 300 s | 37515 | `0x216483` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `response_44` | 300 s | 125997 | `0x20719b` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `response_65` | 300 s | 170150 | `0x2334d0` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `response_87` | 300 s | 229274 | `0x23413e` jb | src/field.rs:71 | `imul  $0x7fe001,%rdx,%rdx; add  %rsi,%rdx` |
| `split_compute_t_44_2x2` | 300 s | 61763 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_compute_t_44_col` | 300 s | 69067 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_compute_t_44_row` | 300 s | 68919 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_ntt_vec_into_1` | 300 s | 7269 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_ntt_vec_into_7` | 300 s | 51537 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_ntt_vec_into_8` | 300 s | 58883 | `0x218f8d` jb | src/field.rs:39 | `lea  0x7fe001(%rdx),%r8d; sub  %esi,%r8d` |
| `split_prepare_sk_44_col` | 300 s | 37311 | `0x2088fd` jae | src/field.rs:39 | `mov  0x444(%rsp,%rax,4),%ecx; cmp  $0x7fe004,%ecx` |
| `split_prepare_sk_44_row` | 3600 s | 59845 | `0x2241bd` jae | src/field.rs:39 | `mov  0x504(%rsp,%rax,4),%ecx; cmp  $0x7ff002,%ecx` |
| `split_prepare_sk_65_col` | 300 s | 110307 | `0x20a42a` ja | src/field.rs:39 | `mov  0x458(%rsp,%rax,4),%ecx; cmp  $0x7ff001,%ecx` |
| `split_prepare_sk_65_row` | 300 s | 45791 | `0x224d2a` ja | src/field.rs:39 | `mov  0x508(%rsp,%rax,4),%ecx; cmp  $0x7fe005,%ecx` |
| `split_prepare_sk_87_2x1` | 300 s | 49979 | `0x225c6d` ja | src/field.rs:39 | `mov  0x514(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `split_prepare_sk_87_4x1` | 300 s | 51850 | `0x2088fd` jae | src/field.rs:39 | `mov  0x444(%rsp,%rax,4),%ecx; cmp  $0x7fe004,%ecx` |
| `split_prepare_sk_87_6x1` | 300 s | 113992 | `0x20a42a` ja | src/field.rs:39 | `mov  0x458(%rsp,%rax,4),%ecx; cmp  $0x7ff001,%ecx` |
| `split_prepare_sk_87_7x1` | 300 s | 53757 | `0x226cea` ja | src/field.rs:39 | `mov  0x518(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `split_prepare_sk_87_col` | 300 s | 54774 | `0x227f0d` jae | src/field.rs:39 | `mov  0x504(%rsp,%rax,4),%ecx; cmp  $0x7fe004,%ecx` |
| `split_prepare_sk_87_row` | 300 s | 51143 | `0x228d1a` ja | src/field.rs:39 | `mov  0x508(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `split_vec_power2round_5` | 300 s | 48548 | `0x22a78d` ja | src/field.rs:39 | `mov  0x5008(%rsp,%r13,4),%eax; cmp  $0xff801ffe,%eax` |
| `split_vec_power2round_6` | 300 s | 56709 | `0x22ad1a` jae | src/field.rs:39 | `mov  (%r14,%rax,4),%ecx; cmp  $0xff801fff,%ecx` |
| `split_vec_power2round_7` | 300 s | 64275 | `0x22af9a` jae | src/field.rs:39 | `mov  (%r14,%rax,4),%ecx; cmp  $0xff801fff,%ecx` |
| `split_vec_power2round_8_hi` | 300 s | 71700 | `0x22b2fd` ja | src/field.rs:39 | `mov  0x8408(%rsp,%r13,4),%eax; cmp  $0xff801ffe,%eax` |
| `split_vec_power2round_8_lo` | 300 s | 71577 | `0x22b85d` ja | src/field.rs:39 | `mov  0x7408(%rsp,%r15,4),%eax; cmp  $0xff801ffe,%eax` |
| `census_sign_internal_44` | 3600 s | 1372577 | `0x211ce7` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |
| `census_sign_prepared_44` | 3600 s | 54314 | `0x211ce7` ja | src/field.rs:39 | `mov  0x408(%rsp,%rax,4),%ecx; cmp  $0x7fe003,%ecx` |

### The six new `insecure` rows: `sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}`

Not in the expected list, so analyzed, not labeled. Every one reports exactly two control-flow leaks, both `jb` at
`src/encode.rs:169` in `poly_in_eta` (for example 44: 0x20fa25 and 0x20fa49), found within 25 s; BINSEC then keeps
exploring the 2^n paths (257 pending at the timeout; the verdict is "insecure", the leak list is not exhaustive).

    encode.rs:169   if w[i] > eta && w[i] + eta < Q { ok = false }
    20fa1e: mov    0x14(%rsp,%rax,4),%ecx
    20fa22: cmp    $0x3,%ecx                  ; w > eta ?
    20fa25: jb     20fa42                     ; <- leak: skip the rest when w <= eta
    20fa27: cmp    $0xfffffffd,%ecx           ; w + eta overflows u32 ?
    20fa2a: ja     panic                      ; the overflow check: not reported (its condition is false for every secret value)
    20fa30: add    $0xff802001,%ecx           ; w + eta - Q ...
    20fa36: cmp    $0xff801fff,%ecx
    20fa3c: setb   %cl
    20fa3f: and    %cl,%r13b

- It is **not** the overflow-check branch. The `ja panic` at 0x20fa2a is not flagged (its condition is the same for all secrets). The flagged branch is the `&&`: with
  `overflow-checks = true` the right operand `w[i] + eta` can panic, so LLVM may not evaluate it speculatively and must keep
  the short-circuit as a branch on `w > eta`. Without the check the same source is if-converted (`nearcore-novec`: `secure`;
  checkct profile: `secure`) or vectorized (`nearcore`: `unknown`, SSE2 `movmskpd`; here with AVX: `unknown` at the VEX
  instruction `vtestps`, probe `exp_sk_wf_wrapadd_44` below, which is the original with `wrapping_add`).
- **Verdict: (b), a real secret-dependent branch in nearcore's build, not a probe artifact.** For a well-formed key
  `w[i] > eta` is true exactly when the coefficient is negative (`w` is `Q-1` or `Q-2` for `eta = 2`), so the branch leaks the
  sign of every coefficient of s1 and s2. The probe domain (arbitrary secret bytes) is a superset of the real one, but the leak
  does not need the extra values: the isolated test on a secret polynomial with canonical coefficients (`exp_poly_orig`,
  domain `[0, Q)`, which `unpack_signed` always produces by the range fact of `field::sub`) leaks in 0.07 s, and no extra
  constraint is missing, since the branch outcome already differs between two valid keys. The overflow cannot occur in the real
  domain (`w < Q`); that is why the guard is not flagged, and why it cannot be assumed away: it is the guard's side effect that
  forces the branch.
- Scope: `sk_is_well_formed_NN` is the optional key check (not called by Sign; its doc comment already says it branches on the
  sign of each coefficient and is to be run "where timing is not observable"). The finding is about nearcore's build of that
  function, in the probe's inlining context (the crate in isolation, not nearcore's callers). Sign, KeyGen and Verify do not call
  it, but `api::pk_from_sk_NN` does (`src/keygen.rs`, first step), so the leak is reachable through it; `pk_from_sk_*` has no
  probe of its own. The doc comment of `api::sk_is_well_formed_NN` says "Not covered by the constant-time checks"; with the older profiles the
  object code happened to be branch-free, with nearcore's it is not.

### Rewrites tested (throwaway probes, `driver/src/experiments.rs`, `EXPERIMENTS=1`; `src/` and `lean/` untouched)

Copies of `poly_in_eta` / `sk_is_well_formed` with only the range test changed. `nearcore-exact`, rustc 1.95.0, 900 s
(blocks 600 s). `K+L` is the number of η-blocks. "secure" has 0 pending paths.

| probe | change | verdict |
|---|---|---|
| `exp_sk_wf_crate_44`, `exp_sk_wf_orig_44`, `exp_sk_wf_orig_1x1_44`, `exp_blk_orig_eta{2,4}`, `exp_poly_orig` | the original, through the crate / a verbatim copy / one block / the polynomial test alone | **insecure** in all of them (two `jb` at the `&&`; copy at `experiments.rs:51`), so the copy is faithful |
| `exp_blk_wrapadd_eta2`, `exp_sk_wf_wrapadd_44` | original with `w.wrapping_add(eta)` (no overflow check in the test) | unknown at once: vectorized with VEX, cut at `vtestps %xmm6,%xmm0` (0x21b968 / 0x219df8, `experiments.rs:64`). Removing the overflow check alone does not lift it |
| `exp_blk_bitand_eta2`, `exp_poly_bitand` | `ok &= !((w > eta) & (w.wrapping_add(eta) < Q))` | **secure** (one block 7,724 instructions, 1,527 control-flow checks) |
| `exp_blk_mask_eta{2,4}`, `exp_poly_mask`, `exp_sk_wf_mask_1x1_44` | integer accumulation: `bad \|= (eta.wrapping_sub(x) >> 31) & (x.wrapping_sub(Q - eta) >> 31)`, one `bad == 0` at the end (also across blocks) | **secure** (1x1: 29,105 instructions, 7,998 control-flow checks) |
| `exp_blk_maskbb_eta{2,4}`, `exp_poly_maskbb`, `exp_sk_wf_maskbb_1x1_44` | same with `black_box` on each element mask | **secure** (1x1: 33,852 instructions, 8,478 checks) |
| `exp_sk_wf_bitand_44`, `exp_sk_wf_mask{,bb}_{44,65,87}`, `exp_sk_wf_mask{,bb}_2x2_44` | the same at full size and with 4 blocks | unknown: one pending path stuck at the overflow-check guard of `field::sub` inside `unpack_signed` (`field.rs:39`, `ja`/`jae`, 0x2070dd for 2x2), the same stall as `sk_decode_*`; not the range test |
| `exp_sk_wf_maskw_{2x2_44,44,65,87}` | the mask test **and** the unpack stage (`bit_unpack`, `field::sub`, `small_reduce`) in `wrapping_*` arithmetic | **secure** at full size: 34,177 (2x2) / 52,773 / 78,838 / 99,470 instructions, 12,706 / 18,907 / 24,019 control-flow checks, 0 pending paths |

So the integer-mask range test is branch-free and liftable under `nearcore-exact`, and the full-size verdict also needs the
unpack stage without overflow-check guards (wrapping arithmetic there, or whatever makes BINSEC's guard queries cheap). The
`black_box` variant is not needed for the one-block verdicts. The mask test relies on `w < 2^31`, which holds because `w` is
`field::sub(eta, z)`, canonical. Scope of the recommendation: (i) the integer-mask range test is a change to `encode.rs`
(`poly_in_eta`) only, and is what removes the branch; (ii) the *full-size* verdicts additionally needed the unpack stage in
`wrapping_*` arithmetic (`exp_sk_wf_maskw_*`), which is the same kind of change in `field::sub`, `field::small_reduce` and
`encode::bit_unpack`: crate-wide code that Lean extracts, where Aeneas models checked and wrapping operations differently, so
it would need re-extraction and re-proof. `maskw` shows what lifts the verdict, not a local fix. Not tested: any source change
to `field.rs`/`ntt.rs` for the other 65 unknowns.

### Censuses and the OOM ledger

| run | container cap | result |
|---|---|---|
| `nearcore-exact` `census_sign_internal_44` | 120 GB, `JOBS=1`, 3600 s | `unknown`: 1 pending path after 1,372,577 instructions (167,830 control-flow and 427,006 memory-access checks passed, no leak), stuck at `sk_decode` `field.rs:39`; resident memory was 1.2 to 1.9 GB at the two samples taken. No `sampling.rs:35` leak was reached (the earlier profiles found it first), so this census says nothing about it |
| `nearcore-exact` `census_sign_prepared_44` | 120 GB, `JOBS=1`, 3600 s | `unknown`: 1 pending path after 54,314 instructions, stuck at the same instruction (0x211ce7), no leak |
| `nearcore-exact-dispatch` `census_sign_internal_44` | 120 GB, `JOBS=1`, 3600 s | `unknown`: 1 pending path after 1,371,009 instructions (167,983 control-flow and 427,222 memory-access checks passed, no leak), stuck at the same `sk_decode` guard (`field.rs:39`, 0x21177d) |
| `nearcore-exact-dispatch` `census_sign_prepared_44` | 120 GB, `JOBS=1`, 3600 s | `unknown`: 1 pending path after 54,809 instructions (15,182 control-flow and 18,080 memory-access checks passed, no leak), same stop |

OOM ledger: none of the runs of this section was killed. The kernel log (`journalctl -k -g 'Killed process'`, checked after the stage-1 sweeps (last 12 hours) and again after
the last census (last 6 hours, which covers the four census runs)) shows only kills of `lean` processes of other jobs on the box; no
`binsec` kill. Every result of the sweep is `secure`, `insecure` or `unknown`; no `error`. The censuses were not
restricted to `JOBS=1` in stage 1/2 because they were excluded from them (`EXCLUDE`); the old "needs more than 120 GB" rows do
not carry over to this build: the overflow-check stall ends the census long before memory matters.

### What this does and does not show

- `nearcore-exact` is a better approximation of nearcore's x86_64 release build than `nearcore`, not the binary: the crate is
  probed in isolation (inlining context), `core` is built from source (above), `memcpy` is `compiler_builtins`', and the
  allocator, `std` and nearcore's callers are absent.
- One class of result: 38 secure, 6 findings that are real in this build (`sk_is_well_formed`), 3 expected, 67 without a
  verdict. Everything that sits on the NTT, on `sk_decode`/`sk_encode`, on the Sign steps (`response`, `hint_step`) and on
  ExpandMask has **no verdict under `nearcore-exact`**: with `overflow-checks = true` BINSEC does not finish them (they were
  `secure` in the checkct profile, and `secure` for `response`/`hint_step` in `nearcore`). That is a loss of evidence for the
  nearcore build, not a leak. Whether the checks leave a secret-dependent branch in those paths is exactly what BINSEC could
  not decide there; the 6 `sk_is_well_formed` rows show that overflow checks can introduce one.
- The panic paths themselves are not analyzed: a reachable panic is outside this tool's questions (abort on a malformed
  input is a robustness property, covered by the Lean panic-freedom statements in STATUS.md, not here).

## Known no-verdict probes (skip unless something changed)

These probes are already known to end with no verdict. Don't rerun them unless one of these changed: the code
under test (`src/` or the probe), the per-probe timeout, the memory cap, or how the probe is split. A rerun that
changes nothing costs hours and gives the same result (about 1.6 h went to such reruns on 2026-11-01). Each entry
says what was tried. When an entry gets a verdict, move it out of this list.

| probe | target / profile | outcome | already tried |
|---|---|---|---|
| `vec_power2round_87` (full size) | riscv32imac default | unknown, 1 pending path | 1 h and 2 h at e9a1c74, 1 h at 15b4ce2 (190,098 instructions, still 1 pending path). Covered by the split windows `split_vec_power2round_8_*` (secure) |
| `split_vec_power2round_{5,6,7}` | riscv32imac | unknown | 1 h, again 1 h at 15b4ce2 (capacity probing only; the 8-wide windows cover the loop) |
| `census_sign_internal_44` | riscv32imac default | unknown, 4 pending paths | 1 h and 2 h at e9a1c74 |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44` | AArch64 `NONEON=1` | unknown: one pending path stuck in one solver query (instruction count identical at 300, 600, 3600 and 7200 s; upstream log U-42) | 1 h and 2 h at e9a1c74, 1 h again at 15b4ce2 (same probes, `control_prepared_*` too). Pieces covered by split probes, except the K = 8 glue of `prepare_sk_87` / `signing_key_87` |
| `split_prepare_sk_87_7x1`, `split_prepare_sk_87_8x1` | AArch64 `NONEON=1` | unknown, same stall | 1 h (round 2 of `split-run.sh`), again 1 h at 15b4ce2 (`split_prepare_sk_87_col` is the `_8x1` probe) |
| `census_sign_internal_44`, `census_sign_prepared_44` | thumbv7em default | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps (ISSUES T-8). Don't raise the cap again; a split would be needed |
| `census_sign_prepared_44` | riscv32imac default; x86_64 `nearcore-dispatch`; x86_64 default and `dispatch` (since 15b4ce2) | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps; x86_64 default also at 110 GB, `dispatch` at 120 GB (15b4ce2, killed at 125.6 GB RSS). It was `insecure` at e9a1c74 for default and `dispatch` after a 120 GB run |
| `control_prepared_branch_44` | thumbv7em | `secure`: the control is invalid there (branch lowered to a select) | every run; expected |
| `control_prepared_branch_44`, `control_prepared_index_44` | AArch64 `NONEON=1` | no verdict | 1 h and 2 h |
| 49 probes: `ntt`, `ntt_inverse`, `multiply_ntt`, `ntt_vec_44`, `compute_t_*`, `matrix_vector_ntt_*`, `scalar_vector_ntt_inverse_1`, `prepare_sk_*`, `signing_key_*`, `prepare_sk_1x1_*`, `control_prepared_*`, `hint_step_*`, `response_*`, 16 `split_*` (list in "`nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2") | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: 48 are cut paths at VEX instructions BINSEC 0.11.3 cannot lift (`vinsertps`, `vblendvps`, `vblendps ymm`), 0 pending paths, stopped in 0.08 to 1.7 s; `prepare_sk_1x1_65` is a solver stall (1 pending path) | 600 s for all, 3600 s with `TRACE=1` for `prepare_sk_1x1_65`. A longer timeout cannot help a cut path. What helps: a build without the vectorizers (`PROFILE=nearcore-exact-novec`: all 49 `secure`) or a BINSEC that lifts VEX (U-44) |
| `census_sign_internal_44`, `census_sign_prepared_44` | x86_64 `nearcore-exact`, `nearcore-exact-dispatch` | unknown: cut at `vinsertps` (`ntt.rs:111`) after 726,927 / 85,683 instructions | 110 GB, `JOBS=1`, 3600 s at 15b4ce2 (cut within 2 s). `nearcore-exact-novec` has a result: `insecure`, only the public `sampling.rs:35` leak |
| `split_prepare_sk_65_col`, `split_prepare_sk_65_row`, `split_prepare_sk_87_6x1` | riscv32imac default | unknown, 1 pending path, stuck at `0x045e28 sw s1,0(a7)` in `ntt_body_mut` (new at 15b4ce2; `secure` at d1f4da0) | 3600 s (sweep), 7200 s alone with `JOBS=2`, 600 s with `TRACE=1`: the same instruction counts every time. Covered by the full-size `prepare_sk_*` / `signing_key_*` rows, which are `secure` |

## Probes (87 entrypoints x 3 targets: riscv32imac-unknown-none-elf, thumbv7em-none-eabihf, x86_64-unknown-linux-gnu)

Already present before this round (40, `probes.rs` and `signing.rs`):

- field/mask: `field_small_reduce`, `barrett_reduce`, `field_add`, `field_sub`, `field_neg`, `field_mul`,
  `ct_lt_mask`, `ct_select` (mask taken from a secret bit); `field_mul_shoup`, `field_mul_mont` and `field_mont_reduce`
  (the Shoup/Montgomery products, added with the NTT rewrite; three probes, so the total is 87 with `field_add` merged
  into `field_small_reduce` in the binary).
- rounding: `power2round`, `decompose`/`high_bits`/`low_bits`/`make_hint` (`_44` for gamma2 = (q-1)/88 and
  `_65_87` for (q-1)/32), `infinity_norm`, `vec_infinity_norm` (4 polynomials).
- `ntt`, `ntt_inverse`, `multiply_ntt` on secret polynomials; `keccak_f1600` with a secret state.
- encode: `bit_pack_{3,4,13,18,20}` (inputs masked to c bits), `sk_encode_{44,65,87}` (secret key, s1, s2, t0;
  public rho and tr), `sk_decode_{44,65,87}` on a secret sk.
- `signing.rs`: `response_{44,65,87}` (z = y + cs1, cs2, r0 = LowBits(w - cs2), both vector norms) and
  `hint_step_{44,65,87}` (ct0, MakeHint(-ct0, w - cs2 + ct0), hamming weight, ct0 norm). c-hat is public.
  These call the production `sign::response` and `sign::hint_step`; the norms are taken on the returned vectors, as
  `attempt` does before its rejection `if`s.

Added in this round (34; `extra.rs`, plus four in `signing.rs`):

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

Earlier results at 2668aa9 plus the probes, superseded by the full sweep at e9a1c74 below (BINSEC 0.11.3, checkct
profile, 3000 s per probe unless noted; targets run one at a time, containers capped at 64 GB):

| probe | x86_64 | thumbv7em | riscv32imac |
|---|---|---|---|
| `prepare_sk_44` / `65` / `87` | secure / secure / secure | secure / secure / secure | unknown / secure / unknown |
| `signing_key_44` / `65` / `87` | secure / secure / secure | secure / secure / secure | unknown / secure / unknown |
| `prepare_sk_1x1_44` / `65` | not run | not run | secure / secure |
| `census_sign_prepared_44` | insecure (see below) | error (see below) | not run |
| `control_prepared_branch_44` | insecure | secure (invalid control, see below) | insecure |
| `control_prepared_index_44` | insecure | insecure | insecure |

- Full-size secure verdicts are not vacuous: 0 pending paths, and for example `prepare_sk_87` on x86_64 visits 3,166,803
  instructions with 207,975 control-flow and 1,038,098 memory-access checks passing; all of them pass in every secure row.
- riscv32imac `prepare_sk_44`/`87` (and `signing_key_44`/`87`, identical numbers) are `unknown`: BINSEC stops with one
  pending path after 457,732 / 641,714 instructions, with no leak found (51,988 / 90,633 control-flow checks, all
  passing), at the 3000 s timeout. This is the solver-capacity pattern seen for `vec_power2round_*` on this target, not a
  finding. The eta = 4 set (`65`) finishes and is secure, and the one-polynomial splits for both eta sets are secure.
- `control_prepared_branch_44` is `secure` on thumbv7em because the compiler turns `if bit {1} else {2}` into a
  conditional select; it is a valid control only where it reports `insecure` (x86_64, riscv32imac). The index control
  cannot be compiled away and is `insecure` on all three targets (memory-access leak), so these probes can see a leak
  in this context.
- `census_sign_prepared_44`: x86_64 `insecure`, first leak `src/sampling.rs:35` (`sample_in_ball`'s accept test, a
  public-outcome branch) at 0x22b638, then one pending path and no verdict; the only leak reported. thumbv7em `error`
  (no `Program status` line): first leak at 0x043db2, again `src/sampling.rs:35`, after 51 s. **Correction
  (2026-10-31): this `error` is an out-of-memory kill.** The rerun with the container cap raised to 120 GB was killed at
  that cap (kernel log: binsec at 125 GB RSS, 16:38:25Z), so it has no verdict; an earlier version of this note said
  the opposite (ISSUES.md T-8). The `census_sign_internal_44` `error` results above are presumed OOM for the same
  reason (binsec kills fall in those runs' windows).
  A census cannot prove anything, as before; the secret halves of an attempt are covered by `response_*` and
  `hint_step_*`. riscv32imac census not run (the unprepared census was `unknown` there).

Run with `rx submit pk-ct -- bash checkct/run-prepared.sh '<regex>' '<targets>' <timeout> [<memory>]` or
`checkct/prepared-leaks.sh` (same arguments; also maps leak addresses to source lines).

Expected-insecure probes. `rej_bounded_poly_eta{2,4}` leak by design: the loop branches on whether a sampled
nibble is accepted, and which positions are rejected is public (it only changes how many XOF bytes are consumed).
`census_sign_internal_44` finds the same kind of branch (a rejection sampler) first. These are not constant-time
bugs; they show what BINSEC cannot distinguish (secret data versus public outcome of a secret-derived value), which
is why the proof of "no secret-dependent branch" is done per step.

## Full sweep at e9a1c74 (October 31 to November 1, 2026)

Superseded by the sweep at 15b4ce2 (above); the counts below are its 'before' column. Every probe of `checkct/driver` (87 distinct entrypoints per target; `field_add` is merged with
`field_small_reduce` in the binary) on the tree at e9a1c74 (lane-wise SHAKE sponge, Shoup/Montgomery NTT, prepared keys
with in-place construction, sponge wipes under `zeroize`), `nightly-2026-10-06`, BINSEC 0.11.3. Everything measured
before this section is on an older tree and is kept below only as history (each table is labeled). Method: the full runs
used `run-select.sh` with `ONLY=.` and `TIMEOUT=3600` (instead of `run.sh`: it streams a line per probe and keeps the check
counts of every probe; every `secure` row of the x86_64, thumbv7em and riscv32imac runs was checked to have 0 pending
paths and a non-zero number of control-flow checks passed), containers capped at 64 GB, parallel probes
sharing that cap (`JOBS` 16 for the default, `nearcore` and `dispatch` runs, 8 for `nearcore-dispatch` and AArch64; the
censuses and the `nearcore` and `nearcore-dispatch` `control_early_exit_44` were killed in those runs, and all reruns used
`JOBS` 4 or less). `unknown` rows were rerun once with `TIMEOUT=7200`; `error` rows were classified from the kernel log
(below) and rerun alone (`JOBS=1`, 64 GB, then 120 GB). Positions of the leaks were mapped with `leaks.sh` (the AArch64
leak lists are the expected ones and were not mapped, `leaks.sh` has no AArch64 case).

Result classes: `secure`; `expected insecure` (the README-documented ones: `rej_bounded_poly_eta{2,4}`, the two
censuses, the positive controls, and on riscv32imac the standalone `ct_lt_mask`, see "Older tree: 74 probes" below); `unexpected
insecure` (a finding); `unknown` (no verdict, no leak found); `oom` (BINSEC killed at the container's memory cap, no
verdict; see ISSUES.md T-8).

| target / profile | secure | expected insecure | unexpected insecure | unknown | oom |
|---|---|---|---|---|---|
| x86_64, default | 80 | 7 | 0 | 0 | 0 |
| x86_64, `nearcore` | 74 | 7 | 0 | 6 | 0 |
| x86_64, `dispatch` | 80 | 7 | 0 | 0 | 0 |
| x86_64, `nearcore-dispatch` | 74 | 6 | 0 | 6 | 1 |
| thumbv7em, default | 81 | 4 | 0 | 0 | 2 |
| riscv32imac, default | 78 | 6 | 0 | 2 | 1 |
| AArch64 `NONEON=1` | 73 | 3 | 0 | 11 | 0 |

No unexpected insecure result on any target or profile: there is no new constant-time finding in this sweep.

Every non-secure probe:

| probe | where | result | reason |
|---|---|---|---|
| `rej_bounded_poly_eta2/4` | all 9 target/profile rows | insecure, expected | sampler accept test, a public outcome (`sampling.rs:129`, `:132`) |
| `census_sign_internal_44`, `census_sign_prepared_44` | x86_64 in the four older profiles (`unknown` under `nearcore-exact*`, stopped at `field.rs:39` before `sampling.rs:35`) | insecure, expected | only leak reported: `sampling.rs:35`, `sample_in_ball`'s accept test (public outcome); then one pending path, no verdict. Needed the 120 GB container, see below. Exception: `census_sign_prepared_44` under `nearcore-dispatch` is `oom` |
| `census_sign_internal_44`, `census_sign_prepared_44` | thumbv7em | oom: needs more than 120 GB | leak at `sampling.rs:35` found first (36 to 61 s), then killed at the cap (RSS 125 GB at the 120 GB cap), no verdict |
| `census_sign_prepared_44` | riscv32imac | oom: needs more than 120 GB | as thumbv7em; first leak `sampling.rs:35` |
| `census_sign_internal_44` | riscv32imac | unknown | 4 pending paths at 3600 s and at 7200 s, no leak found (62,925 control-flow checks passed) |
| `vec_power2round_87` | riscv32imac | unknown | 1 pending path at 3600 s and 7200 s, no leak found (solver capacity, as before) |
| `ct_lt_mask` | riscv32imac | insecure, documented | `field.rs:107` branch of the standalone probe (inputs known to be below 2^63; in-crate callers are secure), as in "Older tree: 74 probes" |
| `sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}` | x86_64 `nearcore`, `nearcore-dispatch` | unknown | within 0.1 s, same at 7200 s: BINSEC cuts the path at an instruction it cannot lift ("uninterpreted KO"), the SSE2 vectorization of the range-check loop (see "nearcore-like release profile" below). 0 pending paths, no leak; `PROFILE=nearcore-novec` is the profile that checks them |
| `compute_t_44` | AArch64 | unknown | 1 pending path (stuck in one solver query: the same 210,835 instructions at 300 s, 3600 s and 7200 s), no leak found |
| `census_sign_internal_44` | AArch64 | unknown | 1 pending path, same pattern (1,302,356 instructions), no leak found |
| `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `census_sign_prepared_44` | AArch64 | unknown | 1 pending path each (the same instruction counts at 3600 s and 7200 s, and at 600 s for `prepare_sk_44` and `control_prepared_branch_44`), no leak found; the one-polynomial splits `prepare_sk_1x1_{44,65}` are secure |
| `control_prepared_branch_44`, `control_prepared_index_44` | AArch64 | unknown | built on `prepare_sk_44`, which does not finish (above), so the controls give no verdict either: the AArch64 `prepare_sk` rows are uncontrolled |
| `control_prepared_branch_44` | thumbv7em | secure: invalid control | the compiler turns `if bit {1} else {2}` into a conditional select (as before) |

Positive controls (`control_early_exit_44`, `control_prepared_branch_44`, `control_prepared_index_44`): `insecure`, as
they must be, on x86_64 in all four profiles (`control_early_exit_44` at `extra.rs:221`, the prepared branch at
`prepared.rs:76`, the prepared index at `prepared.rs:96`), on riscv32imac (`control_prepared_branch_44` was `unknown` at
3600 s and `insecure` in the 7200 s rerun, a leak at 0x01d700 in under a second, so the BINSEC result for that probe
depends on exploration order) and for `control_early_exit_44` and `control_prepared_index_44` on thumbv7em and AArch64.
Invalid: `control_prepared_branch_44` on thumbv7em (secure, above); the two prepared controls on AArch64 (no verdict).

Notes per profile:

- x86_64 default: the CT-2 probes are all secure (`hint_step_*`, `response_*`, `decompose`-family), as are the new
  `prepare_sk_*`, `signing_key_*` and `compute_t_*`; `hint_step_{44,87,1_44,1_65}` finish where they
  were `unknown` at 069b439.
- riscv32imac default: `response_*`, `hint_step_*`, `prepare_sk_{44,87}`, `signing_key_{44,87}` and the full-size
  `compute_t_*` all finish `secure` in this sweep (all earlier `unknown` on this target).
- `nearcore` (opt-level 3, fat LTO, one codegen unit): `hint_step_*`, `response_*`, `decompose_*`, `high_bits_*` and
  `make_hint_*` secure; the six `unknown` rows are the vectorization artifact above.
- `dispatch`, `nearcore-dispatch` (crate feature `avx2`, cache pre-set to 1 in every script, which the log confirms per
  probe: `AVX2 cache 0x... pre-set to 1`): every NTT-reaching probe, every field probe and every signing-step probe gives
  the same verdict as the profile without dispatch. `scan-avx2.sh` on both drivers finds four `*_avx2` functions
  (`ntt_avx2`, `ntt_inverse_avx2`, `ntt_in_place_avx2`, `multiply_ntt_avx2`); conditional jumps are loop back-edges only,
  no `div`/`idiv`/gather/scatter; the only indirect calls are through two `.got` slots (the by-value array copies).
- AArch64 (`NONEON=1`; `aarch64-inner.sh` now includes the `prepared` module, which it silently skipped before): all
  non-prepared probes are secure except `compute_t_44` and `census_sign_internal_44`; `compute_t_65/87` are secure.

### Out-of-memory kills (all `error` results of this sweep)

Every `error` was matched against the kernel log (`journalctl -k -g 'Killed process'`) by run window; the job logs carry
no per-probe timestamps, so a kill is assigned to a probe by the run, the number of kills and the absence of any other
`error` in that run. All of them are OOM kills; none is a tool error. Times are UTC, November 1 unless noted.

| run (container cap, parallel probes) | kills (UTC) | probes with `error` | what happened next |
|---|---|---|---|
| default, 3 targets (64 GB, 16) | Oct 31 19:00:50 (2), 19:02:14 (3); RSS 7 to 20 GB each | `census_sign_internal_44` x86_64 and thumbv7em; `census_sign_prepared_44` x86_64, thumbv7em, riscv32imac | x86_64 reruns: below; thumbv7em and riscv32imac: below |
| `nearcore` (64 GB, 16) | Oct 31 20:03:57 (3), RSS 2 to 32 GB | both x86_64 censuses, `control_early_exit_44` | control alone (64 GB): insecure; censuses (120 GB): insecure, `sampling.rs:35` |
| `dispatch` (64 GB, 16) | Oct 31 21:04:45 (2), RSS 29 and 33 GB | both x86_64 censuses | 120 GB: insecure, `sampling.rs:35` |
| `nearcore-dispatch` (64 GB, 8) | Oct 31 22:05:53 (3) | both censuses, `control_early_exit_44` | control alone (64 GB): insecure; `census_sign_internal_44` (120 GB): insecure; `census_sign_prepared_44` (120 GB): killed again, 07:11:52 |
| rerun, x86_64 default `census_sign_internal_44` alone (64 GB, 1) | Oct 31 22:08:47, RSS 67 GB | the census itself | the census needs more than 64 GB even alone; the 120 GB reruns of both x86_64 default censuses are `insecure` |
| rerun at 120 GB, 1 probe at a time | 02:48:12 riscv32imac `census_sign_prepared_44`; 03:00:31 thumbv7em `census_sign_internal_44`; 03:12:44 thumbv7em `census_sign_prepared_44`; 07:11:52 x86_64 `nearcore-dispatch` `census_sign_prepared_44` | those four | killed at the cap (RSS 125 GB or more): **needs more than 120 GB, no verdict** |

The AArch64 runs had no OOM kills. The census probes that finish at 120 GB end `insecure` with one pending path (the
public `sampling.rs:35` leak is the only one reported); a census cannot prove anything. For a verdict on the four
probes that do not fit in 120 GB, a split (the rejection loop of `sample_in_ball` cut out of the probed region) would
be needed; none was run.

## Split probes (`driver/src/split.rs`, `split-run.sh`; November 1, 2026)

The full sweep above left a few probes without a verdict: BINSEC stops with one pending path stuck in one solver query
(the same instruction count at 3600 s and 7200 s), no leak found. These probes cover the same code in smaller
pieces, so that every piece has a completed verdict. All of them are in `driver/src/split.rs` (the existing probes are
untouched; `main.rs` gains `mod split;` and `aarch64-inner.sh` learns the new module name). Run with
`rx submit sp-ct -- 'set -o pipefail; bash checkct/split-run.sh 2>&1 | tee split.log'`: it starts the AArch64
container (`NONEON=1`, `aarch64.sh`) and the riscv32imac container (`run-select.sh`) side by side, each with 2
BINSEC jobs, 3600 s per probe, and exits nonzero if either fails. The tree is `src/` at the commit that adds
this section; the toolchain and BINSEC are those of the sweep. A probe name starts with `split_`.

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
| `prepare_sk_44`, `prepare_sk_87`, `signing_key_44`, `signing_key_87` | riscv32imac (`unknown` at 2668aa9, `secure` since e9a1c74) | `split_prepare_sk_{44,65,87}_{row,col}`, `split_prepare_sk_87_{2,4,6,7}x1` | not needed for a verdict any more; run for the table |

`signing_key_NN` is `sign::prepare_sk_into` on a zeroed key object plus a `mem::replace` of that object (`api.rs`): the
same instruction and check counts as `prepare_sk_NN` on x86_64 and thumbv7em, so the `prepare_sk` pieces are its pieces. In the sweep above every riscv32imac `prepare_sk_*` and `signing_key_*` row is already `secure` at
full size (they were `unknown` at 2668aa9); the riscv32imac `prepare_sk` splits are run for completeness.

Verdicts (last run of job `sp-ct`: 28 probes on AArch64, 22 on riscv32imac, `split-run.sh` exit 0; the counts are from the
`Summary:` block of its log; every `secure` row has 0 pending paths and all its control-flow and memory-access checks passing;
`split_vec_power2round_*` also ran on AArch64, all `secure`, which `vec_power2round_*` already were there):

| probe | target | verdict | pending paths | control-flow checks passed | memory-access checks passed |
|---|---|---|---|---|---|
| `split_compute_t_44_2x2` | AArch64 | secure | 0 | 21,718 | 39,996 |
| `split_compute_t_44_col` | AArch64 | secure | 0 | 25,825 | 50,467 |
| `split_compute_t_44_row` | AArch64 | secure | 0 | 23,629 | 43,296 |
| `split_ntt_vec_into_1` | AArch64 | secure | 0 | 2,439 | 5,513 |
| `split_ntt_vec_into_7` | AArch64 | secure | 0 | 19,662 | 42,857 |
| `split_ntt_vec_into_8` | AArch64 | secure | 0 | 22,487 | 48,995 |
| `split_prepare_sk_44_col` | AArch64 | secure | 0 | 43,819 | 98,326 |
| `split_prepare_sk_44_row` | AArch64 | secure | 0 | 33,474 | 73,159 |
| `split_prepare_sk_65_col` | AArch64 | secure | 0 | 65,331 | 144,195 |
| `split_prepare_sk_65_row` | AArch64 | secure | 0 | 42,865 | 89,228 |
| `split_prepare_sk_87_2x1` | AArch64 | secure | 0 | 31,328 | 57,927 |
| `split_prepare_sk_87_4x1` | AArch64 | secure | 0 | 49,081 | 101,545 |
| `split_prepare_sk_87_6x1` | AArch64 | secure | 0 | 66,827 | 145,159 |
| `split_prepare_sk_87_7x1` | AArch64 | unknown | 1 | 47,961 | 87,346 |
| `split_prepare_sk_87_col` | AArch64 | unknown | 1 | 53,132 | 99,986 |
| `split_prepare_sk_87_row` | AArch64 | secure | 0 | 55,560 | 117,710 |
| `split_vec_power2round_1` | AArch64 | secure | 0 | 2,546 | 2,961 |
| `split_vec_power2round_2` | AArch64 | secure | 0 | 6,543 | 8,611 |
| `split_vec_power2round_3` | AArch64 | secure | 0 | 9,869 | 12,967 |
| `split_vec_power2round_5` | AArch64 | secure | 0 | 16,514 | 21,671 |
| `split_vec_power2round_6` | AArch64 | secure | 0 | 19,836 | 26,023 |
| `split_vec_power2round_7` | AArch64 | secure | 0 | 23,159 | 30,377 |
| `split_vec_power2round_8_hi` | AArch64 | secure | 0 | 22,979 | 25,513 |
| `split_vec_power2round_8_lo` | AArch64 | secure | 0 | 22,984 | 25,511 |
| `split_vec_power2round_8_q0` | AArch64 | secure | 0 | 21,228 | 20,899 |
| `split_vec_power2round_8_q1` | AArch64 | secure | 0 | 21,238 | 20,903 |
| `split_vec_power2round_8_q2` | AArch64 | secure | 0 | 21,238 | 20,903 |
| `split_vec_power2round_8_q3` | AArch64 | secure | 0 | 21,223 | 20,905 |
| `split_prepare_sk_44_col` | riscv32imac | secure | 0 | 80,493 | 284,765 |
| `split_prepare_sk_44_row` | riscv32imac | secure | 0 | 61,784 | 249,762 |
| `split_prepare_sk_65_col` | riscv32imac | secure | 0 | 120,105 | 423,152 |
| `split_prepare_sk_65_row` | riscv32imac | secure | 0 | 80,137 | 312,196 |
| `split_prepare_sk_87_2x1` | riscv32imac | secure | 0 | 52,251 | 148,950 |
| `split_prepare_sk_87_4x1` | riscv32imac | secure | 0 | 88,669 | 288,855 |
| `split_prepare_sk_87_6x1` | riscv32imac | secure | 0 | 122,233 | 424,440 |
| `split_prepare_sk_87_7x1` | riscv32imac | secure | 0 | 122,834 | 440,207 |
| `split_prepare_sk_87_col` | riscv32imac | secure | 0 | 137,295 | 500,546 |
| `split_prepare_sk_87_row` | riscv32imac | secure | 0 | 88,530 | 376,291 |
| `split_vec_power2round_1` | riscv32imac | secure | 0 | 5,455 | 9,253 |
| `split_vec_power2round_2` | riscv32imac | secure | 0 | 13,249 | 22,839 |
| `split_vec_power2round_3` | riscv32imac | secure | 0 | 19,981 | 34,379 |
| `split_vec_power2round_5` | riscv32imac | unknown | 1 | 26,623 | 43,531 |
| `split_vec_power2round_6` | riscv32imac | unknown | 1 | 29,727 | 46,210 |
| `split_vec_power2round_7` | riscv32imac | unknown | 1 | 32,811 | 48,760 |
| `split_vec_power2round_8_hi` | riscv32imac | secure | 0 | 45,213 | 66,403 |
| `split_vec_power2round_8_lo` | riscv32imac | secure | 0 | 45,219 | 66,399 |
| `split_vec_power2round_8_q0` | riscv32imac | secure | 0 | 40,999 | 53,561 |
| `split_vec_power2round_8_q1` | riscv32imac | secure | 0 | 41,011 | 53,571 |
| `split_vec_power2round_8_q2` | riscv32imac | secure | 0 | 41,011 | 53,569 |
| `split_vec_power2round_8_q3` | riscv32imac | secure | 0 | 40,993 | 53,567 |

Reading the results: no split piece found a leak, and every piece that completed is `secure`. The `unknown` rows are
the same solver stall as the originals (1 pending path, "timeout has left (at least) 1 pending paths", no leak among
the checks that passed), reproduced at smaller sizes: AArch64 `prepare_sk` with K = 7 and 8 (not K <= 6), riscv32imac
`vec_power2round` with K >= 5. For `prepare_sk_87` and `signing_key_87` on AArch64 the cover is therefore by stages
(skDecode, the in-place NTTs, ExpandA on the public rho) plus the K <= 6 and L = 7 whole-function shapes, not by
a smaller instantiation that includes the K = 8 glue; claim it at that strength. The AArch64 build is the scalar
(`NONEON=1`) one, as in the sweep. The pieces were compiled into one driver with the full set of probes
(the new `split` module also changes the code layout of that driver; the earlier verdicts above were measured without it).

## Earlier results (older trees; superseded by the sweep above)

(nightly-2026-10-06, BINSEC 0.11.3, 900 s per probe unless noted.) Column order below is x86_64 / thumbv7em / riscv32imac.

### Original 40 probes, before the CT-1 fix (older tree, unmodified `src/`)

| target | secure | insecure | unknown (timeout) |
|---|---|---|---|
| x86_64-unknown-linux-gnu | all 40 rows | 0 | 0 |
| thumbv7em-none-eabihf | all 40 rows | 0 | 0 |
| riscv32imac-unknown-none-elf | 22 | 12 | 6 |

riscv32imac insecure (control-flow leaks; no memory-access, dividend or divisor leaks anywhere): `ct_lt_mask`,
`ct_select`, `decompose_44/65_87`, `high_bits_44/65_87`, `low_bits_44/65_87`, `make_hint_44/65_87`, `infinity_norm`,
`vec_infinity_norm`; `response_*` and `hint_step_*` unknown. Cause: RV32IMAC has no conditional move, and LLVM lowers
the `a ^ ((a ^ b) & mask)` select and the `(x - y) >> 63` mask to branches. That is ISSUES CT-1; the riscv-only
`barrier_u32` hardening in `field.rs` fixed it, and the rows below are measured on the fixed `src/`.

### Older tree: 74 probes, `src/` at 069b439 (with the CT-1 barrier), checkct profile

Result of a full run (`ct4-900`, 900 s per probe, 71 entrypoints at that time) plus long reruns of the non-secure
rows (`run-select.sh`, 3000 s):

| target | secure | insecure | unknown |
|---|---|---|---|
| x86_64-unknown-linux-gnu | 64 | 3 (`rej_bounded_poly_eta2/4`, and see `hint_step_65` below) | 4 (`hint_step_{44,87,1_44,1_65}`) |
| thumbv7em-none-eabihf | 69 | 2 (`rej_bounded_poly_eta2/4`) | 0 |
| riscv32imac-unknown-none-elf | 66 | 3 (`rej_bounded_poly_eta2/4`, `ct_lt_mask`) | 2 (`vec_power2round_44/87`) |

Long reruns of the non-secure rows with the final driver (`run-select.sh`, `-sse-timeout 3000`, which BINSEC only
checks between paths):

- x86_64 `hint_step_65`: `insecure` (leak found after 1.5 s, `rounding.rs:37`/`field.rs:65`, see the finding below).
  `hint_step_{44,87,1_44,1_65}`: still `unknown` at 3000 s, each with one pending path and no leak among the 18k to
  36k control-flow checks that passed. "Unknown" here is an unfinished proof, not a clean bill.
- riscv32imac `vec_power2round_{44,87}`: `unknown` at 3000 s (one pending path, no leak found in 20k control-flow and
  33k memory checks); thumbv7em and x86_64 finish these two in minutes. The riscv `response_*`/`hint_step_*`
  probes, `unknown` at 900 s with the previous driver, finish as `secure` in about 2 s with the final driver
  (probably because the driver now compiles `sign`, `api` and `keygen` too, which changes inlining and layout). Run with the previous driver and a
  7200 s timeout instead, all six were still without a verdict after 6300 s (killed). So the resolution is the split
  probes and the changed compilation context, not the longer timeout.
- `control_early_exit_44` is `insecure` on all three targets (the positive control works).
- `census_sign_internal_44` (see below).

### Finding: x86_64 `decompose` edge select becomes a branch (inside `hint_step`)

`hint_step_65` on x86_64 is `insecure` at HEAD: a control-flow leak at `src/field.rs:65` (`ct_select`, inlined in
`rounding::decompose`, `rounding.rs:37`) in the `hint_step` probe, found after 1.5 s. The disassembly is
`cmpl $0x7fe000, %r8d; je skip; imulq (%rsp), %r8; shrq $0x30, %r8`: the multiply that computes r1 is skipped when
`diff == q - 1`. `hint_step_{44,87,1_44,1_65}` are `unknown` (BINSEC does not finish, even at 3000 s) on the same code.
In `decompose`, `ct_select(r1, 0, is_edge)` and
`ct_select(r0, r0 - 1, is_edge)` select between a value that is a multiply result (`diff * two_gamma2_div_mult >> 48`)
and a constant; LLVM turns that select into `cmp`/`je` on the secret `diff == q - 1` condition, the same
recognition that RV32IMAC needed `barrier_u32` for. In the standalone `decompose_*` and `high_bits_*` probes the
select stays branch-free; it only becomes a branch when the surrounding code (`hint_step`'s inlining context) lets
LLVM see the multiply feeding the select. The leaked bit is `w - cs2 + ct0` being exactly at the decompose edge
(`diff == q - 1`), i.e. a function of secret data, so this is a real object-code finding for that toolchain and
inlining context, not a tool artifact.

Fix (applied in 069b439, ISSUES CT-2): add an
`opaque_u32` barrier (`core::hint::black_box`, identity under `cfg(miri)`) and apply it to the edge mask in
`rounding::decompose`:

    let is_edge = opaque_u32(!ct_lt_mask(0, (diff ^ (Q - 1)) as u64) as u32);

Verification (throwaway git worktree of HEAD with the patch applied; full 74-probe run, 900 s per probe):

Core probes (the 71 entrypoints of the baseline run), baseline versus patched, 900 s per probe:

| target | baseline secure / insecure / unknown | patched secure / insecure / unknown |
|---|---|---|
| x86_64-unknown-linux-gnu | 64 / 3 / 4 | 69 / 2 / 0 |
| thumbv7em-none-eabihf | 69 / 2 / 0 | 69 / 2 / 0 |
| riscv32imac-unknown-none-elf | 66 / 3 / 2 | 66 / 3 / 2 |

The two x86_64 and thumbv7em insecure rows are `rej_bounded_poly_eta2/4` (by design, see above). On riscv32imac they
are the same two plus the standalone `ct_lt_mask` (64-bit compare of values the compiler knows are below 2^63; its
in-crate callers are secure), and the two unknown rows are `vec_power2round_44/87` (unresolved at 3000 s; no leak
found). With the patch all five x86_64 `hint_step` probes are `secure` in about 3 s each, and `response_*` stays
secure. The patch changes nothing on thumbv7em and riscv32imac, where `barrier_u32` already blocks the select.

Under the nearcore-like profile (see below) the patched tree gives `secure` for every `hint_step_*`, `response_*`,
`decompose_*`, `high_bits_*`, `make_hint_*` and `*sk_is_well_formed*` probe on x86_64 (run `ct4-nvfix`), where the
unpatched tree gives `insecure` for `hint_step_44` and `hint_step_65`.

Caveats: `black_box` is not modeled by Aeneas, so the Lean extraction must see the identity (the patch uses the same
`cfg(miri)` convention as the existing `barrier_u32`; extraction already runs with `--cfg miri`); that has to be
confirmed by the extraction owner because the patch changes extracted source. `cargo test --release` passes with the
patch and the signing cost is within noise (about 0 to 3 percent in the benches).

### Whole-function probe (`census_sign_internal_44`)

A single probe of the whole `api::sign_internal_44`, with a concrete well-formed secret key whose K, s1, s2 and t0
bytes are replaced by secret bytes (rho and tr stay public) and a secret `rnd`. This is a census, not a proof,
because the rejection samplers and the rejection `if`s of `attempt` are public-outcome branches that BINSEC flags.
The bullets below were measured on older trees; the `error` results in them were out-of-memory kills (ISSUES.md T-8), and the
current census results are in the full sweep above.

Final probe design (concrete public rho and tr, from a fixed-seed KeyGen):

- x86_64, nearcore-like profile without vectorization, unpatched tree: `insecure`, and the leak found is the
  `decompose` edge branch (`field.rs:65` in `ct_select`, inlined into `sign_internal_44`), i.e. the same finding as the
  `hint_step` probes, now seen in the real signing function. So the per-step probes were not missing a different
  context: the whole function shows the leak too.
- x86_64, same profile, patched tree: `insecure`, first leak at `sampling.rs:35` (the `SampleInBall` accept test,
  public outcome); no `field.rs:65` leak is reported. The unpatched checkct-profile run is also `insecure` (leak list
  not mapped).
- thumbv7em and riscv32imac (unpatched, checkct profile): BINSEC exits without a `Program status` line (first leak
  found after about 40 s, then no verdict), reported as `error`. The riscv nearcore-like run is `unknown`.
- Every run ends with `insecure` or no verdict and one pending path (about 200k branching points), so the leak lists
  are not exhaustive; this probe cannot prove anything, it only catches an obvious leak early.

An earlier design of the probe with a symbolic (public-nondeterministic) rho, run on the patched tree, flagged the
ExpandA accept test (`sampling.rs:14`) on x86_64 and riscv32imac, expected for the same reason.

So the largest signing steps that complete are `response_*` and `hint_step_*` (the secret-dependent halves of
`attempt`), plus the hash and ExpandMask probes; `sign_internal` itself is covered by those parts and by this census,
whose leaks are the sampler branches and, on the unpatched tree, the decompose edge.

### nearcore-like release profile (opt-level 3, fat LTO, codegen-units 1, panic = abort), older tree (069b439)

Built with `PROFILE=nearcore` (`opt-level = 3`, `lto = "fat"`, `codegen-units = 1`, `panic = "abort"`) and the
unpatched tree, 900 s per probe, then 3000 s reruns of the non-secure rows. x86_64 / thumbv7em / riscv32imac:

| target | secure | insecure | unknown |
|---|---|---|---|
| x86_64-unknown-linux-gnu | 61 | 3 (`rej_bounded_poly_eta2/4`, `control_early_exit_44`) | 8 (+ `census_sign_internal_44`: no verdict) |
| thumbv7em-none-eabihf | 69 | 3 (same three) | `census_sign_internal_44`: error |
| riscv32imac-unknown-none-elf | 60 | 4 (same three, `ct_lt_mask`) | 9 |

Differences from the checkct profile:

- x86_64: `sk_is_well_formed_{44,65,87}` and `encode_sk_is_well_formed_{44,65,87}` are `unknown` within seconds, not
  because of a timeout: with opt-level 3 LLVM vectorizes the range-check loop with SSE2 and BINSEC cuts the path
  at `movmskpd` ("uninterpreted"), so those six verdicts are missing, not negative. `PROFILE=nearcore-novec` adds
  `-C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false` (x86_64 only); with it all six are `secure`
  and the checkct-profile result carries over (`sk_is_well_formed_*` secure, positive control insecure).
- x86_64 `hint_step_{44,65,87}` and `response_*` are `secure` in the vectorized nearcore-like build (LLVM vectorized
  the decompose select, so no branch survives), but `hint_step_1_{44,65}` are `unknown` at 3000 s. Without
  vectorization (`nearcore-novec`), unpatched: `hint_step_44` and `hint_step_65` are `insecure` (leak at `field.rs:65`,
  the decompose edge branch, here compiled as `jl`), `hint_step_{87,1_44,1_65}` unknown, and the whole-function
  census leaks at the same line. With the patch every x86_64 probe is secure under `nearcore-novec` except the
  expected ones (`rej_bounded_poly_*`, `control_early_exit_44`; the census is still unfinished). So the finding is
  real under the downstream release settings, but whether the branch appears depends on the vectorizer: the patch is
  needed regardless.
- riscv32imac: the full-size `response_{44,65,87}` and `hint_step_{44,65,87}` are `unknown` again at 3000 s (no leak
  found; one pending path each), whereas the one-polynomial splits `response_1x1_*` and `hint_step_1_*` are `secure`.
  The `black_box` barriers keep the branches out; the lack of a proof is a solver-capacity issue on the large
  probes, so the split probes are the evidence there.
- thumbv7em: identical to the checkct profile.

### AArch64 (experimental, `aarch64.sh`), older tree (069b439); current numbers are in the full sweep above

BINSEC 0.11.3 supports `-isa aarch64`, and an AArch64 driver binary runs through the same flow, but `cargo-checkct`
does not know the target, so `aarch64.sh` builds the driver for `aarch64-unknown-linux-gnu` itself (release, same
profile, static relocation, `rust-lld`) and generates the BINSEC scripts with the `cargo-checkct` template adapted to
AArch64 (return address in `x30`, `halt at` the panic hook and the sentinel return address). Not a supported
target of `cargo-checkct`; run `bash checkct/aarch64.sh` on the build box.

- Default build: 57 probes `secure`, `control_early_exit_44` and `rej_bounded_poly_eta2/4` `insecure` (expected), and
  12 `unknown`. Eleven of those (`response_*`, `hint_step_*`, `vec_infinity_norm`) stop within two seconds at the first
  NEON instruction the lifter cannot interpret (`umax`/`umin` on `.4s` vectors; the loops are auto-vectorized), so
  the path is cut and no verdict is possible, not a timeout; `ntt` is `unknown` at the 900 s timeout.
- `NONEON=1` (`-C target-feature=-neon,-fp-armv8`, the scalar code path): 69 probes `secure`, the same three
  expected `insecure`, `census_sign_internal_44` `unknown`; the vectorized probes above all complete as `secure`
  (73 distinct entrypoints; `field_add` is merged with `field_small_reduce` in the binary). The positive control
  flags 8 leak sites and the checks report non-trivial coverage (for example `sk_is_well_formed_44`:
  82620 unrolled instructions, 16121 control-flow and 14634 memory-access checks passed), so the secure verdicts are
  not vacuous.
- Caveat: `NONEON` code is not what an AArch64 production build runs (NEON is on). The NEON build is what deployed code
  looks like, and BINSEC cannot verify the vectorized probes there. The scalar result shows the source-level
  structure is constant time with the AArch64 select lowering (`csel`), not that the NEON code is.

## Not covered

- Only the listed steps, on the target/opt-level above (release, debug info) and the nearcore-like profile for the
  rows reported there. Other compilers, versions, opt-levels and inlining contexts can differ, as the x86_64
  `decompose` finding shows: a function that is branch-free in isolation can acquire a branch once inlined into a
  caller. Re-run after toolchain bumps. Release builds of downstream crates (a different codegen-units count, PGO,
  `-C target-cpu=native`) are not covered.
- `sign::attempt` and `sign_internal` as a whole are not proven: the rejection samplers and the two rejection `if`s
  of `attempt` are public-outcome branches that BINSEC cannot tell from leaks, so the proof is by parts (the secret
  steps above) plus the code reading that the glue between them has no secret branch.
- Shake absorb/squeeze with a secret input is covered through `keccak_f1600` and the hash probes
  (`keygen_seed_hash`, `sign_rho_pp_hash`, `expand_mask_*`) only for the parameter sets listed; verify (public data) and
  `use_hint` are not probed; zeroization is outside this tool.
- BINSEC proves absence of secret-dependent control flow/memory/division operands, not absence of data-dependent
  instruction timing (e.g. variable-latency multiplies on some cores; the `multiplication` check is experimental and
  not enabled).
