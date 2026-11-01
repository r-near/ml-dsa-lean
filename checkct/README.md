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
> (below) matched every `error` of that sweep to a kernel OOM kill; the `error` rows of the older-tree sections stay
> "presumed".

## Running

Linux only (BINSEC). On the build box, via Docker:

    docker build -t ct-binsec checkct                           # once; compiles BINSEC from opam, ~10 min
    rx submit ct4 -- 'set -o pipefail; bash checkct/run.sh 2>&1 | tee ct.log'
    rx wait ct4

Scripts (all start from the repository root; `rx kill` does not stop containers, so `docker kill $NAME` too):

| script | purpose | environment |
|---|---|---|
| `run.sh` | all probes, all three targets (`cargo-checkct run --all-leaks`); `JOBS` defaults to every CPU, which does not fit a 64 GB container, so the full sweep of e9a1c74 used `run-select.sh` with `ONLY=.` instead | `TIMEOUT` (900 s per probe), `JOBS`, `OUT` (copies the three `<target>.driver` binaries), `NAME`, `PROFILE=nearcore` |
| `run-select.sh` | only probes matching a regex, long timeouts; builds with `cargo-checkct`, then calls `binsec` directly. Streams a `done <target> <probe> <status>` line per probe and ends with a `Summary:` block like `run.sh` | `ONLY` (regex), `TARGETS`, `TIMEOUT` (7200), `JOBS` (4), `OUT`, `NAME`, `PROFILE` |
| `leaks.sh LOG BINDIR` | maps every leaking instruction address of a `Summary:` block to `file:line` and the instruction (`llvm-objdump -d -l` on the `OUT` binaries) | `OBJDUMP` as third argument |
| `aarch64.sh` | experiment: AArch64 (see below); `cargo-checkct` does not support the target, so it builds the driver for `aarch64-unknown-linux-gnu` in the container and writes the BINSEC scripts itself | `ONLY`, `TIMEOUT`, `JOBS`, `NAME`, `OUT`, `NONEON=1` |
| `split-run.sh [round2]` | the split probes of `driver/src/split.rs` on AArch64 (`NONEON=1`) and riscv32imac, two containers in parallel, exit status nonzero if either fails (see "Split probes") | `TIMEOUT` (3600), `JOBS` (2 per container), `AONLY`, `RONLY` |
| `select-ntt.sh [mode]` | the NTT and field-product probes and the KeyGen/Sign pieces built on them, through `run-select.sh`; `mode` is `default`, `dispatch`, `nearcore-dispatch`, `avx2` or `nearcore-avx2` (see "Profiles for the AVX2 dispatch") | `TIMEOUT` (3600), `JOBS`, `OUT`, `NAME`; the 2nd and 3rd arguments replace the probe regex and the target list |
| `scan-avx2.sh DIR` | static scan of the `*_avx2` functions of a dispatch driver (`DIR` under `~/rx/scratch`, the `OUT` of a dispatch run); fails if there are none | |

`PROFILE=nearcore` builds with `opt-level = 3`, `lto = "fat"`, `codegen-units = 1`, `panic = "abort"` (through
`CARGO_PROFILE_RELEASE_*`). The default is the checkct workspace profile (release plus debug info, `panic = "abort"`,
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

Toolchain: `nightly-2026-10-06` with `rust-src` (`checkct/rust-toolchain.toml`), `-Zbuild-std=core,panic_abort` with
`compiler-builtins-mem` (`.cargo/config.toml`, copied from upstream). BINSEC 0.11.3, unisim_archisec 0.0.14,
cargo-checkct @ 85271e5. Checks: `control-flow,memory-access,dividend,divisor`. Building only (no BINSEC) works
anywhere with the toolchain: `cd checkct && cargo build --release -p driver --target x86_64-unknown-linux-gnu`.

`checkct_macros/src/lib.rs` and `.cargo/config.toml` are copied from upstream (Apache-2.0 OR MIT), as
`cargo-checkct init` generates them. `driver/src/rng.rs` is the same hook pair without the `rand_core` impls.

## Known no-verdict probes (skip unless something changed)

These probes are already known to end with no verdict. Don't rerun them unless one of these changed: the code
under test (`src/` or the probe), the per-probe timeout, the memory cap, or how the probe is split. A rerun that
changes nothing costs hours and gives the same result (about 1.6 h went to such reruns on 2026-11-01). Each entry
says what was tried. When an entry gets a verdict, move it out of this list.

| probe | target / profile | outcome | already tried |
|---|---|---|---|
| `sk_is_well_formed_{44,65,87}`, `encode_sk_is_well_formed_{44,65,87}` | x86_64 `nearcore`, `nearcore-dispatch` | unknown: BINSEC can't lift SSE2 `movmskpd` (stops at 0.1 s) | 1 h and 2 h at e9a1c74. Only a non-vectorized build helps (`PROFILE=nearcore-novec`) |
| `vec_power2round_87` (full size) | riscv32imac default | unknown, 1 pending path | 1 h and 2 h at e9a1c74. Covered by the split windows `split_vec_power2round_8_*` (secure) |
| `split_vec_power2round_{5,6,7}` | riscv32imac | unknown | 1 h (capacity probing only; the 8-wide windows cover the loop) |
| `census_sign_internal_44` | riscv32imac default | unknown, 4 pending paths | 1 h and 2 h at e9a1c74 |
| `compute_t_44`, `prepare_sk_{44,65,87}`, `signing_key_{44,65,87}`, `census_sign_internal_44`, `census_sign_prepared_44` | AArch64 `NONEON=1` | unknown: one pending path stuck in one solver query (instruction count identical at 300, 600, 3600 and 7200 s; upstream log U-42) | 1 h and 2 h at e9a1c74. Pieces covered by split probes, except the K = 8 glue of `prepare_sk_87` / `signing_key_87` |
| `split_prepare_sk_87_7x1`, `split_prepare_sk_87_8x1` | AArch64 `NONEON=1` | unknown, same stall | 1 h (round 2 of `split-run.sh`) |
| `census_sign_internal_44`, `census_sign_prepared_44` | thumbv7em default | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps (ISSUES T-8). Don't raise the cap again; a split would be needed |
| `census_sign_prepared_44` | riscv32imac default; x86_64 `nearcore-dispatch` | OOM: needs more than 120 GB, no verdict | 64 GB and 120 GB caps |
| `control_prepared_branch_44` | thumbv7em | `secure`: the control is invalid there (branch lowered to a select) | every run; expected |
| `control_prepared_branch_44`, `control_prepared_index_44` | AArch64 `NONEON=1` | no verdict | 1 h and 2 h |

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

The current results. Every probe of `checkct/driver` (87 distinct entrypoints per target; `field_add` is merged with
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
| `rej_bounded_poly_eta2/4` | all 7 target/profile rows | insecure, expected | sampler accept test, a public outcome (`sampling.rs:129`, `:132`) |
| `census_sign_internal_44`, `census_sign_prepared_44` | x86_64 in all four profiles | insecure, expected | only leak reported: `sampling.rs:35`, `sample_in_ball`'s accept test (public outcome); then one pending path, no verdict. Needed the 120 GB container, see below. Exception: `census_sign_prepared_44` under `nearcore-dispatch` is `oom` |
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
