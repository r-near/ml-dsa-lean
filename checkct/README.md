# checkct: binary-level constant-time checks (BINSEC)

Port of the RustCrypto `ml-dsa/checkct` harness (signatures repo, rev a3690c4) to this crate. The driver
`#[path]`-includes the crate sources unchanged (`params`, `field`, `rounding`, `ntt`, `keccak`, `encode`, `sampling`,
`keygen`, `sign`, `verify`, `api`; the crate is `no_std` with no dependencies, so no shims are needed), marks every
probe input secret through the `__checkct_private_rand` hook, and lets BINSEC (via `cargo-checkct`) symbolically
execute the compiled release binary, flagging any secret-dependent branch, memory access, or division operand.

This directory is its own workspace (`[workspace]` in `checkct/Cargo.toml`). It is not a member of the main
crate's workspace and the main `Cargo.toml` needed no `exclude`. `src/` is not edited.

## Running

Linux only (BINSEC). On the build box, via Docker:

    docker build -t ct-binsec checkct                           # once; compiles BINSEC from opam, ~10 min
    rx submit ct4 -- 'set -o pipefail; bash checkct/run.sh 2>&1 | tee ct.log'
    rx wait ct4

Scripts (all start from the repository root; `rx kill` does not stop containers, so `docker kill $NAME` too):

| script | purpose | environment |
|---|---|---|
| `run.sh` | all probes, all three targets (`cargo-checkct run --all-leaks`) | `TIMEOUT` (900 s per probe), `JOBS`, `OUT` (copies the three `<target>.driver` binaries), `NAME`, `PROFILE=nearcore` |
| `run-select.sh` | only probes matching a regex, long timeouts; builds with `cargo-checkct`, then calls `binsec` directly. Streams a `done <target> <probe> <status>` line per probe and ends with a `Summary:` block like `run.sh` | `ONLY` (regex), `TARGETS`, `TIMEOUT` (7200), `JOBS` (30), `OUT`, `NAME`, `PROFILE` |
| `leaks.sh LOG BINDIR` | maps every leaking instruction address of a `Summary:` block to `file:line` and the instruction (`llvm-objdump -d -l` on the `OUT` binaries) | `OBJDUMP` as third argument |
| `aarch64.sh` | experiment: AArch64 (see below); `cargo-checkct` does not support the target, so it builds the driver for `aarch64-unknown-linux-gnu` in the container and writes the BINSEC scripts itself | `ONLY`, `TIMEOUT`, `JOBS`, `NAME`, `OUT`, `NONEON=1` |
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
The results tables below were not re-run for these profiles.

Toolchain: `nightly-2026-10-06` with `rust-src` (`checkct/rust-toolchain.toml`), `-Zbuild-std=core,panic_abort` with
`compiler-builtins-mem` (`.cargo/config.toml`, copied from upstream). BINSEC 0.11.3, unisim_archisec 0.0.14,
cargo-checkct @ 85271e5. Checks: `control-flow,memory-access,dividend,divisor`. Building only (no BINSEC) works
anywhere with the toolchain: `cd checkct && cargo build --release -p driver --target x86_64-unknown-linux-gnu`.

`checkct_macros/src/lib.rs` and `.cargo/config.toml` are copied from upstream (Apache-2.0 OR MIT), as
`cargo-checkct init` generates them. `driver/src/rng.rs` is the same hook pair without the `rand_core` impls.

## Probes (85 entrypoints x 3 targets: riscv32imac-unknown-none-elf, thumbv7em-none-eabihf, x86_64-unknown-linux-gnu)

Already present before this round (40, `probes.rs` and `signing.rs`):

- field/mask: `field_small_reduce`, `barrett_reduce`, `field_add`, `field_sub`, `field_neg`, `field_mul`,
  `ct_lt_mask`, `ct_select` (mask taken from a secret bit).
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

### Prepared signing key (`prepared.rs`, 11 probes; HEAD 2668aa9 plus the probes)

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

Results (BINSEC 0.11.3, checkct profile, 3000 s per probe unless noted; targets run one at a time, containers capped at
64 GB):

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
  (no `Program status` line): first leak at 0x043db2, again `src/sampling.rs:35`, after 51 s; unchanged when rerun with the
  container cap raised to 120 GB, so it is not an out-of-memory kill. Same behavior as `census_sign_internal_44` above.
  A census cannot prove anything, as before; the secret halves of an attempt are covered by `response_*` and
  `hint_step_*`. riscv32imac census not run (the unprepared census was `unknown` there).

Run with `rx submit pk-ct -- bash checkct/run-prepared.sh '<regex>' '<targets>' <timeout> [<memory>]` or
`checkct/prepared-leaks.sh` (same arguments; also maps leak addresses to source lines).

Expected-insecure probes. `rej_bounded_poly_eta{2,4}` leak by design: the loop branches on whether a sampled
nibble is accepted, and which positions are rejected is public (it only changes how many XOF bytes are consumed).
`census_sign_internal_44` finds the same kind of branch (a rejection sampler) first. These are not constant-time
bugs; they show what BINSEC cannot distinguish (secret data versus public outcome of a secret-derived value), which
is why the proof of "no secret-dependent branch" is done per step.

## Results (nightly-2026-10-06, BINSEC 0.11.3, 900 s per probe unless noted)

Column order below is x86_64 / thumbv7em / riscv32imac.

### Original 40 probes, before this round (unmodified `src/`)

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

### Now: 74 probes, `src/` at HEAD (with the CT-1 barrier), checkct profile

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

### nearcore-like release profile (opt-level 3, fat LTO, codegen-units 1, panic = abort), `src/` at HEAD

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

### AArch64 (experimental, `aarch64.sh`)

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
