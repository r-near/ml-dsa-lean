# Issues

Bugs found, tool problems and errata, newest last. Each entry: ID, date, what, impact, resolution.

## Bugs (in this crate)

- **CT-1 (2026-10-29): mask-select idiom branches on riscv32imac.** BINSEC (`checkct/`) found control-flow leaks
  in `ct_select`, `ct_lt_mask` and their callers (Decompose, HighBits, LowBits, MakeHint, the infinity norms) on
  riscv32imac: without a conditional move, LLVM turns the masks back into branches on secret data. x86_64 and
  thumbv7em were secure. Fixed with a `core::hint::black_box` barrier on the mask, compiled only for RISC-V and
  not under `--cfg miri` (the extraction cfg), so the proved code is unchanged. Applying it on every target cost
  about 25% in signing, so it is RISC-V only. Trusted-base addition: `black_box` is the identity on values.
  Rerun (39 probes per target, production `response`/`hint_step`): x86_64 39/39 and thumbv7em 39/39 secure;
  riscv32imac 32 secure, 6 unknown (the signing-step probes time out at 900 s there), and 1 insecure: the
  standalone `ct_lt_mask` probe, whose inputs the probe masks below 2^63 so LLVM folds the compare. Every
  in-crate caller (Decompose, HighBits, LowBits, MakeHint, the norms) is secure on riscv32imac.

- **CT-2 (2026-10-30): Decompose's edge select branches on x86_64.** BINSEC found `hint_step_65` insecure (and
  `hint_step_44` with vectorization off, and the whole-Sign census at the same line): LLVM turns the
  `diff == q − 1` mask select in `rounding::decompose` into `cmp; je` around the multiply that computes r1. Decompose
  runs on secret data in Sign (LowBits(w − cs2), MakeHint). Earlier x86_64 runs reported the per-function probes
  secure; the leak appears only in the inlined signing-step contexts. Fixed in 069b439: `field::opaque_u32`
  (`black_box` on every target, identity under `cfg(miri)`, so the extracted code is `ok x` and the theorems are
  unchanged) wraps the edge mask. After the fix every x86_64 Decompose/HighBits/LowBits/MakeHint/hint_step/response
  probe is secure in both the default and nearcore-like profiles; thumbv7em and riscv32imac unchanged. Cost: Sign
  about +2–3%, Verify and KeyGen unchanged.

- **CT-3 (2026-11-03, resolved 2026-11-04 in ae6023c): `sk_is_well_formed` branched on secret coefficients when built
  with overflow checks.** Under nearcore's release settings (`overflow-checks = true`, checkct profile `nearcore-exact`),
  the `&&` in the old `poly_in_eta` (`src/encode.rs`) stayed a conditional branch, because its right operand could
  panic; BINSEC reported two `jb` leaks revealing the sign of each s1/s2 coefficient. Affected the optional key check
  `sk_is_well_formed_*` and its callers (`pk_from_sk_*`); Sign never called it. Fix: `poly_eta_bad`/`eta_block_bad`
  OR per-coefficient mask bits from wrapping differences and `sk_is_well_formed` compares once with zero (exact
  because coefficients are canonical, below 2³¹); `field.rs`, `rounding.rs` and the range test use `wrapping_*`
  arithmetic where the proofs already exclude overflow, so no overflow-check guard remains on secret values; the
  `vec_infinity_norm` running maximum gets `opaque_u32`. Proofs changed only in bodies (770 headline names, witness
  146). Under `nearcore-exact` after the fix: the six `sk_is_well_formed*` probes, `sk_decode`, `sk_encode` and
  `expand_mask` are secure; the remaining unknowns stop at AVX/VEX instructions BINSEC 0.11.3 cannot lift (`vinsertps`,
  `vblendvps`, `vblendps ymm`) and are secure with vectorization off (49 probes; T-9, `checkct/README.md`).

- **Z-1 (2026-11-03): zeroize stack-residue scans fail in unoptimized builds.** `tests/zeroize.rs` has 15 stack
  scans. At opt-level 0, 8 find copies of s1, s2, ŝ1, t0 or K in dead stack frames: `keygen` (44/65/87),
  `pk_from_sk` (44/65/87) and `signing_key` (44/65); `signing_key_87`, `sign` and `sign_prepared` pass. At opt-level 1,
  `keygen_44` and `keygen_65` fail. Release passes 15 of 15, as does the nearcore profile (1.95.0, fat LTO, overflow
  checks). Impact: the stack-residue claims in `src/api.rs` hold for optimized builds only (now stated there); drop
  and explicit wipes are unaffected. A copy vendored as a nearcore workspace member would build at opt-level 0 in
  nearcore's dev profile (`docs/nearcore-integration.md` §4). Open: add wipes at those locals, or keep the scope.
  `scripts/ci.sh` runs the 7 passing scans at opt-level 0 and all 15 in release and under the nearcore profile.

## Tool problems

Known from the campaign (see docs/BLOCKERS.md and docs/SURVEY.md): B-F1 (nested loop reading freshly written outer
data fails in Aeneas; lift the inner loop into a function), B-F2 (`for` ranges pull in `Step` axioms; use `while`),
B-X3 (`--monomorphize` adds unmodeled index axioms; extract generically).

- **T-1 (2026-10-29): Aeneas colors its log tags.** `[Error]` is printed as `[\x1b[91mError\x1b[39m ]`, so a substring
  gate never matches; errors were caught only through the exit code. Fixed in `scripts/extract.py` (strip ANSI escapes,
  regex match, print the first error with context).
- **T-2 (2026-10-29): `return` from a loop followed by another loop fails.** Aeneas reports "Breaks to outer loops are
  not supported yet" and drops the function body (it then appears as an external axiom), even when the `return` is in a
  single-level loop, if a second loop follows in the same function. Fix: one returning loop per function, with the loop
  as the function's last statement before a plain tail value (`hint_bit_unpack_rows` / `_row` / `_padding`). Same root
  family as B-F1.
- **T-3 (2026-10-29): `rx pull` of a single file failed** with an rsync broken pipe; pulling the directory works.
- **T-4 (2026-10-29): extraction feature set.** The pipeline extracted with default features on (inherited from the
  campaign variant). Now `no-default-features = true`, so optional wrapper features (zeroize) stay out of the
  extraction closure.
- **T-5 (2026-10-29): lake default targets.** The pipeline built only `Impl` while the axiom check imports `Proofs`;
  it passed only on a warm box dir. Now `defaultTargets` includes `Spec` and `Proofs` and the script runs `lake build`.
- **T-6 (2026-10-30): rx job exit codes hid build failures.** Ad hoc `rx submit` jobs ran `lake build … 2>&1 | tail -30`
  (or `| grep`) without `pipefail`, so the job exited with the filter's status, not lake's. An audit found 10 of 68
  exit-0 jobs with build errors in their logs. Rechecking the logs that are still retained: `pf-keccak-perm` (lake
  "build failed"), `pf-keccak-full` (a missing-olean error before its real build) and `extract`, `kg-extract`,
  `vf-extract` (extraction gate failures during the hint-unpack fix, T-2). `pf-encode3` had been overwritten by a
  later run of the same name. All were intermediate runs that were superseded, but no result counts on exit code
  alone. Recheck: a fresh worktree of ffc445c (job `verify-head`, cold box dir) ran the full pipeline with pipefail:
  extraction gate clean and `lean/Impl` byte-identical to the committed files, `lake build` succeeded (1736 jobs;
  every `Proofs/*.lean` is in the import closure), and the axiom gate passed on 340 declarations. A source scan found
  no `sorry`/`admit`/`native_decide`/`axiom`/`opaque` in `Proofs/`. Every module listed as proved in STATUS.md stands.
  Rust suites rerun with pipefail on the same tree (job `verify-head-rs`): 28 tests pass with and without `zeroize`. Fixes: `scripts/lean-check.sh [Module…]` is
  now the done-gate (pipefail; fails on a nonzero lake exit, any `error:` or `declaration uses 'sorry'` in the full
  log, or the axiom gate). `scripts/extract-and-build.sh` also greps its build log. Every rx shell string starts
  with `set -o pipefail;`, and output is read afterward with `rx logs <job> 30` rather than filtered in the job.
  (`scripts/check-axioms.sh` was already safe: it fails on any `error` in the Lean output.)
- **T-7 (2026-10-30): Lean gates ran cold, about 10× slower.** Reusing an `rx submit` name keeps only cargo targets
  warm. A job's Lean `.lake/build` comes from this worktree's box copy, and only `rx run` updates that copy. It
  was last refreshed at 10:26Z, so every later gate rebuilt everything changed since then: full gates took 930–1010 s
  instead of about 100–150 s, mostly `Proofs.Witnesses` (about 800 s), and a 2.5 s module took 150–175 s per job.
  Also, rx jobs belong to the worktree that started them: a `rx kill` from the main worktree missed a gate submitted
  from a temporary worktree, and it ran for another 10 minutes. Fix: after each passing gate, the orchestrator (or one
  designated agent) runs `rx run -- 'set -o pipefail; cd lean && lake build'` once to refresh the box copy. Subagents
  never run it, so they don't race on the copy. Before removing a temporary worktree, `rx kill` its jobs from inside
  it. Superseded on 2026-10-30 by an rx update: reusing an `rx submit` name now syncs changes into
  that name's snapshot, so its `.lake/build` stays warm. The extra `rx run` is dropped; each agent keeps one
  stable job name (the orchestrator's full gate is `gate-main`). A new name still starts cold.
- **T-8 (2026-10-31): BINSEC out-of-memory kills were reported as tool errors.** When the kernel kills binsec at a
  container's memory cap (or, before 244aecc, at the box limit), the job log shows only the probe's `error`, with no
  `Program status` line and nothing about memory. `checkct/README.md` said the thumbv7em `census_sign_prepared_44`
  `error` was "not an out-of-memory kill" because it was unchanged with the cap raised to 120 GB. The box kernel log
  shows that rerun killed at the cap (binsec at 125 GB RSS, 2026-10-31 16:38:25Z). Kernel memcg/OOM kills of binsec
  also fall in every earlier CT window: 2026-10-30 21:12–22:46Z, 2026-10-31 07:23–08:49Z, 10:18, 11:53, 12:01,
  16:25, 17:18, and 19:00–21:04Z. The last are parallel probes (2–34 GB each) sharing one container's 64 GB cap, so
  `JOBS=16` at 64 GB was too many for the large probes, and they include the nearcore positive control
  `control_early_exit_44`. Fix: every `error`, and every probe without a `Program status`, is matched against
  `journalctl -k -g 'Killed process'` (with `-b -1` across a reboot) and classified `oom` unless no kill falls in
  its run window. Large probes run with `JOBS` 1–4. A probe killed alone at 120 GB is recorded as "needs more than
  120 GB" instead of the cap being raised again. Until the full sweep at 1000b51+ lands, every `error` in the README is
  presumed OOM and gives no verdict.
- **T-9 (2026-11-04): two BINSEC limits decide what a `nearcore-exact` sweep can show.** (1) *Overflow-check guards on
  secret values stall BINSEC* (cf. upstream U-45 in `docs/upstream-issues.md`). With `overflow-checks = true`, the
  conditional jump to the panic path after `a + Q - b`, a Montgomery step and similar arithmetic left 65 probes at 1
  pending path through 600 to 3600 s (e9a1c74 tree, `checkct/README.md`, section "`nearcore-exact` and
  `nearcore-exact-dispatch`", stop table; summaries in `checkct/results/nearcore-exact.*`). The crate no longer has
  those guards on secret values (ae6023c, CT-3), and at 15b4ce2 those probes are no longer stuck there. The limit is
  not gone: one probe, `prepare_sk_1x1_65`, still ends with 1 pending path at 600 s and at 3600 s (last step a `movdqu`
  store in `ntt_body_mut`), and source that keeps guards on secret values could stall the same way (not tested). (2) *BINSEC 0.11.3
  cannot lift AVX/VEX instructions.* nearcore builds x86_64 with `+fma`, which implies AVX, so LLVM emits VEX forms.
  Under `nearcore-exact` and `nearcore-exact-dispatch` at 15b4ce2, 48 of 113 probes are cut paths ("uninterpreted
  KO", 0 pending paths, no leak among the checks that passed) at `vinsertps` (`ntt.rs:111`, NTT layer), `vblendvps`
  (vectorized `small_reduce` after `mont_reduce`, `field.rs:25`/`:76`) or `vblendps` on `ymm` (`ntt.rs:131`, inverse NTT
  layer): `ntt`, `ntt_inverse`, `multiply_ntt`, `ntt_vec_44`, the `compute_t_*` and `matrix_vector_ntt_*` family,
  `prepare_sk_*` and `signing_key_*`, `hint_step_*`, `response_*`, `split_*` pieces and the censuses
  (`checkct/results/sweep-15b4ce2/x86_64-nearcore-exact.unknowns.txt`). With the loop and SLP vectorizers off
  (`PROFILE=nearcore-exact-novec`, otherwise the same flags) all 113 probes get a verdict (108 secure, 5 expected
  insecure). So nearcore's exact build has no BINSEC verdict for the NTT, `hint_step` and `response`, and the `-novec`
  result is evidence about a different binary, not about nearcore's. Same class as U-40 and U-44. Workaround: build
  the analyzed binary without vectorization, or check the VEX code by another route; neither is done for the
  vectorized NTT/product code.

## Errata (docs, spec, upstream)

- **E-1 (2026-10-29): "Verify for all byte strings" needs length hypotheses.** The core decoders index slices
  directly. `verify_internal` now starts with a length guard (wrong `pk`/`σ` length returns false; FIPS 204 types
  the inputs by length, and the project spec's step 0 returns false), valid when `p` agrees with `K`/`L`, and `verify_internal_spec` has no length hypotheses. `sign_internal` and `keygen_internal` still panic on
  wrong-length slices and their theorems keep the length hypotheses; the API's fixed-size arrays discharge them.
  Since 5d151a6 every module except `api` is crate-private (public only under the `internals` feature for tests and
  fuzzing), so none of these panicking entry points is reachable by a downstream user unless something in its
  dependency graph turns that feature on (Cargo unifies features).
  The guard needs `ω ≤ 255` in `StdParams` (checked `usize` arithmetic in `sig_len`; 80/55/75 for 44/65/87).
- **E-3 (2026-10-29): rejection loops have no provable bound.** Verify runs RejNTTPoly (on ρ from pk) and
  SampleInBall (on c̃ from σ) on attacker-chosen seeds; their termination is probabilistic. The Verify theorem is
  conditioned on the spec's fuel sufficing (`RejTerm`), not stated for every input unconditionally. Resolved for
  every input by partial correctness plus panic-freedom: Verify c9f6663, KeyGen 1be1625, Sign 0074e0c
  (`*_exact` theorems; generic loop lemma by fixpoint induction in `Proofs/Partial.lean`).
- **E-2 (2026-10-29): upstream's `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β.** FIPS 204 Alg 27 does not; Alg 8
  does. Same final verdict; this crate follows FIPS (check in `verify_internal`).

- **E-4 (2026-10-30): Wycheproof `InvalidPrivateKey` vectors.** Six sign vectors (two per set) use an expanded
  secret key whose s1 or s2 has a coefficient outside [−η, η] and expect signing to fail. This crate and the Lean
  spec both sign with them; RustCrypto panics in its decoder. FIPS 204 Algorithm 25 notes that s1 and s2 "may lie
  outside [−η, η] if input is malformed", and Section 7.2 says skDecode should run only on trusted input, so this is
  FIPS-conformant, but it is a hardening gap for callers who load untrusted expanded keys. `tests/wycheproof.rs`
  counts these as `known`. Closing it would add a range check to Sign and a matching ⊥ to the spec. Instead (1e43b4d)
  Sign stays FIPS-literal and `api::sk_is_well_formed_NN` is a separate, proved check callers can run on untrusted
  keys; it agrees with upstream's panic on 200 random mutations per set (`tests/sk_well_formed.rs`).