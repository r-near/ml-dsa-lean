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
  conditioned on the spec's fuel sufficing (`RejTerm`), not stated for every input unconditionally.
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