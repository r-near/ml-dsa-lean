# Upstream issues log

Problems and observations in third-party tools and libraries, found while building and checking this crate. The
orchestrating agent appends entries as work lands. A separate thread triages and files them. Nothing in this file
has been reported upstream unless its **Status** says so, and filing anything needs the user's approval.

Entry format: id, date found, project and version, what happens, minimal trigger or reproducer, impact on us,
workaround, evidence (files or commits in this repo), and status: `open` (not reported), `drafted`, `filed <link>`,
`not a bug` or `wontfix`.

Keep personal information (names, emails, usernames, home-directory paths) out of entries and out of anything
filed.

## Toolchain pins

Charon nightly-2026.09.02, Aeneas build-183e4f0, cargo-hax 0.4.2, Rust nightly-2026-08-18 (extraction),
Lean v4.31.0 with Mathlib. Extraction is generic (no `--monomorphize`), uses `RUSTFLAGS=--cfg miri`, and runs with
no default features. See `scripts/extract.py` and `scripts/setup-tools.sh`.

## Aeneas

- **U-1 (2026-10-29): `return` inside a loop, followed by a second loop in the same function, drops the body.**
  Aeneas reports "Breaks to outer loops are not supported yet" even for a single-level loop, and the function then
  appears as an external axiom instead of a definition. Trigger: a `while` loop containing `return` (an early exit),
  followed by another `while` loop in the same function. Impact: the axiom gate catches it, but the generated Lean
  changes shape silently. Workaround: one returning loop per function, as the last statement before a plain tail
  value (`hint_bit_unpack_rows` / `_row` / `_padding` in `src/encode.rs`). Same family as U-3. Evidence: ISSUES.md
  T-2. Status: open. A minimal reproducer still needs to be written.
- **U-2 (2026-10-29): log tags are colored, so `[Error]` can't be grepped.** Aeneas prints
  `[\x1b[91mError\x1b[39m ]`, so a substring check for `[Error]` never matches and errors show only through the exit
  code. Impact: CI gates that grep logs can silently pass. Workaround: strip ANSI escapes (`scripts/extract.py`).
  Evidence: ISSUES.md T-1. Status: open. It may be intended; a `--no-color` option or a color check based on
  whether output is a terminal (isatty) would fix it.
- **U-3 (earlier campaign, before this repo): a nested loop that reads data the outer loop just wrote fails.**
  Workaround: lift the inner loop into its own function. Evidence: the campaign's BLOCKERS notes (B-F1, outside
  this repo); avoided here by design. Status: open (check whether the campaign reported it).
- **U-4 (earlier campaign): `for` ranges pull in `Step` axioms.** Workaround: `while` loops only. Evidence: B-F2 in
  the campaign notes. Status: open (check the campaign).
- **U-5 (earlier campaign): `--monomorphize` adds unmodeled index axioms.** Workaround: generic extraction.
  Evidence: B-X3 in the campaign notes. Status: open (check the campaign).
- **U-6 (2026-10-30): dead-code pruning changes the generated module.** Probably not a bug. When the only call
  site of `field::neg` was removed (a mutation-testing variant), Aeneas dropped `field.neg` entirely, which broke an
  unrelated proof by changing the module's shape. This is expected behavior, but it makes proofs brittle under
  refactoring. An option to keep all `pub(crate)` items would help. Evidence: STATUS.md, proof mutation testing row
  (M28). Status: not a bug, possible feature request.
- **U-7 (2026-10-31): no model for `u64::from_le_bytes` / `to_le_bytes`.** The lane-wise sponge assembles lanes
  with shifts instead, because the conversion isn't modeled (reported by the agent that wrote it; not yet checked
  against the Aeneas standard library at the pin). Impact: slightly less idiomatic Rust in `src/keccak.rs`
  (`load_lane`, `store_lane`). Status: open (check first; possibly a small library contribution).
- **U-8 (2026-10-31): `core::arch` intrinsics extract as one opaque axiom each.** For example
  `core.core_arch.x86.avx2._mm256_add_epi32`. Expected behavior, not a bug. SymCrypt's verified branch avoids it by
  redirecting the names to Rust shims over lane arrays. A shared, tested model library for common AVX2/NEON
  intrinsics would help every Aeneas user doing SIMD. Evidence: `experiments/simd/README.md`. Status: not a bug,
  possible feature request.

## Charon

- U-3 to U-5 may involve Charon; check where each is triggered before filing.
- **U-10 (2026-10-31): raw-pointer casts between non-literal pointee types fail.** Loading through
  `ptr as *const __m256i` (from an `[i32; 8]` or `[u32]` pointer) makes Charon error with "Raw ptr casts are only
  supported between pointers to literal types". Impact: SIMD loads and stores can't be extracted as written; the
  SIMD study used value-level shims instead. Evidence: `experiments/simd/README.md`, `experiments/simd/evidence/`.
  Status: open (probably a known limitation; check the tracker).

## RustCrypto `ml-dsa` (rev a3690c4)

Do not put details of any undisclosed RustCrypto security advisory in this file. Those go through private
disclosure only.

- **U-20 (2026-10-30): `ExpandedSigningKey::from_expanded` panics on s1/s2 coefficients outside [−η, η].** This is
  documented upstream ("can potentially panic if keys are malformed"), FIPS 204 leaves the case undefined
  (Alg 25), and the expanded-key API is deprecated. Possible contribution: a fallible constructor or a validity
  check (compare our `sk_is_well_formed_NN`). Evidence: ISSUES.md E-4, `fuzz/` decode_roundtrip,
  `tests/sk_well_formed.rs`. Status: open, low value.
- **U-21 (2026-10-30): boundary tests that may be missing upstream.** Our mutation testing found four edge cases our
  own suite missed: a c̃ differing only in its last byte (λ/4-byte compare), a hint count byte above ω, ‖z‖∞ exactly
  γ1 − β, and the `infinity_norm` threshold at (q−1)/2. Check whether upstream's tests cover them before offering.
  Evidence: `tests/mutants.rs`, STATUS.md mutation row. Status: open (unchecked).
- **U-22 (2026-10-29): `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β.** FIPS 204 Alg 27 doesn't; Alg 8 does. The
  final verdict is the same. Not a bug. Evidence: ISSUES.md E-2. Status: not a bug.

## Other projects (observations, mostly not bugs)

- **U-30 (2026-10-30): VCVio `MLDSA.Concrete` HintBitPack with more than ω ones.** Theirs skips writes past ω while
  the counts keep incrementing; ours overwrites the count byte and then indexes out of bounds. Both are outside
  Alg 20's precondition. Not a bug. Evidence: STATUS.md VCVio row, `scripts/diff-vcvio/`. Status: not a bug.
- **U-31 (2026-10-30): VCVio's compiled NTT runs `@[implemented_by]` loop kernels whose equivalence to the structural
  definitions is unproved (their own comment).** We checked equivalence on 600 vectors. Possible contribution: the
  test, or a proof. Status: open (informational).
- **U-32 (2026-10-30): cargo-checkct stubs `cpuid` to report no CPU features.** Runtime-dispatched SIMD paths are
  never explored. A documentation or design note, not a bug. Evidence: `docs/object-code-assurance.md`.
  Status: not a bug (document it).
- **U-33 (2026-10-30): libcrux-ml-dsa CI runs F* with `--admit`; the full-proof job is commented out.** This is an
  observation from their public repo, not something we found with our tools. Evidence:
  `docs/verified-ml-dsa-landscape.md`. Status: informational only, not ours to file.

## BINSEC and cargo-checkct

- **U-40 (2026-10-30): BINSEC 0.11.3 can't lift some AArch64 NEON and x86_64 SSE instructions.** AArch64 `umax`
  and `umin` (vector) stop 11 of our probes at the first such instruction, and x86_64 `movmskpd` stops
  `sk_is_well_formed` under fat LTO with vectorization on. The result is `unknown`, not a wrong verdict. Impact: the
  production NEON build can't be checked. Workaround: build without NEON (`NONEON=1`) or vectorization for analysis.
  Evidence: `checkct/README.md`, `checkct/aarch64.sh`. Status: open; check BINSEC's issue tracker first.
- **U-42 (2026-11-01): BINSEC AArch64 runs stall in a single solver query.** With NEON off, 11 probes
  (`compute_t_44`, `prepare_sk_*`, `signing_key_*`, the censuses) end `unknown` with one pending path, and the
  visited-instruction count is identical at 300, 600, 3600 and 7200 s. `compute_t_44` finished `secure` on the older
  NTT code shape. It looks like one solver query that never returns. Possible report: a reproducer with the probe's
  BINSEC script and binary, and whether a solver timeout option exists. Evidence: `checkct/README.md` "Full sweep at
  e9a1c74". Status: open (needs a minimal reproducer).
- **U-43 (2026-11-03): cargo-checkct drops `RUSTUP_TOOLCHAIN`.** It clears the variable before building the driver
  (`src/run.rs:263` in the version we use), so a toolchain override through the environment is silently ignored and
  the driver is built with the directory's pinned toolchain. Workaround: select the toolchain with a
  `rust-toolchain.toml` and check the driver's `.comment` section (`checkct/run-select.sh`, `nearcore-exact`).
  Status: open (behavior report).
- **U-44 (2026-11-03): BINSEC 0.11.3 can't lift x86_64 `vtestps`.** With nearcore's target features (`+fma` implies
  AVX), LLVM emits VEX `vtestps` for some reductions and BINSEC stops there (`unknown`). Same class as U-40.
  Evidence: `checkct/README.md`, nearcore-exact rewrite experiments. Status: open.
- **U-45 (2026-11-03): BINSEC stalls at overflow-check guards on secret values.** With `overflow-checks = true`, 67
  probes end `unknown` at a conditional jump to the panic thunk after `a + Q - b`, a Montgomery step and similar
  (`checkct/README.md`, stop table). The guards are never taken for in-range inputs, but the analysis does not get
  past them. Possibly expected behavior (the guard's condition is secret-dependent); a small reproducer would settle
  it. Our side: make the arithmetic independent of overflow checks. Status: open (needs a reproducer).
- **U-41 (2026-10-30): cargo-checkct does not support aarch64 targets.** We call BINSEC directly with
  `-isa aarch64` (`checkct/aarch64.sh`). Status: open (feature request).
