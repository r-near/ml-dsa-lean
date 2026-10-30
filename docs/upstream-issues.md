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

## Charon

- No Charon-specific issues so far, separate from the Aeneas items above. U-3 to U-5 may involve Charon; check
  where each is triggered before filing.

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
