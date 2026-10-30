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

## Errata (docs, spec, upstream)

- **E-1 (2026-10-29): "Verify for all byte strings" needs length hypotheses.** The core decoders index slices
  directly, so `verify_internal` panics on wrong-length slices. The theorem is stated for `pk.len = pk_len p` and
  `σ.len = sig_len p`; the API's fixed-size arrays discharge this. (FORK-DESIGN §4 wording predates this.)
- **E-3 (2026-10-29): rejection loops have no provable bound.** Verify runs RejNTTPoly (on ρ from pk) and
  SampleInBall (on c̃ from σ) on attacker-chosen seeds; their termination is probabilistic. The Verify theorem is
  conditioned on the spec's fuel sufficing (`RejTerm`), not stated for every input unconditionally.
- **E-2 (2026-10-29): upstream's `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β.** FIPS 204 Alg 27 does not; Alg 8
  does. Same final verdict; this crate follows FIPS (check in `verify_internal`).
