# xspec: cross-check of `lean/Spec` against the ocaml-pq Lean transcription

Toolchain: Lean v4.34.0 and Mathlib v4.34.0 (the versions ocaml-pq pins). `lean/` stays on v4.31.0.

## Vendored specification (`xspec/Spec*`)

`xspec/Spec.lean` and `xspec/Spec/*.lean` are byte-identical copies of `lean/Spec.lean` and `lean/Spec/*.lean`
(check with `scripts/xspec/sync-ours.sh`). They compile unmodified under v4.34.0. **Changes made to our
specification for the port: none.**

## The other side

ocaml-pq (`https://github.com/thevilledev/ocaml-pq`), revision `ceeb2782e033148fc2bf773c2053752f7de5a1cd`,
sub-directory `formal/lean`, required as the Lake package `OcamlPq`. Nothing of it is copied or modified.

## Proofs (`xspec/XSpec`)

`import XSpec.<File>`; headline theorems in `xspec/headline-theorems.txt`; gate `scripts/xspec/check-axioms.sh`
(only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`,
`implemented_by` in `xspec/XSpec`). Sections of `lean/Proofs/CorrNTT.lean` and `lean/Proofs/NTTOps.lean`
(the loop-to-`foldl` rewriting) are re-used with two changes: the Lean 4.34 `do` notation orders the loop
state as `(ŵ, m, start)` instead of `(m, start, ŵ)`, and `set!` is unfolded with a local `rfl` lemma.

## Compiled differential (`xspec/XSpecDiff`, `scripts/xspec/`)

Test-only. `XSpecDiff/Shadow.lean` is an executable stand-in for ocaml-pq's top-level algorithms (header lists
every deviation); `Theirs.lean` calls ocaml-pq's functions directly for every leaf except the NTT, whose
original cannot be run compiled (see the header of `Shadow.lean`). `implemented_by` and `unsafe` appear only
there (an XOF cache).

## Differential results (see diff-results.txt)

Clean run: 1,357,949 vector lines (leaves, sweeps over Z_q, ACVP-derived KeyGen/Sign/Verify, random and edge inputs),
both sides evaluated compiled on the build box.  The only differences are 3,303 SKD lines: ocaml-pq's skDecode
returns none when an s1/s2 coefficient is outside [-eta, eta], while FIPS 204 Algorithm 25 (and lean/Spec) has no
such check.  All 600 SKD lines with in-range coefficients agree.  HintBitPack with more than omega ones (HBPX) is
outside Algorithm 20's precondition; ours panics on an out-of-range set! there (default value returned), the 363
lines agree anyway.  `diff-results-sensitivity.txt` is the same comparison with `(r1 - 1) % m` in UseHint changed to
`% (m + 1)` in a throwaway copy: 8,129 lines differ (UH leaf, UH sweeps, VRF/VRI including ACVP expected answers).
