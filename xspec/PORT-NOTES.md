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

### Codec proofs (`Bits`, `EncBits`, `Pack`, `HintModel`, `Hint`, `Keys`, `Sig`)

Re-used from `lean/Proofs` (the Aeneas parts stripped, loop state re-ordered for Lean 4.34, where a `do` loop
state is a `Prod` in declaration order and the early-return state is `Option R x B` instead of the reversed `MProd`):
`EncodeBits.lean` -> `EncBits.lean` (closed forms of `IntegerToBits`, `BytesToBits`, `BitsToBytes`, `BitPack`/`BitUnpack`
getters, `pkEncode`/`skEncode`/`w1Encode`, and the `skDecode`/`pkDecode` region lemmas); the hint model of
`Proofs/Hint.lean` -> `HintModel.lean` (`unpackModel`, `packModel`, `hintWeight`); `Proofs/SigCodec.lean` (`sigEncode_eq`,
`sigZ`, `sigZ_get`, the `sigDecode` flattening) -> `Sig.lean`. The rest (`Bits`, `Pack`, `Hint`, `Keys`, and the
ocaml-pq side of `Sig`) is new.

Preconditions and exact characterizations:

* `hintBitPack_eq` needs `HintWeight H <= omega` (the precondition of Algorithm 20); `hintBitUnpack_eq` holds for
  every input, including the `none` cases.
* `sigEncode_eq` needs `HintWeight h <= omega`. `sigDecode_eq` holds for every byte string (neither side checks the
  length; `hintBitUnpack_take` shows that ocaml-pq's `hintBitUnpack` on the whole tail equals ours on the
  `omega + k` byte slice).
* `skDecode_eq` characterizes ocaml-pq's `decodeSk`: `some (...)` exactly when `|sk| = skLen` and the decoded
  `s1`, `s2` lie in `[-eta, eta]` (`SkInRange`), with all six components equal to ours; `none` otherwise. Ours
  never rejects, so the equivalence is on in-range keys and the out-of-range case is fully described by `none`.
* Statements about `pkEncode`/`pkDecode`/`skEncode`/`w1Encode` assume `Std3 p` (one of the three standardized
  parameter sets), which gives `d = 13` and `omega < 256`.

### Hashing, samplers (`Hash`, `Samplers`)

ocaml-pq's `MLDSAAlg` takes SHAKE as an abstract `XOF`.  `Hash.lean` instantiates it with our SHAKE through
ocaml-pq's own `keccakXOF` (`oursShake128`, `oursShake256`; `*_squeeze`, `*_val`, `G_eq`, `H_eq`), so every
statement below is about ocaml-pq's algorithms instantiated with our hash.  **Not proved:** `oursShake* =
ocamlShake*` (equality of the two Keccak-f[1600] transcriptions); that is a separate theorem about Keccak.

`Samplers.lean` ports from `lean/Proofs/SampleA.lean` (`stepA`, `rej_unfold`, `rej_loop`, `stA`, `rej_eq_some`) and
`lean/Proofs/SampleS.lean` (`rbStep`, `rbRun`, `RejBoundedPoly_eq_forIn`, `forIn_rbBody`, `RejBoundedPoly_eq`);
the Lean 4.34 loop state is `(early-return flag, a, j, ctx)`.  Lean 4.34 would not prove `rej_unfold` by `rfl`
against a hand-written `forIn` body (different matcher constants), so the real loop body and tail are obtained by
unification (`obtain ⟨f, k, ...⟩ : ∃ f k, ...`) and shown equal to the model pointwise with `rcases`/`simp`.  The fuel
lemmas `RejNTTPoly_mono` etc. of `Partial*.lean` were *not* needed: the bridge compares the two loops directly, and
ocaml-pq's own `rejNTTPolyLoop_mono` is available for the fuel direction.

Sampler bridge statements (`F` is our fuel; ocaml-pq's `…Returns` has an existential fuel):

* `RN.rejNTT_ours_to_theirs : RejNTTPoly F ρ = some a → RejNTTPolyReturns (oursShake128 (u8ToBytes ρ)) (canon a)`
  (ocaml-pq's fuel is `F + 1`: one extra call observes `j = 256`).
* `RN.rejNTT_theirs_to_ours : RejNTTPolyReturns (oursShake128 (u8ToBytes ρ)) b → ∃ F a, RejNTTPoly F ρ = some a ∧ canon a = b`.
* `RB.rejBounded_ours_to_theirs`, `RB.rejBounded_theirs_to_ours`: the same for `RejBoundedPoly` and
  `RejBoundedReturns p.η (oursShake256 (u8ToBytes ρ))`, with `rfn a` in place of `canon a`.
* `expandMask_eq`: `ExpandMask` is total in both, so it is a plain equality (entry `r < ℓ`).

Remaining (not done): `SampleInBall`, the `ExpandA`/`ExpandS` wrappers (nested `forIn` in `Option`; the plan is to
port `forIn_opt`/`expandA_eq` and apply `forIn_opt` to the real loop bodies by unification), `KeyGen_internal`,
`Sign_internal` (our `Sign_internal_bounded` κ budget against ocaml-pq's 821-iteration bound), `Verify_internal`
and the external `KeyGen`/`Sign`/`Verify` with context, and the Keccak equality above.

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
