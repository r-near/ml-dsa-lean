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

### SampleInBall, ExpandA, ExpandS (`SampleBall`, `Expand`, `Vec`)

* `SB.sampleInBall_ours_to_theirs : SampleInBall p F ρ = some c → SampleInBallReturns p.τ (oursShake256 (u8ToBytes ρ)) (rfn c)`
  and `SB.sampleInBall_theirs_to_ours` (`∃ F0, ∀ F ≥ F0, ∃ c, SampleInBall p F ρ = some c ∧ rfn c = b`).  Fuel: ours at `F`
  is theirs at `F + 1`.  ocaml-pq's `sampleInBall` is total (a default when the sampler does not return), so the
  statements about it carry a termination hypothesis (`SampleInBallReturns`) and "eventually in the fuel".
* `ExpandATerm p ρ` (every `RejNTTPoly` call of ocaml-pq's `ExpandA` returns) and `ExpandSTerm` are the termination
  premises; `expandA_ours_to_theirs` (ours `some A` gives `ExpandATerm` and entrywise `canon A[r][s] = expandA ..`),
  `expandA_theirs_to_ours` (`ExpandATerm` gives `∃ F0, ∀ F ≥ F0, ∃ A, ExpandA p F ρ = some A`), `expandS_*` likewise.
* `Vec.lean`: `matrixVectorNTT_eq` and entrywise lemmas for `NTTVec`, `NTTInvVec`, `+`, `-`.
* Lean 4.34 detail: a `for` loop with early `return` inside `Option` ends in `Break.runK`; the loop state of
  Algorithm 7 is `(early-return flag, κ, (z,h), c̃)` as nested `Prod`.

### KeyGen (`KeyGen`)

`keyGen_ours_to_theirs`, `keyGen_theirs_to_ours` (under `ExpandATerm` and `ExpandSTerm`, for all large fuel),
`keyGen_eq_internal`: `Spec.KeyGen_internal p ξ F = some (pk, sk)` iff ocaml-pq's `keyGenInternal` (with our SHAKE)
gives `(u8ToBytes pk, u8ToBytes sk)`.

### Verify (`Verify`)

`verifyInternal_ours_to_theirs` (`pk`, `σ` of the right length): ours `some b` gives `b = verifyInternal ..`;
`verifyInternal_theirs_to_ours` (under `ExpandATerm` and `SampleInBallReturns` for the decoded `c̃`): eventually in the
fuel, ours returns `some b` with the same `b`.  A wrong length gives `some false` on ours (`verify_of_length_ne`, a
step-0 check absent from ocaml-pq's `verifyInternal`, which is why the length hypotheses are there), a failed
`sigDecode` gives `some false` on both (`verify_of_sigDecode_none`).  External `Verify`: `verify_ours_to_theirs`,
`verify_theirs_to_ours`, and `verify_of_ctx_gt` (`|ctx| > 255` gives `some false` on ours, as in `mldsaVerify`).
Technique: lemmas about an abstract `VerifyFips` bundle (`verifyInternal_of_decode`, `wApproxV`) specialized by `rfl`,
because `rfl` on the concrete bundle hits the maximum recursion depth.

### Sign (`SignModel`, `SignStep`, `Sign`)

* `SignModel.lean`: `Sign_internal_bounded` as a pure function (`pre`, `attemptAt`, `loopRes`, `encodeRes`);
  `SG.Sign_internal_bounded_eq` unfolds Lean 4.34's `do` loop (this is the model of `Proofs/Sign.lean`, part 1, redone
  because the loop state is a `Prod` in a different order).
* `SignStep.lean`: `respond_eq_fipsFinish`, one attempt's rejection tests, `z`, `h` against ocaml-pq's `fipsFinish`
  (`signAttemptSpec`): the norm tests (`N1`-`N3`: `‖v‖∞ ≥ B` against `infNormGe` of the integer lifts, with
  `coeffNorm` depending only on the residue), the hint weight (`N4`), `LowBits`/`MakeHint` against `lowBits`/`makeHintSpec`
  (`lowBits_cast`, `makeHint_cast`).  No range hypothesis on the secret key is needed: everything is a statement
  about residues mod `q`.
* `Sign.lean`: `step_eq` (one attempt of ocaml-pq's `alg7Step` is our `respond`, encoded with `sigEncode_eq`),
  `core_*` (the loop: `alg7Loop_eq`, `loopRes_accept`, `loopRes_none`, `loopRes_accept_of`), and the top level.

Bridging statement.  `keyOfSk sp sk` is ocaml-pq's `ExpandedKey` built from OUR `skDecode` (`ρ`, `K`, `tr`, `s₁`, `s₂`,
`t₀`).  ocaml-pq's `mldsaSign` takes a decoded key, so there is no decoder in the signing statement.
`skDecode_eq` says that on keys of the right length with `s₁`, `s₂` in `[-η, η]` ocaml-pq's decoder returns exactly
these six components (and `keyOfSk_s1/s2/t0` show `keyOfSk` is the `listsToVec` of those lists); on any other key
ocaml-pq's decoder returns `none`, ours does not, and the statements below still hold for the key ours decodes.
`thSignInternal sp sk M' rnd m` is `signInternalMu` with `μ = H(tr ‖ M′)` and `m` iterations, `thSign` is `mldsaSign`
(821 iterations).

* Ours is `Sign_internal_bounded sp B` (at most `B` attempts, `κ = 0, ℓ, 2ℓ, ..`, and `none` if an attempt would need
  `κ + ℓ > 2^16`); `Sign_internal` has `B = kappaBudget sp ∈ {16384, 13107, 9362}`.  ocaml-pq has 821 iterations
  (a proved bound for its own parameter sets).
* `signInternalBounded_ours_to_theirs`: if ours returns `σ`, it accepted at some attempt `a < B`, and for every `m`,
  `thSignInternal .. m = if a < m then some (u8ToBytes σ) else none`.  Hence (`signInternal_ours_to_theirs`,
  `sign_ours_to_theirs`) the two agree iff `a < 821`, and ocaml-pq returns `none` iff `821 ≤ a`: this is the only way
  they differ (our extra attempts beyond 821, which FIPS 204 allows).  No hypothesis other than `Std3`.
* `signInternalBounded_theirs_to_ours` (and `signInternal_theirs_to_ours`, `sign_theirs_to_ours`): if `thSignInternal m`
  returns `s` (`m ≤ B`, `m ℓ ≤ 2^16`; for `Sign` `m = 821`), `ExpandATerm` holds for `ρ`, and `SignTerm` (every
  `SampleInBall` that ocaml-pq's loop reaches, i.e. after only rejected attempts, returns), then eventually in the
  fuel ours returns `σ` with `u8ToBytes σ = s`.  `signInternalBounded_theirs_to_ours_none`/`sign_theirs_to_ours_none`:
  if ocaml-pq's `m` iterations are exhausted, ours with `m` attempts returns `none`.
* `sign_of_ctx_gt_both`: `|ctx| > 255` gives `none` on both sides.
* The termination hypotheses are real: ocaml-pq's `expandA`/`sampleInBall` are total and return a default when
  their rejection loop does not terminate, so without them the statement would be about the default value.
  `SignTerm` is stated in ocaml-pq's terms (`alg7CT`), so it needs no reference to our fuel.

### Remaining

* Keccak: `oursShake* = ocamlShake*` (the two Keccak-f[1600] transcriptions) is not proved; every statement is about
  ocaml-pq's algorithms instantiated with our SHAKE (`oursShake128`, `oursShake256`).
* The termination hypotheses (`ExpandATerm`, `ExpandSTerm`, `SampleInBallReturns`/`SignTerm`) are not discharged; they
  hold for every concrete input of the standard parameter sets (probabilistically) but are not proved to hold always.
* The divergence between ours and ocaml-pq at attempt `a ≥ 821` is characterized, not eliminated.

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
