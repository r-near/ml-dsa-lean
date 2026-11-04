# xspec: cross-check of `lean/Spec` against the ocaml-pq Lean transcription

A separate Lean project that proves `lean/Spec` (our transcription of FIPS 204 and FIPS 202) equal to the independent Lean
transcription in [ocaml-pq](https://github.com/thevilledev/ocaml-pq). It restates what the equivalence covers and what it does not;
`docs/assurance.md` section 1.8 gives the summary.

## How to run

On Linux with elan (the project pins its own Lean toolchain; the first run downloads Mathlib and builds ocaml-pq):

```
bash scripts/xspec/setup.sh            # lake dependencies, Mathlib cache, builds Spec and OcamlPq
bash scripts/xspec/build.sh XSpec      # builds the equivalence proofs
bash scripts/xspec/check-axioms.sh     # the axiom gate over xspec/headline-theorems.txt (144 names)
bash scripts/xspec/run-diff.sh all     # compiled differential, executable check (results: diff-results.txt)
bash scripts/xspec/sync-ours.sh        # checks that the vendored Spec is byte-identical to lean/Spec
```

`scripts/xspec/env.sh` keeps the Lake dependencies in `$XSPEC_WORK` (default `~/xspec-work`) so that several checkouts share one
Mathlib build.

## Attribution

ocaml-pq is by its authors and licensed under the ISC license. This project depends on it as the Lake package `OcamlPq`, pinned to
revision `ceeb2782e033148fc2bf773c2053752f7de5a1cd` (`formal/lean`); no file of it is copied into this repository. The executable
stand-in in `XSpecDiff/Shadow.lean` follows ocaml-pq's definitions step by step (its header lists every deviation) and calls its
functions directly; that file and the proofs in `XSpec/` refer to ocaml-pq's definitions and theorem names throughout.

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
statement below is first about ocaml-pq's algorithms instantiated with our hash.  `oursShake* = ocamlShake*`
(our Keccak against ocaml-pq's independent Keccak) is proved in `KeccakPerm`/`KeccakSponge`/`Shake` (section
"Keccak" below), and `Shake.lean` restates the top-level theorems on ocaml-pq's own SHAKE, except `verify_of_ctx_gt_both` and
`verify_of_sigDecode_none_both`, which hold for any XOF and are stated with `oursShake*` only.

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

The equivalence is the pair `keyGen_ours_to_theirs` / `keyGen_theirs_to_ours`: if `Spec.KeyGen_internal p ξ F =
some (pk, sk)` then the sampler calls of ocaml-pq's `keyGenInternal` terminate (`ExpandATerm`, `ExpandSTerm`) and its
output (with our SHAKE) is `(u8ToBytes pk, u8ToBytes sk)`; conversely, under `ExpandATerm` and `ExpandSTerm`, ours
returns for every large enough fuel with the same bytes.  The premises `ExpandATerm`/`ExpandSTerm` are stated on slices
of OUR seed expansion `KG.seed p ξ` (computed with our hash); `hseed` in the proof shows that, as bytes, it is
ocaml-pq's `oursShake256.squeeze (ξ ‖ k ‖ ℓ) 128`, so the premises are about the seeds ocaml-pq uses.
`keyGen_eq_internal` is only `KeyGen = KeyGen_internal` (`rfl`, Algorithm 1 step 5), so both theorems apply to `KeyGen`.

### Verify (`Verify`)

`verifyInternal_ours_to_theirs` (`pk`, `σ` of the right length): ours `some b` gives `b = verifyInternal ..`;
`verifyInternal_theirs_to_ours` (under `ExpandATerm` and `SampleInBallReturns` for the decoded `c̃`): eventually in the
fuel, ours returns `some b` with the same `b`.  A wrong length gives `some false` on ours (`verify_of_length_ne`, a
step-0 check absent from ocaml-pq's `verifyInternal`, which is why the length hypotheses are there), a failed
`sigDecode` gives `some false` on ours (`verify_of_sigDecode_none`) and `false` on theirs (`verifyInternal_of_none`,
`fipsSigDecode_none`); both are in `verify_of_sigDecode_none_both`.  External `Verify`: `verify_ours_to_theirs`,
`verify_theirs_to_ours`, and `verify_of_ctx_gt_both` (`|ctx| > 255` gives `some false` on ours and `false` on theirs).
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
`t₀`).  ocaml-pq's `mldsaSign` takes a decoded key, so there is no decoder in the signing statement.  The composition
with their decoder is `keyOfSk_of_decode`: if their `decodeSk` on `bytesN sk` returns `some (ρ, K, tr, s₁, s₂, t₀)`, the
`ExpandedKey` `⟨natToBytes ρ, natToBytes K, natToBytes tr, listsToVec s₁, listsToVec s₂, listsToVec t₀⟩` (the shape in
their `decodeSk_secretsInRange`) equals `keyOfSk sp sk` in all six fields, and `thSign_of_decode` restates `thSign` as
`mldsaSign` on that key.  `skDecode_eq` says their decoder accepts exactly the keys of the right length with `s₁`, `s₂`
in `[-η, η]`; on any other key their decoder returns `none`, ours does not, and the statements below still hold for the
key ours decodes.  (`keyOfSk_s1/s2/t0` are unconditional identities used in the proof.)

Two further checks of ocaml-pq's key import are not modeled by ours or by FIPS 204.  `buildSigningKey`
(`MLDSAAlg/KeyGen.lean`; `EndToEnd/MLDSA/KeyImport.lean`, `buildSigningKey_e2e`) rejects a key whose `tr` or `t0`
is inconsistent with `(ρ, K, s₁, s₂)` (`tr = H(pkEncode(ρ, t₁), 64)` and `t₀` the low part of
`Power2Round(A s₁ + s₂)`); FIPS 204's `Sign_internal` (and ours) does not check this.  For such an inconsistent key
`thSign` is ocaml-pq's spec-level `mldsaSign` applied to our decoded key, NOT what ocaml-pq's import API
would return (that API returns an error).  The signing theorems say nothing about the import API on such keys.
`thSignInternal sp sk M' rnd m` is `signInternalMu` with `μ = H(tr ‖ M′)` and `m` iterations, `thSign` is `mldsaSign`
(821 iterations).

* Ours is `Sign_internal_bounded sp B` (at most `B` attempts, `κ = 0, ℓ, 2ℓ, ..`, and `none` if an attempt would need
  `κ + ℓ > 2^16`); `Sign_internal` has `B = kappaBudget sp ∈ {16384, 13107, 9362}`.  ocaml-pq's `signInternalMu`/`mldsaSign` run
  821 iterations.  ocaml-pq proves only the arithmetic `loop_bound_821 : 41^821 * 2^258 < 51^821`; under an assumed
  per-attempt success probability of at least `1/5.1` that bounds the failure probability of 821 iterations below
  `2^-258`.  It is a probabilistic argument about a fixed cut-off, not a proved bound on the number of iterations.
* `signInternalBounded_ours_to_theirs`: if ours returns `σ`, it accepted at some attempt `a < B`, and for every `m`,
  `thSignInternal .. m = if a < m then some (u8ToBytes σ) else none`.  Hence (`signInternal_ours_to_theirs`,
  `sign_ours_to_theirs`) the two agree iff `a < 821`, and ocaml-pq returns `none` iff `821 ≤ a`.  So, WHEN OURS
  RETURNS `some`, our attempts beyond 821 (which FIPS 204 allows) are the only way the two differ.  No hypothesis other
  than `Std3`.  When ours returns `none` the two can also differ for two other reasons: the fuel (the default fuel
  of 512 is not covered by any theorem; ours returns `none` when `ExpandA` or a `SampleInBall` runs out of fuel,
  where ocaml-pq's total functions return something), and the guard `κ + ℓ > 2^16` of `Sign_internal_bounded`
  (only reachable for `B > kappaBudget`; ruled out for `Sign_internal` and for `m ≤ 821`).  The theirs-to-ours theorems
  say what is true in those cases (eventually in the fuel, under the termination hypotheses).
* `signInternalBounded_theirs_to_ours` (and `signInternal_theirs_to_ours`, `sign_theirs_to_ours`): if `thSignInternal m`
  returns `s` (`m ≤ B`, `m ℓ ≤ 2^16`; for `Sign` `m = 821`), `ExpandATerm` holds for `ρ`, and `SignTerm` (every
  `SampleInBall` that ocaml-pq's loop reaches, i.e. after only rejected attempts, returns), then eventually in the
  fuel ours returns `σ` with `u8ToBytes σ = s`.  `signInternalBounded_theirs_to_ours_none`/`sign_theirs_to_ours_none`:
  if ocaml-pq's `m` iterations are exhausted, ours with `m` attempts returns `none`.
* `sign_of_ctx_gt_both`: `|ctx| > 255` gives `none` on both sides.
* The termination hypotheses are real: ocaml-pq's `expandA`/`sampleInBall` are total and return a default when
  their rejection loop does not terminate, so without them the statement would be about the default value.
  `SignTerm` is stated in ocaml-pq's terms (`alg7CT`), so it needs no reference to our fuel.  It is not an extra
  assumption when ours succeeds: `signTerm_of_ours` (and `_internal`, `_sign`) derive `ExpandATerm` and
  `SignTerm sp sk M' rnd m` for every `m` from `Sign_internal_bounded sp B sk M' rnd F = some σ`.

### Keccak (`KeccakPerm`, `KeccakSponge`, `KeccakKAT`, `Shake`)

What ocaml-pq has (all under `formal/lean/OcamlPq/Hash/`, revision ceeb278): (1) `KeccakSpec.lean`, `FIPS202`: an
independent transcription of FIPS 202 on bit strings (the state array `A[x, y, z]`, θ ρ π χ ι with the `rc` LFSR,
`KeccakP`/`KeccakF`, `pad10*1`, `sponge`, `SHAKE128`/`SHAKE256`, written from the standard); (2) `KeccakModel.lean`: a
literal transcription of the OCaml `lib/keccak.ml` (`Keccak.permute`, `sponge`, `shake128`, `shake256` on `BitVec 64`
lanes), proved equal to (1) for all inputs (`permute_eq_KeccakF`, `shake128_eq`, `shake256_eq`).  `Hash.lean`
imports both; `EndToEnd/MLDSA/Shake.lean` builds `ocamlShake128/256` from (2) and `fipsShake128/256` from (1) and
proves `fipsShake* = ocamlShake*`.  Our side (`Spec/Keccak.lean`) is a lane-level `UInt64` permutation and a byte-level
sponge; it shares no code with either.

* `KeccakPerm.lean`: one round and the permutation, bit by bit.  `toArr` reads our `Vector UInt64 25` as ocaml-pq's
  `Array (BitVec 64)` so that their `laneBits`, `toState`, `rho_eq`, `roundConstants_eq_RC` apply; `theta_eq`, `rho_eq`,
  `pi_eq`, `chi_eq`, `iota_eq`, `rnd_eq` (round by round, lane by lane, for `ir < 24`), `rhoOffsets_eq_rotation` and
  `RCs_eq_roundConstants` (kernel checks over the 25 offsets and the 24 round constants), and
  `keccakF_eq : laneBits (toArr (KeccakF1600 A)) = FIPS202.KeccakF (laneBits (toArr A))` for every state.
* `KeccakSponge.lean`: `sponge_bits`, for every message `M`, output length `d` and rate `0 < r ≤ 200` bytes:
  `bytesToBits (Spec.Keccak.sponge r M d) = FIPS202.sponge KeccakF pad101 (8 r) (bytesToBits M ++ 1111) (8 d)`
  (ocaml-pq's transcription of Algorithm 8).  Pieces: `bitsOf_xorBlock`, `bitsOf_absorb`, `pad101_eq` (our padded
  message is the full blocks followed by ocaml-pq's `tailBlock r 0x1f M`, so their `padded_block_full` and
  `padded_block_last` apply), `bitsOf_absorb_pad`, `squeeze_getElem`, `bytesToBits_squeeze`, and ocaml-pq's
  `squeeze_spec`.  Instances `shake128_bits`, `shake256_bits` (rates 168 and 136), then, with ocaml-pq's `shake128_eq` /
  `shake256_eq` and the injectivity of `bytesToBits`, `SHAKE128_eq_ocaml : Spec.SHAKE128 M d = Keccak.shake128 d M` and
  `SHAKE256_eq_ocaml`, equality of byte lists with the model of `Mldsa_keccak.shake128/256`.
* `Shake.lean`: `oursShake128 = ocamlShake128 = fipsShake128` and likewise for 256 (so also `Hash.lean`'s `G_eq`, `H_eq`
  and every statement through it); the top-level theorems restated on `ocamlShake*`: `keyGen_*_ocaml`,
  `verifyInternal_*_ocaml`, `verify_*_ocaml`, `SGB.sign*_ocaml`, `SGB.signTerm_of_ours*_ocaml`, `SGB.thSign_of_decode_ocaml` (not restated: `verify_of_ctx_gt_both` and
  `verify_of_sigDecode_none_both`, true for any XOF). The `keyGen_*_ocaml` premises still name `KG.seed`, which is
  computed with our `Spec.H` (docstring in `Shake.lean`).
  The termination predicates have `O` versions (`ExpandATermO`, `ExpandSTermO`, `SGB.SignTermO`; the `*_iff` lemmas show
  they are propositionally the original ones) and `SGB.thSignO`, `SGB.thSignInternalO`.  Hypotheses of the
  Keccak theorems: `0 < r`, `r ≤ 200` (satisfied by 168 and 136); the restated theorems carry exactly the hypotheses of
  the originals.
* `KeccakKAT.lean`: kernel evaluation of `Spec.SHAKE128 [] 32` and `Spec.SHAKE256 [] 32` against the NIST digests.  These
  are tests of the executable definitions only; ocaml-pq proves the same two digests for its transcription
  (`Hash/KAT.lean`).

Not covered by the Keccak theorems: the byte/bit conventions are those of FIPS 202 Appendix B.1 as transcribed by
ocaml-pq (`FIPS202.bytesToBits`, least significant bit first), the same convention that FIPS 204 uses; the equivalence
is therefore only as independent as ocaml-pq's `FIPS202` transcription is of ours, and ocaml-pq's published-digest
tests (`KAT.lean`) are the external anchor for it.

### Remaining

* The termination hypotheses (`ExpandATerm`, `ExpandSTerm`, `SampleInBallReturns`/`SignTerm`) are not discharged:
  there is no input-independent proof that the rejection samplers terminate.  For a given input they can be checked
  (by running ocaml-pq's samplers or ours with enough fuel).  More importantly, the ours-to-theirs theorems derive them
  whenever ours returns (`expandA_ours_to_theirs`, `sampleInBall_ours_to_theirs`, `keyGen_ours_to_theirs`,
  `signTerm_of_ours`, `verifyInternal_ours_to_theirs`), so they are needed only to conclude that ours returns.
* The divergence between ours and ocaml-pq at attempt `a ≥ 821` is characterized, not eliminated.

## Compiled differential (`xspec/XSpecDiff`, `scripts/xspec/`)

Test-only. `XSpecDiff/Shadow.lean` is an executable stand-in for ocaml-pq's top-level algorithms (header lists
every deviation); `Theirs.lean` calls ocaml-pq's functions directly for every leaf except the NTT, whose
original cannot be run compiled (see the header of `Shadow.lean`). `implemented_by` and `unsafe` appear only
there (an XOF cache).

## Differential results (see diff-results.txt)

Clean run: 1,357,949 vector lines (leaves, sweeps over Z_q, ACVP-derived KeyGen/Sign/Verify, random and edge inputs),
both sides evaluated compiled on a Linux machine.  The only differences are 3,303 SKD lines: ocaml-pq's skDecode
returns none when an s1/s2 coefficient is outside [-eta, eta], while FIPS 204 Algorithm 25 (and lean/Spec) has no
such check.  All 600 SKD lines with in-range coefficients agree.  HintBitPack with more than omega ones (HBPX) is
outside Algorithm 20's precondition; ours panics on an out-of-range set! there (default value returned), the 363
lines agree anyway.  `diff-results-sensitivity.txt` is the same comparison with `(r1 - 1) % m` in UseHint changed to
`% (m + 1)` in a throwaway copy: 8,129 lines differ (UH leaf, UH sweeps, VRF/VRI including ACVP expected answers).
