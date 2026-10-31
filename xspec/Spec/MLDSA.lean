import Spec.Sampling
import Spec.Rounding
import Spec.NTTOps

/-!
# FIPS 204, Sections 5 and 6: ML-DSA key generation, signing and verification (Algorithms 1-3, 6-8)

Everything below is parameterized by a `Params` value `p` (`ML_DSA_44`, `ML_DSA_65`, `ML_DSA_87`).

## Where this differs from the pseudocode, and why

* **Randomness is an argument.** `KeyGen` takes the seed `ξ` and `Sign` the value `rnd` (the standard draws them
  from an RBG in steps 1 and 5; "RBG failure" is not modeled). For the deterministic variant of `Sign`, pass
  `rnd = 0^32` (`List.replicate 32 0`).
* **Messages are byte strings.** FIPS 204 lets `M` and `M′` be bit strings. Here they are `List UInt8`;
  `BytesToBits(x) ‖ M` of Algorithms 2 and 3 is then just the byte concatenation, and `H(BytesToBits(tr) ‖ M′, 64)`
  of Algorithms 7 and 8 (Section 3.7: `SHAKE256(BytesToBits(str), 8ℓ) = SHAKE256(str, 8ℓ)`) is `H (tr ++ M′) 64`.
* **Rejection sampling is fuel-bounded.** `ExpandA`, `ExpandS` and `SampleInBall` return `Option` (see
  `Spec/Sampling.lean`), so `KeyGen_internal`, `Sign_internal_bounded` and `Verify_internal` do too: `none`
  means that one of those loops ran out of its fuel `F`, an event the standard does not have.
* **Algorithm 7's loop is bounded** (`Sign_internal_bounded`), see below.
* **Algorithm 3 returns `false` rather than `⊥` for `|ctx| > 255`** (NIST's list of errata to FIPS 204: "Algorithm 3
  step 2 should return `false`, not `⊥`"). `Verify` and `Verify_internal` return `Option Bool`, `none` being
  the fuel exhaustion above.
* **`Verify_internal` checks the lengths of `pk` and `σ`** (Section 6.3: "If an implementation of
  ML-DSA.Verify_internal can accept inputs for σ or pk of any other length, it shall return false"). That is
  prose, not a numbered step; it is written as step 0.
* Coercions that the pseudocode leaves implicit are explicit: `R → R_q` is `RPoly.toZq`; `z mod± q` is
  `Poly.modPM`.
* `NTT(v)` for a vector is `NTTVec v` (componentwise), `NTT⁻¹` likewise.

## The bound on Algorithm 7's loop

Algorithm 7 is `while (z, h) = ⊥ do ... κ ← κ + ℓ`, which has no bound. `Sign_internal_bounded p B` makes at
most `B` attempts, with `κ = 0, ℓ, 2ℓ, ..., (B − 1) ℓ`, and returns `none` when none of them is accepted (FIPS 204
Section 6.2, footnote 10 / Appendix C allow an implementation to bound the number of iterations). If the
FIPS 204 loop accepts at its attempt number `a ≤ kappaBudget p` (counting from 1), and no sampler runs out of fuel
in attempts `1..a` (a `SampleInBall` fuel exhaustion in a rejected attempt also gives `none`), then
`Sign_internal_bounded p B` returns the same signature for every `B ≥ a`, and `none` for `B < a` (this relation is
the reading of the code, not a theorem proved here).

`ExpandMask` encodes `κ + r` (for `r < ℓ`) with `IntegerToBytes(·, 2)`, i.e. modulo `2^16`. The standard never
discusses `κ ≥ 2^16`; the loop here therefore refuses (returns `none`) to start an attempt with `κ + ℓ > 2^16`.
`kappaBudget p = ⌊(2^16 − ℓ) / ℓ⌋ + 1` is the number of attempts for which that never happens (16384, 13107 and
9362 for ℓ = 4, 5, 7), and `Sign_internal` is `Sign_internal_bounded` with that `B`.
-/

namespace Spec

/-- Algorithm 6: ML-DSA.KeyGen_internal(ξ). Generates a public-private key pair from the seed `ξ ∈ 𝔹^32`;
returns `(pk, sk)`. -/
def KeyGen_internal (p : Params) (ξ : List UInt8) (F : Fuel := {}) : Option (List UInt8 × List UInt8) := Id.run do
  let out := H (ξ ++ IntegerToBytes p.k 1 ++ IntegerToBytes p.ℓ 1) 128    -- 1: expand seed
  let ρ := slice out 0 32                                   --    (ρ, ρ′, K) ∈ 𝔹^32 × 𝔹^64 × 𝔹^32
  let ρ' := slice out 32 64
  let K := slice out 96 32
  let some Â := ExpandA p F.rejNTT ρ | return none           -- 3
  let some (s₁, s₂) := ExpandS p F.rejBounded ρ' | return none    -- 4
  let ŝ₁ := NTTVec (s₁.map RPoly.toZq)
  let t := NTTInvVec (MatrixVectorNTT Â ŝ₁) + s₂.map RPoly.toZq    -- 5: t = A s₁ + s₂
  let (t₁, t₀) := Power2RoundVec p t                        -- 6
  let pk := pkEncode p ρ t₁                                 -- 8
  let tr := H pk 64                                         -- 9
  let sk := skEncode p ρ K tr s₁ s₂ t₀                      -- 10
  return some (pk, sk)                                      -- 11

/-- Algorithm 1: ML-DSA.KeyGen(). Generates a key pair. The random seed `ξ ← 𝔹^32` of step 1 is the argument
`ξ` (the RBG is the caller's job; step 2-4, the RBG failure check, is not modeled). -/
def KeyGen (p : Params) (ξ : List UInt8) (F : Fuel := {}) : Option (List UInt8 × List UInt8) :=
  KeyGen_internal p ξ F                                     -- 5: return KeyGen_internal(ξ)

/-- The number of attempts of the signing loop for which `κ + ℓ ≤ 2^16` holds in every attempt:
`⌊(2^16 − ℓ) / ℓ⌋ + 1` (16384, 13107, 9362 for ML-DSA-44, -65, -87). -/
def kappaBudget (p : Params) : Nat := (2 ^ 16 - p.ℓ) / p.ℓ + 1

example : kappaBudget ML_DSA_44 = 16384 ∧ kappaBudget ML_DSA_65 = 13107 ∧ kappaBudget ML_DSA_87 = 9362 := by
  decide +kernel

/-- Algorithm 7: ML-DSA.Sign_internal(sk, M′, rnd), with the rejection sampling loop (steps 10-32) cut off after
`B` attempts. Returns the signature `σ`, or `none` if no attempt was accepted (or a sampler ran out of fuel).
See the module documentation. -/
def Sign_internal_bounded (p : Params) (B : Nat) (sk M' rnd : List UInt8) (F : Fuel := {}) :
    Option (List UInt8) := Id.run do
  let (ρ, K, tr, s₁, s₂, t₀) := skDecode p sk               -- 1
  let ŝ₁ := NTTVec (s₁.map RPoly.toZq)                      -- 2
  let ŝ₂ := NTTVec (s₂.map RPoly.toZq)                      -- 3
  let t₀hat := NTTVec (t₀.map RPoly.toZq)                   -- 4
  let some Â := ExpandA p F.rejNTT ρ | return none          -- 5
  let μ := H (tr ++ M') 64                                  -- 6: message representative
  let ρ'' := H (K ++ rnd ++ μ) 64                           -- 7: private random seed
  let mut κ := 0                                            -- 8
  let mut zh : Option (Vector Poly p.ℓ × Vector HintPoly p.k) := none    -- 9: (z, h) <- ⊥
  let mut c_tilde : List UInt8 := []
  for _ in [0:B] do                                         -- 10: while (z, h) = ⊥ (at most B attempts)
    if zh.isSome then break
    if 2 ^ 16 < κ + p.ℓ then return none                    -- (κ + r must stay below 2^16, see the module doc)
    let y := (ExpandMask p ρ'' κ).map RPoly.toZq            -- 11: y ∈ R_q^ℓ
    let w := NTTInvVec (MatrixVectorNTT Â (NTTVec y))       -- 12
    let w₁ := HighBitsVec p w                               -- 13: signer's commitment
    c_tilde := H (μ ++ w1Encode p w₁) (p.lam / 4)           -- 15: commitment hash
    let some c := SampleInBall p F.sampleInBall c_tilde | return none    -- 16: verifier's challenge
    let ĉ := NTT c.toZq                                     -- 17
    let cs₁ := NTTInvVec (ScalarVectorNTT ĉ ŝ₁)             -- 18: ⟨⟨c s₁⟩⟩
    let cs₂ := NTTInvVec (ScalarVectorNTT ĉ ŝ₂)             -- 19: ⟨⟨c s₂⟩⟩
    let z := y + cs₁                                        -- 20: signer's response
    let r₀ := LowBitsVec p (w - cs₂)                        -- 21
    if ‖z‖∞ ≥ p.γ₁ - p.β ∨ ‖r₀‖∞ ≥ p.γ₂ - p.β then         -- 23: validity checks
      zh := none                                            --     (z, h) <- ⊥
    else
      let ct₀ := NTTInvVec (ScalarVectorNTT ĉ t₀hat)        -- 25: ⟨⟨c t₀⟩⟩
      let h := MakeHintVec p (-ct₀) (w - cs₂ + ct₀)         -- 26: signer's hint
      if ‖ct₀‖∞ ≥ p.γ₂ ∨ HintWeight h > p.ω then            -- 28
        zh := none                                          --     (z, h) <- ⊥
      else
        zh := some (z, h)
    κ := κ + p.ℓ                                            -- 31: increment counter
  let some (z, h) := zh | return none                       -- (the loop gave up)
  let σ := sigEncode p c_tilde (z.map Poly.modPM) h         -- 33: z mod± q
  return some σ                                             -- 34

/-- Algorithm 7 with the loop bounded by `kappaBudget p` attempts: the largest bound for which `κ` stays below
`2^16`. -/
def Sign_internal (p : Params) (sk M' rnd : List UInt8) (F : Fuel := {}) : Option (List UInt8) :=
  Sign_internal_bounded p (kappaBudget p) sk M' rnd F

/-- Algorithm 2: ML-DSA.Sign(sk, M, ctx). Generates a signature for the message `M` (a byte string) and the
context `ctx`. `rnd ∈ 𝔹^32` is the random value of step 5 (`0^32` for the deterministic variant). Returns
`none` for `⊥`: a context of more than 255 bytes (steps 1-3), or no accepted attempt (see `Sign_internal`). -/
def Sign (p : Params) (sk M ctx rnd : List UInt8) (F : Fuel := {}) : Option (List UInt8) := Id.run do
  if ctx.length > 255 then return none                      -- 1-3
  let M' := IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M    -- 10
  return Sign_internal p sk M' rnd F                        -- 11-12

/-- Algorithm 8: ML-DSA.Verify_internal(pk, M′, σ). Returns `some true` iff `σ` is a valid signature of `M′`
under `pk`. `none` means that `ExpandA` or `SampleInBall` ran out of fuel. -/
def Verify_internal (p : Params) (pk M' σ : List UInt8) (F : Fuel := {}) : Option Bool := Id.run do
  if pk.length ≠ p.pkLen ∨ σ.length ≠ p.sigLen then return some false    -- 0 (Section 6.3: wrong lengths)
  let (ρ, t₁) := pkDecode p pk                              -- 1
  let some (c_tilde, z, h) := sigDecode p σ | return some false    -- 2-4: h = ⊥
  let some Â := ExpandA p F.rejNTT ρ | return none          -- 5
  let tr := H pk 64                                         -- 6
  let μ := H (tr ++ M') 64                                  -- 7
  let some c := SampleInBall p F.sampleInBall c_tilde | return none    -- 8
  let zq := z.map RPoly.toZq
  let t₁2d := (t₁.map RPoly.toZq).map (·.map (· * (2 ^ p.d : Zq)))    -- t₁ ⋅ 2^d
  let w'Approx := NTTInvVec (MatrixVectorNTT Â (NTTVec zq) - ScalarVectorNTT (NTT c.toZq) (NTTVec t₁2d))    -- 9
  let w₁' := UseHintVec p h w'Approx                        -- 10
  let c_tilde' := H (μ ++ w1Encode p w₁') (p.lam / 4)       -- 12 (w1Encode is step 11's input encoding)
  return some (decide (‖z‖∞ < p.γ₁ - p.β) && c_tilde == c_tilde')    -- 13

/-- Algorithm 3: ML-DSA.Verify(pk, M, σ, ctx). Verifies a signature `σ` for the message `M` (a byte string) and
the context `ctx`. A context of more than 255 bytes gives `some false` (the FIPS 204 errata change `⊥` to
`false`). -/
def Verify (p : Params) (pk M σ ctx : List UInt8) (F : Fuel := {}) : Option Bool := Id.run do
  if ctx.length > 255 then return some false                -- 1-3
  let M' := IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M    -- 5
  return Verify_internal p pk M' σ F                        -- 6

end Spec
