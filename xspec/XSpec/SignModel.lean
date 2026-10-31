import XSpec.Verify

/-!
# `Sign_internal` (Algorithm 7), the specification unfolded

`Spec.Sign_internal_bounded` as a pure function: the data of steps 1-7 (`Pre`, `pre`), one iteration of the loop
(`attemptAt`) and the loop itself (`loopRes`).  This is the model of the repository's `Proofs/Sign.lean` (part 1),
re-proved here against Lean 4.34's `do` elaboration.
-/

open Spec

namespace XSpec

namespace SG

/-! ## Part 1: the specification, unfolded -/

/-- The values that Algorithm 7 computes before the loop (steps 1-7); `pre` is `none` if `ExpandA` runs out of
fuel (step 5). -/
structure Pre (sp : Spec.Params) where
  s₁ : Vector RPoly sp.ℓ
  s₂ : Vector RPoly sp.k
  t₀ : Vector RPoly sp.k
  Â : Vector (Vector Poly sp.ℓ) sp.k
  μ : List UInt8
  ρ'' : List UInt8

namespace Pre
variable {sp : Spec.Params}
/-- `ŝ₁` (step 2). -/
def ŝ₁ (P : Pre sp) : Vector Poly sp.ℓ := NTTVec (P.s₁.map RPoly.toZq)
/-- `ŝ₂` (step 3). -/
def ŝ₂ (P : Pre sp) : Vector Poly sp.k := NTTVec (P.s₂.map RPoly.toZq)
/-- `t̂₀` (step 4). -/
def t₀hat (P : Pre sp) : Vector Poly sp.k := NTTVec (P.t₀.map RPoly.toZq)
end Pre

/-- Steps 1-7 of Algorithm 7. -/
def pre (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) : Option (Pre sp) :=
  match Spec.skDecode sp sk with
  | (ρ, K, tr, s₁, s₂, t₀) =>
    match Spec.ExpandA sp F.rejNTT ρ with
    | some Â => some ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩
    | none => none

/-- The accepted pair `(z, h)` of an attempt, or `none` if the attempt was rejected. -/
abbrev Out (sp : Spec.Params) : Type := Option (Vector Poly sp.ℓ × Vector HintPoly sp.k)

/-- Steps 17-30 once the challenge `c` is known: the response `z`, the hint `h`, and the two rejection tests. -/
def respond (sp : Spec.Params) (P : Pre sp) (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) : Out sp :=
  let ĉ := NTT c.toZq
  let cs₁ := NTTInvVec (ScalarVectorNTT ĉ P.ŝ₁)
  let cs₂ := NTTInvVec (ScalarVectorNTT ĉ P.ŝ₂)
  let z := y + cs₁
  let r₀ := LowBitsVec sp (w - cs₂)
  if ‖z‖∞ ≥ sp.γ₁ - sp.β ∨ ‖r₀‖∞ ≥ sp.γ₂ - sp.β then none
  else
    let ct₀ := NTTInvVec (ScalarVectorNTT ĉ P.t₀hat)
    let h := MakeHintVec sp (-ct₀) (w - cs₂ + ct₀)
    if ‖ct₀‖∞ ≥ sp.γ₂ ∨ HintWeight h > sp.ω then none else some (z, h)

theorem respond_eq (sp : Spec.Params) (P : Pre sp) (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) :
    respond sp P y w c =
      if sp.γ₁ - sp.β ≤ ‖y + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₁)‖∞ ∨
          sp.γ₂ - sp.β ≤ ‖LowBitsVec sp (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂))‖∞ then none
      else if sp.γ₂ ≤ ‖NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat)‖∞ ∨
          sp.ω < HintWeight (MakeHintVec sp (-NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))
            (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂) + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat)))
        then none
      else some (y + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₁),
        MakeHintVec sp (-NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))
          (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂) + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))) :=
  rfl

/-- The mask `y` of attempt `κ` (step 11). -/
def maskAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : Vector Poly sp.ℓ :=
  (ExpandMask sp P.ρ'' κ).map RPoly.toZq

/-- The commitment `w` of attempt `κ` (step 12). -/
def commitAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : Vector Poly sp.k :=
  NTTInvVec (MatrixVectorNTT P.Â (NTTVec (maskAt sp P κ)))

/-- The commitment hash `ct` of attempt `κ` (steps 13, 15). -/
def ctildeAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : List UInt8 :=
  H (P.μ ++ w1Encode sp (HighBitsVec sp (commitAt sp P κ))) (sp.lam / 4)

/-- One iteration of the loop body (steps 11-30) with counter `κ`. `none`: `SampleInBall` ran out of fuel.
`some (ct, none)`: the attempt is rejected. `some (ct, some (z, h))`: it is accepted. -/
def attemptAt (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (κ : Nat) : Option (List UInt8 × Out sp) :=
  match Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P κ) with
  | some c => some (ctildeAt sp P κ, respond sp P (maskAt sp P κ) (commitAt sp P κ) c)
  | none => none

/-- The loop with `n` attempts left and counter `κ`. `some none`: no attempt was accepted (budget exhausted, or
the next attempt would need `κ + ℓ > 2^16`); `none`: a `SampleInBall` ran out of fuel first. -/
def loopRes (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    Nat → Nat → Option (Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k))
  | 0, _ => some none
  | n + 1, κ =>
    if 2 ^ 16 < κ + sp.ℓ then some none
    else match attemptAt sp F P κ with
      | none => none
      | some (_, none) => loopRes sp F P n (κ + sp.ℓ)
      | some (ct, some (z, h)) => some (some (ct, z, h))

/-- Step 33: the signature of an accepted attempt. -/
def encodeRes (sp : Spec.Params) :
    Option (Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)) → Option (List UInt8)
  | some (some (ct, z, h)) => some (sigEncode sp ct (z.map Poly.modPM) h)
  | _ => none

/-! ### The `for` loop as an iteration -/

/-- `n` rounds of a step function; a `done` ends the iteration. -/
def iterG {σ : Type} (g : σ → Id (ForInStep σ)) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => match Id.run (g s) with
    | .done b => b
    | .yield b => iterG g n b

theorem forIn_list_const {σ : Type} (g : σ → Id (ForInStep σ)) (l : List Nat) (init : σ) :
    (forIn l init (fun _ r => g r) : Id σ) = iterG g l.length init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, iterG]
    show (match g init with
      | .done b => b
      | .yield b => (forIn l b (fun _ r => g r) : Id σ)) = _
    generalize g init = x
    cases x with
    | done b => rfl
    | yield b => exact ih b

theorem forIn_range_const {σ : Type} (g : σ → Id (ForInStep σ)) (B : Nat) (init : σ) :
    (forIn [0:B] init (fun _ r => g r) : Id σ) = iterG g B init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_const]
  simp [Std.Legacy.Range.size]

/-- The state of the `for` loop of Algorithm 7 (as `do` notation packs it: early-return flag, `κ`, `(z, h)`, `c̃`). -/
abbrev St (sp : Spec.Params) : Type :=
  Prod (Option (Option (List UInt8))) (Prod Nat (Prod (Out sp) (List UInt8)))

/-- What follows the loop in Algorithm 7 (the `return`, step 33). -/
def postSt (sp : Spec.Params) (r : St sp) : Option (List UInt8) :=
  match r.1 with
  | some a => a
  | none =>
    match r.2.2.1 with
    | some (z, h) => some (sigEncode sp r.2.2.2 (z.map Poly.modPM) h)
    | none => none

theorem iterG_accepted (sp : Spec.Params) (g : St sp → Id (ForInStep (St sp)))
    (hg2 : ∀ c x κ, Id.run (g ⟨none, κ, some x, c⟩) = .done ⟨none, κ, some x, c⟩) (c : List UInt8)
    (x : Vector Poly sp.ℓ × Vector HintPoly sp.k) (κ : Nat) :
    ∀ n, iterG g n ⟨none, κ, some x, c⟩ = ⟨none, κ, some x, c⟩ := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp only [iterG, hg2]

theorem iterG_post (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (g : St sp → Id (ForInStep (St sp)))
    (hg1 : ∀ c κ, Id.run (g ⟨none, κ, none, c⟩) =
      if 2 ^ 16 < κ + sp.ℓ then .done ⟨some none, κ, none, c⟩
      else match attemptAt sp F P κ with
        | none => .done ⟨some none, κ, none, ctildeAt sp P κ⟩
        | some (ct, zh) => .yield ⟨none, κ + sp.ℓ, zh, ct⟩)
    (hg2 : ∀ c x κ, Id.run (g ⟨none, κ, some x, c⟩) = .done ⟨none, κ, some x, c⟩) :
    ∀ n κ c, postSt sp (iterG g n ⟨none, κ, none, c⟩) = encodeRes sp (loopRes sp F P n κ) := by
  intro n
  induction n with
  | zero => intro κ c; rfl
  | succ n ih =>
    intro κ c
    simp only [iterG, hg1, loopRes]
    by_cases hκ : 2 ^ 16 < κ + sp.ℓ
    · simp only [hκ, if_true]
      simp [postSt, encodeRes]
    · simp only [hκ, if_false]
      rcases hat : attemptAt sp F P κ with _ | ⟨ct, _ | ⟨z, h⟩⟩
      · simp [postSt, encodeRes]
      · simp only []
        exact ih _ _
      · simp only []
        rw [iterG_accepted sp g hg2]
        simp [postSt, encodeRes]

theorem iterG_post' (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (g : St sp → Id (ForInStep (St sp)))
    (hg1 : ∀ c κ, Id.run (g ⟨none, κ, none, c⟩) =
      if 2 ^ 16 < κ + sp.ℓ then .done ⟨some none, κ, none, c⟩
      else match attemptAt sp F P κ with
        | none => .done ⟨some none, κ, none, ctildeAt sp P κ⟩
        | some (ct, zh) => .yield ⟨none, κ + sp.ℓ, zh, ct⟩)
    (hg2 : ∀ c x κ, Id.run (g ⟨none, κ, some x, c⟩) = .done ⟨none, κ, some x, c⟩) (B : Nat) (I : St sp)
    (hI : iterG g B ⟨none, 0, none, []⟩ = I) :
    postSt sp I = encodeRes sp (loopRes sp F P B 0) := by
  subst hI
  exact iterG_post sp F P g hg1 hg2 B 0 []

theorem Sign_internal_bounded_eq (sp : Spec.Params) (B : Nat) (sk M' rnd : List UInt8) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded sp B sk M' rnd F =
      match pre sp F sk M' rnd with
      | none => none
      | some P => encodeRes sp (loopRes sp F P B 0) := by
  unfold Spec.Sign_internal_bounded pre
  generalize Spec.skDecode sp sk = d
  obtain ⟨ρ, K, tr, s₁, s₂, t₀⟩ := d
  rcases hA : Spec.ExpandA sp F.rejNTT ρ with _ | Â
  · simp [hA]
  · simp only [hA]
    rw [forIn_range_const]
    generalize hI : iterG _ B (⟨none, 0, none, []⟩ : St sp) = I
    have key := iterG_post' sp F ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩ _
      ?h1 ?h2 B I hI
    case h1 =>
      intro c κ
      by_cases hκ : 2 ^ 16 < κ + sp.ℓ
      · simp only [Option.isSome_none, Bool.false_eq_true, hκ, ↓reduceIte, if_true]
        rfl
      · simp only [Option.isSome_none, Bool.false_eq_true, hκ, ↓reduceIte]
        dsimp only [attemptAt, ctildeAt, commitAt, maskAt, respond, Pre.ŝ₁, Pre.ŝ₂, Pre.t₀hat, Id.run]
        generalize SampleInBall sp F.sampleInBall _ = S
        cases S with
        | none => rfl
        | some c =>
          dsimp only
          split_ifs <;> first | rfl | (simp only [*, ↓reduceIte]; try rfl)
    case h2 => intro c x κ; simp
    rw [← key]
    rcases I with ⟨a, κ, zh, c⟩
    rcases a with _ | a <;> rcases zh with _ | ⟨z, h⟩ <;> rfl

end SG

end XSpec
