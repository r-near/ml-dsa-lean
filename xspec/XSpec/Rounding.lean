import Spec
import OcamlPq

/-!
# Equivalence of the rounding and hint functions (FIPS 204 Algorithms 35-40)

Ours (`Spec.Power2Round` ... `Spec.UseHint`, on `Zq = ZMod q`, with a `Spec.Params` record) against ocaml-pq's
`MLDSA.power2RoundSpec` ... `MLDSA.useHintSpec` (on `ℤ`, with `γ2 : ℤ` as an argument).  The adapter is the
canonical representative `r.val : ℤ` of `r : Zq` and `(γ₂ : ℤ)`.  `decompose`, `highBits`, `lowBits`,
`makeHint` and `useHint` are equal for every `γ₂`; `Power2Round` for every parameter record with `d = 13`
(all three sets).
-/

open Spec

namespace XSpec

theorem modPM_eq (m : Int) (α : Nat) :
    Spec.modPM m α = OcamlPq.MLDSA.modPM m (α : Int) := by
  have h : ((α / 2 : Nat) : Int) = (α : Int) / 2 := by omega
  simp only [Spec.modPM, OcamlPq.MLDSA.modPM, h]

theorem val_emod (r : Zq) : (r.val : Int) % OcamlPq.MLDSA.q = r.val := by
  have h1 : r.val < Spec.q := ZMod.val_lt r
  have h3 : Spec.q = 8380417 := rfl
  show (r.val : Int) % 8380417 = r.val
  omega

theorem q_cast : ((Spec.q : Nat) : Int) = OcamlPq.MLDSA.q := rfl

/-- `Power2Round` (Algorithm 35). -/
theorem power2Round_eq (p : Params) (hd : p.d = 13) (r : Zq) :
    Power2Round p r = OcamlPq.MLDSA.power2RoundSpec (r.val : Int) := by
  have h2 : ((2 ^ 13 : Nat) : Int) = (2 : Int) ^ OcamlPq.MLDSA.d := by
    simp [OcamlPq.MLDSA.d]
  simp only [Power2Round, OcamlPq.MLDSA.power2RoundSpec, Id.run, hd, val_emod, modPM_eq, h2]
  rfl

/-- `Decompose` (Algorithm 36). -/
theorem decompose_eq (p : Params) (r : Zq) :
    Decompose p r = OcamlPq.MLDSA.decomposeSpec (p.γ₂ : Int) (r.val : Int) := by
  have h2 : ((2 * p.γ₂ : Nat) : Int) = 2 * (p.γ₂ : Int) := by push_cast; ring
  simp only [Decompose, OcamlPq.MLDSA.decomposeSpec, Id.run, val_emod, modPM_eq, h2, q_cast]
  split_ifs <;> first | rfl | simp_all

/-- `HighBits` (Algorithm 37). -/
theorem highBits_eq (p : Params) (r : Zq) :
    HighBits p r = OcamlPq.MLDSA.highBits (p.γ₂ : Int) (r.val : Int) := by
  simp only [HighBits, OcamlPq.MLDSA.highBits, decompose_eq]

/-- `LowBits` (Algorithm 38). -/
theorem lowBits_eq (p : Params) (r : Zq) :
    LowBits p r = OcamlPq.MLDSA.lowBits (p.γ₂ : Int) (r.val : Int) := by
  simp only [LowBits, OcamlPq.MLDSA.lowBits, decompose_eq]

/-- Their `decomposeSpec` only depends on its argument modulo `q`. -/
theorem decomposeSpec_emod (γ x : Int) :
    OcamlPq.MLDSA.decomposeSpec γ (x % OcamlPq.MLDSA.q) = OcamlPq.MLDSA.decomposeSpec γ x := by
  simp only [OcamlPq.MLDSA.decomposeSpec, Int.emod_emod_of_dvd _ (dvd_refl _)]

theorem highBits_add (p : Params) (z r : Zq) :
    HighBits p (r + z) = OcamlPq.MLDSA.highBits (p.γ₂ : Int) ((r.val : Int) + z.val) := by
  rw [highBits_eq]
  have : ((r + z).val : Int) = ((r.val : Int) + z.val) % Spec.q := by
    rw [ZMod.val_add]; push_cast; rfl
  rw [this]
  simp only [OcamlPq.MLDSA.highBits, q_cast, decomposeSpec_emod]

/-- `MakeHint` (Algorithm 39): ocaml-pq returns the hint bit as `0` / `1`. -/
theorem makeHint_eq (p : Params) (z r : Zq) :
    OcamlPq.MLDSA.makeHintSpec (p.γ₂ : Int) (z.val : Int) (r.val : Int) =
      if MakeHint p z r then 1 else 0 := by
  have e1 := highBits_eq p r
  have e2 := highBits_add p z r
  simp only [OcamlPq.MLDSA.makeHintSpec, MakeHint, e1, e2]
  by_cases hh : OcamlPq.MLDSA.highBits (p.γ₂ : Int) r.val =
      OcamlPq.MLDSA.highBits (p.γ₂ : Int) ((r.val : Int) + z.val)
  · simp [hh, add_comm]
  · simp [hh, add_comm]

/-- `UseHint` (Algorithm 40). -/
theorem useHint_eq (p : Params) (h : Bool) (r : Zq) :
    UseHint p h r = OcamlPq.MLDSA.useHintSpec (p.γ₂ : Int) (if h then 1 else 0) (r.val : Int) := by
  have hm : (((Spec.q - 1) / (2 * p.γ₂) : Nat) : Int) =
      (OcamlPq.MLDSA.q - 1) / (2 * (p.γ₂ : Int)) := by
    have : OcamlPq.MLDSA.q = ((Spec.q : Nat) : Int) := rfl
    rw [this]
    push_cast [Nat.cast_sub (show 1 ≤ Spec.q by decide)]
    rfl
  simp only [UseHint, OcamlPq.MLDSA.useHintSpec, decompose_eq, hm]
  cases h <;> simp

end XSpec
