import Proofs.TopWitnessKA
import Proofs.SampleA

/-!
# `ExpandA` succeeds on the `ρ` derived from `ξ` (ML-DSA-44)

`Spec.ExpandA` on `ρ = rhoS` at fuel 512. A single kernel evaluation of all 16 `RejNTTPoly` calls needs about 160 GB
(measured: 19 min), so each entry is its own kernel check (about 10 GB, 40 s each): the 16 declarations `rejA_r_s` of
`TopWitnessKA`, which also name the sampled polynomials. Here each gives `isSome`, and the 16 are assembled through the
`expandA_eq` characterization of `SampleA`.
-/

open Spec
set_option maxRecDepth 8192

namespace Proofs
namespace TopWitness

/-- Entry `(0, 0)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_0_0 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 0 0)).isSome = true := (congrArg Option.isSome rejA_0_0).trans rfl

/-- Entry `(0, 1)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_0_1 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 0 1)).isSome = true := (congrArg Option.isSome rejA_0_1).trans rfl

/-- Entry `(0, 2)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_0_2 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 0 2)).isSome = true := (congrArg Option.isSome rejA_0_2).trans rfl

/-- Entry `(0, 3)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_0_3 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 0 3)).isSome = true := (congrArg Option.isSome rejA_0_3).trans rfl

/-- Entry `(1, 0)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_1_0 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 1 0)).isSome = true := (congrArg Option.isSome rejA_1_0).trans rfl

/-- Entry `(1, 1)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_1_1 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 1 1)).isSome = true := (congrArg Option.isSome rejA_1_1).trans rfl

/-- Entry `(1, 2)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_1_2 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 1 2)).isSome = true := (congrArg Option.isSome rejA_1_2).trans rfl

/-- Entry `(1, 3)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_1_3 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 1 3)).isSome = true := (congrArg Option.isSome rejA_1_3).trans rfl

/-- Entry `(2, 0)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_2_0 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 2 0)).isSome = true := (congrArg Option.isSome rejA_2_0).trans rfl

/-- Entry `(2, 1)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_2_1 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 2 1)).isSome = true := (congrArg Option.isSome rejA_2_1).trans rfl

/-- Entry `(2, 2)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_2_2 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 2 2)).isSome = true := (congrArg Option.isSome rejA_2_2).trans rfl

/-- Entry `(2, 3)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_2_3 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 2 3)).isSome = true := (congrArg Option.isSome rejA_2_3).trans rfl

/-- Entry `(3, 0)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_3_0 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 3 0)).isSome = true := (congrArg Option.isSome rejA_3_0).trans rfl

/-- Entry `(3, 1)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_3_1 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 3 1)).isSome = true := (congrArg Option.isSome rejA_3_1).trans rfl

/-- Entry `(3, 2)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_3_2 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 3 2)).isSome = true := (congrArg Option.isSome rejA_3_2).trans rfl

/-- Entry `(3, 3)` of `ExpandA` for `ρ`: `RejNTTPoly` succeeds at fuel 512 (from `rejA_*`). -/
theorem rej_a_3_3 : (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS 3 3)).isSome = true := (congrArg Option.isSome rejA_3_3).trans rfl

/-- The 16 entries, assembled. -/
theorem rej_a_all :
    ∀ r, r < Spec.ML_DSA_44.k → ∀ s, s < Spec.ML_DSA_44.ℓ →
      (Spec.RejNTTPoly 512 (SampleA.pSeed rhoS r s)).isSome = true := by
  have hk : Spec.ML_DSA_44.k = 4 := by decide +kernel
  have hl : Spec.ML_DSA_44.ℓ = 4 := by decide +kernel
  rw [hk, hl]
  intro r hr s hs
  match r, hr, s, hs with
  | 0, _, 0, _ => exact rej_a_0_0
  | 0, _, 1, _ => exact rej_a_0_1
  | 0, _, 2, _ => exact rej_a_0_2
  | 0, _, 3, _ => exact rej_a_0_3
  | 1, _, 0, _ => exact rej_a_1_0
  | 1, _, 1, _ => exact rej_a_1_1
  | 1, _, 2, _ => exact rej_a_1_2
  | 1, _, 3, _ => exact rej_a_1_3
  | 2, _, 0, _ => exact rej_a_2_0
  | 2, _, 1, _ => exact rej_a_2_1
  | 2, _, 2, _ => exact rej_a_2_2
  | 2, _, 3, _ => exact rej_a_2_3
  | 3, _, 0, _ => exact rej_a_3_0
  | 3, _, 1, _ => exact rej_a_3_1
  | 3, _, 2, _ => exact rej_a_3_2
  | 3, _, 3, _ => exact rej_a_3_3
  | r + 4, h, _, _ => exact absurd h (by omega)
  | _, _, s + 4, h => exact absurd h (by omega)

/-- **`ExpandA` succeeds** on the `ρ` that `KeyGen` derives from `ξ = 0, 1, ..., 31`, ML-DSA-44, fuel 512. -/
theorem expandA_44_isSome : (Spec.ExpandA Spec.ML_DSA_44 512 rhoS).isSome = true :=
  SampleA.expandA_isSome _ _ _ rej_a_all

end TopWitness
end Proofs
