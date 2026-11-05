import Proofs.SampleA
import Proofs.SampleS
import Proofs.StdParams

/-!
# Satisfiability witnesses for the sampler premises

* ML-DSA-44: `ExpandA` succeeds on the all-zero seed at fuel 512. One kernel evaluation of the whole matrix would
  exceed the 4M-heartbeat cap, so each of the 16 `RejNTTPoly` calls is its own declaration (`rej_ntt_44_r_s`) and
  `SampleA.expandA_isSome` assembles them through the `expandA_eq` characterization of `SampleA`.
* ML-DSA-65 (`η = 4`): `ExpandS` succeeds on the all-zero seed, bundled with `Params.Std`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## `ExpandA` -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(0, 0)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_0_0 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 0 0)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(0, 1)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_0_1 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 0 1)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(0, 2)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_0_2 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 0 2)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(0, 3)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_0_3 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 0 3)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(1, 0)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_1_0 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 1 0)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(1, 1)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_1_1 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 1 1)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(1, 2)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_1_2 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 1 2)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(1, 3)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_1_3 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 1 3)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(2, 0)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_2_0 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 2 0)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(2, 1)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_2_1 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 2 1)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(2, 2)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_2_2 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 2 2)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(2, 3)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_2_3 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 2 3)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(3, 0)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_3_0 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 3 0)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(3, 1)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_3_1 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 3 1)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(3, 2)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_3_2 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 3 2)).isSome = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Entry `(3, 3)` of `ExpandA` for the all-zero seed: `RejNTTPoly` succeeds at fuel 512. -/
theorem rej_ntt_44_3_3 :
    (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) 3 3)).isSome = true := by decide +kernel

/-- The 16 entries, assembled. -/
theorem rej_ntt_44_all :
    ∀ r, r < Spec.ML_DSA_44.k → ∀ s, s < Spec.ML_DSA_44.ℓ →
      (Spec.RejNTTPoly 512 (SampleA.pSeed (List.replicate 32 0) r s)).isSome = true := by
  have hk : Spec.ML_DSA_44.k = 4 := by decide +kernel
  have hl : Spec.ML_DSA_44.ℓ = 4 := by decide +kernel
  rw [hk, hl]
  intro r hr s hs
  match r, hr, s, hs with
  | 0, _, 0, _ => exact rej_ntt_44_0_0
  | 0, _, 1, _ => exact rej_ntt_44_0_1
  | 0, _, 2, _ => exact rej_ntt_44_0_2
  | 0, _, 3, _ => exact rej_ntt_44_0_3
  | 1, _, 0, _ => exact rej_ntt_44_1_0
  | 1, _, 1, _ => exact rej_ntt_44_1_1
  | 1, _, 2, _ => exact rej_ntt_44_1_2
  | 1, _, 3, _ => exact rej_ntt_44_1_3
  | 2, _, 0, _ => exact rej_ntt_44_2_0
  | 2, _, 1, _ => exact rej_ntt_44_2_1
  | 2, _, 2, _ => exact rej_ntt_44_2_2
  | 2, _, 3, _ => exact rej_ntt_44_2_3
  | 3, _, 0, _ => exact rej_ntt_44_3_0
  | 3, _, 1, _ => exact rej_ntt_44_3_1
  | 3, _, 2, _ => exact rej_ntt_44_3_2
  | 3, _, 3, _ => exact rej_ntt_44_3_3
  | r + 4, h, _, _ => exact absurd h (by omega)
  | _, _, s + 4, h => exact absurd h (by omega)

/-- **The `ExpandA` premise holds** for the all-zero seed, ML-DSA-44, fuel 512 (16 kernel evaluations of
SHAKE128 + `RejNTTPoly`, each its own declaration). -/
theorem expand_a_satisfiable :
    ∃ A, Spec.ExpandA Spec.ML_DSA_44 512 (List.replicate 32 0) = some A :=
  Option.isSome_iff_exists.mp (SampleA.expandA_isSome _ _ _ rej_ntt_44_all)

/-- The premise of `expand_a_spec` is satisfiable for the extracted type: the all-zero `ρ : Array U8 32#usize`. -/
theorem expand_a_premise_satisfiable :
    ∃ (ρ : Array U8 32#usize) (A : Vector (Vector Spec.Poly Spec.ML_DSA_44.ℓ) Spec.ML_DSA_44.k) (fuel : Nat),
      Spec.ExpandA Spec.ML_DSA_44 fuel (bytesA ρ) = some A := by
  obtain ⟨A, hA⟩ := expand_a_satisfiable
  refine ⟨Array.repeat 32#usize 0#u8, A, 512, ?_⟩
  rw [bytesA_repeat_zero]
  exact hA

/-! ## `ExpandS` for ML-DSA-65 -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `ExpandS` premise holds for the all-zero seed, ML-DSA-65, fuel 512. -/
theorem expand_s_satisfiable_65 :
    ∃ r, Spec.ExpandS Spec.ML_DSA_65 512 (List.replicate 64 0) = some r := by
  have : (Spec.ExpandS Spec.ML_DSA_65 512 (List.replicate 64 0)).isSome = true := by decide +kernel
  exact Option.isSome_iff_exists.mp this

/-- ML-DSA-65 (`η = 4`): the parameter premises (`Params.Std`) and the `ExpandS` premise hold together, for the
extracted `ip` produced by `params.ML_DSA_65` and the all-zero seed `ρ : Array U8 64#usize` at fuel 512. -/
theorem expand_s_premise_satisfiable_65 :
    ∃ (ip : Impl.params.Params) (ρ : Array U8 64#usize) (s₁ : Vector RPoly Spec.ML_DSA_65.ℓ)
      (s₂ : Vector RPoly Spec.ML_DSA_65.k) (fuel : Nat),
      params.ML_DSA_65 = ok ip ∧ Params.Std ip 6#usize 5#usize Spec.ML_DSA_65 ∧
      Spec.ExpandS Spec.ML_DSA_65 fuel (bytesA ρ) = some (s₁, s₂) := by
  obtain ⟨ip, hip, hstd⟩ := ML_DSA_65_std
  obtain ⟨⟨s₁, s₂⟩, h⟩ := expand_s_satisfiable_65
  refine ⟨ip, Array.repeat 64#usize 0#u8, s₁, s₂, 512, hip, hstd, ?_⟩
  rw [bytesA_repeat_zero]
  exact h

end Proofs
