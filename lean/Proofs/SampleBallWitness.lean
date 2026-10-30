import Proofs.SampleBall

/-!
# Satisfiability of the `SampleInBall` premise (kernel evaluation of SHAKE256)

`sample_in_ball_spec` assumes `Spec.SampleInBall sp fuel (bytes ρ) = some c`. This file shows the premise is
satisfiable: for ML-DSA-44, the all-zero `c̃` of `λ/4 = 32` bytes and fuel 512 (the stream has `8 + 512` bytes)
the spec returns `some c`. The spec is evaluated in the kernel (`decide +kernel`), as for `ExpandA` / `ExpandS`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `SampleInBall` premise holds for the all-zero `c̃` (32 bytes), ML-DSA-44, fuel 512. -/
theorem sample_in_ball_satisfiable :
    ∃ c, Spec.SampleInBall Spec.ML_DSA_44 512 (List.replicate 32 0) = some c := by
  have : (Spec.SampleInBall Spec.ML_DSA_44 512 (List.replicate 32 0)).isSome = true := by decide +kernel
  exact Option.isSome_iff_exists.mp this

/-- The premise of `sample_in_ball_spec` is satisfiable for the extracted type `Slice U8`. -/
theorem sample_in_ball_premise_satisfiable :
    ∃ (ρ : Slice U8) (c : RPoly) (fuel : Nat), Spec.SampleInBall Spec.ML_DSA_44 fuel (bytes ρ) = some c := by
  obtain ⟨c, hc⟩ := sample_in_ball_satisfiable
  refine ⟨Array.to_slice (Array.repeat 32#usize 0#u8), c, 512, ?_⟩
  rw [bytes_to_slice, bytesA_repeat_zero]
  exact hc

end Proofs
