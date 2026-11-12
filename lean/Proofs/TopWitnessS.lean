import Proofs.TopWitnessKS
import Proofs.SampleS

/-!
# `ExpandS` succeeds on the `ρ′` derived from `ξ` (ML-DSA-44)

`Spec.ExpandS` on `ρ′ = rho1S` at fuel 512 makes 8 calls to `RejBoundedPoly`. All 8 in one kernel evaluation need about
18 GB, so each call is its own kernel check: the declarations `rejS_0, ..., rejS_7` of `TopWitnessKS`, which also name the
sampled polynomials. `ExpandS_isSome` (`SampleS`) assembles them.
-/

open Spec

namespace Proofs
namespace TopWitness

/-- **`ExpandS` succeeds** on the `ρ′` that `KeyGen` derives from `ξ = 0, 1, ..., 31`, ML-DSA-44, fuel 512. -/
theorem expandS_44_isSome : (Spec.ExpandS Spec.ML_DSA_44 512 rho1S).isSome = true := by
  apply ExpandS_isSome
  have h8 : Spec.ML_DSA_44.ℓ + Spec.ML_DSA_44.k = 8 := by decide +kernel
  rw [h8]
  intro i hi
  match i, hi with
  | 0, _ => exact (congrArg Option.isSome rejS_0).trans rfl
  | 1, _ => exact (congrArg Option.isSome rejS_1).trans rfl
  | 2, _ => exact (congrArg Option.isSome rejS_2).trans rfl
  | 3, _ => exact (congrArg Option.isSome rejS_3).trans rfl
  | 4, _ => exact (congrArg Option.isSome rejS_4).trans rfl
  | 5, _ => exact (congrArg Option.isSome rejS_5).trans rfl
  | 6, _ => exact (congrArg Option.isSome rejS_6).trans rfl
  | 7, _ => exact (congrArg Option.isSome rejS_7).trans rfl
  | i + 8, h => exact absurd h (by omega)

end TopWitness
end Proofs
