import Proofs.TopWitnessSeed

/-!
# `ExpandS` succeeds on the `ρ′` derived from `ξ` (ML-DSA-44)

One kernel evaluation of the 8 `RejBoundedPoly` calls (measured: 38 GB, 4.7 min).
-/

open Spec

namespace Proofs
namespace TopWitness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`ExpandS` succeeds** on the `ρ′` that `KeyGen` derives from `ξ = 0, 1, ..., 31`, ML-DSA-44, fuel 512. -/
theorem expandS_44_isSome : (Spec.ExpandS Spec.ML_DSA_44 512 rho1S).isSome = true := by decide +kernel

end TopWitness
end Proofs
