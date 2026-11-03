import Proofs.TopWitnessLit
import Proofs.TopWitnessNf1

/-!
# Inverse NTTs of `ĉ ∘ ·` (kernel stage lemmas): `cs1`
-/

open Spec

namespace Proofs
namespace TopWitness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `cs1[0]`. -/
theorem nttI_cs1_0 :
    NTTInv (Vector.zipWith (· * ·) (Pl Data.ch) (Pl Data.s1h_0)) = Pl Data.cs1_0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `cs1[1]`. -/
theorem nttI_cs1_1 :
    NTTInv (Vector.zipWith (· * ·) (Pl Data.ch) (Pl Data.s1h_1)) = Pl Data.cs1_1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `cs1[2]`. -/
theorem nttI_cs1_2 :
    NTTInv (Vector.zipWith (· * ·) (Pl Data.ch) (Pl Data.s1h_2)) = Pl Data.cs1_2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `cs1[3]`. -/
theorem nttI_cs1_3 :
    NTTInv (Vector.zipWith (· * ·) (Pl Data.ch) (Pl Data.s1h_3)) = Pl Data.cs1_3 := by decide +kernel

end TopWitness
end Proofs
