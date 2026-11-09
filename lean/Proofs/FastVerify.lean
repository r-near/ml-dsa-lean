import Proofs.FastVerifyCore
import Proofs.Divergence

/-!
# The 4-way verify body: the `api` wrappers

`verify.verify_internal_x4 K L` is equal to the scalar `verify.verify_internal K L` (`verify_internal_x4_eq`, in
`Proofs/FastVerifyCore.lean`). The public `api.verify_NN` and `api.verifying_key_NN` call the 4-way functions, so
`Proofs/API.lean` and `Proofs/PreparedVerify.lean` use that equality to connect them to the scalar bodies the refinement
theorems are about. This file states it for the `api` wrapper bodies:

* `verify_internal_x4_NN_exact`, `verify_internal_x4_NN_div_iff` : the `_exact` and `_div_iff` forms of
  `verify_internal_NN` for the three standard sets, stated about the `api` wrapper body run with the 4-way verifier.

The 4-way Keccak (`keccak4.keccak_f1600_x4`, plain Rust) is proved equal, state by state, to the scalar permutation
(`keccak_f1600_x4_spec`), so this says that the 4-way verifier computes FIPS 204 Algorithm 8 exactly.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open Verify APIInternal
open SampleA

/-! ### The three standard sets -/

/-- ML-DSA-44: the 4-way verifier is `api.verify_internal_44`. -/
theorem verify_internal_x4_44_eq (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    verifyInternalX4API 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig =
      api.verify_internal_44 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_internal_44_eq, hip]
  exact verifyInternalX4API_eq hp _ _ pk m sig

/-- ML-DSA-65: the 4-way verifier is `api.verify_internal_65`. -/
theorem verify_internal_x4_65_eq (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    verifyInternalX4API 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig =
      api.verify_internal_65 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_internal_65_eq, hip]
  exact verifyInternalX4API_eq hp _ _ pk m sig

/-- ML-DSA-87: the 4-way verifier is `api.verify_internal_87`. -/
theorem verify_internal_x4_87_eq (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    verifyInternalX4API 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig =
      api.verify_internal_87 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_internal_87_eq, hip]
  exact verifyInternalX4API_eq hp _ _ pk m sig

/-- **ML-DSA-44 4-way `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_x4_44_exact (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, verifyInternalX4API 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      verifyInternalX4API 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig = ok b) ∧
    (∀ b, verifyInternalX4API 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_x4_44_eq]
  exact verify_internal_44_exact pk m sig

/-- **ML-DSA-65 4-way `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_x4_65_exact (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, verifyInternalX4API 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      verifyInternalX4API 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig = ok b) ∧
    (∀ b, verifyInternalX4API 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_x4_65_eq]
  exact verify_internal_65_exact pk m sig

/-- **ML-DSA-87 4-way `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_x4_87_exact (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, verifyInternalX4API 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      verifyInternalX4API 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig = ok b) ∧
    (∀ b, verifyInternalX4API 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_x4_87_eq]
  exact verify_internal_87_exact pk m sig

/-- **The 4-way ML-DSA-44 verifier diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_x4_44_div_iff (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    verifyInternalX4API 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_x4_44_eq]
  exact verify_internal_44_div_iff pk m sig

/-- **The 4-way ML-DSA-65 verifier diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_x4_65_div_iff (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    verifyInternalX4API 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_x4_65_eq]
  exact verify_internal_65_div_iff pk m sig

/-- **The 4-way ML-DSA-87 verifier diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_x4_87_div_iff (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    verifyInternalX4API 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_x4_87_eq]
  exact verify_internal_87_div_iff pk m sig

end Proofs
