import XSpec.NTTInv
import XSpec.NTTOps

/-!
# The arithmetic building blocks of ocaml-pq's end-to-end specification

`fipsNTT`, `fipsNTTinv`, `fipsMulNTT`, `fipsAddPoly` (`EndToEnd/MLDSA/Arith.lean`) work on `ℕ → ℤ` index
functions of canonical representatives.  Adapter: `canon a = fun i => ((a[i]!).val : ℤ)`.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

/-- Canonical representatives in `[0, q)` as an index function. -/
def canon (a : Poly) : ℕ → ℤ := fun i => ((a[i]!).val : ℤ)

theorem toZq_canon (a : Poly) : toZq (canon a) = I a := by
  funext i
  simp [toZq, OcamlPq.MLDSA.castArr, canon, I]

theorem ofZq_I (a : Poly) : ofZq (I a) = canon a := rfl

/-- `fipsNTT` is our `NTT` on canonical representatives. -/
theorem fipsNTT_eq (w : Poly) : fipsNTT (canon w) = canon (NTT w) := by
  unfold fipsNTT
  rw [toZq_canon, nttSpec_eq, ofZq_I]

theorem canon_zero_of_ge (a : Poly) {i : ℕ} (h : 256 ≤ i) : canon a i = 0 := by
  have : ¬ i < 256 := by omega
  simp [canon, getElem!_neg a i (by simpa using this), default_zq]

/-- `fipsNTTinv` is our `NTTInv` on canonical representatives. -/
theorem fipsNTTinv_eq (w : Poly) : fipsNTTinv (canon w) = canon (NTTInv w) := by
  unfold fipsNTTinv
  rw [toZq_canon, invNttSpec_eq, ofZq_I]
  funext i
  unfold trunc
  by_cases h : i < 256
  · simp [h]
  · simp [h, canon_zero_of_ge _ (by omega : 256 ≤ i)]

/-- `fipsMulNTT` is our `MultiplyNTT` on canonical representatives. -/
theorem fipsMulNTT_eq (a b : Poly) : fipsMulNTT (canon a) (canon b) = canon (MultiplyNTT a b) := by
  unfold fipsMulNTT
  rw [toZq_canon, toZq_canon]
  exact congrArg ofZq (multiplyNTT_eq a b).symm

/-- `fipsAddPoly` is our `AddNTT` on canonical representatives. -/
theorem fipsAddPoly_eq (a b : Poly) : fipsAddPoly (canon a) (canon b) = canon (AddNTT a b) := by
  unfold fipsAddPoly
  rw [toZq_canon, toZq_canon]
  exact congrArg ofZq (addNTT_eq a b).symm

end XSpec
