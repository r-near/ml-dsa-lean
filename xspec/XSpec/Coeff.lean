import Spec
import OcamlPq

/-!
# Algorithms 14 and 15 (`CoeffFromThreeBytes`, `CoeffFromHalfByte`)

Both sides are transcriptions of the same pseudocode.  The adapters are `UInt8.toNat` on the bytes and
`Nat.cast : ℕ → Zq` on the result of Algorithm 14.
-/

open Spec

namespace XSpec

/-- `CoeffFromHalfByte` (Algorithm 15). -/
theorem coeffFromHalfByte_eq (η b : Nat) :
    CoeffFromHalfByte η b = OcamlPq.MLDSAAlg.coeffFromHalfByte η b := rfl

/-- `CoeffFromThreeBytes` (Algorithm 14). -/
theorem coeffFromThreeBytes_eq (b₀ b₁ b₂ : UInt8) :
    CoeffFromThreeBytes b₀ b₁ b₂ =
      Option.map (Nat.cast : Nat → Zq) (OcamlPq.MLDSAAlg.coeffFromThreeBytes b₀.toNat b₁.toNat b₂.toNat) := by
  have hq : OcamlPq.MLDSAAlg.q = Spec.q := rfl
  unfold CoeffFromThreeBytes OcamlPq.MLDSAAlg.coeffFromThreeBytes
  simp only [hq, Id.run]
  by_cases h : b₂.toNat > 127
  · simp only [h, ↓reduceIte]
    split_ifs <;> rfl
  · simp only [h, ↓reduceIte]
    split_ifs <;> rfl

end XSpec
