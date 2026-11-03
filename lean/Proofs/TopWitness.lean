import Proofs.TopWitnessA
import Proofs.TopWitnessS
import Proofs.Correctness

/-!
# Non-vacuity of the `KeyGen` premise, ML-DSA-44 (kernel-checked, concrete `ξ`)

For the seed `ξ = 0x00 0x01 ... 0x1f` and the default fuel (512 for each of the three samplers), `Spec.KeyGen`
returns `some (pk, sk)`. The proof is by composition of kernel evaluations:

* `hout_44` (`TopWitnessSeed`): the first hash of Algorithm 6, `H(ξ ‖ 4 ‖ 4, 128) = outL`;
* `expandA_44_isSome` (`TopWitnessA`): `ExpandA` succeeds on `ρ = outL[0..32]` (16 `RejNTTPoly` declarations);
* `expandS_44_isSome` (`TopWitnessS`): `ExpandS` succeeds on `ρ′ = outL[32..96]`;
* `Proofs.KeyGen.keygen_isSome_iff` (the spec returns `some` exactly when those two do).

`keygen_44_nonvacuous` then feeds this to `keygen_44_correct`: for this `ξ` the extracted `api.keygen_44` returns
`ok (pk, sk)` and the bytes equal what the spec returns, with no premise left.

**What is not witnessed here.** Neither `Spec.Sign` nor `Spec.Verify` has a kernel witness. The values `pk`, `sk` are
existentially quantified, not named. One signing attempt needs `skDecode`, `ExpandMask` (four `BitUnpack`s), about 25
NTTs and the `w1Encode`; each of `BitUnpack`, `skDecode`, `pkEncode` and `skEncode` alone exceeded 100 GB of kernel
memory when measured, so the `correct_44` premise `hs` has no witness (see `STATUS.md`).
-/

open Aeneas Aeneas.Std RustM
open Spec
open Impl

namespace Proofs
namespace TopWitness

/-- **`Spec.KeyGen` returns `some` for ML-DSA-44** on `ξ = 0, 1, ..., 31` at the default fuel. -/
theorem keygen_44_isSome : (Spec.KeyGen Spec.ML_DSA_44 xiL {}).isSome = true := by
  unfold Spec.KeyGen
  rw [Proofs.KeyGen.keygen_isSome_iff, hout_44]
  exact ⟨expandA_44_isSome, expandS_44_isSome⟩

/-- The `hk` premise of `correct_44` / `keygen_44_correct` is satisfiable at the spec level. -/
theorem keygen_44_witness : ∃ pk sk, Spec.KeyGen Spec.ML_DSA_44 xiL {} = some (pk, sk) := by
  obtain ⟨⟨pk, sk⟩, h⟩ := Option.isSome_iff_exists.mp keygen_44_isSome
  exact ⟨pk, sk, h⟩

/-- Every byte list of the right length is the byte view of some array. -/
theorem exists_arrayA {n : Usize} (l : List UInt8) (h : l.length = n.val) : ∃ a : Array U8 n, bytesA a = l := by
  refine ⟨⟨l.map (fun b => (⟨b.toBitVec⟩ : U8)), by simpa using h⟩, ?_⟩
  unfold bytesA
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left (fun b _ => ?_)
  simp [Function.comp, UScalar.val]

/-- **`keygen_44_correct` with no premise left, for one concrete seed.** There is a seed array `ξ` (the bytes
`0, 1, ..., 31`) for which `Spec.KeyGen` returns `some (pk₀, sk₀)`, and the extracted `api.keygen_44 ξ` returns
`ok (pk, sk)` with `bytesA pk = pk₀` and `bytesA sk = sk₀`. -/
theorem keygen_44_nonvacuous :
    ∃ (ξ : Array U8 32#usize) (pk : Array U8 1312#usize) (sk : Array U8 2560#usize) (pk₀ sk₀ : List UInt8),
      bytesA ξ = xiL ∧ Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) {} = some (pk₀, sk₀) ∧
      api.keygen_44 ξ = ok (pk, sk) ∧ bytesA pk = pk₀ ∧ bytesA sk = sk₀ := by
  obtain ⟨ξ, hξ⟩ := exists_arrayA (n := 32#usize) xiL (by decide +kernel)
  obtain ⟨pk₀, sk₀, h⟩ := keygen_44_witness
  have h' : Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) {} = some (pk₀, sk₀) := by rw [hξ]; exact h
  obtain ⟨⟨pk, sk⟩, hkg, hpk, hsk⟩ := WP.spec_imp_exists (keygen_44_correct ξ {} pk₀ sk₀ h')
  exact ⟨ξ, pk, sk, pk₀, sk₀, hξ, h', hkg, hpk, hsk⟩

end TopWitness
end Proofs
