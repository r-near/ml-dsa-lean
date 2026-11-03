import Proofs.TopWitnessSign

/-!
# `correct_44` and `correct_external` are non-vacuous (ML-DSA-44)

For `ξ = 0, 1, ..., 31`, `rnd = 0^32`, `M = [0]`, `ctx = []` and the default fuel, `Spec.KeyGen` returns a key pair
(`TopWitnessKG.keygen_lit`), `Spec.Sign` returns a signature on the secret key (`TopWitnessSign.sign_lit_isSome`),
and therefore all the hypotheses of `correct_44` hold with nothing left over: `Spec.Verify` accepts and the extracted
`api.keygen_44`, `api.sign_44` and `api.verify_44` chain to `true`.

The bytes of `pk₀`, `sk₀` are the literals `Data.pkL` and `skL`; `σ₀` is existentially quantified (the kernel shows
that the first signing attempt is accepted, so a signature exists, without writing it out).
-/

open Aeneas Aeneas.Std RustM
open Spec
open Impl

namespace Proofs
namespace TopWitness

/-- Every byte list of length at most `Usize.max` is the byte view of some slice. -/
theorem exists_slice (l : List UInt8) (h : l.length ≤ Usize.max) : ∃ s : Slice U8, bytes s = l := by
  refine ⟨⟨l.map (fun b => (⟨b.toBitVec⟩ : U8)), by simpa using h⟩, ?_⟩
  unfold bytes
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left (fun b _ => ?_)
  simp [Function.comp, UScalar.val]

/-- **`correct_44` with no premise left.** With the seed `ξ = 0, 1, ..., 31`, `rnd = 0^32`, `M = [0]`, `ctx = []`
and the default fuel: the spec's `KeyGen` returns `(pk₀, sk₀)`, its `Sign` returns `σ₀`, its `Verify` returns
`some true`, and the extracted `api.keygen_44 ξ` returns `ok (pk, sk)` with the spec's bytes, `api.sign_44 sk m ctx rnd`
returns `ok (some σ)` with the spec's bytes, and `api.verify_44 pk m ctx σ` returns `ok true`. -/
theorem correct_44_nonvacuous :
    ∃ (ξ : Array U8 32#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) (pk₀ sk₀ σ₀ : List UInt8),
      bytesA ξ = xiL ∧ bytes m = [0] ∧ bytes ctx = [] ∧ bytesA rnd = List.replicate 32 0 ∧
      Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) {} = some (pk₀, sk₀) ∧
      Spec.Sign Spec.ML_DSA_44 sk₀ (bytes m) (bytes ctx) (bytesA rnd) {} = some σ₀ ∧
      Spec.Verify Spec.ML_DSA_44 pk₀ (bytes m) σ₀ (bytes ctx) {} = some true ∧
      ∃ (pk : Array U8 1312#usize) (sk : Array U8 2560#usize) (σ : Array U8 2420#usize),
        api.keygen_44 ξ = ok (pk, sk) ∧ bytesA pk = pk₀ ∧ bytesA sk = sk₀ ∧
        api.sign_44 sk m ctx rnd = ok (some σ) ∧ bytesA σ = σ₀ ∧
        api.verify_44 pk m ctx σ = ok true := by
  obtain ⟨ξ, hξ⟩ := exists_arrayA (n := 32#usize) xiL (by decide +kernel)
  obtain ⟨m, hm⟩ := exists_slice [0] (by have := Usize.cMax_bound_concrete.1; simp; omega)
  obtain ⟨ctx, hctx⟩ := exists_slice [] (by simp)
  obtain ⟨rnd, hrnd⟩ := exists_arrayA (n := 32#usize) (List.replicate 32 0) (by simp)
  have hk : Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) {} = some (Data.pkL, skL) := by rw [hξ]; exact keygen_lit
  have hsome : (Spec.Sign Spec.ML_DSA_44 skL (bytes m) (bytes ctx) (bytesA rnd) {}).isSome = true := by
    rw [hm, hctx, hrnd]; exact sign_lit_isSome
  obtain ⟨σ₀, hs⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨pk, sk, σ, hkg, hpk, hsk, hsg, hσ, hvf⟩ := correct_44 ξ m ctx rnd {} Data.pkL skL σ₀ hk hs
  have hv := correct_external stdParams_44 (bytesA ξ) (bytes m) (bytes ctx) (bytesA rnd) {} Data.pkL skL σ₀ hk hs
  exact ⟨ξ, m, ctx, rnd, Data.pkL, skL, σ₀, hξ, hm, hctx, hrnd, hk, hs, hv, pk, sk, σ, hkg, hpk, hsk, hsg, hσ, hvf⟩

end TopWitness
end Proofs
