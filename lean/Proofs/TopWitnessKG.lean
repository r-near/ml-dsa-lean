import Proofs.TopWitness
import Proofs.TopWitnessKA
import Proofs.TopWitnessKS
import Proofs.TopWitnessNf1
import Proofs.TopWitnessNi
import Proofs.TopWitnessMisc

/-!
# `Spec.KeyGen` returns a named key pair for `ξ = 0, 1, ..., 31` (ML-DSA-44)

Chains the kernel stage lemmas (`TopWitnessKA`, `KS`, `Nf1`, `Ni`, `Misc`): each large step is its own declaration
that proves `spec piece (literal input) = literal output`. This module only rewrites with them.

* `expandA_lit`, `expandS_lit`: `ExpandA` and `ExpandS` on the derived seeds return the literals `Av`, `(S1v, S2v)`;
* `tvec_lit`: `t = NTT⁻¹(Â ∘ NTT(s₁)) + s₂` is the literal `Tv`;
* `keygen_lit`: `Spec.KeyGen ML_DSA_44 ξ {} = some (pkL, skL)` with `pkL` the literal public key and `skL` the
  `skEncode` of the literals.
-/

open Spec
set_option maxRecDepth 100000

namespace Proofs
namespace TopWitness

theorem expandA_lit : Spec.ExpandA Spec.ML_DSA_44 512 rhoS = some Av := by
  apply expandA_of_entries
  intro r hr s hs
  have h4 : r < 4 := hr
  have h4' : s < 4 := hs
  interval_cases r <;> interval_cases s
  exacts [rejA_0_0, rejA_0_1, rejA_0_2, rejA_0_3, rejA_1_0, rejA_1_1, rejA_1_2, rejA_1_3, rejA_2_0, rejA_2_1, rejA_2_2, rejA_2_3, rejA_3_0, rejA_3_1, rejA_3_2, rejA_3_3]

theorem expandS_lit {s₁ : Vector RPoly Spec.ML_DSA_44.ℓ} {s₂ : Vector RPoly Spec.ML_DSA_44.k}
    (h : Spec.ExpandS Spec.ML_DSA_44 512 rho1S = some (s₁, s₂)) : s₁ = S1v ∧ s₂ = S2v := by
  obtain ⟨h1, h2⟩ := ExpandS_some _ _ _ _ _ h
  constructor
  · apply Vector.ext
    intro i hi
    have h4 : i < 4 := hi
    interval_cases i
    · exact Option.some.inj ((h1 0 hi).symm.trans rejS_0)
    · exact Option.some.inj ((h1 1 hi).symm.trans rejS_1)
    · exact Option.some.inj ((h1 2 hi).symm.trans rejS_2)
    · exact Option.some.inj ((h1 3 hi).symm.trans rejS_3)
  · apply Vector.ext
    intro i hi
    have h4 : i < 4 := hi
    interval_cases i
    · exact Option.some.inj ((h2 0 hi).symm.trans rejS_4)
    · exact Option.some.inj ((h2 1 hi).symm.trans rejS_5)
    · exact Option.some.inj ((h2 2 hi).symm.trans rejS_6)
    · exact Option.some.inj ((h2 3 hi).symm.trans rejS_7)

theorem ntt_s1_lit : Spec.NTTVec (S1v.map RPoly.toZq) = S1hv := by
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTVec, Vector.getElem_map]
  interval_cases i
  · exact nttF_s1_0
  · exact nttF_s1_1
  · exact nttF_s1_2
  · exact nttF_s1_3

theorem tvec_lit : KeyGen.tVec Spec.ML_DSA_44 Av S1v S2v = Tv := by
  unfold KeyGen.tVec
  rw [ntt_s1_lit, mv_lit]
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  show (Vector.zipWith (· + ·) (Spec.NTTInvVec MVv) (S2v.map RPoly.toZq))[i] = Tv[i]
  simp only [Vector.getElem_zipWith, Spec.NTTInvVec, Vector.getElem_map]
  interval_cases i
  · exact nttI_t_0
  · exact nttI_t_1
  · exact nttI_t_2
  · exact nttI_t_3

/-- The secret key of the witness: `skEncode` of the literals. -/
def skL : List UInt8 := Spec.skEncode Spec.ML_DSA_44 rhoS Data.kL Data.trL S1v S2v T0v

/-- **`Spec.KeyGen` returns the literal key pair** for `ξ = 0, 1, ..., 31` (ML-DSA-44, default fuel). -/
theorem keygen_lit : Spec.KeyGen Spec.ML_DSA_44 xiL {} = some (Data.pkL, skL) := by
  obtain ⟨⟨pk, sk⟩, hk⟩ := Option.isSome_iff_exists.mp keygen_44_isSome
  have hk' := hk
  unfold Spec.KeyGen at hk'
  obtain ⟨A, s₁, s₂, hA, hS, hpk, hsk⟩ := KeyGen.keygen_some _ _ _ _ _ hk'
  rw [hout_44] at hA hS hpk hsk
  have hA' : Spec.ExpandA Spec.ML_DSA_44 512 rhoS = some A := hA
  have hAv : A = Av := Option.some.inj (hA'.symm.trans expandA_lit)
  have hS' : Spec.ExpandS Spec.ML_DSA_44 512 rho1S = some (s₁, s₂) := hS
  obtain ⟨hs1, hs2⟩ := expandS_lit hS'
  subst hAv hs1 hs2
  rw [tvec_lit, p2r_lit] at hpk hsk
  have hpk2 : pkEncode Spec.ML_DSA_44 (slice outL 0 32) (T1v, T0v).1 = Data.pkL :=
    (pkEncode_fast _ _ _).trans pk_lit
  have hpk' : pk = Data.pkL := hpk.trans hpk2
  have hsk' : sk = skL := by
    rw [hsk, hpk2, tr_lit, kL_eq]
    rfl
  rw [hk, hpk', hsk']

end TopWitness
end Proofs
