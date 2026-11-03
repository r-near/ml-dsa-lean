import XSpec.KeyGen
import XSpec.Verify
import XSpec.Sign
import XSpec.KeccakSponge

/-!
# The top-level equivalences on ocaml-pq's own SHAKE

`Hash.lean` instantiates ocaml-pq's abstract `XOF` with our SHAKE (`oursShake128`, `oursShake256`), so the
equivalence theorems of `KeyGen`, `Verify` and `Sign` are about ocaml-pq's algorithms *with our hash*.
`KeccakSponge.lean` proves `Spec.SHAKE128 M d = Keccak.shake128 d M` (and for SHAKE256) against ocaml-pq's
independent Keccak-f[1600], so this file

* identifies the streams: `oursShake128 = ocamlShake128 = fipsShake128` (and for 256), and
* restates the top-level theorems with `ocamlShake128` / `ocamlShake256` (ocaml-pq's `Mldsa_keccak.shake128` /
  `shake256`) in place of ours.  The restatements are `*_ocaml`; the termination predicates get `O` versions
  (`ExpandATermO`, `ExpandSTermO`, `SignTermO`) that are propositionally equivalent to the originals.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

/-! ## The streams -/

/-- **Our SHAKE128 stream is ocaml-pq's `Mldsa_keccak.shake128` stream.** -/
theorem oursShake128_eq_ocaml : oursShake128 = ocamlShake128 := by
  unfold oursShake128 ocamlShake128
  have h : (fun L M => Spec.SHAKE128 M L) = OcamlPq.Hash.Keccak.shake128 := by
    funext L M; exact KC.SHAKE128_eq_ocaml M L
  rw [h]

/-- **Our SHAKE256 stream is ocaml-pq's `Mldsa_keccak.shake256` stream.** -/
theorem oursShake256_eq_ocaml : oursShake256 = ocamlShake256 := by
  unfold oursShake256 ocamlShake256
  have h : (fun L M => Spec.SHAKE256 M L) = OcamlPq.Hash.Keccak.shake256 := by
    funext L M; exact KC.SHAKE256_eq_ocaml M L
  rw [h]

/-- Our SHAKE128 stream is the stream of ocaml-pq's FIPS 202 `SHAKE128` on bit strings. -/
theorem oursShake128_eq_fips : oursShake128 = fipsShake128 :=
  oursShake128_eq_ocaml.trans fipsShake128_eq.symm

/-- Our SHAKE256 stream is the stream of ocaml-pq's FIPS 202 `SHAKE256` on bit strings. -/
theorem oursShake256_eq_fips : oursShake256 = fipsShake256 :=
  oursShake256_eq_ocaml.trans fipsShake256_eq.symm

/-! ## KeyGen -/

/-- `ExpandATerm` with ocaml-pq's own SHAKE128. -/
def ExpandATermO (p : Spec.Params) (ρ : List UInt8) : Prop :=
  ∀ r < p.k, ∀ s < p.ℓ, ∃ a, OcamlPq.MLDSAAlg.RejNTTPolyReturns
    (ocamlShake128 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes s 1 ++ OcamlPq.MLDSAAlg.integerToBytes r 1)) a

theorem ExpandATermO_iff (p : Spec.Params) (ρ : List UInt8) : ExpandATermO p ρ ↔ ExpandATerm p ρ := by
  unfold ExpandATermO ExpandATerm
  rw [oursShake128_eq_ocaml]

/-- `ExpandSTerm` with ocaml-pq's own SHAKE256. -/
def ExpandSTermO (p : Spec.Params) (ρ : List UInt8) : Prop :=
  (∀ r < p.ℓ, ∃ a, OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (ocamlShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes r 2)) a) ∧
  (∀ r < p.k, ∃ a, OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (ocamlShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes (r + p.ℓ) 2)) a)

theorem ExpandSTermO_iff (p : Spec.Params) (ρ : List UInt8) : ExpandSTermO p ρ ↔ ExpandSTerm p ρ := by
  unfold ExpandSTermO ExpandSTerm
  rw [oursShake256_eq_ocaml]

/-- **KeyGen_internal, ours to theirs, on ocaml-pq's SHAKE.**  `keyGen_ours_to_theirs` with ocaml-pq's
`Mldsa_keccak.shake256` / `shake128` (the seed premises are on the seed `KG.seed p ξ`, which is
`H(ξ ‖ k ‖ ℓ, 128)` computed with our hash; by `KeccakSponge.SHAKE256_eq_ocaml` it is ocaml-pq's too). -/
theorem keyGen_ours_to_theirs_ocaml {p : Spec.Params} (hp : Std3 p) (ξ : List UInt8) (F : Spec.Fuel)
    (pk sk : List UInt8) (h : Spec.KeyGen_internal p ξ F = some (pk, sk)) :
    ExpandATermO p (slice (KG.seed p ξ) 0 32) ∧ ExpandSTermO p (slice (KG.seed p ξ) 32 64) ∧
    (u8ToBytes pk, u8ToBytes sk) =
      OcamlPq.MLDSAAlg.keyGenInternal (keyFips (algParams p)) (algParams p) ocamlShake256 ocamlShake128
        (u8ToBytes ξ) := by
  obtain ⟨hA, hS, he⟩ := keyGen_ours_to_theirs hp ξ F pk sk h
  rw [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at he
  exact ⟨(ExpandATermO_iff _ _).mpr hA, (ExpandSTermO_iff _ _).mpr hS, he⟩

/-- **KeyGen_internal, theirs to ours, on ocaml-pq's SHAKE.** -/
theorem keyGen_theirs_to_ours_ocaml {p : Spec.Params} (hp : Std3 p) (ξ : List UInt8)
    (hA : ExpandATermO p (slice (KG.seed p ξ) 0 32)) (hS : ExpandSTermO p (slice (KG.seed p ξ) 32 64)) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.rejBounded →
      ∃ pk sk, Spec.KeyGen_internal p ξ F = some (pk, sk) ∧
        (u8ToBytes pk, u8ToBytes sk) =
          OcamlPq.MLDSAAlg.keyGenInternal (keyFips (algParams p)) (algParams p) ocamlShake256 ocamlShake128
            (u8ToBytes ξ) := by
  obtain ⟨F0, h⟩ := keyGen_theirs_to_ours hp ξ ((ExpandATermO_iff _ _).mp hA) ((ExpandSTermO_iff _ _).mp hS)
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨pk, sk, hk, he⟩ := h F h1 h2
  rw [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at he
  exact ⟨pk, sk, hk, he⟩

/-! ## Verify -/

/-- **`Verify_internal`, ours to theirs, on ocaml-pq's SHAKE.** -/
theorem verifyInternal_ours_to_theirs_ocaml {p : Spec.Params} (hp : Std3 p) (F : Spec.Fuel)
    (pk M' σ : List UInt8) (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen) (b : Bool)
    (h : Spec.Verify_internal p pk M' σ F = some b) :
    b = OcamlPq.MLDSAAlg.verifyInternal (verifyFips (algParams p)) (algParams p) p.lam ocamlShake256 ocamlShake128
      (u8ToBytes pk) (u8ToBytes M') (u8ToBytes σ) := by
  have := verifyInternal_ours_to_theirs hp F pk M' σ hpk hσ b h
  rwa [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at this

/-- **`Verify_internal`, theirs to ours, on ocaml-pq's SHAKE.** -/
theorem verifyInternal_theirs_to_ours_ocaml {p : Spec.Params} (hp : Std3 p) (pk M' σ : List UInt8)
    (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen)
    (hA : ExpandATermO p (Spec.pkDecode p pk).1)
    (hC : ∀ c' z hh, Spec.sigDecode p σ = some (c', z, hh) →
      ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns p.τ (ocamlShake256 (u8ToBytes c')) b) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ b, Spec.Verify_internal p pk M' σ F = some b ∧
        b = OcamlPq.MLDSAAlg.verifyInternal (verifyFips (algParams p)) (algParams p) p.lam ocamlShake256
          ocamlShake128 (u8ToBytes pk) (u8ToBytes M') (u8ToBytes σ) := by
  rw [← oursShake256_eq_ocaml] at hC
  obtain ⟨F0, h⟩ := verifyInternal_theirs_to_ours hp pk M' σ hpk hσ ((ExpandATermO_iff _ _).mp hA) hC
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨b, hb, he⟩ := h F h1 h2
  rw [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at he
  exact ⟨b, hb, he⟩

/-- **`Verify` (Algorithm 3), ours to theirs, on ocaml-pq's SHAKE.** -/
theorem verify_ours_to_theirs_ocaml {p : Spec.Params} (hp : Std3 p) (F : Spec.Fuel) (pk M σ ctx : List UInt8)
    (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen) (b : Bool)
    (h : Spec.Verify p pk M σ ctx F = some b) :
    b = OcamlPq.MLDSAAlg.mldsaVerify (verifyFips (algParams p)) (algParams p) p.lam ocamlShake256 ocamlShake128
      (u8ToBytes pk) (u8ToBytes M) (u8ToBytes σ) (u8ToBytes ctx) := by
  have := verify_ours_to_theirs hp F pk M σ ctx hpk hσ b h
  rwa [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at this

/-- **`Verify`, theirs to ours, on ocaml-pq's SHAKE** (context of at most 255 bytes). -/
theorem verify_theirs_to_ours_ocaml {p : Spec.Params} (hp : Std3 p) (pk M σ ctx : List UInt8)
    (hc : ctx.length ≤ 255) (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen)
    (hA : ExpandATermO p (Spec.pkDecode p pk).1)
    (hC : ∀ c' z hh, Spec.sigDecode p σ = some (c', z, hh) →
      ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns p.τ (ocamlShake256 (u8ToBytes c')) b) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ b, Spec.Verify p pk M σ ctx F = some b ∧
        b = OcamlPq.MLDSAAlg.mldsaVerify (verifyFips (algParams p)) (algParams p) p.lam ocamlShake256 ocamlShake128
          (u8ToBytes pk) (u8ToBytes M) (u8ToBytes σ) (u8ToBytes ctx) := by
  rw [← oursShake256_eq_ocaml] at hC
  obtain ⟨F0, h⟩ := verify_theirs_to_ours hp pk M σ ctx hc hpk hσ ((ExpandATermO_iff _ _).mp hA) hC
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨b, hb, he⟩ := h F h1 h2
  rw [oursShake128_eq_ocaml, oursShake256_eq_ocaml] at he
  exact ⟨b, hb, he⟩

/-! ## Sign -/

namespace SGB

/-- `μ = H(tr ‖ M′, 64)` on ocaml-pq's SHAKE256. -/
def muThO (sp : Spec.Params) (sk M' : List UInt8) : OcamlPq.MLDSAAlg.Bytes :=
  ocamlShake256.squeeze ((keyOfSk sp sk).tr ++ u8ToBytes M') 64

theorem muThO_eq (sp : Spec.Params) (sk M' : List UInt8) : muThO sp sk M' = muTh sp sk M' := by
  unfold muThO muTh
  rw [oursShake256_eq_ocaml]

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)` on ocaml-pq's SHAKE256. -/
def rppThO (sp : Spec.Params) (sk M' rnd : List UInt8) : OcamlPq.MLDSAAlg.Bytes :=
  ocamlShake256.squeeze ((keyOfSk sp sk).key ++ u8ToBytes rnd ++ muThO sp sk M') 64

theorem rppThO_eq (sp : Spec.Params) (sk M' rnd : List UInt8) : rppThO sp sk M' rnd = rppTh sp sk M' rnd := by
  unfold rppThO rppTh
  rw [muThO_eq, oursShake256_eq_ocaml]

/-- The masking vector `y` of attempt `κ` on ocaml-pq's SHAKE256. -/
def mkO (sp : Spec.Params) (rhoPP : OcamlPq.MLDSAAlg.Bytes) (κ : ℕ) : OcamlPq.MLDSAAlg.PolyVec :=
  fun r => OcamlPq.MLDSAAlg.expandMask ocamlShake256 (algParams sp) fipsBitUnpack rhoPP κ r

theorem mkO_eq (sp : Spec.Params) (rhoPP : OcamlPq.MLDSAAlg.Bytes) (κ : ℕ) : mkO sp rhoPP κ = mk sp rhoPP κ := by
  unfold mkO mk
  rw [oursShake256_eq_ocaml]

/-- One attempt of ocaml-pq's loop, on ocaml-pq's SHAKE. -/
noncomputable def thStepO (sp : Spec.Params) (key : OcamlPq.MLDSAAlg.ExpandedKey)
    (rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes) (j : ℕ) : Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam ocamlShake256
    (OcamlPq.MLDSAAlg.expandA ocamlShake128 rho) mu (mkO sp rhoPP (j * sp.ℓ))

theorem thStepO_eq (sp : Spec.Params) (key : OcamlPq.MLDSAAlg.ExpandedKey)
    (rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes) (j : ℕ) :
    thStepO sp key rho mu rhoPP j = thStep sp key rho mu rhoPP j := by
  unfold thStepO thStep
  rw [mkO_eq, oursShake256_eq_ocaml, oursShake128_eq_ocaml]

/-- `SignTerm` with ocaml-pq's own SHAKE. -/
def SignTermO (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) : Prop :=
  ∀ j, j < m →
    (∀ j', j' < j → thStepO sp (keyOfSk sp sk) (keyOfSk sp sk).rho (muThO sp sk M') (rppThO sp sk M' rnd) j' =
      none) →
    ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns (algParams sp).tau
      (ocamlShake256 (alg7CT (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam ocamlShake256
        (OcamlPq.MLDSAAlg.expandA ocamlShake128 (keyOfSk sp sk).rho) (muThO sp sk M')
        (mkO sp (rppThO sp sk M' rnd) (j * sp.ℓ)))) b

theorem SignTermO_iff (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) :
    SignTermO sp sk M' rnd m ↔ SignTerm sp sk M' rnd m := by
  unfold SignTermO SignTerm
  simp only [thStepO_eq, muThO_eq, rppThO_eq, mkO_eq, oursShake256_eq_ocaml, oursShake128_eq_ocaml]

/-- ocaml-pq's `signInternalMu` for our decoded key, on ocaml-pq's SHAKE. -/
noncomputable def thSignInternalO (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) :
    Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.signInternalMu (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam ocamlShake256
    ocamlShake128 (keyOfSk sp sk).rho (keyOfSk sp sk).key (muThO sp sk M') (u8ToBytes rnd) m

theorem thSignInternalO_eq (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) :
    thSignInternalO sp sk M' rnd m = thSignInternal sp sk M' rnd m := by
  unfold thSignInternalO thSignInternal
  rw [muThO_eq, oursShake256_eq_ocaml, oursShake128_eq_ocaml]

/-- ocaml-pq's `mldsaSign` for our decoded key, on ocaml-pq's SHAKE. -/
noncomputable def thSignO (sp : Spec.Params) (sk M ctx rnd : List UInt8) : Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.mldsaSign (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam ocamlShake256
    ocamlShake128 (keyOfSk sp sk) (u8ToBytes M) (u8ToBytes ctx) (u8ToBytes rnd)

theorem thSignO_eq (sp : Spec.Params) (sk M ctx rnd : List UInt8) :
    thSignO sp sk M ctx rnd = thSign sp sk M ctx rnd := by
  unfold thSignO thSign
  rw [oursShake256_eq_ocaml, oursShake128_eq_ocaml]

/-- **`Sign_internal`, ours to theirs, on ocaml-pq's SHAKE** (bounded loop). -/
theorem signInternalBounded_ours_to_theirs_ocaml {sp : Spec.Params} (hp : Std3 sp) (B : ℕ)
    (sk M' rnd : List UInt8) (F : Spec.Fuel) (σ : List UInt8)
    (h : Spec.Sign_internal_bounded sp B sk M' rnd F = some σ) :
    ∃ a, a < B ∧ ∀ m, thSignInternalO sp sk M' rnd m = if a < m then some (u8ToBytes σ) else none := by
  obtain ⟨a, ha, h'⟩ := signInternalBounded_ours_to_theirs hp B sk M' rnd F σ h
  exact ⟨a, ha, fun m => by rw [thSignInternalO_eq]; exact h' m⟩

/-- **`Sign_internal`, theirs to ours, on ocaml-pq's SHAKE** (bounded loop, accepting). -/
theorem signInternalBounded_theirs_to_ours_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (B m : ℕ) (hm : m ≤ B) (hmℓ : m * sp.ℓ ≤ 2 ^ 16) (s : OcamlPq.MLDSAAlg.Bytes)
    (hs : thSignInternalO sp sk M' rnd m = some s) (hA : ExpandATermO sp (Spec.skDecode sp sk).1)
    (hC : SignTermO sp sk M' rnd m) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign_internal_bounded sp B sk M' rnd F = some σ ∧ u8ToBytes σ = s :=
  signInternalBounded_theirs_to_ours hp sk M' rnd B m hm hmℓ s (by rwa [thSignInternalO_eq] at hs)
    ((ExpandATermO_iff _ _).mp hA) ((SignTermO_iff _ _ _ _ _).mp hC)

/-- **`Sign_internal`, theirs to ours, on ocaml-pq's SHAKE** (bounded loop, exhausted). -/
theorem signInternalBounded_theirs_to_ours_none_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (m : ℕ) (hmℓ : m * sp.ℓ ≤ 2 ^ 16) (hs : thSignInternalO sp sk M' rnd m = none)
    (hA : ExpandATermO sp (Spec.skDecode sp sk).1) (hC : SignTermO sp sk M' rnd m) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      Spec.Sign_internal_bounded sp m sk M' rnd F = none :=
  signInternalBounded_theirs_to_ours_none hp sk M' rnd m hmℓ (by rwa [thSignInternalO_eq] at hs)
    ((ExpandATermO_iff _ _).mp hA) ((SignTermO_iff _ _ _ _ _).mp hC)

/-- **`Sign_internal`, ours to theirs, on ocaml-pq's SHAKE** (`B = kappaBudget`, 821 iterations). -/
theorem signInternal_ours_to_theirs_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (F : Spec.Fuel) (σ : List UInt8) (h : Spec.Sign_internal sp sk M' rnd F = some σ) :
    ∃ a, a < Spec.kappaBudget sp ∧ (a < 821 → thSignInternalO sp sk M' rnd 821 = some (u8ToBytes σ)) ∧
      (821 ≤ a → thSignInternalO sp sk M' rnd 821 = none) := by
  obtain ⟨a, ha, h1, h2⟩ := signInternal_ours_to_theirs hp sk M' rnd F σ h
  exact ⟨a, ha, fun h => by rw [thSignInternalO_eq]; exact h1 h, fun h => by rw [thSignInternalO_eq]; exact h2 h⟩

/-- **`Sign_internal`, theirs to ours, on ocaml-pq's SHAKE** (821 iterations, accepting). -/
theorem signInternal_theirs_to_ours_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (s : OcamlPq.MLDSAAlg.Bytes) (hs : thSignInternalO sp sk M' rnd 821 = some s)
    (hA : ExpandATermO sp (Spec.skDecode sp sk).1) (hC : SignTermO sp sk M' rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign_internal sp sk M' rnd F = some σ ∧ u8ToBytes σ = s :=
  signInternal_theirs_to_ours hp sk M' rnd s (by rwa [thSignInternalO_eq] at hs)
    ((ExpandATermO_iff _ _).mp hA) ((SignTermO_iff _ _ _ _ _).mp hC)

/-- **`Sign` (Algorithm 2), ours to theirs, on ocaml-pq's SHAKE.** -/
theorem sign_ours_to_theirs_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8) (F : Spec.Fuel)
    (σ : List UInt8) (h : Spec.Sign sp sk M ctx rnd F = some σ) :
    ctx.length ≤ 255 ∧ ∃ a, a < Spec.kappaBudget sp ∧
      (a < 821 → thSignO sp sk M ctx rnd = some (u8ToBytes σ)) ∧ (821 ≤ a → thSignO sp sk M ctx rnd = none) := by
  obtain ⟨hc, a, ha, h1, h2⟩ := sign_ours_to_theirs hp sk M ctx rnd F σ h
  exact ⟨hc, a, ha, fun h => by rw [thSignO_eq]; exact h1 h, fun h => by rw [thSignO_eq]; exact h2 h⟩

/-- **`Sign`, theirs to ours, on ocaml-pq's SHAKE** (accepting; `|ctx| ≤ 255`). -/
theorem sign_theirs_to_ours_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8)
    (hc : ctx.length ≤ 255) (s : OcamlPq.MLDSAAlg.Bytes) (hs : thSignO sp sk M ctx rnd = some s)
    (hA : ExpandATermO sp (Spec.skDecode sp sk).1) (hC : SignTermO sp sk (mPrime M ctx) rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign sp sk M ctx rnd F = some σ ∧ u8ToBytes σ = s :=
  sign_theirs_to_ours hp sk M ctx rnd hc s (by rwa [thSignO_eq] at hs)
    ((ExpandATermO_iff _ _).mp hA) ((SignTermO_iff _ _ _ _ _).mp hC)

/-- **`Sign`, theirs to ours, on ocaml-pq's SHAKE** (ocaml-pq's 821 iterations exhausted). -/
theorem sign_theirs_to_ours_none_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8)
    (hc : ctx.length ≤ 255) (hs : thSignO sp sk M ctx rnd = none)
    (hA : ExpandATermO sp (Spec.skDecode sp sk).1) (hC : SignTermO sp sk (mPrime M ctx) rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      Spec.Sign_internal_bounded sp 821 sk (mPrime M ctx) rnd F = none :=
  sign_theirs_to_ours_none hp sk M ctx rnd hc (by rwa [thSignO_eq] at hs)
    ((ExpandATermO_iff _ _).mp hA) ((SignTermO_iff _ _ _ _ _).mp hC)

/-- A context of more than 255 bytes: both `Sign`s return `none`, on ocaml-pq's SHAKE. -/
theorem sign_of_ctx_gt_both_ocaml (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel)
    (hc : ctx.length > 255) : Spec.Sign sp sk M ctx rnd F = none ∧ thSignO sp sk M ctx rnd = none := by
  rw [thSignO_eq]
  exact sign_of_ctx_gt_both sp sk M ctx rnd F hc

/-- **Our success supplies the termination hypotheses**, on ocaml-pq's SHAKE. -/
theorem signTerm_of_ours_ocaml {sp : Spec.Params} (hp : Std3 sp) (B : ℕ) (sk M' rnd : List UInt8)
    (F : Spec.Fuel) (σ : List UInt8) (h : Spec.Sign_internal_bounded sp B sk M' rnd F = some σ) :
    ExpandATermO sp (Spec.skDecode sp sk).1 ∧ ∀ m, SignTermO sp sk M' rnd m := by
  obtain ⟨hA, hC⟩ := signTerm_of_ours hp B sk M' rnd F σ h
  exact ⟨(ExpandATermO_iff _ _).mpr hA, fun m => (SignTermO_iff _ _ _ _ _).mpr (hC m)⟩

/-- The same for `Sign_internal`. -/
theorem signTerm_of_ours_internal_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (F : Spec.Fuel) (σ : List UInt8) (h : Spec.Sign_internal sp sk M' rnd F = some σ) :
    ExpandATermO sp (Spec.skDecode sp sk).1 ∧ ∀ m, SignTermO sp sk M' rnd m :=
  signTerm_of_ours_ocaml hp _ sk M' rnd F σ h

/-- The same for `Sign`. -/
theorem signTerm_of_ours_sign_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8)
    (F : Spec.Fuel) (σ : List UInt8) (h : Spec.Sign sp sk M ctx rnd F = some σ) :
    ExpandATermO sp (Spec.skDecode sp sk).1 ∧ ∀ m, SignTermO sp sk (mPrime M ctx) rnd m := by
  obtain ⟨hA, hC⟩ := signTerm_of_ours_sign hp sk M ctx rnd F σ h
  exact ⟨(ExpandATermO_iff _ _).mpr hA, fun m => (SignTermO_iff _ _ _ _ _).mpr (hC m)⟩

/-- **Composition with ocaml-pq's decoder, on ocaml-pq's SHAKE**: `thSignO` is ocaml-pq's `mldsaSign` on the key
their decoder returned. -/
theorem thSign_of_decode_ocaml {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8) {rho key tr : List ℕ}
    {s1 s2 t0 : List (List ℤ)}
    (h : OcamlPq.Encoding.Mldsa.decodeSk (encParams (algParams sp)) (bytesN sk) =
      some (rho, key, tr, s1, s2, t0)) :
    thSignO sp sk M ctx rnd =
      OcamlPq.MLDSAAlg.mldsaSign
        (signFips (algParams sp) ⟨natToBytes rho, natToBytes key, natToBytes tr, listsToVec s1, listsToVec s2,
          listsToVec t0⟩) (algParams sp) sp.lam ocamlShake256 ocamlShake128
        ⟨natToBytes rho, natToBytes key, natToBytes tr, listsToVec s1, listsToVec s2, listsToVec t0⟩
        (u8ToBytes M) (u8ToBytes ctx) (u8ToBytes rnd) := by
  have := thSign_of_decode hp sk M ctx rnd h
  rw [thSignO_eq, this, oursShake256_eq_ocaml, oursShake128_eq_ocaml]

end SGB

end XSpec
