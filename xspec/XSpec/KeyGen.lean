import XSpec.Vec
import XSpec.Rounding

/-!
# `KeyGen_internal` (Algorithm 6) and `KeyGen` (Algorithm 1)

Ours: `Spec.KeyGen_internal p ξ F = some (pk, sk)`; theirs: `keyGenInternal (keyFips P) P H G ξ` with `H`, `G`
instantiated with our SHAKE256 / SHAKE128 (`oursShake256`, `oursShake128`), a total function of the seed.

* `keyGen_ours_to_theirs`: if ours returns, every `RejNTTPoly` / `RejBoundedPoly` call terminates on ocaml-pq's
  side and the two key pairs are byte for byte equal.
* `keyGen_theirs_to_ours`: if those calls terminate, ours returns for every large enough fuel.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

namespace KG

/-- The vector `t = NTT⁻¹(Â ∘ NTT(s₁)) + s₂` of Algorithm 6, step 5. -/
def tVec (sp : Spec.Params) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ)
    (s₂ : Vector RPoly sp.k) : Vector Spec.Poly sp.k :=
  NTTInvVec (MatrixVectorNTT A (NTTVec (s₁.map RPoly.toZq))) + s₂.map RPoly.toZq

/-- The seed expansion `H(ξ ‖ k ‖ ℓ, 128)` of step 1. -/
def seed (p : Spec.Params) (ξ : List UInt8) : List UInt8 :=
  Spec.H (ξ ++ IntegerToBytes p.k 1 ++ IntegerToBytes p.ℓ 1) 128

theorem keygen_some (sp : Spec.Params) (F : Spec.Fuel) (ξ pk' sk' : List UInt8)
    (hs : Spec.KeyGen_internal sp ξ F = some (pk', sk')) :
    ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k),
      Spec.ExpandA sp F.rejNTT (slice (seed sp ξ) 0 32) = some A ∧
      Spec.ExpandS sp F.rejBounded (slice (seed sp ξ) 32 64) = some (s₁, s₂) ∧
      pk' = Spec.pkEncode sp (slice (seed sp ξ) 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1 ∧
      sk' = Spec.skEncode sp (slice (seed sp ξ) 0 32) (slice (seed sp ξ) 96 32)
        (Spec.H (Spec.pkEncode sp (slice (seed sp ξ) 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64)
        s₁ s₂ (Power2RoundVec sp (tVec sp A s₁ s₂)).2 := by
  unfold Spec.KeyGen_internal at hs
  unfold seed
  generalize Spec.H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hs ⊢
  cases hA : Spec.ExpandA sp F.rejNTT (slice out 0 32) with
  | none => simp [hA] at hs
  | some A =>
    cases hS : Spec.ExpandS sp F.rejBounded (slice out 32 64) with
    | none => simp [hA, hS] at hs
    | some r =>
      obtain ⟨s₁, s₂⟩ := r
      simp [hA, hS] at hs
      exact ⟨A, s₁, s₂, rfl, rfl, hs.1.symm, hs.2.symm⟩

theorem keygen_of_expand (sp : Spec.Params) (F : Spec.Fuel) (ξ : List UInt8)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k)
    (hA : Spec.ExpandA sp F.rejNTT (slice (seed sp ξ) 0 32) = some A)
    (hS : Spec.ExpandS sp F.rejBounded (slice (seed sp ξ) 32 64) = some (s₁, s₂)) :
    ∃ pk sk, Spec.KeyGen_internal sp ξ F = some (pk, sk) := by
  unfold Spec.KeyGen_internal
  unfold seed at hA hS
  generalize Spec.H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hA hS ⊢
  simp [hA, hS]

/-! ### Congruence of ocaml-pq's encoders -/

theorem foldl_range_congr {α : Type} (n : ℕ) (f g : α → ℕ → α) (h : ∀ a i, i < n → f a i = g a i) (a : α) :
    (List.range n).foldl f a = (List.range n).foldl g a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (fun a i hi => h a i (by omega)),
      List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil, h _ n (by omega)]

theorem pkEncode_congr (F : OcamlPq.MLDSAAlg.KeyFips) (P : OcamlPq.MLDSAAlg.Params) (rho : OcamlPq.MLDSAAlg.Bytes)
    (t1 t1' : OcamlPq.MLDSAAlg.PolyVec) (h : ∀ i < P.k, t1 i = t1' i) :
    OcamlPq.MLDSAAlg.pkEncode F P rho t1 = OcamlPq.MLDSAAlg.pkEncode F P rho t1' := by
  unfold OcamlPq.MLDSAAlg.pkEncode
  exact foldl_range_congr _ _ _ (fun a i hi => by rw [h i hi]) _

theorem skEncode_congr (F : OcamlPq.MLDSAAlg.KeyFips) (P : OcamlPq.MLDSAAlg.Params)
    (rho K tr : OcamlPq.MLDSAAlg.Bytes) (s1 s1' s2 s2' t0 t0' : OcamlPq.MLDSAAlg.PolyVec)
    (h1 : ∀ i < P.l, s1 i = s1' i) (h2 : ∀ i < P.k, s2 i = s2' i) (h3 : ∀ i < P.k, t0 i = t0' i) :
    OcamlPq.MLDSAAlg.skEncode F P rho K tr s1 s2 t0 = OcamlPq.MLDSAAlg.skEncode F P rho K tr s1' s2' t0' := by
  unfold OcamlPq.MLDSAAlg.skEncode
  dsimp only
  rw [foldl_range_congr P.l (fun sk i => sk ++ F.bitPack (s1 i) P.eta P.eta)
      (fun sk i => sk ++ F.bitPack (s1' i) P.eta P.eta) (fun a i hi => by rw [h1 i hi]),
    foldl_range_congr P.k (fun sk i => sk ++ F.bitPack (s2 i) P.eta P.eta)
      (fun sk i => sk ++ F.bitPack (s2' i) P.eta P.eta) (fun a i hi => by rw [h2 i hi]),
    foldl_range_congr P.k (fun sk i => sk ++ F.bitPack (t0 i) (2 ^ (OcamlPq.MLDSAAlg.d - 1) - 1)
      (2 ^ (OcamlPq.MLDSAAlg.d - 1))) (fun sk i => sk ++ F.bitPack (t0' i) (2 ^ (OcamlPq.MLDSAAlg.d - 1) - 1)
      (2 ^ (OcamlPq.MLDSAAlg.d - 1))) (fun a i hi => by rw [h3 i hi])]

/-! ### The pieces of `publicParts` -/

theorem fipsAddPoly_rfn (a : ℕ → ℤ) (w : RPoly) : fipsAddPoly a (rfn w) = fipsAddPoly a (canon (RPoly.toZq w)) := by
  unfold fipsAddPoly
  rw [toZq_rfn, toZq_canon]

theorem power2Round_zero : OcamlPq.MLDSA.power2RoundSpec 0 = (0, 0) := by
  decide +kernel

theorem power2RoundVec_get {n : ℕ} (p : Spec.Params) (hd : p.d = 13) (t : Vector Spec.Poly n) (r : ℕ)
    (hr : r < n) :
    (rfn (Power2RoundVec p t).1[r]! = fun i => (OcamlPq.MLDSA.power2RoundSpec (canon t[r]! i)).1) ∧
    (rfn (Power2RoundVec p t).2[r]! = fun i => (OcamlPq.MLDSA.power2RoundSpec (canon t[r]! i)).2) := by
  unfold Power2RoundVec
  simp only []
  refine ⟨?_, ?_⟩ <;> funext i <;> by_cases hi : i < 256
  · rw [map_get!_lt _ _ r hr]
    simp only [rfn]
    rw [map_get!_lt _ _ i hi]
    simp only [canon, power2Round_eq p hd]
  · rw [map_get!_lt _ _ r hr]
    simp only [rfn]
    rw [getElem!_neg _ i (by simpa using hi)]
    simp only [canon, RN.poly_ge _ i hi, ZMod.val_zero, Nat.cast_zero, power2Round_zero]
    rfl
  · rw [map_get!_lt _ _ r hr]
    simp only [rfn]
    rw [map_get!_lt _ _ i hi]
    simp only [canon, power2Round_eq p hd]
  · rw [map_get!_lt _ _ r hr]
    simp only [rfn]
    rw [getElem!_neg _ i (by simpa using hi)]
    simp only [canon, RN.poly_ge _ i hi, ZMod.val_zero, Nat.cast_zero, power2Round_zero]
    rfl

theorem tVec_get {sp : Spec.Params} (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ)
    (s₂ : Vector RPoly sp.k) (r : ℕ) (hr : r < sp.k)
    (S1 : ℕ → OcamlPq.MLDSAAlg.Poly) (S2 : ℕ → OcamlPq.MLDSAAlg.Poly) (M : OcamlPq.MLDSAAlg.PolyMat)
    (cA : ∀ s < sp.ℓ, M r s = canon (A[r]!)[s]!)
    (c1 : ∀ s < sp.ℓ, rfn s₁[s]! = S1 s) (c2 : rfn s₂[r]! = S2 r) :
    canon (tVec sp A s₁ s₂)[r]! =
      fipsAddPoly (fipsNTTinv (fipsMulMatVec sp.ℓ M (fun i => fipsNTT (S1 i)) r)) (S2 r) := by
  unfold tVec
  rw [addVec_get _ _ r hr, canon_add, NTTInvVec_get _ r hr, ← fipsNTTinv_eq,
    matrixVectorNTT_eq _ _ r hr, map_get!_lt _ _ r hr, ← c2, fipsAddPoly_rfn]
  congr 2
  apply fipsMulMatVec_local
  · intro s hs
    exact (cA s hs).symm
  · intro s hs
    rw [← c1 s hs, fipsNTT_rfn, NTTVec_get _ s hs, map_get!_lt _ _ s hs]

end KG

/-- **KeyGen_internal, ours to theirs.**  If ours returns `(pk, sk)` then every sampler call of ocaml-pq's
`KeyGen_internal` terminates (on our SHAKE) and its `(pk, sk)` is ours, byte for byte. -/
theorem keyGen_ours_to_theirs {p : Spec.Params} (hp : Std3 p) (ξ : List UInt8) (F : Spec.Fuel)
    (pk sk : List UInt8) (h : Spec.KeyGen_internal p ξ F = some (pk, sk)) :
    ExpandATerm p (slice (KG.seed p ξ) 0 32) ∧ ExpandSTerm p (slice (KG.seed p ξ) 32 64) ∧
    (u8ToBytes pk, u8ToBytes sk) =
      OcamlPq.MLDSAAlg.keyGenInternal (keyFips (algParams p)) (algParams p) oursShake256 oursShake128
        (u8ToBytes ξ) := by
  obtain ⟨A, s₁, s₂, hA, hS, hpk, hsk⟩ := KG.keygen_some p F ξ pk sk h
  obtain ⟨tA, cA⟩ := expandA_ours_to_theirs p _ _ A hA
  obtain ⟨tS, c1, c2⟩ := expandS_ours_to_theirs p _ _ s₁ s₂ hS
  refine ⟨tA, tS, ?_⟩
  set ρ := slice (KG.seed p ξ) 0 32 with hρ
  set ρ' := slice (KG.seed p ξ) 32 64 with hρ'
  set K := slice (KG.seed p ξ) 96 32 with hK
  have hlen : (KG.seed p ξ).length = 128 := Spec.SHAKE256_length _ _
  -- the seed expansion
  have hseed : u8ToBytes (KG.seed p ξ) = oursShake256.squeeze (u8ToBytes ξ ++
      OcamlPq.MLDSAAlg.integerToBytes (algParams p).k 1 ++ OcamlPq.MLDSAAlg.integerToBytes (algParams p).l 1) 128 := by
    unfold KG.seed
    rw [H_eq, u8ToBytes_append, u8ToBytes_append, integerToBytes_alg_eq, integerToBytes_alg_eq]
    rfl
  have eρ : u8ToBytes ρ = (u8ToBytes (KG.seed p ξ)).take 32 := by
    simp [hρ, slice, u8ToBytes, List.map_take, List.map_drop]
  have eρ' : u8ToBytes ρ' = ((u8ToBytes (KG.seed p ξ)).drop 32).take 64 := by
    simp [hρ', slice, u8ToBytes, List.map_take, List.map_drop]
  have eK : u8ToBytes K = (u8ToBytes (KG.seed p ξ)).drop 96 := by
    have : K = (KG.seed p ξ).drop 96 := by
      simp only [hK, slice]
      apply List.take_of_length_le
      simp [hlen]
    simp [this, u8ToBytes, List.map_drop]
  unfold OcamlPq.MLDSAAlg.keyGenInternal
  rw [← hseed]
  simp only [← eρ, ← eρ', ← eK]
  have hd := hp.d
  set Sx := OcamlPq.MLDSAAlg.expandS oursShake256 (algParams p) (u8ToBytes ρ') with hSx
  set tv := Power2RoundVec p (KG.tVec p A s₁ s₂) with htv
  have ht : ∀ r (hr : r < p.k), canon (KG.tVec p A s₁ s₂)[r]! =
      fipsAddPoly (fipsNTTinv (fipsMulMatVec (algParams p).l
        (OcamlPq.MLDSAAlg.expandA oursShake128 (u8ToBytes ρ)) (fun i => fipsNTT (Sx.1 i)) r)) (Sx.2 r) := by
    intro r hr
    exact KG.tVec_get (sp := p) A s₁ s₂ r hr Sx.1 Sx.2
      (OcamlPq.MLDSAAlg.expandA oursShake128 (u8ToBytes ρ))
      (fun s hs => (cA r hr s hs).symm)
      (fun s hs => by rw [getElem!_pos s₁ s (by simpa using hs)]; exact c1 s hs)
      (by rw [getElem!_pos s₂ r (by simpa using hr)]; exact c2 r hr)
  have hpp1 : ∀ r (hr : r < p.k), (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128
      (u8ToBytes ρ) Sx.1 Sx.2).1 r = rfn tv.1[r]! := by
    intro r hr
    rw [(KG.power2RoundVec_get p hd _ r hr).1, ht r hr]
    rfl
  have hpp2 : ∀ r (hr : r < p.k), (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128
      (u8ToBytes ρ) Sx.1 Sx.2).2 r = rfn tv.2[r]! := by
    intro r hr
    rw [(KG.power2RoundVec_get p hd _ r hr).2, ht r hr]
    rfl
  have hpk' : u8ToBytes pk = OcamlPq.MLDSAAlg.pkEncode (keyFips (algParams p)) (algParams p) (u8ToBytes ρ)
      (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128 (u8ToBytes ρ) Sx.1 Sx.2).1 := by
    rw [hpk, pkEncode_eq hp]
    exact KG.pkEncode_congr _ _ _ _ _ (fun i hi => (hpp1 i hi).symm)
  have htr : u8ToBytes (Spec.H pk 64) = oursShake256.squeeze (OcamlPq.MLDSAAlg.pkEncode (keyFips (algParams p))
      (algParams p) (u8ToBytes ρ) (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128
        (u8ToBytes ρ) Sx.1 Sx.2).1) 64 := by
    rw [H_eq, hpk']
  have hsk' : u8ToBytes sk = OcamlPq.MLDSAAlg.skEncode (keyFips (algParams p)) (algParams p) (u8ToBytes ρ)
      (u8ToBytes K) (oursShake256.squeeze (OcamlPq.MLDSAAlg.pkEncode (keyFips (algParams p))
      (algParams p) (u8ToBytes ρ) (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128
        (u8ToBytes ρ) Sx.1 Sx.2).1) 64) Sx.1 Sx.2
      (OcamlPq.MLDSAAlg.publicParts (keyFips (algParams p)) oursShake128 (u8ToBytes ρ) Sx.1 Sx.2).2 := by
    rw [hsk, skEncode_eq hp, ← htr, ← hpk]
    refine KG.skEncode_congr _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    · intro i hi
      have hi' : i < p.ℓ := hi
      show rfn s₁[i]! = Sx.1 i
      rw [getElem!_pos s₁ i (by simpa using hi')]; exact c1 i hi'
    · intro i hi
      have hi' : i < p.k := hi
      show rfn s₂[i]! = Sx.2 i
      rw [getElem!_pos s₂ i (by simpa using hi')]; exact c2 i hi'
    · intro i hi
      exact (hpp2 i hi).symm
  exact Prod.ext hpk' hsk'

/-- **KeyGen_internal, theirs to ours.**  If every sampler call of ocaml-pq's `KeyGen_internal` terminates, then
ours returns a key pair for every sufficiently large fuel, and it is ocaml-pq's. -/
theorem keyGen_theirs_to_ours {p : Spec.Params} (hp : Std3 p) (ξ : List UInt8)
    (hA : ExpandATerm p (slice (KG.seed p ξ) 0 32)) (hS : ExpandSTerm p (slice (KG.seed p ξ) 32 64)) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.rejBounded →
      ∃ pk sk, Spec.KeyGen_internal p ξ F = some (pk, sk) ∧
        (u8ToBytes pk, u8ToBytes sk) =
          OcamlPq.MLDSAAlg.keyGenInternal (keyFips (algParams p)) (algParams p) oursShake256 oursShake128
            (u8ToBytes ξ) := by
  obtain ⟨F1, h1⟩ := expandA_theirs_to_ours p _ hA
  obtain ⟨F2, h2⟩ := expandS_theirs_to_ours p _ hS
  refine ⟨max F1 F2, fun F hF1 hF2 => ?_⟩
  obtain ⟨A, hA'⟩ := h1 F.rejNTT (le_trans (le_max_left _ _) hF1)
  obtain ⟨s, hS'⟩ := h2 F.rejBounded (le_trans (le_max_right _ _) hF2)
  obtain ⟨pk, sk, hk⟩ := KG.keygen_of_expand p F ξ A s.1 s.2 hA' hS'
  exact ⟨pk, sk, hk, (keyGen_ours_to_theirs hp ξ F pk sk hk).2.2⟩

/-- **KeyGen (Algorithm 1)** is `KeyGen_internal` (step 5), so the two theorems above hold for it as well. -/
theorem keyGen_eq_internal (p : Spec.Params) (ξ : List UInt8) (F : Spec.Fuel) :
    Spec.KeyGen p ξ F = Spec.KeyGen_internal p ξ F := rfl

end XSpec
