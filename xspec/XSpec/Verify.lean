import XSpec.KeyGen

/-!
# `Verify_internal` (Algorithm 8) and `Verify` (Algorithm 3)

Ours: `Spec.Verify_internal p pk M' σ F : Option Bool`; theirs: `verifyInternal (verifyFips P) P λ H G pk M' σ : Bool`
with `H`, `G` our SHAKE256 / SHAKE128.

Their `verifyInternal` has no length checks (their decoders are total), ours returns `some false` for a key or
signature of the wrong length (`verify_of_length_ne`); the equivalence is stated for inputs of the right
lengths.  For those, ours returns `none` exactly when `ExpandA` or `SampleInBall` runs out of fuel, and:

* `verifyInternal_ours_to_theirs`: if ours returns `some b`, then `b` is their verdict, and the samplers terminate
  on their side;
* `verifyInternal_theirs_to_ours`: if the samplers terminate on their side, ours returns `some b` with `b` their
  verdict for every large enough fuel.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

namespace VF

/-- `w′_Approx = NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁ · 2^d))` (Algorithm 8, step 9). -/
def wApprox (sp : Spec.Params) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (z : Vector RPoly sp.ℓ)
    (t₁ : Vector RPoly sp.k) (c : RPoly) : Vector Spec.Poly sp.k :=
  NTTInvVec (MatrixVectorNTT A (NTTVec (z.map RPoly.toZq)) -
    ScalarVectorNTT (NTT c.toZq) (NTTVec ((t₁.map RPoly.toZq).map (·.map (· * (2 ^ sp.d : Zq))))))

/-- `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` with `μ = H(tr ‖ M′, 64)`, `tr = H(pk, 64)` (steps 6, 7, 12). -/
def cTildePrime (sp : Spec.Params) (pk M' : List UInt8) (w₁ : Vector RPoly sp.k) : List UInt8 :=
  H (H (H pk 64 ++ M') 64 ++ w1Encode sp w₁) (sp.lam / 4)

theorem verify_some (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8) (b : Bool)
    (hpk : pk.length = sp.pkLen) (hσ : σ.length = sp.sigLen)
    (c' : List UInt8) (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k)
    (hsd : Spec.sigDecode sp σ = some (c', z, h))
    (hs : Spec.Verify_internal sp pk M' σ F = some b) :
    ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (c : RPoly),
      Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1 = some A ∧
      Spec.SampleInBall sp F.sampleInBall c' = some c ∧
      b = (decide (‖z‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pk M' (UseHintVec sp h (wApprox sp A z (Spec.pkDecode sp pk).2 c))) := by
  unfold Spec.Verify_internal at hs
  simp [Id.run, hpk, hσ, hsd] at hs
  rcases hA : Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1 with _ | A
  · simp [hA] at hs
  rcases hC : Spec.SampleInBall sp F.sampleInBall c' with _ | c
  · simp [hA, hC] at hs
  simp [hA, hC] at hs
  refine ⟨A, c, rfl, rfl, ?_⟩
  have h2 := Option.some.inj (show some _ = some b from hs)
  rw [← h2]
  simp [wApprox, cTildePrime, Vector.map_map]

theorem verify_of_some (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (c' : List UInt8) (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k)
    (hpk : pk.length = sp.pkLen) (hσ : σ.length = sp.sigLen)
    (hsd : Spec.sigDecode sp σ = some (c', z, h))
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (c : RPoly)
    (hA : Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1 = some A)
    (hC : Spec.SampleInBall sp F.sampleInBall c' = some c) :
    Spec.Verify_internal sp pk M' σ F =
      some (decide (‖z‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pk M' (UseHintVec sp h (wApprox sp A z (Spec.pkDecode sp pk).2 c))) := by
  unfold Spec.Verify_internal
  simp [Id.run, hpk, hσ, hsd, hA, hC]
  simp [wApprox, cTildePrime, Vector.map_map]
  rfl

end VF


/-! ## Leaf lemmas -/

theorem scalarVectorNTT_get {n : ℕ} (c : Poly) (v : Vector Poly n) (r : ℕ) (hr : r < n) :
    (ScalarVectorNTT c v)[r]! = MultiplyNTT c v[r]! := by
  have h : ScalarVectorNTT c v = (List.range' 0 n).foldl
      (fun (w : Vector Poly n) a => w.set! a (MultiplyNTT c v[a]!)) (Vector.replicate n Poly.zero) := by
    unfold ScalarVectorNTT
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [h, getElem!_pos _ r (by simpa using hr)]
  refine (EB.vec_fold_gen (m := n) Poly.zero (fun a => MultiplyNTT c v[a]!) n r hr).trans ?_
  rw [if_pos hr]

theorem fipsNTT_of_toZq (f : ℕ → ℤ) (u : Poly) (h : toZq f = I u) : fipsNTT f = canon (NTT u) := by
  unfold fipsNTT
  rw [h, nttSpec_eq, ofZq_I]

theorem toZq_shift (t : RPoly) (d : ℕ) :
    toZq (fun i => rfn t i * 2 ^ d) = I ((RPoly.toZq t).map (· * (2 ^ d : Zq))) := by
  funext i
  by_cases hi : i < 256
  · simp only [toZq, OcamlPq.MLDSA.castArr, rfn, I, RPoly.toZq]
    rw [getElem!_pos t i (by simpa using hi), getElem!_pos (Vector.map _ _) i (by simpa using hi)]
    simp
  · simp only [toZq, OcamlPq.MLDSA.castArr, rfn, I, RPoly.toZq]
    rw [getElem!_neg t i (by simpa using hi), getElem!_neg (Vector.map _ _) i (by simpa using hi)]
    simp [default_zq]

theorem useHintSpec_zero (γ2 : ℤ) (h : 0 < γ2) : OcamlPq.MLDSA.useHintSpec γ2 0 0 = 0 := by
  unfold OcamlPq.MLDSA.useHintSpec OcamlPq.MLDSA.decomposeSpec OcamlPq.MLDSA.modPM
  have h1 : ¬ ((0 : ℤ) > γ2) := by omega
  have h2 : ¬ ((0 : ℤ) = OcamlPq.MLDSA.q - 1) := by unfold OcamlPq.MLDSA.q; omega
  simp [h1, h2]

theorem hpoly_apply {k : ℕ} (H : Vector HintPoly k) (r i : ℕ) (hr : r < k) (hi : i < 256) :
    hpoly H r i = if (H[r]!)[i]! then 1 else 0 := by
  unfold hpoly hv
  by_cases h : (H[r]!)[i]! = true <;> simp [h, hr, hi]

theorem hpoly_ge {k : ℕ} (H : Vector HintPoly k) (r i : ℕ) (hi : 256 ≤ i) : hpoly H r i = 0 := by
  unfold hpoly hv
  have : ¬ i < 256 := by omega
  simp [this]

theorem useHintVec_get {n : ℕ} (p : Spec.Params) (H : Vector HintPoly n) (W : Vector Poly n) (r : ℕ) (hr : r < n)
    (i : ℕ) (hi : i < 256) :
    ((UseHintVec p H W)[r]!)[i]! = UseHint p ((H[r]!)[i]!) ((W[r]!)[i]!) := by
  have h1 : (UseHintVec p H W)[r]! = Vector.zipWith (UseHint p) H[r] W[r] := by
    rw [getElem!_pos _ r (by simpa using hr)]
    simp [UseHintVec]
  rw [h1, getElem!_pos H r (by simpa using hr), getElem!_pos W r (by simpa using hr),
    getElem!_pos _ i (by simpa using hi), getElem!_pos H[r] i (by simpa using hi),
    getElem!_pos W[r] i (by simpa using hi)]
  simp

/-- Row `r` of `UseHintVec`, as an index function. -/
theorem useHintVec_rfn {p : Spec.Params} (hp : Std3 p) (H : Vector HintPoly p.k) (W : Vector Poly p.k) (r : ℕ)
    (hr : r < p.k) :
    rfn ((UseHintVec p H W)[r]!) =
      fun i => OcamlPq.MLDSA.useHintSpec (p.γ₂ : ℤ) (hpoly H r i) (canon (W[r]!) i) := by
  funext i
  by_cases hi : i < 256
  · rw [hpoly_apply H r i hr hi]
    simp only [rfn, canon]
    rw [useHintVec_get p H W r hr i hi, useHint_eq]
  · have hi' : 256 ≤ i := by omega
    rw [hpoly_ge H r i hi', canon_zero_of_ge _ hi']
    simp only [rfn]
    rw [getElem!_neg _ i (by simpa using hi)]
    have hg : 0 < (p.γ₂ : ℤ) := by rcases hp with rfl | rfl | rfl <;> decide +kernel
    rw [useHintSpec_zero _ hg]
    rfl

/-! ## ocaml-pq's `Verify_internal`, unfolded -/

/-- ocaml-pq's `w′_Approx` (Algorithm 8 step 9), as a function of the decoded data. -/
def wApproxTh (P : OcamlPq.MLDSAAlg.Params) (A : OcamlPq.MLDSAAlg.PolyMat) (z t1 : OcamlPq.MLDSAAlg.PolyVec)
    (c : OcamlPq.MLDSAAlg.Poly) : OcamlPq.MLDSAAlg.PolyVec :=
  fun r => fipsNTTinv (fipsSubPoly (fipsMulMatVec P.l A (fun i => fipsNTT (z i)) r)
    (fipsMulNTT (fipsNTT c) (fipsNTT (fun i => t1 r i * 2 ^ OcamlPq.MLDSAAlg.d))))

/-- `w1FoldFips` for an abstract `VerifyFips` bundle. -/
def w1FoldV (F : OcamlPq.MLDSAAlg.VerifyFips) (P : OcamlPq.MLDSAAlg.Params) (w1 : OcamlPq.MLDSAAlg.PolyVec) :
    OcamlPq.MLDSAAlg.Bytes :=
  (List.range P.k).foldl (fun acc i => acc ++ F.simpleBitPack (w1 i)
    ((OcamlPq.MLDSAAlg.q - 1) / (2 * P.gamma2) - 1)) []

/-- `wApproxTh` for an abstract `VerifyFips` bundle. -/
def wApproxV (F : OcamlPq.MLDSAAlg.VerifyFips) (P : OcamlPq.MLDSAAlg.Params) (A : OcamlPq.MLDSAAlg.PolyMat)
    (z t1 : OcamlPq.MLDSAAlg.PolyVec) (c : OcamlPq.MLDSAAlg.Poly) : OcamlPq.MLDSAAlg.PolyVec :=
  fun r => F.NTTinv (F.subPoly (F.mulMatVec A (fun i => F.NTT (z i)) r)
    (F.mulNTT (F.NTT c) (F.NTT (fun i => t1 r i * 2 ^ OcamlPq.MLDSAAlg.d))))

theorem verifyInternal_of_decode (F : OcamlPq.MLDSAAlg.VerifyFips) (P : OcamlPq.MLDSAAlg.Params) (lam : ℕ)
    (H G : OcamlPq.MLDSAAlg.XOF) (pk M' sig cT : OcamlPq.MLDSAAlg.Bytes) (z h : OcamlPq.MLDSAAlg.PolyVec)
    (hs : F.sigDecode sig = some (cT, z, h)) :
    OcamlPq.MLDSAAlg.verifyInternal F P lam H G pk M' sig =
      (F.zNormOk z && decide (cT = H.squeeze (H.squeeze (H.squeeze pk 64 ++ M') 64 ++
        w1FoldV F P (fun r i => F.useHint (h r i)
          (wApproxV F P (OcamlPq.MLDSAAlg.expandA G (F.pkDecode pk).1) z (F.pkDecode pk).2
            (OcamlPq.MLDSAAlg.sampleInBall P.tau (H cT)) r i))) (lam / 4))) := by
  unfold OcamlPq.MLDSAAlg.verifyInternal
  rw [hs]
  rfl

theorem wApproxV_verifyFips (P : OcamlPq.MLDSAAlg.Params) (A : OcamlPq.MLDSAAlg.PolyMat)
    (z t1 : OcamlPq.MLDSAAlg.PolyVec) (c : OcamlPq.MLDSAAlg.Poly) :
    wApproxV (verifyFips P) P A z t1 c = wApproxTh P A z t1 c := rfl

theorem verifyInternal_of_none (P : OcamlPq.MLDSAAlg.Params) (lam : ℕ) (H G : OcamlPq.MLDSAAlg.XOF)
    (pk M' sig : OcamlPq.MLDSAAlg.Bytes) (hs : fipsSigDecode P sig = none) :
    OcamlPq.MLDSAAlg.verifyInternal (verifyFips P) P lam H G pk M' sig = false := by
  have hs' : (verifyFips P).sigDecode sig = none := hs
  unfold OcamlPq.MLDSAAlg.verifyInternal
  rw [hs']

/-! ## `w′_Approx` -/

theorem wApproxTh_eq {p : Spec.Params} (hp : Std3 p) (A : Vector (Vector Poly p.ℓ) p.k)
    (Ath : OcamlPq.MLDSAAlg.PolyMat) (hA : ∀ r < p.k, ∀ s < p.ℓ, canon ((A[r]!)[s]!) = Ath r s)
    (z : Vector RPoly p.ℓ) (t₁ : Vector RPoly p.k) (c : RPoly) (r : ℕ) (hr : r < p.k) :
    wApproxTh (algParams p) Ath (fun i => rfn z[i]!) (fun r => rfn t₁[r]!) (rfn c) r =
      canon ((VF.wApprox p A z t₁ c)[r]!) := by
  have hd : p.d = 13 := hp.d
  have hd2 : OcamlPq.MLDSAAlg.d = 13 := rfl
  unfold VF.wApprox wApproxTh
  rw [NTTInvVec_get _ r hr, ← fipsNTTinv_eq, subVec_get _ _ r hr, canon_sub, matrixVectorNTT_eq _ _ r hr,
    scalarVectorNTT_get _ _ r hr, NTTVec_get _ r hr, ← fipsMulNTT_eq]
  have e1 : fipsMulMatVec p.ℓ Ath (fun i => fipsNTT (rfn z[i]!)) r =
      fipsMulMatVec p.ℓ (fun r s => canon ((A[r]!)[s]!)) (fun s => canon (NTTVec (z.map RPoly.toZq))[s]!) r :=
    fipsMulMatVec_local p.ℓ _ _ _ _ r (fun s hs => (hA r hr s hs).symm) (fun s hs => by
      rw [NTTVec_get _ s hs, map_get!_lt _ _ s hs]
      exact fipsNTT_rfn _)
  have e2 : fipsNTT (fun i => rfn t₁[r]! i * 2 ^ OcamlPq.MLDSAAlg.d) =
      canon (NTT (((t₁.map RPoly.toZq).map (·.map (· * (2 ^ p.d : Zq))))[r]!)) := by
    apply fipsNTT_of_toZq
    rw [map_get!_lt _ _ r hr, map_get!_lt _ _ r hr, hd2, hd]
    exact toZq_shift _ 13
  simp only [algParams]
  rw [e1, e2, fipsNTT_rfn]

/-! ## The `‖z‖∞` check -/

theorem coeffNorm_eq (w : ℤ) (h : |w| ≤ 2 ^ 19) : OcamlPq.MLDSA.coeffNorm w = |w| := by
  have hm : OcamlPq.MLDSA.modPM w OcamlPq.MLDSA.q = w := by
    rw [abs_le] at h
    unfold OcamlPq.MLDSA.modPM OcamlPq.MLDSA.q
    split_ifs <;> omega
  unfold OcamlPq.MLDSA.coeffNorm
  rw [hm]

theorem foldl_max_lt {α : Type} (f : α → ℕ) (l : List α) (B init : ℕ) :
    l.foldl (fun m x => max m (f x)) init < B ↔ init < B ∧ ∀ x ∈ l, f x < B := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, max_lt_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem vec_foldl_max_lt {α : Type} {n : ℕ} (f : α → ℕ) (v : Vector α n) (B init : ℕ) :
    v.foldl (fun m x => max m (f x)) init < B ↔ init < B ∧ ∀ x ∈ v.toList, f x < B := by
  rw [← foldl_max_lt]
  simp [Vector.foldl]

theorem infNorm_lt_iff {n : ℕ} (z : Vector RPoly n) (B : ℕ) (hB : 0 < B) :
    ‖z‖∞ < B ↔ ∀ r < n, ∀ i < 256, ((z[r]!)[i]!).natAbs < B := by
  have key : ∀ x : RPoly, ‖x‖∞ < B ↔ ∀ i < 256, (x[i]!).natAbs < B := by
    intro x
    show x.foldl (fun m a => max m (a.natAbs)) 0 < B ↔ _
    rw [vec_foldl_max_lt]
    simp only [hB, true_and]
    constructor
    · intro h i hi
      rw [getElem!_pos x i (by simpa using hi)]
      exact h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))
    · intro h y hy
      obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hy)
      have := h i hi
      rwa [getElem!_pos x i (by simpa using hi)] at this
  show z.foldl (fun m a => max m (InfNorm.infNorm a)) 0 < B ↔ _
  rw [vec_foldl_max_lt]
  simp only [hB, true_and]
  constructor
  · intro h r hr i hi
    have h1 : ‖z[r]‖∞ < B := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hr))
    rw [getElem!_pos z r (by simpa using hr)]
    exact (key _).mp h1 i hi
  · intro h x hx
    obtain ⟨r, hr, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    rw [key]
    intro i hi
    have := h r hr i hi
    rwa [getElem!_pos z r (by simpa using hr)] at this

theorem Std3.two_pow_bitlen {p : Spec.Params} (h : Std3 p) : 2 ^ Spec.bitlen (2 * p.γ₁ - 1) = 2 * p.γ₁ := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem Std3.gamma1_le {p : Spec.Params} (h : Std3 p) : p.γ₁ ≤ 2 ^ 19 := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem sigDecode_z {p : Spec.Params} {σ c' z hh} (hs : Spec.sigDecode p σ = some (c', z, hh)) : z = sigZ p σ := by
  rw [sigDecode_flat] at hs
  obtain ⟨h0, -, he⟩ := Option.map_eq_some_iff.mp hs
  have := (Prod.mk.inj he).2
  exact (Prod.mk.inj this).1.symm

theorem sigZ_range {p : Spec.Params} (hp : Std3 p) (σ : List UInt8) (r : ℕ) (hr : r < p.ℓ) (i : ℕ) (hi : i < 256) :
    |((sigZ p σ)[r]!)[i]!| ≤ (p.γ₁ : ℤ) := by
  rw [getElem!_pos _ r (by simpa using hr), sigZ_get p σ r hr, getElem!_pos _ i (by simpa using hi),
    EB.BitUnpack_get _ _ _ i hi]
  have hb : p.γ₁ - 1 + p.γ₁ = 2 * p.γ₁ - 1 := by
    have : 0 < p.γ₁ := by rcases hp with rfl | rfl | rfl <;> decide +kernel
    omega
  rw [hb]
  generalize slice σ (p.lam / 4 + r * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))) = v
  have hlt := EB.BV_lt (EB.byteBit v) (fun t => EB.byteBit_le _ t)
    (Spec.bitlen (2 * p.γ₁ - 1) * i) (Spec.bitlen (2 * p.γ₁ - 1))
  rw [hp.two_pow_bitlen] at hlt
  rw [abs_le]
  constructor <;> omega

theorem fipsZNormOk_eq {p : Spec.Params} (hp : Std3 p) (z : Vector RPoly p.ℓ)
    (hz : ∀ r < p.ℓ, ∀ i < 256, |(z[r]!)[i]!| ≤ (p.γ₁ : ℤ)) :
    fipsZNormOk (algParams p) (fun r => rfn z[r]!) = decide (‖z‖∞ < p.γ₁ - p.β) := by
  have hB : 0 < p.γ₁ - p.β := by rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hle : p.β ≤ p.γ₁ := by omega
  have hβ : p.τ * p.η = p.β := rfl
  have hbound : ∀ r < p.ℓ, ∀ i < 256, |(z[r]!)[i]!| ≤ 2 ^ 19 := fun r hr i hi =>
    le_trans (hz r hr i hi) (by exact_mod_cast hp.gamma1_le)
  rw [Bool.eq_iff_iff, fipsZNormOk_iff, decide_eq_true_iff, infNorm_lt_iff z _ hB]
  constructor
  · intro h r hr i hi
    have := h r hr i hi
    simp only [rfn, algParams] at this
    rw [coeffNorm_eq _ (hbound r hr i hi), hβ, Int.abs_eq_natAbs] at this
    omega
  · intro h r hr i hi
    have := h r hr i hi
    simp only [rfn, algParams]
    rw [coeffNorm_eq _ (hbound r hr i hi), hβ, Int.abs_eq_natAbs]
    omega

/-! ## The bridge -/

/-- A key for `signFips` (only its `simpleBitPack` field is used below). -/
def dummyKey : OcamlPq.MLDSAAlg.ExpandedKey := ⟨[], [], [], fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

theorem u8ToBytes_inj {a b : List UInt8} (h : u8ToBytes a = u8ToBytes b) : a = b := by
  simpa using congrArg bytesToU8 h

/-- **ocaml-pq's `verifyInternal`, evaluated on the data our `Verify_internal` computes.**  `A` and `c` are the
values of `ExpandA` and `SampleInBall` (compared entrywise with ocaml-pq's `expandA` / `sampleInBall`). -/
theorem verifyInternal_theirs_eq {p : Spec.Params} (hp : Std3 p) (pk M' σ : List UInt8)
    (c' : List UInt8) (z : Vector RPoly p.ℓ) (hh : Vector HintPoly p.k)
    (hsd : Spec.sigDecode p σ = some (c', z, hh))
    (A : Vector (Vector Poly p.ℓ) p.k) (c : RPoly)
    (hA : ∀ r < p.k, ∀ s < p.ℓ, canon ((A[r]!)[s]!) =
      OcamlPq.MLDSAAlg.expandA oursShake128 (u8ToBytes (Spec.pkDecode p pk).1) r s)
    (hC : rfn c = OcamlPq.MLDSAAlg.sampleInBall p.τ (oursShake256 (u8ToBytes c'))) :
    OcamlPq.MLDSAAlg.verifyInternal (verifyFips (algParams p)) (algParams p) p.lam oursShake256 oursShake128
        (u8ToBytes pk) (u8ToBytes M') (u8ToBytes σ) =
      (decide (‖z‖∞ < p.γ₁ - p.β) &&
        c' == VF.cTildePrime p pk M' (UseHintVec p hh (VF.wApprox p A z (Spec.pkDecode p pk).2 c))) := by
  have hsd' : (verifyFips (algParams p)).sigDecode (u8ToBytes σ) =
      some (u8ToBytes c', (fun r => rfn z[r]!), hpoly hh) := by
    have := sigDecode_eq hp σ
    rw [hsd] at this
    exact this.symm
  obtain ⟨hpk1, hpk2⟩ := pkDecode_eq hp pk
  have hz : ∀ r < p.ℓ, ∀ i < 256, |(z[r]!)[i]!| ≤ (p.γ₁ : ℤ) := by
    intro r hr i hi
    rw [sigDecode_z hsd]
    exact sigZ_range hp σ r hr i hi
  rw [verifyInternal_of_decode _ _ _ _ _ _ _ _ _ _ _ hsd']
  refine congrArg₂ and (fipsZNormOk_eq hp z hz) ?_
  have key : ∀ X, X = u8ToBytes (VF.cTildePrime p pk M' (UseHintVec p hh (VF.wApprox p A z (Spec.pkDecode p pk).2 c))) →
      decide (u8ToBytes c' = X) = (c' == VF.cTildePrime p pk M' (UseHintVec p hh (VF.wApprox p A z (Spec.pkDecode p pk).2 c))) := by
    intro X hX
    subst hX
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
    exact ⟨u8ToBytes_inj, fun h => h ▸ rfl⟩
  refine key _ ?_
  have key2 : ∀ Y, Y = u8ToBytes (Spec.w1Encode p (UseHintVec p hh (VF.wApprox p A z (Spec.pkDecode p pk).2 c))) →
      oursShake256.squeeze (oursShake256.squeeze (oursShake256.squeeze (u8ToBytes pk) 64 ++ u8ToBytes M') 64 ++ Y)
        (p.lam / 4) =
      u8ToBytes (VF.cTildePrime p pk M' (UseHintVec p hh (VF.wApprox p A z (Spec.pkDecode p pk).2 c))) := by
    intro Y hY
    subst hY
    simp only [VF.cTildePrime, H_eq, u8ToBytes_append]
  refine key2 _ ?_
  rw [w1Encode_eq hp (signFips (algParams p) dummyKey) (by simp only [signFips])]
  unfold w1FoldV OcamlPq.MLDSAAlg.w1Encode
  refine KG.foldl_range_congr _ _ _ (fun a i hi => ?_) _
  beta_reduce
  simp only [verifyFips, signFips, wApproxV]
  refine congrArg (fun w => a ++ fipsSimpleBitPack w ((OcamlPq.MLDSAAlg.q - 1) / (2 * (algParams p).gamma2) - 1)) ?_
  have hi' : i < p.k := hi
  rw [useHintVec_rfn hp hh _ i hi']
  funext c0
  have e := congrFun (wApproxTh_eq hp A (OcamlPq.MLDSAAlg.expandA oursShake128 (u8ToBytes (Spec.pkDecode p pk).1)) hA
    z (Spec.pkDecode p pk).2 c i hi') c0
  have hC' : rfn c = OcamlPq.MLDSAAlg.sampleInBall (algParams p).tau (oursShake256 (u8ToBytes c')) := hC
  rw [← hpk1, ← hpk2, ← hC']
  exact congrArg (OcamlPq.MLDSA.useHintSpec _ (hpoly hh i c0)) e

/-- Wrong lengths: `Verify_internal` returns `some false` (step 0). -/
theorem verify_of_length_ne (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hl : pk.length ≠ sp.pkLen ∨ σ.length ≠ sp.sigLen) :
    Spec.Verify_internal sp pk M' σ F = some false := by
  unfold Spec.Verify_internal
  simp [Id.run, hl]
  rfl

/-- A malformed hint (`sigDecode = ⊥`): `Verify_internal` returns `some false` before `ExpandA` runs. -/
theorem verify_of_sigDecode_none (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hsd : Spec.sigDecode sp σ = none) :
    Spec.Verify_internal sp pk M' σ F = some false := by
  unfold Spec.Verify_internal
  simp [Id.run, hsd]
  rfl

/-! ## Headline theorems -/

theorem fipsSigDecode_none {p : Spec.Params} (hp : Std3 p) {σ : List UInt8} (hsd : Spec.sigDecode p σ = none) :
    fipsSigDecode (algParams p) (u8ToBytes σ) = none := by
  have := sigDecode_eq hp σ
  rw [hsd] at this
  exact this.symm

/-- **`Verify_internal` (Algorithm 8), ours to theirs.**  For a key and a signature of the right lengths, if our
`Verify_internal` returns `some b` (that is, `ExpandA` and `SampleInBall` finished within their fuel), then `b` is
the verdict of ocaml-pq's `verifyInternal` (its FIPS 204 building blocks, our SHAKE).  No termination hypothesis
is needed: our samplers returning is the termination evidence. -/
theorem verifyInternal_ours_to_theirs {p : Spec.Params} (hp : Std3 p) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen) (b : Bool)
    (h : Spec.Verify_internal p pk M' σ F = some b) :
    b = OcamlPq.MLDSAAlg.verifyInternal (verifyFips (algParams p)) (algParams p) p.lam oursShake256 oursShake128
      (u8ToBytes pk) (u8ToBytes M') (u8ToBytes σ) := by
  cases hsd : Spec.sigDecode p σ with
  | none =>
    rw [verify_of_sigDecode_none p F pk M' σ hsd] at h
    rw [← Option.some.inj h]
    exact (verifyInternal_of_none _ _ _ _ _ _ _ (fipsSigDecode_none hp hsd)).symm
  | some t =>
    obtain ⟨c', z, hh⟩ := t
    obtain ⟨A, c, hA, hC, hb⟩ := VF.verify_some p F pk M' σ b hpk hσ c' z hh hsd h
    rw [verifyInternal_theirs_eq hp pk M' σ c' z hh hsd A c
      (expandA_ours_to_theirs p F.rejNTT _ A hA).2
      (SB.sampleInBall_ours_to_theirs hp c' F.sampleInBall c hC).eq, hb]

/-- **`Verify_internal`, theirs to ours.**  If every `RejNTTPoly` call of ocaml-pq's `ExpandA` terminates on the
public seed of `pk` and `SampleInBall` terminates on the `c̃` of `σ` (if `σ` decodes), then for all large enough
fuel our `Verify_internal` returns `some b`, and `b` is ocaml-pq's verdict. -/
theorem verifyInternal_theirs_to_ours {p : Spec.Params} (hp : Std3 p) (pk M' σ : List UInt8)
    (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen)
    (hA : ExpandATerm p (Spec.pkDecode p pk).1)
    (hC : ∀ c' z hh, Spec.sigDecode p σ = some (c', z, hh) →
      ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns p.τ (oursShake256 (u8ToBytes c')) b) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ b, Spec.Verify_internal p pk M' σ F = some b ∧
        b = OcamlPq.MLDSAAlg.verifyInternal (verifyFips (algParams p)) (algParams p) p.lam oursShake256 oursShake128
          (u8ToBytes pk) (u8ToBytes M') (u8ToBytes σ) := by
  cases hsd : Spec.sigDecode p σ with
  | none =>
    exact ⟨0, fun F _ _ => ⟨false, verify_of_sigDecode_none p F pk M' σ hsd,
      (verifyInternal_of_none _ _ _ _ _ _ _ (fipsSigDecode_none hp hsd)).symm⟩⟩
  | some t =>
    obtain ⟨c', z, hh⟩ := t
    obtain ⟨FA, hFA⟩ := expandA_theirs_to_ours p _ hA
    obtain ⟨b0, hb0⟩ := hC c' z hh hsd
    obtain ⟨FC, hFC⟩ := SB.sampleInBall_theirs_to_ours hp c' _ hb0
    refine ⟨max FA FC, fun F h1 h2 => ?_⟩
    obtain ⟨A, hAF⟩ := hFA F.rejNTT (le_trans (le_max_left _ _) h1)
    obtain ⟨c, hCF, -⟩ := hFC F.sampleInBall (le_trans (le_max_right _ _) h2)
    exact ⟨_, VF.verify_of_some p F pk M' σ c' z hh hpk hσ hsd A c hAF hCF,
      (verifyInternal_theirs_eq hp pk M' σ c' z hh hsd A c
        (expandA_ours_to_theirs p F.rejNTT _ A hAF).2
        (SB.sampleInBall_ours_to_theirs hp c' F.sampleInBall c hCF).eq).symm⟩

/-- **`Verify` (Algorithm 3), ours to theirs.**  ocaml-pq's `mldsaVerify` (a context of more than 255 bytes gives
`false`, as in ours). -/
theorem verify_ours_to_theirs {p : Spec.Params} (hp : Std3 p) (F : Spec.Fuel) (pk M σ ctx : List UInt8)
    (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen) (b : Bool)
    (h : Spec.Verify p pk M σ ctx F = some b) :
    b = OcamlPq.MLDSAAlg.mldsaVerify (verifyFips (algParams p)) (algParams p) p.lam oursShake256 oursShake128
      (u8ToBytes pk) (u8ToBytes M) (u8ToBytes σ) (u8ToBytes ctx) := by
  unfold Spec.Verify at h
  unfold OcamlPq.MLDSAAlg.mldsaVerify
  by_cases hc : ctx.length > 255
  · simp only [Id.run, hc, if_true] at h
    have hc' : (u8ToBytes ctx).length > 255 := by simpa [u8ToBytes] using hc
    simp only [hc', if_true]
    have h' : some false = some b := h
    exact (Option.some.inj h').symm
  · simp only [Id.run, hc, if_false] at h
    have hl : (u8ToBytes ctx).length = ctx.length := by simp [u8ToBytes]
    have hc' : ¬ (u8ToBytes ctx).length > 255 := by rw [hl]; exact hc
    simp only [hc', if_false]
    have h' : Spec.Verify_internal p pk (IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M) σ F = some b := h
    have := verifyInternal_ours_to_theirs hp F pk _ σ hpk hσ b h'
    rw [this]
    congr 2
    simp only [u8ToBytes_append, integerToBytes_alg_eq, hl, List.append_assoc]

/-- A context of more than 255 bytes: `Verify` returns `some false` for every fuel. -/
theorem verify_of_ctx_gt (p : Spec.Params) (F : Spec.Fuel) (pk M σ ctx : List UInt8) (hc : ctx.length > 255) :
    Spec.Verify p pk M σ ctx F = some false := by
  unfold Spec.Verify
  simp [Id.run, hc]
  rfl

/-- **`Verify`, theirs to ours** (context of at most 255 bytes; a longer one is `verify_of_ctx_gt`). -/
theorem verify_theirs_to_ours {p : Spec.Params} (hp : Std3 p) (pk M σ ctx : List UInt8)
    (hc : ctx.length ≤ 255) (hpk : pk.length = p.pkLen) (hσ : σ.length = p.sigLen)
    (hA : ExpandATerm p (Spec.pkDecode p pk).1)
    (hC : ∀ c' z hh, Spec.sigDecode p σ = some (c', z, hh) →
      ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns p.τ (oursShake256 (u8ToBytes c')) b) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ b, Spec.Verify p pk M σ ctx F = some b ∧
        b = OcamlPq.MLDSAAlg.mldsaVerify (verifyFips (algParams p)) (algParams p) p.lam oursShake256 oursShake128
          (u8ToBytes pk) (u8ToBytes M) (u8ToBytes σ) (u8ToBytes ctx) := by
  obtain ⟨F0, hF0⟩ := verifyInternal_theirs_to_ours hp pk
    (IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M) σ hpk hσ hA hC
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨b, hb, hb2⟩ := hF0 F h1 h2
  refine ⟨b, ?_, ?_⟩
  · unfold Spec.Verify
    simp only [Id.run, show ¬ ctx.length > 255 by omega, if_false]
    exact hb
  · unfold OcamlPq.MLDSAAlg.mldsaVerify
    have hl : (u8ToBytes ctx).length = ctx.length := by simp [u8ToBytes]
    have hc' : ¬ (u8ToBytes ctx).length > 255 := by rw [hl]; omega
    simp only [hc', if_false]
    rw [hb2]
    congr 2
    simp only [u8ToBytes_append, integerToBytes_alg_eq, hl, List.append_assoc]

end XSpec
