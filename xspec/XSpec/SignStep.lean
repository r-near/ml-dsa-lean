import XSpec.SignModel

/-!
# One attempt of the signing loop: the response and the rejection tests

`SG.respond` (steps 17-30 of Algorithm 7, on `Vector`s over `Z_q`) against ocaml-pq's `fipsFinish` (the
arithmetic area's `signAttemptSpec` on lists of integers).  The adapters are the ones used throughout:
`canon` (canonical representatives of a `Poly`), `rfn` (an `RPoly`), `hpoly` (a hint).
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

/-! ## Centered representatives and norms -/

theorem zqModPM_eq (a : Zq) : Zq.modPM a = OcamlPq.MLDSA.modPM (a.val : ℤ) OcamlPq.MLDSA.q :=
  modPM_eq (a.val : ℤ) Spec.q

theorem modPM_emod (m α : ℤ) : OcamlPq.MLDSA.modPM (m % α) α = OcamlPq.MLDSA.modPM m α := by
  unfold OcamlPq.MLDSA.modPM
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- The centered representative of an integer only depends on its residue. -/
theorem modPM_cast (x : ℤ) (a : Zq) (h : (x : Zq) = a) :
    OcamlPq.MLDSA.modPM x OcamlPq.MLDSA.q = Zq.modPM a := by
  have hv : (a.val : ℤ) = x % OcamlPq.MLDSA.q := by
    rw [← h, ZMod.val_intCast]
    rfl
  rw [zqModPM_eq, hv, modPM_emod]

theorem coeffNorm_cast (x : ℤ) (a : Zq) (h : (x : Zq) = a) :
    OcamlPq.MLDSA.coeffNorm x = ((Zq.modPM a).natAbs : ℤ) := by
  unfold OcamlPq.MLDSA.coeffNorm
  rw [modPM_cast x a h, Int.abs_eq_natAbs]

/-- The canonical representative of `a` casts back to `a`. -/
theorem cast_val (a : Zq) : (((a.val : ℤ)) : Zq) = a := by
  simp

theorem toList_range {α : Type} [Inhabited α] {n : ℕ} (v : Vector α n) :
    v.toList = (List.range n).map (fun i => v[i]!) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp [getElem!_pos v i hi]

/-- `‖z‖∞ < B` for a vector of vectors, entrywise. -/
theorem infNorm_vec_lt_iff {α : Type} [InfNorm α] [Inhabited α] {n m : ℕ} (z : Vector (Vector α m) n) (B : ℕ)
    (hB : 0 < B) : ‖z‖∞ < B ↔ ∀ r < n, ∀ i < m, ‖(z[r]!)[i]!‖∞ < B := by
  have key : ∀ x : Vector α m, ‖x‖∞ < B ↔ ∀ i < m, ‖x[i]!‖∞ < B := by
    intro x
    show x.foldl (fun m a => max m (InfNorm.infNorm a)) 0 < B ↔ _
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

/-- Our `‖z‖∞ ≥ B` against ocaml-pq's `infNormGe`, for `z` a vector of polynomials over `Z_q` and an integer matrix
`x` of lifts. -/
theorem infNorm_ge_iff_infNormGe {n : ℕ} (z : Vector Poly n) (x : ℕ → ℕ → ℤ) (B : ℕ) (hB : 0 < B)
    (hx : ∀ r < n, ∀ i < 256, (x r i : Zq) = (z[r]!)[i]!) :
    ‖z‖∞ ≥ B ↔ OcamlPq.MLDSA.infNormGe (mkRows n x) (B : ℤ) := by
  rw [ge_iff_le, ← not_lt, infNorm_vec_lt_iff z B hB, OcamlPq.EndToEnd.MLDSA.infNormGe_mkRows]
  constructor
  · intro h
    by_contra h'
    apply h
    intro r hr i hi
    by_contra h2
    apply h'
    refine ⟨r, hr, i, hi, ?_⟩
    rw [coeffNorm_cast _ _ (hx r hr i hi)]
    have : B ≤ ‖(z[r]!)[i]!‖∞ := not_lt.mp h2
    show (B : ℤ) ≤ ((Zq.modPM (z[r]!)[i]!).natAbs : ℤ)
    exact_mod_cast this
  · rintro ⟨r, hr, i, hi, h⟩ h'
    have := h' r hr i hi
    rw [coeffNorm_cast _ _ (hx r hr i hi)] at h
    have h3 : B ≤ ‖(z[r]!)[i]!‖∞ := by
      show B ≤ (Zq.modPM (z[r]!)[i]!).natAbs
      exact_mod_cast h
    omega

/-- The same for a vector of integer polynomials. -/
theorem infNorm_ge_iff_infNormGe_int {n : ℕ} (z : Vector RPoly n) (x : ℕ → ℕ → ℤ) (B : ℕ) (hB : 0 < B)
    (hx : ∀ r < n, ∀ i < 256, OcamlPq.MLDSA.coeffNorm (x r i) = (((z[r]!)[i]!).natAbs : ℤ)) :
    ‖z‖∞ ≥ B ↔ OcamlPq.MLDSA.infNormGe (mkRows n x) (B : ℤ) := by
  rw [ge_iff_le, ← not_lt, infNorm_vec_lt_iff z B hB, OcamlPq.EndToEnd.MLDSA.infNormGe_mkRows]
  constructor
  · intro h
    by_contra h'
    apply h
    intro r hr i hi
    by_contra h2
    apply h'
    refine ⟨r, hr, i, hi, ?_⟩
    rw [hx r hr i hi]
    have : B ≤ ‖(z[r]!)[i]!‖∞ := not_lt.mp h2
    show (B : ℤ) ≤ (((z[r]!)[i]!).natAbs : ℤ)
    exact_mod_cast this
  · rintro ⟨r, hr, i, hi, h⟩ h'
    have := h' r hr i hi
    rw [hx r hr i hi] at h
    have h3 : B ≤ ‖(z[r]!)[i]!‖∞ := by
      show B ≤ ((z[r]!)[i]!).natAbs
      exact_mod_cast h
    omega

/-! ## Rounding on lifts -/

theorem decomposeSpec_congr (γ x y : ℤ) (h : x % OcamlPq.MLDSA.q = y % OcamlPq.MLDSA.q) :
    OcamlPq.MLDSA.decomposeSpec γ x = OcamlPq.MLDSA.decomposeSpec γ y := by
  rw [← decomposeSpec_emod γ x, ← decomposeSpec_emod γ y, h]

theorem val_cast_emod (x : ℤ) (a : Zq) (h : (x : Zq) = a) : (a.val : ℤ) = x % OcamlPq.MLDSA.q := by
  rw [← h, ZMod.val_intCast]
  rfl

theorem lowBits_cast (p : Spec.Params) (x : ℤ) (a : Zq) (h : (x : Zq) = a) :
    LowBits p a = OcamlPq.MLDSA.lowBits (p.γ₂ : ℤ) x := by
  rw [lowBits_eq]
  unfold OcamlPq.MLDSA.lowBits
  rw [decomposeSpec_congr _ _ x (by rw [val_cast_emod x a h, Int.emod_emod_of_dvd _ (dvd_refl _)])]

theorem makeHintSpec_congr (γ z z' r r' : ℤ) (hz : z % OcamlPq.MLDSA.q = z' % OcamlPq.MLDSA.q)
    (hr : r % OcamlPq.MLDSA.q = r' % OcamlPq.MLDSA.q) :
    OcamlPq.MLDSA.makeHintSpec γ z r = OcamlPq.MLDSA.makeHintSpec γ z' r' := by
  unfold OcamlPq.MLDSA.makeHintSpec OcamlPq.MLDSA.highBits
  rw [decomposeSpec_congr γ r r' hr, decomposeSpec_congr γ (r + z) (r' + z')
    (by rw [Int.add_emod, hz, hr, ← Int.add_emod])]

theorem makeHint_cast (p : Spec.Params) (z' r' : ℤ) (a b : Zq) (hz : (z' : Zq) = a) (hr : (r' : Zq) = b) :
    OcamlPq.MLDSA.makeHintSpec (p.γ₂ : ℤ) z' r' = if MakeHint p a b then 1 else 0 := by
  rw [← makeHint_eq, makeHintSpec_congr _ z' a.val r' b.val
    (by rw [val_cast_emod z' a hz, Int.emod_emod_of_dvd _ (dvd_refl _)])
    (by rw [val_cast_emod r' b hr, Int.emod_emod_of_dvd _ (dvd_refl _)])]

theorem lowBits_abs {p : Spec.Params} (hp : Std3 p) (x : ℤ) : |OcamlPq.MLDSA.lowBits (p.γ₂ : ℤ) x| ≤ 2 ^ 19 := by
  have hf := e2eFacts hp.valid
  have := OcamlPq.MLDSA.decomposeSpec_range hf.gamma2Ok x
  have h2 : (p.γ₂ : ℤ) ≤ 2 ^ 19 := by rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hr : -(p.γ₂ : ℤ) ≤ (OcamlPq.MLDSA.decomposeSpec (p.γ₂ : ℤ) x).2 ∧
      (OcamlPq.MLDSA.decomposeSpec (p.γ₂ : ℤ) x).2 ≤ (p.γ₂ : ℤ) := ⟨this.2.2.1, this.2.2.2.1⟩
  unfold OcamlPq.MLDSA.lowBits
  rw [abs_le]
  constructor <;> omega

/-! ## The hint weight -/

theorem countP_sum (l : List Bool) : (l.countP (fun b => b) : ℤ) = (l.map (fun b => if b then (1 : ℤ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> simp [List.countP_cons, ih] <;> omega

theorem hintWeight_sum {k : ℕ} (h : Vector HintPoly k) :
    (HintWeight h : ℤ) = ((mkRows k (fun r i => if (h[r]!)[i]! then (1 : ℤ) else 0)).map (fun row => row.sum)).sum := by
  rw [HM.hintWeight_eq]
  unfold HM.restW mkRows
  rw [List.drop_zero, toList_range h, Nat.cast_list_sum]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp_apply]
  rw [countP_sum, toList_range (h[r]!), List.map_map]
  rfl

/-! ## Entries of vectors and polynomials -/

theorem vadd_get {α : Type} [Inhabited α] [Add α] {n : ℕ} (a b : Vector α n) (i : ℕ) (hi : i < n) :
    (a + b)[i]! = a[i]! + b[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos a i (by simpa using hi),
    getElem!_pos b i (by simpa using hi)]
  show (Vector.zipWith (· + ·) a b)[i] = a[i] + b[i]
  simp

theorem vsub_get {α : Type} [Inhabited α] [Sub α] {n : ℕ} (a b : Vector α n) (i : ℕ) (hi : i < n) :
    (a - b)[i]! = a[i]! - b[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos a i (by simpa using hi),
    getElem!_pos b i (by simpa using hi)]
  show (Vector.zipWith (· - ·) a b)[i] = a[i] - b[i]
  simp

theorem vneg_get {α : Type} [Inhabited α] [Neg α] {n : ℕ} (a : Vector α n) (i : ℕ) (hi : i < n) :
    (-a)[i]! = -(a[i]!) := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos a i (by simpa using hi)]
  show (Vector.map (- ·) a)[i] = -a[i]
  simp

theorem canon_cast (a : Poly) (i : ℕ) : ((canon a i : ℤ) : Zq) = a[i]! := by
  simp only [canon]
  exact cast_val _

theorem rfn_cast (w : RPoly) (i : ℕ) (hi : i < 256) : ((rfn w i : ℤ) : Zq) = (RPoly.toZq w)[i]! := by
  simp only [rfn, RPoly.toZq]
  rw [getElem!_pos w i (by simpa using hi), getElem!_pos (w.map _) i (by simpa using hi)]
  simp

theorem makeHintVec_get {n : ℕ} (p : Spec.Params) (Z R : Vector Poly n) (r : ℕ) (hr : r < n) (i : ℕ) (hi : i < 256) :
    ((MakeHintVec p Z R)[r]!)[i]! = MakeHint p ((Z[r]!)[i]!) ((R[r]!)[i]!) := by
  have h1 : (MakeHintVec p Z R)[r]! = Vector.zipWith (MakeHint p) Z[r] R[r] := by
    rw [getElem!_pos _ r (by simpa using hr)]
    simp [MakeHintVec]
  rw [h1, getElem!_pos Z r (by simpa using hr), getElem!_pos R r (by simpa using hr),
    getElem!_pos _ i (by simpa using hi), getElem!_pos Z[r] i (by simpa using hi),
    getElem!_pos R[r] i (by simpa using hi)]
  simp

theorem lowBitsVec_get {n : ℕ} (p : Spec.Params) (R : Vector Poly n) (r : ℕ) (hr : r < n) (i : ℕ) (hi : i < 256) :
    ((LowBitsVec p R)[r]!)[i]! = LowBits p ((R[r]!)[i]!) := by
  unfold LowBitsVec
  rw [map_get!_lt _ _ r hr, map_get!_lt _ _ i hi]

/-! ## The products `⟨⟨c s⟩⟩` -/

theorem fipsProduct_eq (c s : RPoly) :
    fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn s)) = canon (NTTInv (MultiplyNTT (NTT c.toZq) (NTT s.toZq))) := by
  unfold fipsProduct
  rw [fipsNTT_rfn, fipsNTT_rfn, fipsMulNTT_eq, fipsNTTinv_eq]

theorem cs_canon {n : ℕ} (c : RPoly) (V : Vector RPoly n) (r : ℕ) (hr : r < n) :
    canon ((NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (V.map RPoly.toZq))))[r]!) =
      fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn V[r]!)) := by
  rw [NTTInvVec_get _ r hr, scalarVectorNTT_get _ _ r hr, NTTVec_get _ r hr, map_get!_lt _ _ r hr, fipsProduct_eq]

/-- `⟨⟨c s₁⟩⟩`, `⟨⟨c s₂⟩⟩`, `⟨⟨c t₀⟩⟩` of an attempt. -/
def csOne (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) : Vector Poly sp.ℓ :=
  NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₁)

def csTwo (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) : Vector Poly sp.k :=
  NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂)

def ctZero (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) : Vector Poly sp.k :=
  NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat)

theorem csOne_canon (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) (r : ℕ) (hr : r < sp.ℓ) :
    canon ((csOne sp P c)[r]!) = fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.s₁[r]!)) :=
  cs_canon c P.s₁ r hr

theorem csTwo_canon (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) (r : ℕ) (hr : r < sp.k) :
    canon ((csTwo sp P c)[r]!) = fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.s₂[r]!)) :=
  cs_canon c P.s₂ r hr

theorem ctZero_canon (sp : Spec.Params) (P : SG.Pre sp) (c : RPoly) (r : ℕ) (hr : r < sp.k) :
    canon ((ctZero sp P c)[r]!) = fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.t₀[r]!)) :=
  cs_canon c P.t₀ r hr

theorem respond_eq' (sp : Spec.Params) (P : SG.Pre sp) (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) :
    SG.respond sp P y w c =
      if sp.γ₁ - sp.β ≤ ‖y + csOne sp P c‖∞ ∨ sp.γ₂ - sp.β ≤ ‖LowBitsVec sp (w - csTwo sp P c)‖∞ then none
      else if sp.γ₂ ≤ ‖ctZero sp P c‖∞ ∨
          sp.ω < HintWeight (MakeHintVec sp (-ctZero sp P c) (w - csTwo sp P c + ctZero sp P c)) then none
      else some (y + csOne sp P c, MakeHintVec sp (-ctZero sp P c) (w - csTwo sp P c + ctZero sp P c)) :=
  rfl

/-! ## The abstract shape of `respond` and `signAttemptSpec` -/

theorem ite_map_congr {α β γ : Type} (f : α → γ) (g : β → γ) {A B C D A' B' C' D' : Prop}
    [Decidable A] [Decidable B] [Decidable C] [Decidable D] [Decidable A'] [Decidable B'] [Decidable C']
    [Decidable D'] (z : α) (z' : β) (hAB : (A ∨ B) ↔ (A' ∨ B')) (hCD : (C ∨ D) ↔ (C' ∨ D'))
    (hv : f z = g z') :
    Option.map f (if A ∨ B then none else if C ∨ D then none else some z) =
      Option.map g (if A' ∨ B' then none else if C' ∨ D' then none else some z') := by
  by_cases h1 : A ∨ B
  · rw [if_pos h1, if_pos (hAB.mp h1)]; rfl
  · rw [if_neg h1, if_neg (fun h => h1 (hAB.mpr h))]
    by_cases h2 : C ∨ D
    · rw [if_pos h2, if_pos (hCD.mp h2)]; rfl
    · rw [if_neg h2, if_neg (fun h => h2 (hCD.mpr h))]
      exact congrArg some hv

/-! ## The response -/

section Resp

variable {sp : Spec.Params} (P : SG.Pre sp) (Y : Vector RPoly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly)

/-- ocaml-pq's `z` entries before the centered reduction, `y + ⟨⟨c s₁⟩⟩` over `ℤ`. -/
def zTh (r i : ℕ) : ℤ := rfn Y[r]! i + fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.s₁[r]!)) i

def cs2Th (r i : ℕ) : ℤ := fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.s₂[r]!)) i

def ct0Th (r i : ℕ) : ℤ := fipsProduct (fipsNTT (rfn c)) (fipsNTT (rfn P.t₀[r]!)) i

def wTh (r i : ℕ) : ℤ := canon w[r]! i

theorem zTh_cast (r : ℕ) (hr : r < sp.ℓ) (i : ℕ) (hi : i < 256) :
    ((zTh P Y c r i : ℤ) : Zq) = (((Y.map RPoly.toZq + csOne sp P c)[r]!)[i]!) := by
  unfold zTh
  rw [← csOne_canon sp P c r hr, Int.cast_add, canon_cast, rfn_cast _ _ hi, addVec_get _ _ r hr,
    map_get!_lt _ _ r hr, vadd_get _ _ i hi]

theorem wTh_cast (r i : ℕ) : ((wTh w r i : ℤ) : Zq) = (w[r]!)[i]! := canon_cast _ _

theorem cs2Th_cast (r : ℕ) (hr : r < sp.k) (i : ℕ) : ((cs2Th P c r i : ℤ) : Zq) = ((csTwo sp P c)[r]!)[i]! := by
  unfold cs2Th
  rw [← csTwo_canon sp P c r hr]
  exact canon_cast _ _

theorem ct0Th_cast (r : ℕ) (hr : r < sp.k) (i : ℕ) : ((ct0Th P c r i : ℤ) : Zq) = ((ctZero sp P c)[r]!)[i]! := by
  unfold ct0Th
  rw [← ctZero_canon sp P c r hr]
  exact canon_cast _ _

theorem N1 (hp : Std3 sp) :
    sp.γ₁ - sp.β ≤ ‖Y.map RPoly.toZq + csOne sp P c‖∞ ↔
      OcamlPq.MLDSA.infNormGe (mkRows sp.ℓ (zTh P Y c)) ((sp.γ₁ : ℤ) - (sp.β : ℤ)) := by
  have hB : 0 < sp.γ₁ - sp.β := by rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hle : sp.β ≤ sp.γ₁ := by omega
  have := infNorm_ge_iff_infNormGe (Y.map RPoly.toZq + csOne sp P c) (zTh P Y c) (sp.γ₁ - sp.β) hB
    (fun r hr i hi => zTh_cast P Y c r hr i hi)
  rw [Nat.cast_sub hle] at this
  exact this

theorem N2 (hp : Std3 sp) :
    sp.γ₂ - sp.β ≤ ‖LowBitsVec sp (w - csTwo sp P c)‖∞ ↔
      OcamlPq.MLDSA.infNormGe (mkRows sp.k (fun r i => OcamlPq.MLDSA.lowBits (sp.γ₂ : ℤ) (wTh w r i - cs2Th P c r i)))
        ((sp.γ₂ : ℤ) - (sp.β : ℤ)) := by
  have hB : 0 < sp.γ₂ - sp.β := by rcases hp with rfl | rfl | rfl <;> decide +kernel
  have hle : sp.β ≤ sp.γ₂ := by omega
  have := infNorm_ge_iff_infNormGe_int (LowBitsVec sp (w - csTwo sp P c))
    (fun r i => OcamlPq.MLDSA.lowBits (sp.γ₂ : ℤ) (wTh w r i - cs2Th P c r i)) (sp.γ₂ - sp.β) hB (by
      intro r hr i hi
      have hc : (((wTh w r i - cs2Th P c r i : ℤ)) : Zq) = ((w - csTwo sp P c)[r]!)[i]! := by
        rw [Int.cast_sub, wTh_cast, cs2Th_cast P c r hr i, vsub_get _ _ r hr, vsub_get _ _ i hi]
      rw [lowBitsVec_get sp _ r hr i hi, lowBits_cast sp _ _ hc, coeffNorm_eq _ (lowBits_abs hp _),
        Int.abs_eq_natAbs])
  rw [Nat.cast_sub hle] at this
  exact this

theorem N3 (hp : Std3 sp) :
    sp.γ₂ ≤ ‖ctZero sp P c‖∞ ↔
      OcamlPq.MLDSA.infNormGe (mkRows sp.k (ct0Th P c)) (sp.γ₂ : ℤ) := by
  have hB : 0 < sp.γ₂ := by rcases hp with rfl | rfl | rfl <;> decide +kernel
  have := infNorm_ge_iff_infNormGe (ctZero sp P c) (ct0Th P c) sp.γ₂ hB (fun r hr i hi => ct0Th_cast P c r hr i)
  exact this


/-- The hint of an attempt, as an index function (`makeHintSpec` on the integer lifts). -/
def hTh (r i : ℕ) : ℤ :=
  OcamlPq.MLDSA.makeHintSpec (sp.γ₂ : ℤ) (-(ct0Th P c r i)) (wTh w r i - cs2Th P c r i + ct0Th P c r i)

theorem hTh_eq (r : ℕ) (hr : r < sp.k) (i : ℕ) (hi : i < 256) :
    hTh P w c r i =
      if ((MakeHintVec sp (-ctZero sp P c) (w - csTwo sp P c + ctZero sp P c))[r]!)[i]! then 1 else 0 := by
  unfold hTh
  rw [makeHintVec_get sp _ _ r hr i hi, vneg_get _ r hr, vneg_get _ i hi, vadd_get _ _ r hr, vadd_get _ _ i hi,
    vsub_get _ _ r hr, vsub_get _ _ i hi]
  apply makeHint_cast
  · rw [Int.cast_neg, ct0Th_cast P c r hr i]
  · rw [Int.cast_add, Int.cast_sub, wTh_cast w r i, cs2Th_cast P c r hr i, ct0Th_cast P c r hr i]

theorem N4 :
    (HintWeight (MakeHintVec sp (-ctZero sp P c) (w - csTwo sp P c + ctZero sp P c)) : ℤ) =
      ((mkRows sp.k (hTh P w c)).map (fun row => row.sum)).sum := by
  rw [hintWeight_sum, mkRows_congr (f' := hTh P w c)]
  intro r hr i hi
  rw [hTh_eq P w c r hr i hi]


theorem polyModPM_get (a : Poly) (i : ℕ) (hi : i < 256) : (Poly.modPM a)[i]! = Zq.modPM (a[i]!) :=
  map_get!_lt _ a i hi

theorem respond_value {n : ℕ} (zv : Vector Poly n) (x : ℕ → ℕ → ℤ) (hx : ∀ r < n, ∀ i < 256, ((x r i : ℤ) : Zq) = (zv[r]!)[i]!)
    (r i : ℕ) :
    rfn ((zv.map Poly.modPM)[r]!) i =
      listsToVec ((mkRows n x).map (List.map fun x => OcamlPq.MLDSA.modPM x OcamlPq.MLDSA.q)) r i := by
  rw [mkRows_map, listsToVec_mkRows_trunc]
  by_cases h : r < n ∧ i < 256
  · rw [if_pos h]
    simp only [rfn]
    rw [map_get!_lt _ _ r h.1, polyModPM_get _ i h.2, modPM_cast _ _ (hx r h.1 i h.2)]
  · rw [if_neg h]
    by_cases hr : r < n
    · have hi : ¬ i < 256 := fun hi => h ⟨hr, hi⟩
      simp only [rfn]
      rw [map_get!_lt _ _ r hr]
      have : (Poly.modPM zv[r]!)[i]! = default := getElem!_neg _ i (by simpa using hi)
      rw [this]; rfl
    · simp only [rfn]
      have : (zv.map Poly.modPM)[r]! = default := getElem!_neg _ r (by simpa using hr)
      rw [this]
      show (default : RPoly)[i]! = 0
      by_cases hi : i < 256
      · rw [getElem!_pos _ i (by simpa using hi)]
        simp [default, Inhabited.default]
      · rw [getElem!_neg _ i (by simpa using hi)]
        rfl


theorem respond_hint_value (r i : ℕ) :
    hpoly (MakeHintVec sp (-ctZero sp P c) (w - csTwo sp P c + ctZero sp P c)) r i =
      listsToVec (mkRows sp.k (hTh P w c)) r i := by
  rw [listsToVec_mkRows_trunc]
  unfold hpoly hv
  by_cases h : r < sp.k ∧ i < 256
  · rw [if_pos h, hTh_eq P w c r h.1 i h.2]
    simp [h]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.1, hh.2.1⟩)]
    rfl

/-- **One attempt's response is `fipsFinish`.** -/
theorem respond_eq_fipsFinish (hp : Std3 sp) (key : OcamlPq.MLDSAAlg.ExpandedKey)
    (hs1 : ∀ r, key.s1 r = rfn P.s₁[r]!) (hs2 : ∀ r, key.s2 r = rfn P.s₂[r]!)
    (ht0 : ∀ r, key.t0 r = rfn P.t₀[r]!) :
    (SG.respond sp P (Y.map RPoly.toZq) w c).map
        (fun x => ((fun r => rfn ((x.1.map Poly.modPM)[r]!)), hpoly x.2)) =
      OcamlPq.EndToEnd.MLDSA.fipsFinish (algParams sp) key (fun r => rfn Y[r]!) (fun r => canon w[r]!)
        (fipsNTT (rfn c)) := by
  rw [respond_eq']
  unfold OcamlPq.EndToEnd.MLDSA.fipsFinish OcamlPq.MLDSA.signAttemptSpec
  simp only [hs1, hs2, ht0, mkRows_map]
  refine ite_map_congr _ _ _ _ (or_congr (N1 P Y c hp) (N2 P w c hp)) ?_ ?_
  · refine or_congr (N3 P c hp) ?_
    show _ ↔ (sp.ω : ℤ) < ((mkRows sp.k (hTh P w c)).map (fun row => row.sum)).sum
    rw [← N4 P w c]
    exact Nat.cast_lt.symm
  · refine Prod.ext (funext fun r => funext fun i => ?_) (funext fun r => funext fun i => ?_)
    · exact respond_value (Y.map RPoly.toZq + csOne sp P c) (zTh P Y c)
        (fun r hr i hi => zTh_cast P Y c r hr i hi) r i
    · exact respond_hint_value P w c r i

end Resp

end XSpec
