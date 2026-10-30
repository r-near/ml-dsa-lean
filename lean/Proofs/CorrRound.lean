import Proofs.RoundingArith

/-!
# Correctness of the rounding functions (the lemmas behind `Verify (Sign sk M) = true`)

Imports only `Spec.*` (through `Proofs.RoundingArith`, which is Impl-free). All statements are about the
transcribed specification of `Spec/Rounding.lean`, coefficientwise on `Zq` and then lifted to `Vector Poly n`.

* `power2Round_spec`, `power2RoundVec_spec`: `t₁ ⋅ 2^d + t₀ = t` (Algorithm 6, step 6, and the `t₁ ⋅ 2^d` of
  Algorithm 8), with the ranges `0 ≤ t₁ < 2^10`, `-2^12 < t₀ ≤ 2^12`.
* `highBits_add_small`, `highBitsVec_add_small`, `highBitsVec_sub_add`: if `‖x‖∞ ≤ β` and
  `‖LowBits r‖∞ < γ₂ - β` then `HighBits (r + x) = HighBits r` (Sign: `w₁ = HighBits(w) = HighBits(w - c s₂)`).
* `useHint_makeHint`, `useHintVec_makeHintVec`, `useHintVec_makeHintVec_sign`: `‖z‖∞ ≤ γ₂` implies
  `UseHint (MakeHint z r) r = HighBits (r + z)`. Note the argument order: `UseHint` is applied to `r`, not to
  `r + z` (Sign: `r = w - c s₂ + c t₀`, `z = -c t₀`, so `UseHint h r = HighBits (w - c s₂)`).

The arithmetic holds for `γ₂ ∈ {95232, 261888}` (`StdGamma2`) and `d = 13`; the proofs split on the two values of
`γ₂` and finish with `omega`.
-/

set_option maxRecDepth 8192

namespace Proofs.Corr
open Spec

/-! ## Facts about `mod±` and `Decompose` -/

/-- `Zq.modPM z` is `z.val` shifted by a multiple of `q`, in `[-(q-1)/2, (q-1)/2]`. -/
theorem zq_modPM_facts (z : Zq) :
    ∃ k : Int, Zq.modPM z = (z.val : Int) + 8380417 * k ∧ -4190208 ≤ Zq.modPM z ∧ Zq.modPM z ≤ 4190208 := by
  obtain ⟨k, hk⟩ := modPM_dvd (z.val : Int) q
  have hl := modPM_lower (z.val : Int) q (by decide)
  have hu := modPM_upper (z.val : Int) q (by decide)
  unfold Zq.modPM
  have hq : (q : Int) = 8380417 := rfl
  refine ⟨k, ?_, ?_, ?_⟩ <;> simp only [hq] at hk hl hu ⊢ <;> omega

theorem std_cases (p : Params) (hg : Proofs.StdGamma2 p) :
    (p.γ₂ = 95232 ∧ p.m = 44) ∨ (p.γ₂ = 261888 ∧ p.m = 16) := by
  rcases hg with h | h
  · left; exact ⟨h, by unfold Params.m; rw [h]; decide +kernel⟩
  · right; exact ⟨h, by unfold Params.m; rw [h]; decide +kernel⟩

/-- The shape of `Decompose`: either `y = y₁ ⋅ 2γ₂ + y₀` with `-γ₂ < y₀ ≤ γ₂`, or the special case of step 3
(`y₁ = 0`, `y = q + y₀`, `-γ₂ ≤ y₀ ≤ -1`). In both cases `0 ≤ y₁ < m`. -/
theorem decompose_facts (p : Params) (hg : Proofs.StdGamma2 p) (y : Zq) :
    ∃ y1 y0 : Int, Decompose p y = (y1, y0) ∧ 0 ≤ y1 ∧ y1 < (p.m : Int) ∧
      -(p.γ₂ : Int) ≤ y0 ∧ y0 ≤ (p.γ₂ : Int) ∧
      (((y.val : Int) = y1 * (2 * p.γ₂) + y0 ∧ -(p.γ₂ : Int) < y0) ∨
       (y1 = 0 ∧ (y.val : Int) = 8380417 + y0 ∧ y0 ≤ -1)) := by
  haveI : NeZero q := ⟨by decide⟩
  have hlt : y.val < 8380417 := ZMod.val_lt y
  have hq : (q : Int) = 8380417 := rfl
  obtain ⟨G, hGp⟩ : ∃ G, p.γ₂ = G := ⟨_, rfl⟩
  obtain ⟨M, hMp⟩ : ∃ M, p.m = M := ⟨_, rfl⟩
  have hc := std_cases p hg
  rw [hGp, hMp] at hc
  rw [Decompose_eq, hGp, hMp]
  obtain ⟨k, hk⟩ := modPM_dvd (y.val : Int) (2 * G)
  have hl := modPM_lower (y.val : Int) (2 * G) (by omega)
  have hu := modPM_upper (y.val : Int) (2 * G) (by omega)
  generalize Spec.modPM (y.val : Int) (2 * G) = b at *
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · split_ifs with hcase
    · refine ⟨0, b - 1, rfl, ?_⟩
      omega
    · refine ⟨_, b, rfl, ?_⟩
      omega

/-! ## Power2Round -/

/-- Algorithm 35: `t₁ ⋅ 2^d + t₀ = r` in `Z_q`, with `0 ≤ t₁ < 2^10` and `-2^12 < t₀ ≤ 2^12`. -/
theorem power2Round_spec (p : Params) (hd : p.d = 13) (r : Zq) :
    (((Power2Round p r).1 : Int) : Zq) * 2 ^ p.d + (((Power2Round p r).2 : Int) : Zq) = r ∧
    0 ≤ (Power2Round p r).1 ∧ (Power2Round p r).1 < 1024 ∧
    -4096 < (Power2Round p r).2 ∧ (Power2Round p r).2 ≤ 4096 := by
  haveI : NeZero q := ⟨by decide⟩
  have hlt : r.val < 8380417 := ZMod.val_lt r
  rw [Power2Round_eq, hd]
  obtain ⟨k, hk⟩ := modPM_dvd (r.val : Int) (2 ^ 13)
  have hl := modPM_lower (r.val : Int) (2 ^ 13) (by norm_num)
  have hu := modPM_upper (r.val : Int) (2 ^ 13) (by norm_num)
  generalize Spec.modPM (r.val : Int) (2 ^ 13) = b at *
  push_cast at *
  have hdiv : ((r.val : Int) - b) / 2 ^ 13 * 2 ^ 13 + b = r.val := by omega
  refine ⟨?_, by omega, by omega, by omega, by omega⟩
  have h2 : ((((r.val : Int) - b) / 2 ^ 13 * 2 ^ 13 + b : Int) : Zq) = ((r.val : Int) : Zq) := by
    rw [hdiv]
  push_cast at h2
  have e : (2 : Zq) ^ 13 = 8192 := by norm_num
  rw [e, h2]
  simp

/-! ## Infinity norm of vectors -/

theorem list_foldl_max_le {α : Type} (f : α → Nat) (l : List α) (a B : Nat) :
    l.foldl (fun m x => max m (f x)) a ≤ B ↔ a ≤ B ∧ ∀ x ∈ l, f x ≤ B := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, Nat.max_le, List.mem_cons, forall_eq_or_imp]
    tauto

/-- `‖v‖∞ ≤ B` iff every entry has norm at most `B`. -/
theorem infNorm_vec_le_iff {α : Type} [InfNorm α] {n : Nat} (v : Vector α n) (B : Nat) :
    ‖v‖∞ ≤ B ↔ ∀ i (h : i < n), ‖v[i]‖∞ ≤ B := by
  show v.foldl (fun m x => max m (InfNorm.infNorm x)) 0 ≤ B ↔ _
  rw [← Vector.foldl_toList, list_foldl_max_le]
  constructor
  · rintro ⟨-, h⟩ i hi
    exact h _ (by simp)
  · intro h
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Vector.mem_iff_getElem.mp (by simpa using hx)
    exact h i hi

theorem infNorm_vec_getElem_le {α : Type} [InfNorm α] {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) :
    ‖v[i]‖∞ ≤ ‖v‖∞ :=
  (infNorm_vec_le_iff v _).mp (Nat.le_refl _) i hi

theorem vec_add_getElem {α : Type} [Add α] {n : Nat} (a b : Vector α n) (i : Nat) (hi : i < n) :
    (a + b)[i] = a[i] + b[i] := by
  show (Vector.zipWith (· + ·) a b)[i] = _
  simp

theorem vec_sub_getElem {α : Type} [Sub α] {n : Nat} (a b : Vector α n) (i : Nat) (hi : i < n) :
    (a - b)[i] = a[i] - b[i] := by
  show (Vector.zipWith (· - ·) a b)[i] = _
  simp

theorem vec_neg_getElem {α : Type} [Neg α] {n : Nat} (a : Vector α n) (i : Nat) (hi : i < n) :
    (-a)[i] = -a[i] := by
  show (Vector.map (- ·) a)[i] = _
  simp

theorem zq_infNorm_neg (z : Zq) : ‖-z‖∞ = ‖z‖∞ := by
  show (Zq.modPM (-z)).natAbs = (Zq.modPM z).natAbs
  haveI : NeZero q := ⟨by decide⟩
  obtain ⟨k, hk, hl, hu⟩ := zq_modPM_facts z
  obtain ⟨k', hk', hl', hu'⟩ := zq_modPM_facts (-z)
  have hq : q = 8380417 := rfl
  have h := ZMod.neg_val z
  have h0 : z = 0 ↔ z.val = 0 := (ZMod.val_eq_zero z).symm
  by_cases hz : z = 0
  · rw [if_pos hz] at h
    have := h0.mp hz
    omega
  · rw [if_neg hz] at h
    have : z.val ≠ 0 := fun e => hz (h0.mpr e)
    have h2 : z.val < 8380417 := ZMod.val_lt z
    omega

theorem infNorm_neg_vec_le {α : Type} [InfNorm α] [Neg α] (hα : ∀ a : α, ‖-a‖∞ = ‖a‖∞) {n : Nat}
    (v : Vector α n) (B : Nat) (h : ‖v‖∞ ≤ B) : ‖-v‖∞ ≤ B := by
  rw [infNorm_vec_le_iff] at h ⊢
  intro i hi
  rw [vec_neg_getElem _ _ hi, hα]
  exact h i hi

/-- `‖-v‖∞ ≤ B` from `‖v‖∞ ≤ B` for vectors of polynomials. -/
theorem infNorm_neg_vecPoly_le {n : Nat} (v : Vector Poly n) (B : Nat) (h : ‖v‖∞ ≤ B) : ‖-v‖∞ ≤ B := by
  refine infNorm_neg_vec_le (α := Poly) (fun a => ?_) v B h
  apply Nat.le_antisymm
  · exact (infNorm_vec_le_iff _ _).mpr fun i hi => by
      rw [vec_neg_getElem _ _ hi, zq_infNorm_neg]
      exact infNorm_vec_getElem_le _ i hi
  · exact (infNorm_vec_le_iff _ _).mpr fun i hi => by
      have := infNorm_vec_getElem_le (-a) i hi
      rw [vec_neg_getElem _ _ hi, zq_infNorm_neg] at this
      exact this

/-- `(r + x).val = r.val + (x mod± q) + q j` for some `j ∈ {-1, 0, 1}`. -/
theorem add_val_facts (r x : Zq) :
    ∃ j : Int, ((r + x).val : Int) = r.val + Zq.modPM x + 8380417 * j ∧ (j = -1 ∨ j = 0 ∨ j = 1) := by
  haveI : NeZero q := ⟨by decide⟩
  obtain ⟨k, hk, hl, hu⟩ := zq_modPM_facts x
  have hv : (r + x).val = (r.val + x.val) % 8380417 := ZMod.val_add r x
  have hrlt : r.val < 8380417 := ZMod.val_lt r
  have hxlt : x.val < 8380417 := ZMod.val_lt x
  have hvlt : (r + x).val < 8380417 := ZMod.val_lt (r + x)
  refine ⟨-(((r.val + x.val) / 8380417 : Nat) : Int) - k, ?_, ?_⟩ <;> omega

/-! ## HighBits is stable under small perturbations -/

/-- Dilithium's "Lemma 1": if `‖x‖∞ ≤ β` and `|LowBits r| < γ₂ - β` then `HighBits (r + x) = HighBits r`. -/
theorem highBits_add_small (p : Params) (hg : Proofs.StdGamma2 p) (β : Nat) (r x : Zq)
    (hx : ‖x‖∞ ≤ β) (hr : (LowBits p r).natAbs < p.γ₂ - β) :
    HighBits p (r + x) = HighBits p r := by
  haveI : NeZero q := ⟨by decide⟩
  obtain ⟨r1, r0, hd, hr1, hr2, hr3, hr4, hr5⟩ := decompose_facts p hg r
  obtain ⟨u1, u0, hd', hu1, hu2, hu3, hu4, hu5⟩ := decompose_facts p hg (r + x)
  obtain ⟨k, hk, hl, hu⟩ := zq_modPM_facts x
  obtain ⟨j, hj, hj3⟩ := add_val_facts r x
  have e1 : HighBits p r = r1 := by simp [HighBits, hd]
  have e2 : HighBits p (r + x) = u1 := by simp [HighBits, hd']
  have e3 : LowBits p r = r0 := by simp [LowBits, hd]
  rw [e1, e2]
  rw [e3] at hr
  have hx' : (Zq.modPM x).natAbs ≤ β := hx
  have hrlt : r.val < 8380417 := ZMod.val_lt r
  clear e1 e2 e3 hd hd' hx hk
  have hc := std_cases p hg
  generalize p.γ₂ = G at *
  generalize p.m = M at *
  generalize Zq.modPM x = s at *
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> rcases hu5 with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega

/-! ## UseHint after MakeHint -/

/-- For `‖z‖∞ ≤ γ₂`: `UseHint (MakeHint z r) r = HighBits (r + z)`. -/
theorem useHint_makeHint (p : Params) (hg : Proofs.StdGamma2 p) (z r : Zq) (hz : ‖z‖∞ ≤ p.γ₂) :
    UseHint p (MakeHint p z r) r = HighBits p (r + z) := by
  haveI : NeZero q := ⟨by decide⟩
  obtain ⟨r1, r0, hd, hr1, hr2, hr3, hr4, hr5⟩ := decompose_facts p hg r
  obtain ⟨u1, u0, hd', hu1, hu2, hu3, hu4, hu5⟩ := decompose_facts p hg (r + z)
  obtain ⟨k, hk, hl, hu⟩ := zq_modPM_facts z
  have e1 : HighBits p r = r1 := by simp [HighBits, hd]
  have e2 : HighBits p (r + z) = u1 := by simp [HighBits, hd']
  have hz' : (Zq.modPM z).natAbs ≤ p.γ₂ := hz
  obtain ⟨j, hj, hj3⟩ := add_val_facts r z
  have hrlt : r.val < 8380417 := ZMod.val_lt r
  rw [UseHint_eq, e2, hd]
  simp only [MakeHint, e1, e2, bne_iff_ne, ne_eq]
  clear e1 e2 hd hd' hz hk
  have hc := std_cases p hg
  generalize p.γ₂ = G at *
  generalize p.m = M at *
  generalize Zq.modPM z = s at *
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rcases hr5 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> rcases hu5 with ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;>
      split_ifs <;> omega

/-! ## Lifts to vectors of polynomials -/

theorem vec2_add_getElem {n : Nat} (a b : Vector Poly n) (i : Nat) (hi : i < n) (j : Nat) (hj : j < 256) :
    (a + b)[i][j] = a[i][j] + b[i][j] := by
  simp only [vec_add_getElem a b i hi]
  exact vec_add_getElem _ _ j hj

theorem highBitsVec_getElem (p : Params) {n : Nat} (v : Vector Poly n) (i : Nat) (hi : i < n) (j : Nat)
    (hj : j < 256) : (HighBitsVec p v)[i][j] = HighBits p v[i][j] := by
  simp [HighBitsVec]

theorem lowBitsVec_getElem (p : Params) {n : Nat} (v : Vector Poly n) (i : Nat) (hi : i < n) (j : Nat)
    (hj : j < 256) : (LowBitsVec p v)[i][j] = LowBits p v[i][j] := by
  simp [LowBitsVec]

theorem makeHintVec_getElem (p : Params) {n : Nat} (z r : Vector Poly n) (i : Nat) (hi : i < n) (j : Nat)
    (hj : j < 256) : (MakeHintVec p z r)[i][j] = MakeHint p z[i][j] r[i][j] := by
  simp [MakeHintVec]

theorem useHintVec_getElem (p : Params) {n : Nat} (h : Vector HintPoly n) (r : Vector Poly n) (i : Nat)
    (hi : i < n) (j : Nat) (hj : j < 256) :
    (UseHintVec p h r)[i][j] = UseHint p h[i][j] r[i][j] := by
  simp [UseHintVec]

theorem vec_sub_add_cancel {n : Nat} (w x : Vector Poly n) : w - x + x = w := by
  apply Vector.ext; intro i hi
  rw [vec_add_getElem _ _ i hi, vec_sub_getElem _ _ i hi]
  apply Vector.ext; intro j hj
  rw [vec_add_getElem _ _ j hj, vec_sub_getElem _ _ j hj]
  exact sub_add_cancel _ _

theorem vec_add_neg_cancel {n : Nat} (w x : Vector Poly n) : w + x + -x = w := by
  apply Vector.ext; intro i hi
  rw [vec_add_getElem _ _ i hi, vec_add_getElem _ _ i hi, vec_neg_getElem _ _ hi]
  apply Vector.ext; intro j hj
  rw [vec_add_getElem _ _ j hj, vec_add_getElem _ _ j hj, vec_neg_getElem _ _ hj]
  exact add_neg_cancel_right _ _

/-- Algorithm 6, step 6 and Algorithm 8: `t₁ ⋅ 2^d + t₀ = t` for `Power2RoundVec`, where `t₁ ⋅ 2^d` is written
exactly as in `Verify_internal` and `t₀` is the coercion `R → R_q`. -/
theorem power2RoundVec_spec (p : Params) (hd : p.d = 13) {n : Nat} (t : Vector Poly n) :
    ((Power2RoundVec p t).1.map RPoly.toZq).map (·.map (· * (2 ^ p.d : Zq))) +
      (Power2RoundVec p t).2.map RPoly.toZq = t := by
  apply Vector.ext; intro i hi
  rw [vec_add_getElem _ _ i hi]
  apply Vector.ext; intro j hj
  rw [vec_add_getElem _ _ j hj]
  have := (power2Round_spec p hd t[i][j]).1
  simpa [Power2RoundVec, RPoly.toZq] using this

/-- The ranges of `t₁` and `t₀` (every coefficient). -/
theorem power2RoundVec_range (p : Params) (hd : p.d = 13) {n : Nat} (t : Vector Poly n) (i : Nat) (hi : i < n)
    (j : Nat) (hj : j < 256) :
    0 ≤ (Power2RoundVec p t).1[i][j] ∧ (Power2RoundVec p t).1[i][j] < 1024 ∧
    -4096 < (Power2RoundVec p t).2[i][j] ∧ (Power2RoundVec p t).2[i][j] ≤ 4096 := by
  have := power2Round_spec p hd t[i][j]
  simpa [Power2RoundVec] using this.2

/-- Vector form of `highBits_add_small`. -/
theorem highBitsVec_add_small (p : Params) (hg : Proofs.StdGamma2 p) {n : Nat} (β : Nat) (r x : Vector Poly n)
    (hx : ‖x‖∞ ≤ β) (hr : ‖LowBitsVec p r‖∞ < p.γ₂ - β) :
    HighBitsVec p (r + x) = HighBitsVec p r := by
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  rw [highBitsVec_getElem _ _ i hi j hj, highBitsVec_getElem _ _ i hi j hj, vec2_add_getElem _ _ i hi j hj]
  apply highBits_add_small p hg β
  · have h1 := infNorm_vec_getElem_le x i hi
    have h2 := infNorm_vec_getElem_le x[i] j hj
    omega
  · have h1 := infNorm_vec_getElem_le (LowBitsVec p r) i hi
    have h2 := infNorm_vec_getElem_le (LowBitsVec p r)[i] j hj
    have h3 : ‖(LowBitsVec p r)[i][j]‖∞ = (LowBits p r[i][j]).natAbs := by
      rw [lowBitsVec_getElem _ _ i hi j hj]; rfl
    omega

/-- Sign, step 13 versus Verify: `HighBits(w) = HighBits(w - c s₂)` when `‖c s₂‖∞ ≤ β` and
`‖LowBits(w - c s₂)‖∞ < γ₂ - β`. -/
theorem highBitsVec_sub_add (p : Params) (hg : Proofs.StdGamma2 p) {n : Nat} (β : Nat) (w cs2 : Vector Poly n)
    (hx : ‖cs2‖∞ ≤ β) (hr : ‖LowBitsVec p (w - cs2)‖∞ < p.γ₂ - β) :
    HighBitsVec p w = HighBitsVec p (w - cs2) := by
  have := highBitsVec_add_small p hg β (w - cs2) cs2 hx hr
  rwa [vec_sub_add_cancel] at this

/-- Vector form of `useHint_makeHint`. -/
theorem useHintVec_makeHintVec (p : Params) (hg : Proofs.StdGamma2 p) {n : Nat} (z r : Vector Poly n)
    (hz : ‖z‖∞ ≤ p.γ₂) :
    UseHintVec p (MakeHintVec p z r) r = HighBitsVec p (r + z) := by
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  rw [useHintVec_getElem _ _ _ i hi j hj, makeHintVec_getElem _ _ _ i hi j hj, highBitsVec_getElem _ _ i hi j hj,
    vec2_add_getElem _ _ i hi j hj]
  apply useHint_makeHint p hg
  have h1 := infNorm_vec_getElem_le z i hi
  have h2 := infNorm_vec_getElem_le z[i] j hj
  omega

/-- Sign's hint `h = MakeHint(-c t₀, w - c s₂ + c t₀)`, applied by Verify to `w - c s₂ + c t₀`, recovers
`HighBits(w - c s₂)` when `‖c t₀‖∞ ≤ γ₂`. -/
theorem useHintVec_makeHintVec_sign (p : Params) (hg : Proofs.StdGamma2 p) {n : Nat} (w' ct0 : Vector Poly n)
    (hz : ‖ct0‖∞ ≤ p.γ₂) :
    UseHintVec p (MakeHintVec p (-ct0) (w' + ct0)) (w' + ct0) = HighBitsVec p w' := by
  rw [useHintVec_makeHintVec p hg _ _ (infNorm_neg_vecPoly_le _ _ hz), vec_add_neg_cancel]

/-- The assembled statement for `Verify (Sign ..)`: with the checks of Algorithm 7 (steps 23 and 28 passed),
the verifier's `w₁'` equals the signer's `w₁ = HighBits(w)`. -/
theorem sign_verify_w1 (p : Params) (hg : Proofs.StdGamma2 p) {n : Nat} (w cs2 ct0 : Vector Poly n)
    (hcs2 : ‖cs2‖∞ ≤ p.β) (hr0 : ¬ (‖LowBitsVec p (w - cs2)‖∞ ≥ p.γ₂ - p.β))
    (hct0 : ¬ (‖ct0‖∞ ≥ p.γ₂)) :
    UseHintVec p (MakeHintVec p (-ct0) (w - cs2 + ct0)) (w - cs2 + ct0) = HighBitsVec p w := by
  rw [useHintVec_makeHintVec_sign p hg _ _ (by omega)]
  exact (highBitsVec_sub_add p hg p.β w cs2 hcs2 (by omega)).symm

end Proofs.Corr
