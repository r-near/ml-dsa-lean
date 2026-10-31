import XSpec.Expand

/-!
# Vectors and matrices over `T_q` / `R_q`

Bridges between our vector-level operations (`NTTVec`, `NTTInvVec`, `MatrixVectorNTT`, `+`, `Power2RoundVec`, ...)
and ocaml-pq's index-function versions (`fipsNTT`, `fipsNTTinv`, `fipsMulMatVec`, `fipsAddPoly`, ...).

Adapters: a polynomial `a : Poly` is `canon a : ℕ → ℤ` (canonical representatives, zero beyond 256), an
`RPoly` is `rfn`, a vector is read entry by entry (`v[r]!`).
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

/-! ## Entrywise lemmas -/

theorem map_get! {α β : Type} [Inhabited α] [Inhabited β] {n : ℕ} (f : α → β) (hf : f default = default)
    (v : Vector α n) (i : ℕ) : (v.map f)[i]! = f v[i]! := by
  by_cases hi : i < n
  · rw [getElem!_pos _ i (by simpa using hi), getElem!_pos v i (by simpa using hi)]
    simp
  · rw [getElem!_neg _ i (by simpa using hi), getElem!_neg v i (by simpa using hi), hf]

theorem map_get!_lt {α β : Type} [Inhabited α] [Inhabited β] {n : ℕ} (f : α → β)
    (v : Vector α n) (i : ℕ) (hi : i < n) : (v.map f)[i]! = f v[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos v i (by simpa using hi)]
  simp

theorem I_add (a b : Poly) (i : ℕ) : I (a + b) i = I a i + I b i := by
  by_cases hi : i < 256
  · simp only [I, vget! _ i hi]
    show (Vector.zipWith (· + ·) a b)[i] = a[i] + b[i]
    simp
  · simp [I, RN.poly_ge _ i hi]

/-- Addition in `R_q` / `T_q` (our `+` on `Poly`) is `fipsAddPoly` on canonical representatives. -/
theorem canon_add (a b : Poly) : canon (a + b) = fipsAddPoly (canon a) (canon b) := by
  unfold fipsAddPoly
  rw [toZq_canon, toZq_canon, ← ofZq_I]
  congr 1
  funext i
  exact I_add a b i

theorem I_sub (a b : Poly) (i : ℕ) : I (a - b) i = I a i - I b i := by
  by_cases hi : i < 256
  · simp only [I, vget! _ i hi]
    show (Vector.zipWith (· - ·) a b)[i] = a[i] - b[i]
    simp
  · simp [I, RN.poly_ge _ i hi]

/-- Subtraction in `R_q` / `T_q` (our `-` on `Poly`) is `fipsSubPoly` on canonical representatives. -/
theorem canon_sub (a b : Poly) : canon (a - b) = fipsSubPoly (canon a) (canon b) := by
  unfold fipsSubPoly
  rw [toZq_canon, toZq_canon, ← ofZq_I]
  congr 1
  funext i
  exact I_sub a b i

theorem toZq_rfn (w : RPoly) : toZq (rfn w) = I (RPoly.toZq w) := by
  funext i
  by_cases hi : i < 256
  · simp only [toZq, OcamlPq.MLDSA.castArr, rfn, I, RPoly.toZq]
    rw [getElem!_pos w i (by simpa using hi), getElem!_pos (w.map _) i (by simpa using hi)]
    simp
  · simp only [toZq, OcamlPq.MLDSA.castArr, rfn, I, RPoly.toZq]
    rw [getElem!_neg w i (by simpa using hi), getElem!_neg (w.map _) i (by simpa using hi)]
    simp [default_zq]

theorem fipsNTT_rfn (w : RPoly) : fipsNTT (rfn w) = canon (NTT (RPoly.toZq w)) := by
  rw [← fipsNTT_eq]
  unfold fipsNTT
  rw [toZq_rfn, toZq_canon]

theorem NTTVec_get {n : ℕ} (v : Vector Poly n) (r : ℕ) (hr : r < n) : (NTTVec v)[r]! = NTT v[r]! :=
  map_get!_lt NTT v r hr

theorem NTTInvVec_get {n : ℕ} (v : Vector Poly n) (r : ℕ) (hr : r < n) : (NTTInvVec v)[r]! = NTTInv v[r]! :=
  map_get!_lt NTTInv v r hr

theorem addVec_get {n : ℕ} (a b : Vector Poly n) (r : ℕ) (hr : r < n) : (a + b)[r]! = a[r]! + b[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), getElem!_pos a r (by simpa using hr),
    getElem!_pos b r (by simpa using hr)]
  show (Vector.zipWith (· + ·) a b)[r] = a[r] + b[r]
  simp

theorem subVec_get {n : ℕ} (a b : Vector Poly n) (r : ℕ) (hr : r < n) : (a - b)[r]! = a[r]! - b[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), getElem!_pos a r (by simpa using hr),
    getElem!_pos b r (by simpa using hr)]
  show (Vector.zipWith (· - ·) a b)[r] = a[r] - b[r]
  simp

/-! ## `MatrixVectorNTT` -/

section MV

variable {k ℓ : ℕ}

theorem MatrixVectorNTT_fold (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) :
    MatrixVectorNTT M v = (List.range' 0 k).foldl (fun w i => (List.range' 0 ℓ).foldl
      (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w) (Vector.replicate k Poly.zero) := by
  unfold MatrixVectorNTT
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem I_addNTT (a b : Poly) (c : ℕ) : I (AddNTT a b) c = I a c + I b c := by
  have := congrFun (addNTT_eq a b) c
  simpa [idx, I] using this

theorem I_mulNTT (a b : Poly) (c : ℕ) : I (MultiplyNTT a b) c = I a c * I b c := by
  have := congrFun (multiplyNTT_eq a b) c
  simpa [idx, I, OcamlPq.MLDSA.multiplyNttSpec] using this

theorem mv_inner (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) (i : ℕ) (hi : i < k) :
    ∀ (m : ℕ) (w : Vector Poly k),
      (∀ c, I ((List.range' 0 m).foldl (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w)[i]! c =
          I w[i]! c + ∑ j ∈ Finset.range m, I (M[i]!)[j]! c * I v[j]! c) ∧
      (∀ r, r ≠ i → ((List.range' 0 m).foldl (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w)[r]! = w[r]!) := by
  intro m
  induction m with
  | zero => intro w; exact ⟨fun c => by simp, fun r _ => rfl⟩
  | succ m ih =>
    intro w
    obtain ⟨h1, h2⟩ := ih w
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    generalize hY : (List.range' 0 m).foldl (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w = Y at h1 h2
    refine ⟨fun c => ?_, fun r hr => ?_⟩
    · rw [vset_get_eq _ _ hi, I_addNTT, I_mulNTT, h1 c, Finset.sum_range_succ]
      ring
    · rw [vset_get_ne _ _ _ _ (Ne.symm hr)]
      exact h2 r hr

theorem mv_outer (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) :
    ∀ n, n ≤ k → ∀ r, r < k → ∀ c,
      I ((List.range' 0 n).foldl (fun w i => (List.range' 0 ℓ).foldl
        (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w) (Vector.replicate k Poly.zero))[r]! c =
        if r < n then ∑ j ∈ Finset.range ℓ, I (M[r]!)[j]! c * I v[j]! c else 0 := by
  intro n
  induction n with
  | zero =>
    intro _ r hr c
    simp only [List.range'_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
    rw [getElem!_pos _ r (by simpa using hr)]
    simp [I, Poly.zero]
    by_cases hc : c < 256
    · rw [getElem!_pos _ c (by simpa using hc)]; simp
    · rw [getElem!_neg _ c (by simpa using hc)]; exact default_zq
  | succ n ih =>
    intro hn r hr c
    rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    generalize hY : (List.range' 0 n).foldl (fun w i => (List.range' 0 ℓ).foldl
        (fun w j => w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! v[j]!))) w) (Vector.replicate k Poly.zero) = Y at ih
    obtain ⟨h1, h2⟩ := mv_inner M v n (by omega) ℓ Y
    by_cases hrn : r = n
    · subst hrn
      rw [h1 c, ih (by omega) r hr c]
      simp
    · rw [h2 r hrn, ih (by omega) r hr c]
      by_cases hlt : r < n
      · simp [hlt, show r < n + 1 by omega]
      · simp [hlt, show ¬ r < n + 1 by omega]

/-- Row `r` of `MatrixVectorNTT`, coefficientwise. -/
theorem MatrixVectorNTT_I (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) (r : ℕ) (hr : r < k) (c : ℕ)
    (hc : c < 256) :
    I (MatrixVectorNTT M v)[r]! c = ∑ j ∈ Finset.range ℓ, I (M[r]!)[j]! c * I v[j]! c := by
  rw [MatrixVectorNTT_fold, mv_outer M v k le_rfl r hr c, ite_eq_left hr]

/-- **`MatrixVectorNTT` is `fipsMulMatVec`** (row `r < k`, on canonical representatives). -/
theorem matrixVectorNTT_eq (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) (r : ℕ) (hr : r < k) :
    canon (MatrixVectorNTT M v)[r]! =
      fipsMulMatVec ℓ (fun r s => canon (M[r]!)[s]!) (fun s => canon v[s]!) r := by
  unfold fipsMulMatVec trunc
  funext c
  simp only [toZq_canon]
  by_cases hc : c < 256
  · simp only [ite_eq_left hc, ofZq]
    rw [← ofZq_I]
    simp only [ofZq]
    rw [MatrixVectorNTT_I M v r hr c hc]
    simp [OcamlPq.MLDSA.matrixVectorRowSpec]
  · simp only [ite_eq_right hc]
    exact canon_zero_of_ge _ (by omega)

end MV

end XSpec
