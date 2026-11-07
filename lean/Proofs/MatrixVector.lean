import Proofs.CorrNTT
import Proofs.NTTOps

/-!
# `MatrixVectorNTT`: the coefficient formula

Coefficient `κ` of row `i` of `Â ∘ v̂` is `∑_j Â[i][j][κ] · v̂[j][κ]` (`MVN2!`). It is used by `Proofs.Correctness` (linearity
of `MatrixVectorNTT`) and by `Proofs.VerifyArith` (the fused multiply-accumulate row of verify).
-/

set_option maxRecDepth 8192

namespace Proofs.Corr
open Spec

theorem get!_sub (a b : Poly) (k : Nat) : (a - b)[k]! = a[k]! - b[k]! := by
  by_cases hk : k < 256
  · rw [vget! _ hk, vget! _ hk, vget! _ hk]
    show (Vector.zipWith (· - ·) a b)[k] = _
    simp
  · rw [getElem!_neg (a - b) k (by simpa using hk), getElem!_neg a k (by simpa using hk),
      getElem!_neg b k (by simpa using hk), default_zq]
    simp

/-- One step of the accumulation in row `i` of `MatrixVectorNTT`. -/
def rowStep {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (acc : Poly) (j : Nat) :
    Poly :=
  AddNTT acc (MultiplyNTT (M[i]!)[j]! V[j]!)

theorem rowStep_eq {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (acc : Poly)
    (j : Nat) : rowStep M V i acc j = AddNTT acc (MultiplyNTT (M[i]!)[j]! V[j]!) := rfl

theorem mvInner_eq {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (w : Vector Poly k)
    (j : Nat) : mvInner M V i w j = w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! V[j]!)) := rfl

theorem mvOuter_eq {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (w : Vector Poly k) (i : Nat) :
    mvOuter M V w i = (List.range' 0 ℓ).foldl (mvInner M V i) w := rfl

theorem vget!_set! {α : Type} [Inhabited α] {n : Nat} (w : Vector α n) (j : Nat) (x : α) {i : Nat}
    (hi : i < n) : (w.set! j x)[i]! = if i = j then x else w[i]! := by
  rw [vgetG (w.set! j x) hi]
  show (w.setIfInBounds j x)[i] = _
  rw [Vector.getElem_setIfInBounds hi]
  by_cases h : i = j
  · subst h
    simp
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h', vgetG w hi]

theorem set!_set!_same {α : Type} {n : Nat} (w : Vector α n) (i : Nat) (a b : α) :
    (w.set! i a).set! i b = w.set! i b := by
  apply Vector.ext
  intro j hj
  show ((w.setIfInBounds i a).setIfInBounds i b)[j] = (w.setIfInBounds i b)[j]
  simp only [Vector.getElem_setIfInBounds hj]
  by_cases h : i = j <;> simp [h]

theorem inner_fold {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (hi : i < k)
    (w : Vector Poly k) : ∀ n,
    (List.range' 0 n).foldl (mvInner M V i) w = w.set! i ((List.range' 0 n).foldl (rowStep M V i) w[i]!) := by
  intro n
  induction n with
  | zero =>
    show w = w.set! i w[i]!
    apply Vector.ext
    intro j hj
    show w[j] = (w.setIfInBounds i w[i]!)[j]
    rw [Vector.getElem_setIfInBounds hj]
    by_cases h : i = j
    · subst h
      simp [vgetG w hi]
    · simp [h]
  | succ n ih =>
    rw [fold_step_range, fold_step_range, ih, mvInner_eq, rowStep_eq]
    rw [vget!_set! w i _ hi, if_pos rfl, set!_set!_same]

theorem outer_fold {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) : ∀ n, n ≤ k → ∀ i, i < k →
    ((List.range' 0 n).foldl (mvOuter M V) (Vector.replicate k Poly.zero))[i]! =
      if i < n then (List.range' 0 ℓ).foldl (rowStep M V i) Poly.zero else Poly.zero := by
  intro n
  induction n with
  | zero =>
    intro _ i hi
    show (Vector.replicate k Poly.zero)[i]! = _
    rw [vgetG _ hi]
    simp
  | succ n ih =>
    intro hn i hi
    have hnk : n < k := hn
    rw [fold_step_range, mvOuter_eq]
    rw [inner_fold M V n hnk, vget!_set! _ _ _ hi, ih (by omega) n hnk, if_neg (lt_irrefl n)]
    by_cases e : i = n
    · subst e
      simp
    · rw [if_neg e, ih (by omega) i hi]
      by_cases h2 : i < n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem MVN_row {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) {i : Nat} (hi : i < k) :
    (MatrixVectorNTT M V)[i]! = (List.range' 0 ℓ).foldl (rowStep M V i) Poly.zero := by
  rw [MatrixVectorNTT_eq, outer_fold M V k le_rfl i hi, if_pos hi]

theorem rowStep_coef {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (acc : Poly)
    (κ : Nat) (hκ : κ < 256) : ∀ n,
    ((List.range' 0 n).foldl (rowStep M V i) acc)[κ]! =
      acc[κ]! + ∑ j ∈ Finset.range n, ((M[i]!)[j]!)[κ]! * (V[j]!)[κ]! := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [fold_step_range, Finset.sum_range_succ]
    rw [rowStep_eq, AddNTT_eq_add, get!_add, ih, MultiplyNTT_get _ _ κ hκ]
    ring

/-- Coefficient `κ` of row `i` of `Â ∘ v̂`: `∑_j Â[i][j][κ] · v̂[j][κ]`. -/
theorem MVN2! {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) {i : Nat} (hi : i < k) {κ : Nat}
    (hκ : κ < 256) :
    ((MatrixVectorNTT M V)[i]!)[κ]! = ∑ j ∈ Finset.range ℓ, ((M[i]!)[j]!)[κ]! * (V[j]!)[κ]! := by
  rw [MVN_row M V hi, rowStep_coef M V i Poly.zero κ hκ ℓ, zero_get!, zero_add]

end Proofs.Corr
