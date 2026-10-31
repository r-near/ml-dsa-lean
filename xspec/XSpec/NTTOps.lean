import Spec
import OcamlPq

/-!
# `AddNTT` and `MultiplyNTT` (FIPS 204 Algorithms 44 and 45)

Ours work on `Poly = Vector Zq 256`; ocaml-pq's `multiplyNttSpec` is pointwise on index functions
`ℕ → Zq`.  Adapter: `idx a = fun i => a[i]!` (zero beyond 256).  The two loops are ported from
`lean/Proofs/NTTOps.lean` (same fold model), unchanged apart from names.
-/

open Spec

namespace XSpec

theorem vget! {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) : v[i]! = v[i] :=
  getElem!_pos v i (by simpa using h)

theorem set!_eq' {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := rfl

theorem default_zq : (default : Zq) = 0 := rfl

/-- The index function of a polynomial (zero beyond 256). -/
def idx (a : Poly) : ℕ → Zq := fun i => a[i]!

/-- One iteration of the spec's pointwise loop: `c[j] := op a[j] b[j]`. -/
def pwF (op : Zq → Zq → Zq) (a b : Poly) (c : Poly) (j : Nat) : Poly := c.set! j (op a[j]! b[j]!)

theorem pwFold_getElem (op : Zq → Zq → Zq) (a b : Poly) (n k : Nat) (hk : k < 256) :
    ((List.range' 0 n).foldl (pwF op a b) Poly.zero)[k] = if k < n then op a[k] b[k] else 0 := by
  induction n with
  | zero => simp [Poly.zero]
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [pwF, set!_eq', Vector.getElem_setIfInBounds hk, Nat.zero_add, Nat.one_mul]
    by_cases e : n = k
    · subst e
      simp [vget! a n hk, vget! b n hk]
    · have hh : (k < n + 1 ↔ k < n) := by omega
      simp [e, hh, ih]

theorem pwFold_full (op : Zq → Zq → Zq) (a b : Poly) :
    (List.range' 0 256).foldl (pwF op a b) Poly.zero = Vector.zipWith op a b := by
  apply Vector.ext
  intro k hk
  rw [pwFold_getElem op a b 256 k hk, if_pos hk, Vector.getElem_zipWith]

theorem AddNTT_eq_fold (a b : Poly) :
    AddNTT a b = (List.range' 0 256).foldl (pwF (· + ·) a b) Poly.zero := by
  simp [AddNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

theorem MultiplyNTT_eq_fold (a b : Poly) :
    MultiplyNTT a b = (List.range' 0 256).foldl (pwF (· * ·) a b) Poly.zero := by
  simp [MultiplyNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

/-- `MultiplyNTT` (Algorithm 45) is ocaml-pq's `multiplyNttSpec`, at every index. -/
theorem multiplyNTT_eq (a b : Poly) :
    idx (MultiplyNTT a b) = OcamlPq.MLDSA.multiplyNttSpec (idx a) (idx b) := by
  funext i
  simp only [OcamlPq.MLDSA.multiplyNttSpec, idx]
  rw [MultiplyNTT_eq_fold, pwFold_full]
  by_cases h : i < 256
  · simp [vget! _ i h]
  · simp [getElem!_neg, h, default_zq]

/-- `AddNTT` (Algorithm 44) is pointwise addition (ocaml-pq's `fipsAddPoly` is `ofZq (toZq a + toZq b)`). -/
theorem addNTT_eq (a b : Poly) :
    idx (AddNTT a b) = fun i => idx a i + idx b i := by
  funext i
  simp only [idx]
  rw [AddNTT_eq_fold, pwFold_full]
  by_cases h : i < 256
  · simp [vget! _ i h]
  · simp [getElem!_neg, h, default_zq]

end XSpec
