import Proofs.NTTInverse
import Spec.NTTOps

/-!
# Arithmetic under the NTT: the extracted Rust equals FIPS 204 Algorithms 44-48

Refinement lemmas for `Impl.ntt.{add_poly, sub_poly, multiply_ntt, ntt_vec, scalar_vector_ntt_inverse,
matrix_vector_ntt}` against `Spec.AddNTT`, `Spec.MultiplyNTT`, `Spec.NTTVec`, `Spec.ScalarVectorNTT` (followed by
`Spec.NTTInvVec`) and `Spec.MatrixVectorNTT`, in the house style of `Proofs/Repr.lean`.

All Rust loops here run in the same order as the spec's loops (rows `i` outer, columns `j` inner, accumulating
into `w[i]`), so the invariants are `foldl` models over `List.range'` and no reassociation of the sum is needed.
The matrix is `k × ℓ` (`m[i][j]` is row `i`, column `j`), as in `Spec.MatrixVectorNTT`.

Also here: `field.neg` on canonical inputs (`neg_zmod`), which the earlier field lemmas lacked.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## `field.neg` -/

theorem neg_spec (a : U32) (ha : a.val < 8380417) :
    field.neg a ⦃ y => y.val = (8380417 - a.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.neg
  simp only [global_simps]
  step*

theorem neg_zmod (a : U32) (ha : a.val < 8380417) :
    field.neg a ⦃ y => y.val < 8380417 ∧ ((y.val : Nat) : ZMod 8380417) = -((a.val : Nat) : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (neg_spec a ha)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  have hq : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
  rw [h1, ZMod.natCast_mod, Nat.cast_sub (by omega), hq]
  ring

attribute [step] neg_zmod

/-! ## Spec side: the pointwise loops as folds -/

theorem vget! {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) : v[i]! = v[i] :=
  getElem!_pos v i (by simpa using h)

/-- One iteration of the spec's pointwise loop: `c[j] := op a[j] b[j]`. -/
def pwF (op : Zq → Zq → Zq) (a b : Poly) (c : Poly) (j : Nat) : Poly := c.set! j (op a[j]! b[j]!)

theorem pwFold_getElem (op : Zq → Zq → Zq) (a b : Poly) (n k : Nat) (hk : k < 256) :
    ((List.range' 0 n).foldl (pwF op a b) Poly.zero)[k] = if k < n then op a[k] b[k] else 0 := by
  induction n with
  | zero => simp [Poly.zero]
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [pwF, set!_eq, Vector.getElem_setIfInBounds hk, Nat.zero_add, Nat.one_mul]
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

/-- `AddNTT` is the componentwise sum (the `+` on `Poly` used throughout `Spec/MLDSA.lean`). -/
theorem AddNTT_eq_add (a b : Poly) : AddNTT a b = a + b := by
  rw [AddNTT_eq_fold, pwFold_full]
  rfl

/-! ## The pointwise loops -/

theorem pw_step (op : Zq → Zq → Zq) (a b c : Array U32 256#usize) (i : Usize) (x : U32)
    (hi : i.val < 256)
    (h : toZq c = (List.range' 0 i.val).foldl (pwF op (toZq a) (toZq b)) Poly.zero)
    (hx : ((x.val : Nat) : Zq) = op (toZq a)[i.val]! (toZq b)[i.val]!) :
    toZq (c.set i x) = (List.range' 0 (i.val + 1)).foldl (pwF op (toZq a) (toZq b)) Poly.zero := by
  rw [toZq_set c i x hi, h, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, pwF, hx]
  simp

theorem add_poly_loop_spec (a b : Array U32 256#usize) (ha : Canonical a) (hb : Canonical b) :
    ntt.add_poly_loop a b (Array.repeat 256#usize 0#u32) 0#usize ⦃ c => Canonical c ∧
      toZq c = (List.range' 0 256).foldl (pwF (· + ·) (toZq a) (toZq b)) Poly.zero ⦄ := by
  unfold ntt.add_poly_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => Canonical p.1 ∧ p.2.val ≤ 256 ∧
       toZq p.1 = (List.range' 0 p.2.val).foldl (pwF (· + ·) (toZq a) (toZq b)) Poly.zero)
  · rintro ⟨c, i⟩ ⟨hc, h1, h2⟩
    dsimp only at hc h1 h2
    simp only [ntt.add_poly_loop.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := hi
      have hA : i.val < a.val.length := by rw [len256 a]; exact hi'
      have hB : i.val < b.val.length := by rw [len256 b]; exact hi'
      step*
      all_goals try subst_vars
      all_goals try first
        | exact canon_get ha _
        | exact canon_get hb _
      have e : i4.val = i.val + 1 := by scalar_tac
      refine ⟨canonical_set _ _ _ hc i3_post1, by omega, ?_, by omega⟩
      rw [e]
      apply pw_step _ a b c i i3 hi' h2
      rw [i3_post2, toZq_getElem a i.val hA, toZq_getElem b i.val hB]
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hc, by rw [h2, hi']⟩
  · exact ⟨canonical_repeat_zero, by simp, by simp [toZq_repeat_zero]⟩

theorem sub_poly_loop_spec (a b : Array U32 256#usize) (ha : Canonical a) (hb : Canonical b) :
    ntt.sub_poly_loop a b (Array.repeat 256#usize 0#u32) 0#usize ⦃ c => Canonical c ∧
      toZq c = (List.range' 0 256).foldl (pwF (· - ·) (toZq a) (toZq b)) Poly.zero ⦄ := by
  unfold ntt.sub_poly_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => Canonical p.1 ∧ p.2.val ≤ 256 ∧
       toZq p.1 = (List.range' 0 p.2.val).foldl (pwF (· - ·) (toZq a) (toZq b)) Poly.zero)
  · rintro ⟨c, i⟩ ⟨hc, h1, h2⟩
    dsimp only at hc h1 h2
    simp only [ntt.sub_poly_loop.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := hi
      have hA : i.val < a.val.length := by rw [len256 a]; exact hi'
      have hB : i.val < b.val.length := by rw [len256 b]; exact hi'
      step*
      all_goals try subst_vars
      all_goals try first
        | exact canon_get ha _
        | exact canon_get hb _
      have e : i4.val = i.val + 1 := by scalar_tac
      refine ⟨canonical_set _ _ _ hc i3_post1, by omega, ?_, by omega⟩
      rw [e]
      apply pw_step _ a b c i i3 hi' h2
      rw [i3_post2, toZq_getElem a i.val hA, toZq_getElem b i.val hB]
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hc, by rw [h2, hi']⟩
  · exact ⟨canonical_repeat_zero, by simp, by simp [toZq_repeat_zero]⟩

theorem multiply_ntt_loop_spec (a b : Array U32 256#usize) (ha : Canonical a) (hb : Canonical b) :
    ntt.multiply_ntt_body_loop a b (Array.repeat 256#usize 0#u32) 0#usize ⦃ c => Canonical c ∧
      toZq c = (List.range' 0 256).foldl (pwF (· * ·) (toZq a) (toZq b)) Poly.zero ⦄ := by
  unfold ntt.multiply_ntt_body_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => Canonical p.1 ∧ p.2.val ≤ 256 ∧
       toZq p.1 = (List.range' 0 p.2.val).foldl (pwF (· * ·) (toZq a) (toZq b)) Poly.zero)
  · rintro ⟨c, i⟩ ⟨hc, h1, h2⟩
    dsimp only at hc h1 h2
    simp only [ntt.multiply_ntt_body_loop.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := hi
      have hA : i.val < a.val.length := by rw [len256 a]; exact hi'
      have hB : i.val < b.val.length := by rw [len256 b]; exact hi'
      step*
      all_goals try subst_vars
      all_goals try first
        | exact canon_get ha _
        | exact canon_get hb _
      have e : i4.val = i.val + 1 := by scalar_tac
      refine ⟨canonical_set _ _ _ hc i3_post1, by omega, ?_, by omega⟩
      rw [e]
      apply pw_step _ a b c i i3 hi' h2
      rw [i3_post2, toZq_getElem a i.val hA, toZq_getElem b i.val hB]
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hc, by rw [h2, hi']⟩
  · exact ⟨canonical_repeat_zero, by simp, by simp [toZq_repeat_zero]⟩

/-! ## Algorithms 44 and 45, and the subtraction -/

/-- Algorithm 44 `AddNTT`. -/
@[step]
theorem add_poly_spec (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ntt.add_poly a b ⦃ r => Repr r (Spec.AddNTT A B) ⦄ := by
  unfold ntt.add_poly
  apply WP.spec_mono (add_poly_loop_spec a b ha.canon hb.canon)
  rintro r ⟨hr1, hr2⟩
  exact ⟨hr1, by rw [hr2, AddNTT_eq_fold, ha.eq, hb.eq]⟩

/-- `add_poly` computes the componentwise sum `A + B` of `Spec.MLDSA` (e.g. `t = NTT⁻¹(…) + s₂`). -/
theorem add_poly_add_spec (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ntt.add_poly a b ⦃ r => Repr r (A + B) ⦄ := by
  apply WP.spec_mono (add_poly_spec a b A B ha hb)
  intro r hr
  rwa [AddNTT_eq_add] at hr

/-- The componentwise difference `A - B` (used for `w - c·t₁·2^d` and `w - c s₂`). -/
@[step]
theorem sub_poly_spec (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ntt.sub_poly a b ⦃ r => Repr r (A - B) ⦄ := by
  unfold ntt.sub_poly
  apply WP.spec_mono (sub_poly_loop_spec a b ha.canon hb.canon)
  rintro r ⟨hr1, hr2⟩
  refine ⟨hr1, ?_⟩
  rw [hr2, ha.eq, hb.eq, pwFold_full]
  rfl

/-- Algorithm 45 `MultiplyNTT`. -/
@[step]
theorem multiply_ntt_spec (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ntt.multiply_ntt a b ⦃ r => Repr r (Spec.MultiplyNTT A B) ⦄ := by
  unfold ntt.multiply_ntt ntt.dispatch.multiply_ntt ntt.multiply_ntt_body
  apply WP.spec_mono (multiply_ntt_loop_spec a b ha.canon hb.canon)
  rintro r ⟨hr1, hr2⟩
  exact ⟨hr1, by rw [hr2, MultiplyNTT_eq_fold, ha.eq, hb.eq]⟩

theorem add_poly_correct (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ∃ r, ntt.add_poly a b = ok r ∧ Repr r (Spec.AddNTT A B) :=
  WP.spec_imp_exists (add_poly_spec a b A B ha hb)

theorem sub_poly_correct (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ∃ r, ntt.sub_poly a b = ok r ∧ Repr r (A - B) :=
  WP.spec_imp_exists (sub_poly_spec a b A B ha hb)

theorem multiply_ntt_correct (a b : Array U32 256#usize) (A B : Poly) (ha : Repr a A) (hb : Repr b B) :
    ∃ r, ntt.multiply_ntt a b = ok r ∧ Repr r (Spec.MultiplyNTT A B) :=
  WP.spec_imp_exists (multiply_ntt_spec a b A B ha hb)

/-! ## Vector helpers -/

theorem ReprVec_repeat_zero (N : Usize) (k : Nat) (hN : N.val = k) :
    ReprVec (Array.repeat N (Array.repeat 256#usize 0#u32)) (Vector.replicate k Poly.zero) := by
  refine ⟨hN, fun i hi => ?_⟩
  simp only [Array.repeat_val, List.getElem_replicate, Vector.getElem_replicate]
  exact repr_repeat_zero

theorem ReprMat.index_spec {K L : Usize} {k ℓ : Nat} {a : Array (Array (Array U32 256#usize) L) K}
    {m : Vector (Vector Poly ℓ) k} (h : ReprMat a m) (i : Usize) (hi : i.val < k) :
    Array.index_usize a i ⦃ x => ReprVec x m[i.val] ⦄ := by
  have hlt : i.val < a.val.length := by have := a.property; have := h.len; omega
  have e : a[i]? = some (a.val[i.val]'hlt) := by simp
  unfold Array.index_usize
  rw [e]
  simp only [WP.spec_ok]
  exact h.elt i.val hi

theorem foldl_set_replicate {α : Type} (m : Nat) (z : α) (h : Nat → α) (n : Nat) :
    (List.range' 0 n).foldl (fun (c : Vector α m) j => c.set! j (h j)) (Vector.replicate m z) =
      Vector.ofFn (fun k : Fin m => if k.val < n then h k.val else z) := by
  induction n with
  | zero => apply Vector.ext; intro k hk; simp
  | succ n ih =>
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    apply Vector.ext
    intro k hk
    rw [set!_eq', Vector.getElem_setIfInBounds hk]
    simp only [Vector.getElem_ofFn, Nat.zero_add, Nat.one_mul]
    by_cases e : n = k
    · subst e; simp
    · have hh : (k < n + 1 ↔ k < n) := by omega
      simp [e, Ne.symm e, hh]

theorem foldl_set_replicate_full {α : Type} (m : Nat) (z : α) (h : Nat → α) :
    (List.range' 0 m).foldl (fun (c : Vector α m) j => c.set! j (h j)) (Vector.replicate m z) =
      Vector.ofFn (fun k : Fin m => h k.val) := by
  rw [foldl_set_replicate]
  congr 1
  funext k
  simp [k.isLt]

theorem fold_step_range {β : Type} (f : β → Nat → β) (x : β) (n : Nat) :
    (List.range' 0 (n + 1)).foldl f x = f ((List.range' 0 n).foldl f x) n := by
  rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp

/-! ## `ntt_vec` -/

/-- One iteration of `NTTVec`'s per-entry NTT, as a function of the vector. -/
def nttVecF {k : Nat} (V : Vector Poly k) (c : Vector Poly k) (j : Nat) : Vector Poly k :=
  c.set! j (NTT V[j]!)

theorem NTTVec_eq {k : Nat} (V : Vector Poly k) :
    Spec.NTTVec V = (List.range' 0 k).foldl (nttVecF V) (Vector.replicate k Poly.zero) := by
  unfold nttVecF
  rw [foldl_set_replicate_full k Poly.zero (fun j => NTT V[j]!)]
  apply Vector.ext
  intro j hj
  simp [Spec.NTTVec, vget! V j hj]

theorem ntt_vec_loop_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    ntt.ntt_vec_loop v (Array.repeat N (Array.repeat 256#usize 0#u32)) 0#usize ⦃ r =>
      ReprVec r ((List.range' 0 k).foldl (nttVecF V) (Vector.replicate k Poly.zero)) ⦄ := by
  have hN : N.val = k := hv.len
  unfold ntt.ntt_vec_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) N × Usize) => N.val - p.2.val)
    (fun p => p.2.val ≤ N.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (nttVecF V) (Vector.replicate k Poly.zero)))
  · rintro ⟨out, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [ntt.ntt_vec_loop.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < k := by omega
      step with hv.index_spec i hik as ⟨a, ha⟩
      step with ntt_spec a ha.canon as ⟨a1, ha1, ha2⟩
      step*
      have e : i1.val = i.val + 1 := by scalar_tac
      rw [e, fold_step_range]
      have hr : Repr a1 (NTT V[i.val]!) := ⟨ha1, by rw [ha2, ha.eq, vget! V i.val hik]⟩
      rw [a2_post]
      exact ⟨by scalar_tac, h2.set i a1 _ hr hik, by scalar_tac⟩
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi', hN] at h2
      exact h2
  · exact ⟨by simp, by simpa using ReprVec_repeat_zero N k hN⟩

@[step]
theorem ntt_vec_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    ntt.ntt_vec v ⦃ r => ReprVec r (Spec.NTTVec V) ⦄ := by
  unfold ntt.ntt_vec
  apply WP.spec_mono (ntt_vec_loop_spec v V hv)
  intro r hr
  rwa [NTTVec_eq]

/-! ## `ntt_vec_into` (the same loop writing into a caller-provided array) -/

theorem ntt_vec_into_loop_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    ntt.ntt_vec_into_loop v (Array.repeat N (Array.repeat 256#usize 0#u32)) 0#usize ⦃ r =>
      ReprVec r ((List.range' 0 k).foldl (nttVecF V) (Vector.replicate k Poly.zero)) ⦄ := by
  have hN : N.val = k := hv.len
  unfold ntt.ntt_vec_into_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) N × Usize) => N.val - p.2.val)
    (fun p => p.2.val ≤ N.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (nttVecF V) (Vector.replicate k Poly.zero)))
  · rintro ⟨out, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [ntt.ntt_vec_into_loop.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < k := by omega
      step with hv.index_spec i hik as ⟨t, ht⟩
      step with ntt_in_place_spec t ht.canon as ⟨t1, ht1, ht2⟩
      step*
      have e : i1.val = i.val + 1 := by scalar_tac
      rw [e, fold_step_range]
      have hr : Repr t1 (NTT V[i.val]!) := ⟨ht1, by rw [ht2, ht.eq, vget! V i.val hik]⟩
      rw [a_post]
      exact ⟨by scalar_tac, h2.set i t1 _ hr hik, by scalar_tac⟩
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi', hN] at h2
      exact h2
  · exact ⟨by simp, by simpa using ReprVec_repeat_zero N k hN⟩

/-- `ntt_vec_into v out` (whatever `out` held) represents `NTTVec V`. -/
@[step]
theorem ntt_vec_into_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (out : Array (Array U32 256#usize) N)
    (V : Vector Poly k) (hv : ReprVec v V) :
    ntt.ntt_vec_into v out ⦃ r => ReprVec r (Spec.NTTVec V) ⦄ := by
  unfold ntt.ntt_vec_into
  apply WP.spec_mono (ntt_vec_into_loop_spec v V hv)
  intro r hr
  rwa [NTTVec_eq]

theorem ntt_vec_correct {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    ∃ r, ntt.ntt_vec v = ok r ∧ ReprVec r (Spec.NTTVec V) :=
  WP.spec_imp_exists (ntt_vec_spec v V hv)

/-! ## `scalar_vector_ntt_inverse` -/

/-- One iteration of `NTT⁻¹(ScalarVectorNTT(ĉ, v̂))`, entrywise. -/
def svF {ℓ : Nat} (C : Poly) (V : Vector Poly ℓ) (c : Vector Poly ℓ) (j : Nat) : Vector Poly ℓ :=
  c.set! j (NTTInv (MultiplyNTT C V[j]!))

theorem ScalarVectorNTT_eq {ℓ : Nat} (C : Poly) (V : Vector Poly ℓ) :
    Spec.NTTInvVec (Spec.ScalarVectorNTT C V) =
      (List.range' 0 ℓ).foldl (svF C V) (Vector.replicate ℓ Poly.zero) := by
  unfold svF
  rw [foldl_set_replicate_full ℓ Poly.zero (fun j => NTTInv (MultiplyNTT C V[j]!))]
  have h1 : Spec.ScalarVectorNTT C V =
      (List.range' 0 ℓ).foldl (fun (c : Vector Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero) := by
    simp [Spec.ScalarVectorNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [h1, foldl_set_replicate_full ℓ Poly.zero (fun j => MultiplyNTT C V[j]!)]
  apply Vector.ext
  intro j hj
  simp [Spec.NTTInvVec]

theorem scalar_vector_loop_spec {N : Usize} {k : Nat} (c : Array U32 256#usize) (C : Poly) (hc : Repr c C)
    (v : Array (Array U32 256#usize) N) (V : Vector Poly k) (hv : ReprVec v V) :
    ntt.scalar_vector_ntt_inverse_loop c v (Array.repeat N (Array.repeat 256#usize 0#u32)) 0#usize ⦃ r =>
      ReprVec r ((List.range' 0 k).foldl (svF C V) (Vector.replicate k Poly.zero)) ⦄ := by
  have hN : N.val = k := hv.len
  unfold ntt.scalar_vector_ntt_inverse_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) N × Usize) => N.val - p.2.val)
    (fun p => p.2.val ≤ N.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (svF C V) (Vector.replicate k Poly.zero)))
  · rintro ⟨out, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [ntt.scalar_vector_ntt_inverse_loop.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < k := by omega
      step with hv.index_spec i hik as ⟨a, ha⟩
      step with multiply_ntt_spec c a C _ hc ha as ⟨a1, ha1⟩
      step with ntt_inverse_spec a1 ha1.canon as ⟨a2, ha2, ha3⟩
      step*
      have e : i1.val = i.val + 1 := by scalar_tac
      rw [e, fold_step_range]
      have hr : Repr a2 (NTTInv (MultiplyNTT C V[i.val]!)) :=
        ⟨ha2, by rw [ha3, ha1.eq, vget! V i.val hik]⟩
      rw [a3_post]
      exact ⟨by scalar_tac, h2.set i a2 _ hr hik, by scalar_tac⟩
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi', hN] at h2
      exact h2
  · exact ⟨by simp, by simpa using ReprVec_repeat_zero N k hN⟩

/-- `scalar_vector_ntt_inverse ĉ v̂ = NTT⁻¹(ĉ ∘ v̂)`, the combination `⟨⟨c v⟩⟩` of Algorithms 47 and 42. -/
@[step]
theorem scalar_vector_ntt_inverse_spec {N : Usize} {k : Nat} (c : Array U32 256#usize) (C : Poly)
    (hc : Repr c C) (v : Array (Array U32 256#usize) N) (V : Vector Poly k) (hv : ReprVec v V) :
    ntt.scalar_vector_ntt_inverse c v ⦃ r =>
      ReprVec r (Spec.NTTInvVec (Spec.ScalarVectorNTT C V)) ⦄ := by
  unfold ntt.scalar_vector_ntt_inverse
  apply WP.spec_mono (scalar_vector_loop_spec c C hc v V hv)
  intro r hr
  rwa [ScalarVectorNTT_eq]

theorem scalar_vector_ntt_inverse_correct {N : Usize} {k : Nat} (c : Array U32 256#usize) (C : Poly)
    (hc : Repr c C) (v : Array (Array U32 256#usize) N) (V : Vector Poly k) (hv : ReprVec v V) :
    ∃ r, ntt.scalar_vector_ntt_inverse c v = ok r ∧
      ReprVec r (Spec.NTTInvVec (Spec.ScalarVectorNTT C V)) :=
  WP.spec_imp_exists (scalar_vector_ntt_inverse_spec c C hc v V hv)

/-! ## `matrix_vector_ntt` (Algorithm 48) -/

/-- One iteration of the inner `for j` loop of `MatrixVectorNTT`, as a function of the accumulator vector. -/
def mvInner {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (i : Nat) (w : Vector Poly k)
    (j : Nat) : Vector Poly k :=
  w.set! i (AddNTT w[i]! (MultiplyNTT (M[i]!)[j]! V[j]!))

/-- One iteration of the outer `for i` loop of `MatrixVectorNTT`. -/
def mvOuter {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) (w : Vector Poly k)
    (i : Nat) : Vector Poly k :=
  (List.range' 0 ℓ).foldl (mvInner M V i) w

theorem MatrixVectorNTT_eq {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (V : Vector Poly ℓ) :
    Spec.MatrixVectorNTT M V =
      (List.range' 0 k).foldl (mvOuter M V) (Vector.replicate k Poly.zero) := by
  simp [Spec.MatrixVectorNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

theorem mv_inner_loop {K L : Usize} {k ℓ : Nat}
    (m : Array (Array (Array U32 256#usize) L) K) (M : Vector (Vector Poly ℓ) k) (hM : ReprMat m M)
    (v : Array (Array U32 256#usize) L) (V : Vector Poly ℓ) (hv : ReprVec v V)
    (i : Usize) (hi : i.val < k)
    (w0 : Array (Array U32 256#usize) K) (W0 : Vector Poly k) (hw0 : ReprVec w0 W0) :
    ntt.matrix_vector_ntt_loop0_loop0 m v w0 i 0#usize ⦃ w =>
      ReprVec w ((List.range' 0 ℓ).foldl (mvInner M V i.val) W0) ⦄ := by
  have hL : L.val = ℓ := hv.len
  have hK : K.val = k := hM.len
  unfold ntt.matrix_vector_ntt_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Usize) => L.val - p.2.val)
    (fun p => p.2.val ≤ L.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (mvInner M V i.val) W0))
  · rintro ⟨w, j⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [ntt.matrix_vector_ntt_loop0_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < L.val := hj
      have hjl : j.val < ℓ := by omega
      step with h2.index_spec i hi as ⟨a, ha⟩
      step with hM.index_spec i hi as ⟨a1, ha1⟩
      step with ha1.index_spec j hjl as ⟨a2, ha2⟩
      step with hv.index_spec j hjl as ⟨a3, ha3⟩
      step with multiply_ntt_spec a2 a3 _ _ ha2 ha3 as ⟨a4, ha4⟩
      step with add_poly_spec a a4 _ _ ha ha4 as ⟨a5, ha5⟩
      step*
      have e : j1.val = j.val + 1 := by scalar_tac
      rw [e, fold_step_range]
      have hr : Repr a5 (AddNTT ((List.range' 0 j.val).foldl (mvInner M V i.val) W0)[i.val]!
          (MultiplyNTT (M[i.val]!)[j.val]! V[j.val]!)) := by
        rw [vget! ((List.range' 0 j.val).foldl (mvInner M V i.val) W0) i.val hi, vget! M i.val hi,
          vget! M[i.val] j.val hjl, vget! V j.val hjl]
        exact ha5
      rw [a6_post]
      exact ⟨by scalar_tac, h2.set i a5 _ hr hi, by scalar_tac⟩
    · rename_i hj
      have hj' : j.val = L.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hj', hL] at h2
      exact h2
  · exact ⟨by simp, by simpa using hw0⟩

theorem mv_outer_loop {K L : Usize} {k ℓ : Nat}
    (m : Array (Array (Array U32 256#usize) L) K) (M : Vector (Vector Poly ℓ) k) (hM : ReprMat m M)
    (v : Array (Array U32 256#usize) L) (V : Vector Poly ℓ) (hv : ReprVec v V) :
    ntt.matrix_vector_ntt_loop0 m v (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize ⦃ w =>
      ReprVec w ((List.range' 0 k).foldl (mvOuter M V) (Vector.replicate k Poly.zero)) ⦄ := by
  have hK : K.val = k := hM.len
  unfold ntt.matrix_vector_ntt_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Usize) => K.val - p.2.val)
    (fun p => p.2.val ≤ K.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (mvOuter M V) (Vector.replicate k Poly.zero)))
  · rintro ⟨w, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [ntt.matrix_vector_ntt_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      step with mv_inner_loop m M hM v V hv i hik w _ h2 as ⟨w1, hw1⟩
      step*
      have e : i1.val = i.val + 1 := by scalar_tac
      rw [e, fold_step_range]
      exact ⟨by scalar_tac, hw1, by scalar_tac⟩
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi', hK] at h2
      exact h2
  · exact ⟨by simp, by simpa using ReprVec_repeat_zero K k hK⟩

/-- Algorithm 48 `MatrixVectorNTT`: `w[i] = Σ_j M[i][j] ∘ v[j]` for a `k × ℓ` matrix. -/
@[step]
theorem matrix_vector_ntt_spec {K L : Usize} {k ℓ : Nat}
    (m : Array (Array (Array U32 256#usize) L) K) (M : Vector (Vector Poly ℓ) k) (hM : ReprMat m M)
    (v : Array (Array U32 256#usize) L) (V : Vector Poly ℓ) (hv : ReprVec v V) :
    ntt.matrix_vector_ntt m v ⦃ w => ReprVec w (Spec.MatrixVectorNTT M V) ⦄ := by
  unfold ntt.matrix_vector_ntt
  apply WP.spec_mono (mv_outer_loop m M hM v V hv)
  intro r hr
  rwa [MatrixVectorNTT_eq]

theorem matrix_vector_ntt_correct {K L : Usize} {k ℓ : Nat}
    (m : Array (Array (Array U32 256#usize) L) K) (M : Vector (Vector Poly ℓ) k) (hM : ReprMat m M)
    (v : Array (Array U32 256#usize) L) (V : Vector Poly ℓ) (hv : ReprVec v V) :
    ∃ w, ntt.matrix_vector_ntt m v = ok w ∧ ReprVec w (Spec.MatrixVectorNTT M V) :=
  WP.spec_imp_exists (matrix_vector_ntt_spec m M hM v V hv)

end Proofs
