import Proofs.NTT

/-!
# Inverse NTT: the extracted Rust equals FIPS 204 Algorithm 42
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem vec_getElem!_set!_eq (xs : Vector Zq 256) {i : Nat} (x : Zq) (hi : i < 256) :
    (xs.set! i x)[i]! = x := by
  rw [set!_eq, getElem!_pos _ _ (by simpa using hi)]
  exact Vector.getElem_setIfInBounds_self hi

theorem vec_set!_set! (xs : Vector Zq 256) (i : Nat) (a b : Zq) :
    (xs.set! i a).set! i b = xs.set! i b := by
  rw [set!_eq, set!_eq, set!_eq]
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_setIfInBounds hk]
  split <;> rfl

/-! ## The inner loop (Algorithm 42, steps 9-13) -/

/-- One iteration of the inner `for j` loop of `nttInvLayer`, as a function of the polynomial. -/
def ibfly (len : Nat) (z : Zq) (w : Poly) (j : Nat) : Poly :=
  let w1 := w.set! j (w[j]! + w[j + len]!)
  let w2 := w1.set! (j + len) (w[j]! - w1[j + len]!)
  w2.set! (j + len) (z * w2[j + len]!)

theorem toZq_ibfly (w : Array U32 256#usize) (LEN : Nat) (z : Zq) (j i1 : Usize) (i3 i5 i6 : U32)
    (hLEN : 0 < LEN) (hj : j.val + LEN < 256) (hi1 : i1.val = j.val + LEN)
    (h1 : i1.val < w.val.length) (h2 : j.val < w.val.length)
    (h3 : ((i3.val : Nat) : Zq) = ((w.val[j.val]).val : Nat) + ((w.val[i1.val]).val : Nat))
    (h4 : i1.val < (w.set j i3).val.length)
    (h5 : ((i5.val : Nat) : Zq) = ((w.val[j.val]).val : Nat) - (((w.set j i3).val[i1.val]).val : Nat))
    (h6 : ((i6.val : Nat) : Zq) = z * (i5.val : Nat)) :
    toZq ((w.set j i3).set i1 i6) = ibfly LEN z (toZq w) j.val := by
  have hj256 : j.val < 256 := by omega
  have hi256 : i1.val < 256 := by omega
  have hne : j.val ≠ i1.val := by omega
  have hW1 : (toZq w)[j.val + LEN]! = (((w.val[i1.val]).val : Nat) : Zq) := by
    rw [← hi1]; exact toZq_getElem w _ h1
  have hW2 : (toZq w)[j.val]! = (((w.val[j.val]).val : Nat) : Zq) := toZq_getElem w _ h2
  have hset : (w.set j i3).val[i1.val] = w.val[i1.val] := by
    simp [Array.set_val_eq, List.getElem_set_ne hne]
  rw [hset] at h5
  rw [toZq_set _ _ _ hi256, toZq_set _ _ _ hj256, ibfly, hi1,
    vec_getElem!_set!_eq _ _ (by omega), vec_set!_set!,
    vec_getElem!_set!_ne _ _ (by omega) (by omega : j.val ≠ j.val + LEN)]
  rw [hi1] at *
  rw [h6, h5, h3, hW1, hW2]

@[step]
theorem inner_loop_inv (LEN start : Usize) (z : U32) (hz : z.val < Spec.q)
    (hLEN : 0 < LEN.val) (hfit : start.val + 2 * LEN.val ≤ 256)
    (w0 : Array U32 256#usize) (hw0 : Canonical w0) :
    ntt.ntt_inverse_layer_loop0_loop0 LEN w0 start z start ⦃ w =>
      Canonical w ∧
      toZq w = (List.range' start.val LEN.val).foldl (ibfly LEN.val (z.val : Zq)) (toZq w0) ⦄ := by
  unfold ntt.ntt_inverse_layer_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => start.val + LEN.val - p.2.val)
    (fun p => Canonical p.1 ∧ start.val ≤ p.2.val ∧ p.2.val ≤ start.val + LEN.val ∧
       toZq p.1 = (List.range' start.val (p.2.val - start.val)).foldl
         (ibfly LEN.val (z.val : Zq)) (toZq w0))
  · rintro ⟨w, j⟩ ⟨hc, h1, h2, h3⟩
    dsimp only at hc h1 h2 h3
    simp only [ntt.ntt_inverse_layer_loop0_loop0.body]
    step*
    all_goals try subst_vars
    all_goals try exact canon_get hc _
    all_goals try exact canon_get (canonical_set _ _ _ hc ‹_›) _
    have hb := toZq_ibfly w LEN.val (z.val : Zq) j i1 i3 i5 i6 hLEN (by scalar_tac) i1_post i2 t
      i3_post2 i4 i5_post2 i6_post2
    refine ⟨canonical_set _ _ _ (canonical_set _ _ _ hc i3_post1) i6_post1, by omega, by scalar_tac,
      ?_, by scalar_tac⟩
    rw [hb, h3, show j1.val - start.val = (j.val - start.val) + 1 by omega, List.range'_concat,
      List.foldl_append, List.foldl_cons, List.foldl_nil,
      show start.val + 1 * (j.val - start.val) = j.val by omega]
  · refine ⟨hw0, le_refl _, by simp, by simp⟩

/-! ## One layer (Algorithm 42, steps 5-14) -/

/-- One iteration of the block loop `while start < 256`, on the state `(m, start, w)`. -/
def blockFInv (len : Nat) (b : MProd Nat (MProd Nat Poly)) (_a : Nat) :
    MProd Nat (MProd Nat Poly) :=
  ⟨b.fst - 1, b.snd.fst + 2 * len,
    (List.range' b.snd.fst len).foldl (ibfly len (-zeta (b.fst - 1))) b.snd.snd⟩

/-- The block loop state after `i` blocks. -/
def blockFoldInv (len m0 : Nat) (w0 : Poly) (i : Nat) : MProd Nat (MProd Nat Poly) :=
  (List.range' 0 i).foldl (blockFInv len) ⟨m0, 0, w0⟩

theorem nttInvLayer_eq (len : Nat) (w : Poly) (m : Nat) :
    nttInvLayer len w m =
      ((blockFoldInv len m w (256 / (2 * len))).snd.snd,
        (blockFoldInv len m w (256 / (2 * len))).fst) := by
  unfold nttInvLayer blockFoldInv
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, -neg_mul]
  constructor <;> rfl

theorem blockFoldInv_succ (len m0 : Nat) (w0 : Poly) (i : Nat) :
    blockFoldInv len m0 w0 (i + 1) = blockFInv len (blockFoldInv len m0 w0 i) i := by
  simp [blockFoldInv, List.range'_concat, List.foldl_append]

theorem blockFoldInv_zero (len m0 : Nat) (w0 : Poly) : blockFoldInv len m0 w0 0 = ⟨m0, 0, w0⟩ := rfl

theorem blockFoldInv_fst (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (blockFoldInv len m0 w0 i).fst = m0 - i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [blockFoldInv_succ]; simp [blockFInv, ih]; omega

theorem blockFoldInv_start (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (blockFoldInv len m0 w0 i).snd.fst = 2 * len * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [blockFoldInv_succ]; simp [blockFInv, ih]; ring

theorem outer_loop_inv (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (w0 : Array U32 256#usize) (hw0 : Canonical w0) (m0 : Usize)
    (hm : ITER.val ≤ m0.val) (hm' : m0.val ≤ 256) :
    ntt.ntt_inverse_layer_loop0 LEN ITER w0 m0 0#usize ⦃ r =>
      Canonical r.1 ∧ r.2.val = m0.val - ITER.val ∧
      toZq r.1 = (blockFoldInv LEN.val m0.val (toZq w0) ITER.val).snd.snd ⦄ := by
  unfold ntt.ntt_inverse_layer_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize × Usize) => ITER.val - p.2.2.val)
    (fun p => Canonical p.1 ∧ p.2.2.val ≤ ITER.val ∧ p.2.1.val = m0.val - p.2.2.val ∧
       toZq p.1 = (blockFoldInv LEN.val m0.val (toZq w0) p.2.2.val).snd.snd)
  · rintro ⟨w, m, i⟩ ⟨hc, h1, h2, h3⟩
    dsimp only at hc h1 h2 h3
    simp only [ntt.ntt_inverse_layer_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < ITER.val := hi
      have hbound : 2 * LEN.val * (i.val + 1) ≤ 256 := by
        have := Nat.mul_le_mul_left LEN.val (show i.val + 1 ≤ ITER.val by omega)
        nlinarith
      have hbound2 : (i.val * 2) * LEN.val ≤ 256 := by nlinarith
      have e : (i.val * 2 * LEN.val) + 2 * LEN.val = 2 * LEN.val * (i.val + 1) := by ring
      step*
      all_goals try first
        | exact (zetas_get m1 (by omega) ‹_› _ ‹_›).1
        | (rw [start_post, i1_post]; omega)
        | (rw [i1_post]; scalar_tac)
      obtain ⟨_, hzeta⟩ := zetas_get m1 (by omega) ‹_› _ ‹_›
      have e1 : m1.val = m0.val - i.val - 1 := by omega
      have e2 : start.val = 2 * LEN.val * i.val := by rw [start_post, i1_post]; ring
      have hzc : ((z.val : Nat) : Zq) = -zeta m1.val := by
        rw [z_post2, hzeta]; simp
      refine ⟨w1_post1, by omega, by omega, ?_, by omega⟩
      rw [w1_post2, hzc, i3_post, blockFoldInv_succ, e1, e2, h3]
      simp [blockFInv, blockFoldInv_fst, blockFoldInv_start]
    · rename_i hi
      have hi' : i.val = ITER.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨hc, by omega, by rw [h3, hi']⟩
  · refine ⟨hw0, by simp, by simp, ?_⟩
    simp [blockFoldInv_zero]


theorem layer_inv_spec (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (w : Array U32 256#usize) (hw : Canonical w) (m : Usize)
    (hm : ITER.val ≤ m.val) (hm' : m.val ≤ 256) :
    ntt.ntt_inverse_layer LEN ITER w m ⦃ r => Canonical r.1 ∧ r.2.val = m.val - ITER.val ∧
      (toZq r.1, r.2.val) = nttInvLayer LEN.val (toZq w) m.val ⦄ := by
  unfold ntt.ntt_inverse_layer
  apply WP.spec_mono (outer_loop_inv LEN ITER hLEN hprod w hw m hm hm')
  rintro ⟨w', m'⟩ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  have hdiv : 256 / (2 * LEN.val) = ITER.val := by
    apply Nat.div_eq_of_eq_mul_right (by omega)
    nlinarith
  rw [nttInvLayer_eq, hdiv]
  simp only at h2 h3 ⊢
  rw [h3, h2, blockFoldInv_fst]

attribute [step] layer_inv_spec

/-! ## The final scaling by 256⁻¹ (Algorithm 42, steps 16-18) -/

/-- One iteration of the scaling loop `for j`, as a function of the polynomial. -/
def scaleF (b : Poly) (a : Nat) : Poly := Vector.set! b a (8347681 * b[a]!)

theorem scale_loop (w0 : Array U32 256#usize) (hw0 : Canonical w0) :
    ntt.ntt_inverse_loop w0 0#usize ⦃ w => Canonical w ∧
      toZq w = (List.range' 0 256).foldl scaleF (toZq w0) ⦄ := by
  unfold ntt.ntt_inverse_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => Canonical p.1 ∧ p.2.val ≤ 256 ∧
       toZq p.1 = (List.range' 0 p.2.val).foldl scaleF (toZq w0))
  · rintro ⟨w, j⟩ ⟨hc, h1, h2⟩
    dsimp only at hc h1 h2
    simp only [ntt.ntt_inverse_loop.body]
    step*
    all_goals try subst_vars
    all_goals try first
      | exact canon_get hc _
      | scalar_tac
    have hj : j.val < 256 := by scalar_tac
    refine ⟨canonical_set _ _ _ hc i1_post1, by omega, ?_, by omega⟩
    have hW := toZq_getElem w j.val i
    rw [toZq_set _ _ _ hj, i1_post2, j1_post, List.range'_concat, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ← h2, scaleF, zero_add, one_mul, hW]
    rfl
  · refine ⟨hw0, by simp, by simp⟩

/-- Algorithm 42 is the composition of its eight layers followed by the scaling loop. -/
theorem NTTInv_eq_layers (w : Poly) :
    NTTInv w = (List.range' 0 256).foldl scaleF
             (let p := nttInvLayer 1 w 256
              let p := nttInvLayer 2 p.1 p.2
              let p := nttInvLayer 4 p.1 p.2
              let p := nttInvLayer 8 p.1 p.2
              let p := nttInvLayer 16 p.1 p.2
              let p := nttInvLayer 32 p.1 p.2
              let p := nttInvLayer 64 p.1 p.2
              (nttInvLayer 128 p.1 p.2).1) := by
  simp [NTTInv, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    show List.range' 0 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rfl

theorem ntt_inverse_spec (w : Array U32 256#usize) (hw : Canonical w) :
    ntt.ntt_inverse w ⦃ r => Canonical r ∧ toZq r = Spec.NTTInv (toZq w) ⦄ := by
  unfold ntt.ntt_inverse
  step*
  apply WP.spec_mono (scale_loop w_hat8 w_hat8_post1)
  rintro r ⟨hr1, hr2⟩
  refine ⟨hr1, ?_⟩
  rw [hr2, NTTInv_eq_layers]
  simp only [← w_hat1_post3, ← w_hat2_post3, ← w_hat3_post3, ← w_hat4_post3, ← w_hat5_post3,
    ← w_hat6_post3, ← w_hat7_post3, ← w_hat8_post3]

/-- **Inverse NTT.** On canonical input the extracted `ntt_inverse` returns, without failing or
diverging, a canonical array whose coefficients are those of FIPS 204 Algorithm 42 applied to the input. -/
theorem ntt_inverse_correct (w : Array U32 256#usize) (hw : Canonical w) :
    ∃ r, ntt.ntt_inverse w = ok r ∧ Canonical r ∧ toZq r = Spec.NTTInv (toZq w) := by
  obtain ⟨r, hr, h⟩ := WP.spec_imp_exists (ntt_inverse_spec w hw)
  exact ⟨r, hr, h⟩

end Proofs
