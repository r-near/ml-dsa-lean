import Proofs.NTTOps

/-!
# The verify-only lazy NTT and NTT⁻¹ equal FIPS 204 Algorithms 41 and 42

`verify_arith.ntt_pub` and `verify_arith.ntt_inverse_pub` skip the per-butterfly reductions of `ntt.ntt` and
`ntt.ntt_inverse`: Shoup multiplication accepts any 32-bit input and returns a value in `[0, 2q)`, so a forward layer
grows every coefficient by at most `2q` and an inverse layer doubles the bound. The coefficients stay below `17q` (forward,
reduced once at the end) and `256q` (inverse, finished by the exact `mul_shoup` scaling), so no `u32` operation wraps.
The statements have the shape of `ntt_spec` and `ntt_inverse_spec` (canonical in, canonical out, `toZq` equals
`Spec.NTT`/`Spec.NTTInv`), so everything built on those holds for the lazy versions.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem Q_eq : field.Q = 8380417#u32 := by
  unfold field.Q; rfl

/-- Every coefficient is below `B`. -/
def LazyBounded (B : Nat) (w : Array U32 256#usize) : Prop := ∀ x ∈ w.val, x.val < B

theorem bounded_mono {B B' : Nat} (h : B ≤ B') {w : Array U32 256#usize} (hw : LazyBounded B w) : LazyBounded B' w :=
  fun x hx => lt_of_lt_of_le (hw x hx) h

theorem bounded_set (B : Nat) (w : Array U32 256#usize) (i : Usize) (x : U32) (hw : LazyBounded B w)
    (hx : x.val < B) : LazyBounded B (w.set i x) := by
  intro y hy
  rw [Array.set_val_eq] at hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hw y h
  · subst h; exact hx

theorem bounded_get {B : Nat} {w : Array U32 256#usize} (hw : LazyBounded B w) {k : Nat} (h : k < w.val.length) :
    (w.val[k]).val < B := hw _ (List.getElem_mem h)

theorem canonical_iff_bounded (w : Array U32 256#usize) : Canonical w ↔ LazyBounded 8380417 w := Iff.rfl

/-! ## Lazy Shoup product -/

theorem shoup_lazy_nat (z zp x : U32) (hzp : zp.val = z.val * 4294967296 / 8380417) :
    verify_arith.shoup_lazy z zp x ⦃ y => y.val < 2 * 8380417 ∧ y.val % 8380417 = (z.val * x.val) % 8380417 ⦄ := by
  have hx32 : x.val < 4294967296 := x.hBounds
  have hzp32 : zp.val < 4294967296 := zp.hBounds
  have hn := mul_shoup_nat z.val zp.val x.val hzp hx32
  have hxm : x.val % 18446744073709551616 = x.val := Nat.mod_eq_of_lt (by omega)
  have hzpm : zp.val % 18446744073709551616 = zp.val := Nat.mod_eq_of_lt (by omega)
  have hprod : x.val * zp.val < 4294967296 * 4294967296 := Nat.mul_lt_mul'' hx32 hzp32
  unfold verify_arith.shoup_lazy
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_sub_val_u32, wrapping_mul_val_u32, UScalar.cast_val_eq,
    Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U64.numBits, U32.numBits, UScalarTy.numBits] at *
  all_goals rw [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hzpm] at i2_post
  all_goals generalize hzx : z.val * x.val = P at *
  all_goals generalize hxz : x.val * zp.val = A at *
  all_goals omega

theorem shoup_lazy_zmod (z zp x : U32) (hzp : zp.val = z.val * 4294967296 / 8380417) :
    verify_arith.shoup_lazy z zp x ⦃ y => y.val < 2 * 8380417 ∧
      ((y.val : Nat) : Zq) = (z.val : Zq) * (x.val : Zq) ⦄ := by
  apply WP.spec_mono (shoup_lazy_nat z zp x hzp)
  rintro y ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  have := (ZMod.natCast_eq_natCast_iff' y.val (z.val * x.val) 8380417).mpr h2
  rw [this, Nat.cast_mul]

attribute [step] shoup_lazy_zmod

/-! ## Forward layer -/

/-- Index sets of the inner loop of one block at counter `cur`: not yet processed, and processed. -/
def Unproc (start LEN cur k : Nat) : Prop :=
  (cur ≤ k ∧ k < start + LEN) ∨ (cur + LEN ≤ k ∧ k < start + 2 * LEN)
def Proc (start LEN cur k : Nat) : Prop :=
  (start ≤ k ∧ k < cur) ∨ (start + LEN ≤ k ∧ k < cur + LEN)

/-- The bounds of the inner loop: unprocessed entries are below `Bin`, processed ones below `Bout`, entries outside the
block are those of `w0`. -/
def LazyInv (start LEN cur Bin Bout : Nat) (w0 w : Array U32 256#usize) : Prop :=
  (∀ k x, Unproc start LEN cur k → w.val[k]? = some x → x.val < Bin) ∧
  (∀ k x, Proc start LEN cur k → w.val[k]? = some x → x.val < Bout) ∧
  (∀ k, ¬ (start ≤ k ∧ k < start + 2 * LEN) → w.val[k]? = w0.val[k]?)

theorem get?_set (w : Array U32 256#usize) (i : Usize) (x : U32) (k : Nat) (hi : i.val < 256) :
    (w.set i x).val[k]? = if i.val = k then some x else w.val[k]? := by
  rw [Array.set_val_eq, List.getElem?_set]
  have hl := len256 w
  by_cases h : i.val = k
  · subst h; simp [hl, hi]
  · simp [h]

theorem lazy_read {start LEN cur Bin Bout : Nat} {w0 w : Array U32 256#usize}
    (hinv : LazyInv start LEN cur Bin Bout w0 w) {k : Nat} (hk : Unproc start LEN cur k)
    (hl : k < w.val.length) : (w.val[k]).val < Bin :=
  hinv.1 k _ hk (List.getElem?_eq_getElem hl)

theorem lazy_inv_step {start LEN j Bin Bout : Nat} {w0 w : Array U32 256#usize} (i1 jj : Usize) (i5 i6 : U32)
    (hinv : LazyInv start LEN j Bin Bout w0 w) (hLEN : 0 < LEN) (hs : start ≤ j) (hj : j < start + LEN)
    (hfit : start + 2 * LEN ≤ 256) (hi1 : i1.val = j + LEN) (hjj : jj.val = j)
    (h5 : i5.val < Bout) (h6 : i6.val < Bout) :
    LazyInv start LEN (j + 1) Bin Bout w0 ((w.set i1 i5).set jj i6) := by
  have e1 : i1.val < 256 := by omega
  have e2 : jj.val < 256 := by omega
  obtain ⟨hu, hp, ho⟩ := hinv
  have key : ∀ k, ((w.set i1 i5).set jj i6).val[k]? =
      if jj.val = k then some i6 else if i1.val = k then some i5 else w.val[k]? := by
    intro k
    rw [get?_set _ _ _ _ e2, get?_set _ _ _ _ e1]
  refine ⟨?_, ?_, ?_⟩
  · intro k x hk hkx
    rw [key] at hkx
    simp only [Unproc] at hk
    rw [if_neg (by omega), if_neg (by omega)] at hkx
    exact hu k x (by simp only [Unproc]; omega) hkx
  · intro k x hk hkx
    rw [key] at hkx
    simp only [Proc] at hk
    by_cases h1 : jj.val = k
    · rw [if_pos h1] at hkx; cases hkx; exact h6
    · rw [if_neg h1] at hkx
      by_cases h2 : i1.val = k
      · rw [if_pos h2] at hkx; cases hkx; exact h5
      · rw [if_neg h2] at hkx
        exact hp k x (by simp only [Proc]; omega) hkx
  · intro k hk
    rw [key, if_neg (by omega), if_neg (by omega)]
    exact ho k hk

theorem lazy_inner_loop (LEN start : Usize) (z zp : U32)
    (hzp : zp.val = z.val * 4294967296 / 8380417) (hLEN : 0 < LEN.val)
    (hfit : start.val + 2 * LEN.val ≤ 256) (Bin : Nat) (hB : Bin + 2 * 8380417 ≤ 4294967296)
    (w0 : Array U32 256#usize)
    (hw0 : ∀ k x, start.val ≤ k → k < start.val + 2 * LEN.val → w0.val[k]? = some x → x.val < Bin) :
    verify_arith.ntt_lazy_layer_loop0_loop0 LEN w0 start z zp start ⦃ w =>
      (∀ k x, start.val ≤ k → k < start.val + 2 * LEN.val → w.val[k]? = some x →
        x.val < Bin + 2 * 8380417) ∧
      (∀ k, ¬ (start.val ≤ k ∧ k < start.val + 2 * LEN.val) → w.val[k]? = w0.val[k]?) ∧
      toZq w = (List.range' start.val LEN.val).foldl (bfly LEN.val (z.val : Zq)) (toZq w0) ⦄ := by
  unfold verify_arith.ntt_lazy_layer_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => start.val + LEN.val - p.2.val)
    (fun p => LazyInv start.val LEN.val p.2.val Bin (Bin + 2 * 8380417) w0 p.1 ∧
       start.val ≤ p.2.val ∧ p.2.val ≤ start.val + LEN.val ∧
       toZq p.1 = (List.range' start.val (p.2.val - start.val)).foldl
         (bfly LEN.val (z.val : Zq)) (toZq w0))
  · rintro ⟨w, j⟩ ⟨hinv, h1, h2, h3⟩
    dsimp only at hinv h1 h2 h3
    simp only [verify_arith.ntt_lazy_layer_loop0_loop0.body, Q_eq]
    step*
    all_goals try subst_vars
    · have hjlt : j.val < start.val + LEN.val := by scalar_tac
      have hl : w.val.length = 256 := len256 w
      have hjl : j.val < w.val.length := by omega
      have hi1l : i1.val < w.val.length := by omega
      have hA : (w.val[j.val]).val < Bin :=
        hinv.1 _ _ (Or.inl ⟨le_refl _, hjlt⟩) (List.getElem?_eq_getElem hjl)
      have hX : (w.val[i1.val]).val < Bin :=
        hinv.1 i1.val _ (Or.inr ⟨by omega, by omega⟩) (List.getElem?_eq_getElem hi1l)
      have e4 : (core.num.U32.wrapping_add w.val[j.val] i3).val = (w.val[j.val]).val + 2 * 8380417 := by
        rw [wrapping_add_val_u32, i3_post]; exact Nat.mod_eq_of_lt (by omega)
      have e5 : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add w.val[j.val] i3) t).val =
          (w.val[j.val]).val + 2 * 8380417 - t.val := by
        rw [wrapping_sub_val_u32, e4]; omega
      have e6 : (core.num.U32.wrapping_add w.val[j.val] t).val = (w.val[j.val]).val + t.val := by
        rw [wrapping_add_val_u32]; exact Nat.mod_eq_of_lt (by omega)
      have hq : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
      rw [j1_post]
      refine ⟨lazy_inv_step i1 j _ _ hinv hLEN h1 hjlt hfit i1_post rfl (by rw [e5]; omega)
        (by rw [e6]; omega), by omega, by omega, ?_, by omega⟩
      have h4 : ((((core.num.U32.wrapping_sub (core.num.U32.wrapping_add w.val[j.val] i3) t).val : Nat)) : Zq) =
          ((w.val[j.val]).val : Nat) - (t.val : Nat) := by
        rw [e5, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul]
        simp
      have h6 : (((core.num.U32.wrapping_add w.val[j.val] t).val : Nat) : Zq) =
          (((w.set i1 (core.num.U32.wrapping_sub (core.num.U32.wrapping_add w.val[j.val] i3) t)).val[j.val]'(by rw [len256]; omega)).val : Nat)
            + (t.val : Nat) := by
        rw [e6, Nat.cast_add]
        have hne : i1.val ≠ j.val := by omega
        simp [Array.set_val_eq, List.getElem_set_ne hne]
      have hb := toZq_bfly w LEN.val z j i1 t _ _ hLEN (by omega) i1_post hi1l hjl
        (by rw [len256]; omega)
        t_post2 h4 h6
      rw [hb, h3, show j.val + 1 - start.val = (j.val - start.val) + 1 by omega, List.range'_concat,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        show start.val + 1 * (j.val - start.val) = j.val by omega]
    · have hjge : start.val + LEN.val ≤ j.val := by scalar_tac
      have hj : j.val = start.val + LEN.val := by omega
      obtain ⟨_, hp, ho⟩ := hinv
      refine ⟨?_, ho, ?_⟩
      · intro k x hk1 hk2 hkx
        exact hp k x (by simp only [Proc]; omega) hkx
      · rw [h3, hj, Nat.add_sub_cancel_left]
  · refine ⟨⟨?_, ?_, ?_⟩, le_refl _, by simp, by simp⟩
    · intro k x hk hkx
      have : Unproc start.val LEN.val start.val k → start.val ≤ k ∧ k < start.val + 2 * LEN.val := by
        intro h; simp only [Unproc] at h; omega
      exact hw0 k x (this hk).1 (this hk).2 hkx
    · intro k x hk; simp only [Proc] at hk; omega
    · intro k _; rfl

/-! ## The block loop -/

/-- Blocks `0 … i-1` of the layer are done (below `Bin + 2q`), the others are untouched (below `Bin`). -/
def OutInv (LEN i Bin : Nat) (w : Array U32 256#usize) : Prop :=
  ∀ k x, w.val[k]? = some x → x.val < (if k < 2 * LEN * i then Bin + 2 * 8380417 else Bin)

theorem outer_lazy_loop (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (Bin : Nat) (hB : Bin + 2 * 8380417 ≤ 4294967296)
    (w0 : Array U32 256#usize) (hw0 : LazyBounded Bin w0) (m0 : Usize) (hm : m0.val + ITER.val < 256) :
    verify_arith.ntt_lazy_layer_loop0 LEN ITER w0 m0 0#usize ⦃ r =>
      LazyBounded (Bin + 2 * 8380417) r.1 ∧ r.2.val = m0.val + ITER.val ∧
      toZq r.1 = (blockFold LEN.val m0.val (toZq w0) ITER.val).snd.snd ⦄ := by
  unfold verify_arith.ntt_lazy_layer_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize × Usize) => ITER.val - p.2.2.val)
    (fun p => OutInv LEN.val p.2.2.val Bin p.1 ∧ p.2.2.val ≤ ITER.val ∧ p.2.1.val = m0.val + p.2.2.val ∧
       toZq p.1 = (blockFold LEN.val m0.val (toZq w0) p.2.2.val).snd.snd)
  · rintro ⟨w, m, i⟩ ⟨hc, h1, h2, h3⟩
    dsimp only at hc h1 h2 h3
    simp only [verify_arith.ntt_lazy_layer_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < ITER.val := hi
      have hbound : 2 * LEN.val * (i.val + 1) ≤ 256 := by
        have := Nat.mul_le_mul_left LEN.val (show i.val + 1 ≤ ITER.val by omega)
        nlinarith
      have hbound2 : (i.val * 2) * LEN.val ≤ 256 := by nlinarith
      step*
      · rw [i1_post]; scalar_tac
      rw [z_post2, zp_post2]
      have hm1 : m1.val < 256 := by omega
      obtain ⟨_, hzeta⟩ := zetas_get m1 hm1 ‹_› _ rfl
      have hzp := zetas_shoup_get m1 hm1 ‹_› ‹_› _ _ rfl rfl
      have eA : 2 * LEN.val * i.val = start.val := by rw [start_post, i1_post]; ring
      have eB : 2 * LEN.val * (i.val + 1) = start.val + 2 * LEN.val := by rw [← eA]; ring
      have hfit : start.val + 2 * LEN.val ≤ 256 := by omega
      step with lazy_inner_loop LEN start _ _ hzp hLEN hfit Bin hB w (by
        intro k x hk1 hk2 hkx
        have := hc k x hkx
        rwa [if_neg (by omega)] at this) as ⟨w1, hb1, ho1, ht1⟩
      step*
      refine ⟨?_, by omega, by omega, ?_, by omega⟩
      · intro k x hkx
        rw [i2_post, eB]
        by_cases hk : start.val ≤ k ∧ k < start.val + 2 * LEN.val
        · rw [if_pos (by omega)]; exact hb1 k x hk.1 hk.2 hkx
        · rw [ho1 k hk] at hkx
          have := hc k x hkx
          rw [eA] at this
          by_cases c1 : k < start.val
          · rw [if_pos c1] at this; rw [if_pos (by omega)]; exact this
          · rw [if_neg c1] at this; rw [if_neg (by omega)]; exact this
      · have e1 : m1.val = m0.val + i.val + 1 := by omega
        rw [ht1, hzeta, h3, i2_post, blockFold_succ, e1, ← eA]
        simp [blockF, blockFold_fst, blockFold_start]
    · rename_i hi
      have hi' : i.val = ITER.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, by omega, by rw [h3, hi']⟩
      intro x hx
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      have := hc k x hk
      rw [hi', mul_assoc, hprod, if_pos (by have := len256 w; omega)] at this
      exact this
  · refine ⟨?_, by simp, by simp, ?_⟩
    · intro k x hk
      rw [if_neg (by simp)]
      exact hw0 x (List.mem_iff_getElem?.mpr ⟨k, hk⟩)
    · simp [blockFold_zero]

@[step]
theorem lazy_layer_spec (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (w : Array U32 256#usize) (Bin : Nat) (hw : LazyBounded Bin w) (hB : Bin + 2 * 8380417 ≤ 4294967296)
    (m : Usize) (hm : m.val + ITER.val < 256) :
    verify_arith.ntt_lazy_layer LEN ITER w m ⦃ r => LazyBounded (Bin + 2 * 8380417) r.1 ∧
      r.2.val = m.val + ITER.val ∧ (toZq r.1, r.2.val) = nttLayer LEN.val (toZq w) m.val ⦄ := by
  unfold verify_arith.ntt_lazy_layer
  apply WP.spec_mono (outer_lazy_loop LEN ITER hLEN hprod Bin hB w hw m hm)
  rintro ⟨w', m'⟩ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  have hdiv : 256 / (2 * LEN.val) = ITER.val := by
    apply Nat.div_eq_of_eq_mul_right (by omega)
    nlinarith
  rw [nttLayer_eq, hdiv]
  simp only at h2 h3 ⊢
  rw [h3, h2, blockFold_fst]

/-! ## The final reduction -/

theorem reduce_lazy_spec (x : U32) :
    verify_arith.reduce_lazy x ⦃ y => y.val = x.val % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hx := x.hBounds
  unfold verify_arith.reduce_lazy
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_sub_val_u32, wrapping_mul_val_u32,
    Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U32.numBits, UScalarTy.numBits] at *
  · have hI : i.val ≤ 511 := by omega
    have hm : i.val * 8380417 % 4294967296 = i.val * 8380417 := Nat.mod_eq_of_lt (by omega)
    have e : 4294967296 - i.val * 8380417 + x.val = (x.val - i.val * 8380417) + 4294967296 := by omega
    rw [hm, e, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show x.val - i.val * 8380417 < 4294967296 by omega)]
    omega
  · have hI : i.val ≤ 511 := by omega
    have hm : i.val * 8380417 % 4294967296 = i.val * 8380417 := Nat.mod_eq_of_lt (by omega)
    have e : 4294967296 - i.val * 8380417 + x.val = (x.val - i.val * 8380417) + 4294967296 := by omega
    rw [hm, e, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show x.val - i.val * 8380417 < 4294967296 by omega)] at y_post1
    refine ⟨?_, y_post2⟩
    omega

attribute [step] reduce_lazy_spec

theorem toZq_set_same (w : Array U32 256#usize) (j : Usize) (y : U32) (hj : j.val < 256)
    (h : ((y.val : Nat) : Zq) = (((w.val[j.val]'(by rw [len256 w]; exact hj)).val : Nat) : Zq)) :
    toZq (w.set j y) = toZq w := by
  rw [toZq_set _ _ _ hj]
  apply Vector.ext
  intro k hk
  rw [set!_eq, Vector.getElem_setIfInBounds hk]
  split
  · rename_i hjk
    subst hjk
    rw [h, toZq_get w j.val hj]
  · rfl

theorem reduce_loop (w0 : Array U32 256#usize) :
    verify_arith.ntt_pub_in_place_loop w0 0#usize ⦃ r => Canonical r ∧ toZq r = toZq w0 ⦄ := by
  unfold verify_arith.ntt_pub_in_place_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ k x, k < p.2.val → p.1.val[k]? = some x → x.val < 8380417) ∧
       toZq p.1 = toZq w0)
  · rintro ⟨w, j⟩ ⟨h1, hc, h3⟩
    dsimp only at h1 hc h3
    simp only [verify_arith.ntt_pub_in_place_loop.body]
    split
    · rename_i hi
      have hj : j.val < 256 := by scalar_tac
      step*
      subst i_post2
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro k x hk hkx
        rw [a_post, get?_set _ _ _ _ hj] at hkx
        by_cases hkj : j.val = k
        · rw [if_pos hkj] at hkx; cases hkx; exact i1_post2
        · rw [if_neg hkj] at hkx; exact hc k x (by omega) hkx
      · rw [a_post, toZq_set_same w j _ hj, h3]
        rw [i1_post1, ZMod.natCast_mod]
    · rename_i hi
      have hj : j.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, h3⟩
      intro x hx
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      rw [len256 w] at hkl
      exact hc k x (by omega) hk
  · refine ⟨by simp, by intro k x hk; simp at hk, rfl⟩

/-- `ntt_pub_in_place` is `Spec.NTT` on canonical input, with canonical output. -/
theorem ntt_pub_in_place_spec (w : Array U32 256#usize) (hw : Canonical w) :
    verify_arith.ntt_pub_in_place w ⦃ r => Canonical r ∧ toZq r = Spec.NTT (toZq w) ⦄ := by
  have hw0 : LazyBounded 8380417 w := hw
  unfold verify_arith.ntt_pub_in_place
  step with lazy_layer_spec 128#usize 1#usize (by scalar_tac) (by scalar_tac) w _ hw0 (by norm_num) 0#usize (by simp)
  step with lazy_layer_spec 64#usize 2#usize (by scalar_tac) (by scalar_tac) w1 _ w1_post1 (by norm_num) m (by scalar_tac)
  step with lazy_layer_spec 32#usize 4#usize (by scalar_tac) (by scalar_tac) w2 _ w2_post1 (by norm_num) m1 (by scalar_tac)
  step with lazy_layer_spec 16#usize 8#usize (by scalar_tac) (by scalar_tac) w3 _ w3_post1 (by norm_num) m2 (by scalar_tac)
  step with lazy_layer_spec 8#usize 16#usize (by scalar_tac) (by scalar_tac) w4 _ w4_post1 (by norm_num) m3 (by scalar_tac)
  step with lazy_layer_spec 4#usize 32#usize (by scalar_tac) (by scalar_tac) w5 _ w5_post1 (by norm_num) m4 (by scalar_tac)
  step with lazy_layer_spec 2#usize 64#usize (by scalar_tac) (by scalar_tac) w6 _ w6_post1 (by norm_num) m5 (by scalar_tac)
  step with lazy_layer_spec 1#usize 128#usize (by scalar_tac) (by scalar_tac) w7 _ w7_post1 (by norm_num) m6 (by scalar_tac)
  apply WP.spec_mono (reduce_loop w8)
  rintro r ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rw [h2]
  simp only [NTT_eq_layers, ← w1_post3, ← w2_post3, ← w3_post3, ← w4_post3, ← w5_post3,
    ← w6_post3, ← w7_post3, ← w8_post3]

@[step]
theorem ntt_pub_spec (w : Array U32 256#usize) (hw : Canonical w) :
    verify_arith.ntt_pub w ⦃ r => Canonical r ∧ toZq r = Spec.NTT (toZq w) ⦄ := by
  unfold verify_arith.ntt_pub
  exact ntt_pub_in_place_spec w hw

theorem ntt_vec_pub_loop_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    verify_arith.ntt_vec_pub_loop v (Array.repeat N (Array.repeat 256#usize 0#u32)) 0#usize ⦃ r =>
      ReprVec r ((List.range' 0 k).foldl (nttVecF V) (Vector.replicate k Poly.zero)) ⦄ := by
  have hN : N.val = k := hv.len
  unfold verify_arith.ntt_vec_pub_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) N × Usize) => N.val - p.2.val)
    (fun p => p.2.val ≤ N.val ∧
       ReprVec p.1 ((List.range' 0 p.2.val).foldl (nttVecF V) (Vector.replicate k Poly.zero)))
  · rintro ⟨out, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [verify_arith.ntt_vec_pub_loop.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < k := by omega
      step with hv.index_spec i hik as ⟨a, ha⟩
      step with ntt_pub_spec a ha.canon as ⟨a1, ha1, ha2⟩
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
theorem ntt_vec_pub_spec {N : Usize} {k : Nat} (v : Array (Array U32 256#usize) N) (V : Vector Poly k)
    (hv : ReprVec v V) :
    verify_arith.ntt_vec_pub v ⦃ r => ReprVec r (Spec.NTTVec V) ⦄ := by
  unfold verify_arith.ntt_vec_pub
  apply WP.spec_mono (ntt_vec_pub_loop_spec v V hv)
  intro r hr
  rwa [NTTVec_eq]

/-! ## The inverse layer -/

theorem lazy_inv_step2 {start LEN j Bin Bout : Nat} {w0 w : Array U32 256#usize} (ja jb : Usize) (x y : U32)
    (hinv : LazyInv start LEN j Bin Bout w0 w) (hLEN : 0 < LEN) (hs : start ≤ j) (hj : j < start + LEN)
    (hfit : start + 2 * LEN ≤ 256) (hja : ja.val = j) (hjb : jb.val = j + LEN)
    (hx : x.val < Bout) (hy : y.val < Bout) :
    LazyInv start LEN (j + 1) Bin Bout w0 ((w.set ja x).set jb y) := by
  have e1 : ja.val < 256 := by omega
  have e2 : jb.val < 256 := by omega
  obtain ⟨hu, hp, ho⟩ := hinv
  have key : ∀ k, ((w.set ja x).set jb y).val[k]? =
      if jb.val = k then some y else if ja.val = k then some x else w.val[k]? := by
    intro k
    rw [get?_set _ _ _ _ e2, get?_set _ _ _ _ e1]
  refine ⟨?_, ?_, ?_⟩
  · intro k x' hk hkx
    rw [key] at hkx
    simp only [Unproc] at hk
    rw [if_neg (by omega), if_neg (by omega)] at hkx
    exact hu k x' (by simp only [Unproc]; omega) hkx
  · intro k x' hk hkx
    rw [key] at hkx
    simp only [Proc] at hk
    by_cases h1 : jb.val = k
    · rw [if_pos h1] at hkx; cases hkx; exact hy
    · rw [if_neg h1] at hkx
      by_cases h2 : ja.val = k
      · rw [if_pos h2] at hkx; cases hkx; exact hx
      · rw [if_neg h2] at hkx
        exact hp k x' (by simp only [Proc]; omega) hkx
  · intro k hk
    rw [key, if_neg (by omega), if_neg (by omega)]
    exact ho k hk

theorem lazy_inv_inner_loop (LEN start : Usize) (b z zp : U32)
    (hzp : zp.val = z.val * 4294967296 / 8380417) (hLEN : 0 < LEN.val)
    (hfit : start.val + 2 * LEN.val ≤ 256) (hb0 : ((b.val : Nat) : Zq) = 0)
    (hbq : 8380417 ≤ b.val) (hbB : 2 * b.val ≤ 4294967296)
    (w0 : Array U32 256#usize)
    (hw0 : ∀ k x, start.val ≤ k → k < start.val + 2 * LEN.val → w0.val[k]? = some x → x.val < b.val) :
    verify_arith.ntt_inverse_lazy_layer_loop0_loop0 LEN w0 b start z zp start ⦃ w =>
      (∀ k x, start.val ≤ k → k < start.val + 2 * LEN.val → w.val[k]? = some x → x.val < 2 * b.val) ∧
      (∀ k, ¬ (start.val ≤ k ∧ k < start.val + 2 * LEN.val) → w.val[k]? = w0.val[k]?) ∧
      toZq w = (List.range' start.val LEN.val).foldl (ibfly LEN.val (z.val : Zq)) (toZq w0) ⦄ := by
  unfold verify_arith.ntt_inverse_lazy_layer_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => start.val + LEN.val - p.2.val)
    (fun p => LazyInv start.val LEN.val p.2.val b.val (2 * b.val) w0 p.1 ∧
       start.val ≤ p.2.val ∧ p.2.val ≤ start.val + LEN.val ∧
       toZq p.1 = (List.range' start.val (p.2.val - start.val)).foldl
         (ibfly LEN.val (z.val : Zq)) (toZq w0))
  · rintro ⟨w, j⟩ ⟨hinv, h1, h2, h3⟩
    dsimp only at hinv h1 h2 h3
    simp only [verify_arith.ntt_inverse_lazy_layer_loop0_loop0.body]
    step*
    all_goals try subst_vars
    · have hjlt : j.val < start.val + LEN.val := by scalar_tac
      have hl : w.val.length = 256 := len256 w
      have hjl : j.val < w.val.length := by omega
      have hi1l : i1.val < w.val.length := by omega
      have hT : (w.val[j.val]).val < b.val :=
        hinv.1 _ _ (Or.inl ⟨le_refl _, hjlt⟩) (List.getElem?_eq_getElem hjl)
      have hU : (w.val[i1.val]).val < b.val :=
        hinv.1 i1.val _ (Or.inr ⟨by omega, by omega⟩) (List.getElem?_eq_getElem hi1l)
      have e2 : (core.num.U32.wrapping_add w.val[j.val] w.val[i1.val]).val =
          (w.val[j.val]).val + (w.val[i1.val]).val := by
        rw [wrapping_add_val_u32]; exact Nat.mod_eq_of_lt (by omega)
      have e3 : (core.num.U32.wrapping_add w.val[j.val] b).val = (w.val[j.val]).val + b.val := by
        rw [wrapping_add_val_u32]; exact Nat.mod_eq_of_lt (by omega)
      have e4 : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add w.val[j.val] b) w.val[i1.val]).val =
          (w.val[j.val]).val + b.val - (w.val[i1.val]).val := by
        rw [wrapping_sub_val_u32, e3]; omega
      have hne : j.val ≠ i1.val := by omega
      have h3' : (((core.num.U32.wrapping_add w.val[j.val] w.val[i1.val]).val : Nat) : Zq) =
          ((w.val[j.val]).val : Nat) + ((w.val[i1.val]).val : Nat) := by rw [e2, Nat.cast_add]
      have h4' : i1.val < (w.set j (core.num.U32.wrapping_add w.val[j.val] w.val[i1.val])).val.length := by
        rw [len256]; omega
      have h5' : (((core.num.U32.wrapping_sub (core.num.U32.wrapping_add w.val[j.val] b) w.val[i1.val]).val
            : Nat) : Zq) = ((w.val[j.val]).val : Nat) -
          (((w.set j (core.num.U32.wrapping_add w.val[j.val] w.val[i1.val])).val[i1.val]'h4').val : Nat) := by
        have hset : (w.set j (core.num.U32.wrapping_add w.val[j.val] w.val[i1.val])).val[i1.val]'h4' =
            w.val[i1.val] := by
          simp [Array.set_val_eq, List.getElem_set_ne hne]
        rw [hset, e4, Nat.cast_sub (by omega), Nat.cast_add, hb0]
        simp
      have hb := toZq_ibfly w LEN.val (z.val : Zq) j i1 _ _ i5 hLEN (by omega) i1_post hi1l hjl
        h3' h4' h5' i5_post2
      rw [j1_post]
      refine ⟨lazy_inv_step2 j i1 _ _ hinv hLEN h1 hjlt hfit rfl i1_post (by rw [e2]; omega)
        (by omega), by omega, by omega, ?_, by omega⟩
      rw [hb, h3, show j.val + 1 - start.val = (j.val - start.val) + 1 by omega, List.range'_concat,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        show start.val + 1 * (j.val - start.val) = j.val by omega]
    · have hjge : start.val + LEN.val ≤ j.val := by scalar_tac
      have hj : j.val = start.val + LEN.val := by omega
      obtain ⟨_, hp, ho⟩ := hinv
      refine ⟨?_, ho, ?_⟩
      · intro k x hk1 hk2 hkx
        exact hp k x (by simp only [Proc]; omega) hkx
      · rw [h3, hj, Nat.add_sub_cancel_left]
  · refine ⟨⟨?_, ?_, ?_⟩, le_refl _, by simp, by simp⟩
    · intro k x hk hkx
      have : Unproc start.val LEN.val start.val k → start.val ≤ k ∧ k < start.val + 2 * LEN.val := by
        intro h; simp only [Unproc] at h; omega
      exact hw0 k x (this hk).1 (this hk).2 hkx
    · intro k x hk; simp only [Proc] at hk; omega
    · intro k _; rfl

theorem zeta_neg_data (k : Usize) (hk : k.val < 256) (hlt : k.val < ntt.ZETAS.val.length)
    (hlt2 : k.val < ntt.ZETAS_NEG_SHOUP.val.length) :
    (ntt.ZETAS_NEG_SHOUP.val[k.val]).val =
      (core.num.U32.wrapping_sub 8380417#u32 ntt.ZETAS.val[k.val]).val * 4294967296 / 8380417 ∧
    ((((core.num.U32.wrapping_sub 8380417#u32 ntt.ZETAS.val[k.val]).val : Nat)) : Zq) = -zeta k.val := by
  obtain ⟨hzlt, hzeta⟩ := zetas_get k hk hlt _ rfl
  have h := (shoup_tables ⟨k.val, hk⟩).2.2
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    List.getElem?_eq_getElem hlt2, Option.getD_some] at h
  have hq : (8380417#u32).val = 8380417 := rfl
  have hqq : Spec.q = 8380417 := rfl
  have hv : (core.num.U32.wrapping_sub 8380417#u32 ntt.ZETAS.val[k.val]).val =
      8380417 - (ntt.ZETAS.val[k.val]).val := by
    rw [wrapping_sub_val_u32, hq]; omega
  have hq0 : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
  refine ⟨?_, ?_⟩
  · rw [hv]; exact h
  · rw [hv, Nat.cast_sub (by omega), hzeta, hq0]; simp

def OutInvG (LEN i Bin Bout : Nat) (w : Array U32 256#usize) : Prop :=
  ∀ k x, w.val[k]? = some x → x.val < (if k < 2 * LEN * i then Bout else Bin)

theorem outer_lazy_inv_loop (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (b : U32) (hb0 : ((b.val : Nat) : Zq) = 0) (hbq : 8380417 ≤ b.val) (hbB : 2 * b.val ≤ 4294967296)
    (w0 : Array U32 256#usize) (hw0 : LazyBounded b.val w0) (m0 : Usize)
    (hm : ITER.val ≤ m0.val) (hm' : m0.val ≤ 256) :
    verify_arith.ntt_inverse_lazy_layer_loop0 LEN ITER w0 m0 b 0#usize ⦃ r =>
      LazyBounded (2 * b.val) r.1 ∧ r.2.val = m0.val - ITER.val ∧
      toZq r.1 = (blockFoldInv LEN.val m0.val (toZq w0) ITER.val).snd.snd ⦄ := by
  unfold verify_arith.ntt_inverse_lazy_layer_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize × Usize) => ITER.val - p.2.2.val)
    (fun p => OutInvG LEN.val p.2.2.val b.val (2 * b.val) p.1 ∧ p.2.2.val ≤ ITER.val ∧
       p.2.1.val = m0.val - p.2.2.val ∧
       toZq p.1 = (blockFoldInv LEN.val m0.val (toZq w0) p.2.2.val).snd.snd)
  · rintro ⟨w, m, i⟩ ⟨hc, h1, h2, h3⟩
    dsimp only at hc h1 h2 h3
    simp only [verify_arith.ntt_inverse_lazy_layer_loop0.body, Q_eq]
    split
    · rename_i hi
      have hi' : i.val < ITER.val := hi
      have hbound : 2 * LEN.val * (i.val + 1) ≤ 256 := by
        have := Nat.mul_le_mul_left LEN.val (show i.val + 1 ≤ ITER.val by omega)
        nlinarith
      have hbound2 : (i.val * 2) * LEN.val ≤ 256 := by nlinarith
      step*
      · rw [i1_post]; scalar_tac
      rw [z_post, i2_post2, zp_post2]
      have hm1 : m1.val < 256 := by omega
      obtain ⟨hzp, hzc⟩ := zeta_neg_data m1 hm1 ‹_› ‹_›
      have eA : 2 * LEN.val * i.val = start.val := by rw [start_post, i1_post]; ring
      have eB : 2 * LEN.val * (i.val + 1) = start.val + 2 * LEN.val := by rw [← eA]; ring
      have hfit : start.val + 2 * LEN.val ≤ 256 := by omega
      step with lazy_inv_inner_loop LEN start b _ _ hzp hLEN hfit hb0 hbq hbB w (by
        intro k x hk1 hk2 hkx
        have := hc k x hkx
        rwa [if_neg (by omega)] at this) as ⟨w1, hb1, ho1, ht1⟩
      step*
      refine ⟨?_, by omega, by omega, ?_, by omega⟩
      · intro k x hkx
        rw [i3_post, eB]
        by_cases hk : start.val ≤ k ∧ k < start.val + 2 * LEN.val
        · rw [if_pos (by omega)]; exact hb1 k x hk.1 hk.2 hkx
        · rw [ho1 k hk] at hkx
          have := hc k x hkx
          rw [eA] at this
          by_cases c1 : k < start.val
          · rw [if_pos c1] at this; rw [if_pos (by omega)]; exact this
          · rw [if_neg c1] at this; rw [if_neg (by omega)]; exact this
      · have e1 : m1.val = m0.val - i.val - 1 := by omega
        rw [ht1, hzc, h3, i3_post, blockFoldInv_succ, e1, ← eA]
        simp [blockFInv, blockFoldInv_fst, blockFoldInv_start]
    · rename_i hi
      have hi' : i.val = ITER.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, by omega, by rw [h3, hi']⟩
      intro x hx
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      have := hc k x hk
      rw [hi', mul_assoc, hprod, if_pos (by have := len256 w; omega)] at this
      exact this
  · refine ⟨?_, by simp, by simp, ?_⟩
    · intro k x hk
      rw [if_neg (by simp)]
      exact hw0 x (List.mem_iff_getElem?.mpr ⟨k, hk⟩)
    · simp [blockFoldInv_zero]

theorem lazy_inv_layer_spec (LEN ITER : Usize) (hLEN : 0 < LEN.val) (hprod : LEN.val * ITER.val = 128)
    (w : Array U32 256#usize) (b : U32) (hw : LazyBounded b.val w) (hb0 : ((b.val : Nat) : Zq) = 0)
    (hbq : 8380417 ≤ b.val) (hbB : 2 * b.val ≤ 4294967296) (m : Usize)
    (hm : ITER.val ≤ m.val) (hm' : m.val ≤ 256) :
    verify_arith.ntt_inverse_lazy_layer LEN ITER w m b ⦃ r => LazyBounded (2 * b.val) r.1 ∧
      r.2.val = m.val - ITER.val ∧ (toZq r.1, r.2.val) = nttInvLayer LEN.val (toZq w) m.val ⦄ := by
  unfold verify_arith.ntt_inverse_lazy_layer
  apply WP.spec_mono (outer_lazy_inv_loop LEN ITER hLEN hprod b hb0 hbq hbB w hw m hm hm')
  rintro ⟨w', m'⟩ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  have hdiv : 256 / (2 * LEN.val) = ITER.val := by
    apply Nat.div_eq_of_eq_mul_right (by omega)
    nlinarith
  rw [nttInvLayer_eq, hdiv]
  simp only at h2 h3 ⊢
  rw [h3, h2, blockFoldInv_fst]

/-! ## The scaling pass and the whole inverse -/

theorem scale_pub_loop (w0 : Array U32 256#usize) :
    verify_arith.ntt_inverse_pub_in_place_loop w0 0#usize ⦃ w => Canonical w ∧
      toZq w = (List.range' 0 256).foldl scaleF (toZq w0) ⦄ := by
  unfold verify_arith.ntt_inverse_pub_in_place_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ k x, k < p.2.val → p.1.val[k]? = some x → x.val < 8380417) ∧
       toZq p.1 = (List.range' 0 p.2.val).foldl scaleF (toZq w0))
  · rintro ⟨w, j⟩ ⟨h1, hc, h2⟩
    dsimp only at h1 hc h2
    simp only [verify_arith.ntt_inverse_pub_in_place_loop.body]
    split
    · rename_i hi
      have hj : j.val < 256 := by scalar_tac
      step*
      all_goals try subst_vars
      all_goals try first
        | exact f_shoup_eq
        | scalar_tac
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro k x hk hkx
        rw [get?_set _ _ _ _ hj] at hkx
        by_cases hkj : j.val = k
        · rw [if_pos hkj] at hkx; cases hkx; exact i1_post1
        · rw [if_neg hkj] at hkx; exact hc k x (by omega) hkx
      · have hW := toZq_getElem w j.val i
        rw [toZq_set _ _ _ hj, i1_post2, j1_post, List.range'_concat, List.foldl_append,
          List.foldl_cons, List.foldl_nil, ← h2, scaleF, zero_add, one_mul, hW]
        rfl
    · rename_i hi
      have hj : j.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, by rw [h2, hj]⟩
      intro x hx
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
      have hkl := (List.getElem?_eq_some_iff.mp hk).1
      rw [len256 w] at hkl
      exact hc k x (by omega) hk
  · refine ⟨by simp, by intro k x hk; simp at hk, rfl⟩

theorem cast_q_eq_zero (b : U32) (n : Nat) (h : b.val = n * 8380417) : ((b.val : Nat) : Zq) = 0 := by
  have hq0 : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
  rw [h, Nat.cast_mul, hq0, mul_zero]

/-- `ntt_inverse_pub_in_place` is `Spec.NTTInv` on canonical input, with canonical output. -/
theorem ntt_inverse_pub_in_place_spec (w : Array U32 256#usize) (hw : Canonical w) :
    verify_arith.ntt_inverse_pub_in_place w ⦃ r => Canonical r ∧ toZq r = Spec.NTTInv (toZq w) ⦄ := by
  have hw0 : LazyBounded 8380417 w := hw
  unfold verify_arith.ntt_inverse_pub_in_place
  simp only [Q_eq]
  step with lazy_inv_layer_spec 1#usize 128#usize (by scalar_tac) (by scalar_tac) w 8380417#u32 hw0 (cast_q_eq_zero _ 1 (by scalar_tac)) (by scalar_tac) (by scalar_tac) 256#usize (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 2#usize 64#usize (by scalar_tac) (by scalar_tac) w1 i (bounded_mono (by scalar_tac) w1_post1) (cast_q_eq_zero _ 2 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 4#usize 32#usize (by scalar_tac) (by scalar_tac) w2 i1 (bounded_mono (by scalar_tac) w2_post1) (cast_q_eq_zero _ 4 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m1 (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 8#usize 16#usize (by scalar_tac) (by scalar_tac) w3 i2 (bounded_mono (by scalar_tac) w3_post1) (cast_q_eq_zero _ 8 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m2 (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 16#usize 8#usize (by scalar_tac) (by scalar_tac) w4 i3 (bounded_mono (by scalar_tac) w4_post1) (cast_q_eq_zero _ 16 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m3 (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 32#usize 4#usize (by scalar_tac) (by scalar_tac) w5 i4 (bounded_mono (by scalar_tac) w5_post1) (cast_q_eq_zero _ 32 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m4 (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 64#usize 2#usize (by scalar_tac) (by scalar_tac) w6 i5 (bounded_mono (by scalar_tac) w6_post1) (cast_q_eq_zero _ 64 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m5 (by scalar_tac) (by scalar_tac)
  step
  step with lazy_inv_layer_spec 128#usize 1#usize (by scalar_tac) (by scalar_tac) w7 i6 (bounded_mono (by scalar_tac) w7_post1) (cast_q_eq_zero _ 128 (by scalar_tac)) (by scalar_tac) (by scalar_tac) m6 (by scalar_tac) (by scalar_tac)
  apply WP.spec_mono (scale_pub_loop w8)
  rintro r ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  rw [h2, NTTInv_eq_layers]
  simp only [← w1_post3, ← w2_post3, ← w3_post3, ← w4_post3, ← w5_post3,
    ← w6_post3, ← w7_post3, ← w8_post3]

@[step]
theorem ntt_inverse_pub_spec (w : Array U32 256#usize) (hw : Canonical w) :
    verify_arith.ntt_inverse_pub w ⦃ r => Canonical r ∧ toZq r = Spec.NTTInv (toZq w) ⦄ := by
  unfold verify_arith.ntt_inverse_pub
  exact ntt_inverse_pub_in_place_spec w hw

end Proofs
