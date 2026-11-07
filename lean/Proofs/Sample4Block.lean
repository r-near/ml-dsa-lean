import Proofs.Keccak4
import Proofs.PartialSample

/-!
# The branchless block parse of the 4-way sampler

`sampling.rate_bytes_x4`, `sampling.three_bytes_value`, `sampling.rej_ntt_block_x4`, `sampling.rej_ntt_lane_x4` and
`sampling.first_256` against the byte-wise sampler's pure fold `SampleA.stA`.

The lane's coefficients live in a 312-word scratch array `a` with fill count `j`. The block parse writes every
candidate to `a[j]` and advances `j` only when the candidate is `< q`, so words from index `min j 256` on are
unspecified (rejected candidates, and the 56 words of slack past 256). `LaneInv T n a j` says that after the first `n`
candidates of the stream `T` the first `(stA T n).2` words of `a` are the pure fold's coefficients and that
`min 256 j` is that count.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

/-! ## Candidate values -/

@[step]
theorem three_bytes_value_spec (b0 b1 b2 : U8) :
    sampling.three_bytes_value b0 b1 b2 ⦃ z =>
      z.val = 2 ^ 16 * (b2.val % 128) + 2 ^ 8 * b1.val + b0.val ⦄ := by
  unfold sampling.three_bytes_value
  simp only [global_simps, lift, bind_tc_ok]
  step*
  exact three_val b0 b1 b2 _ _ i1_post1 i3_post1

/-- The pure candidate of the stream triple at `n`, from the three bytes the Rust code read. -/
theorem triAt_of_bytes (T : List UInt8) (n : Nat) (b0 b1 b2 : U8) (z : U32)
    (h0 : (tripleAt T n)[0]! = UInt8.ofNat b0.val) (h1 : (tripleAt T n)[1]! = UInt8.ofNat b1.val)
    (h2 : (tripleAt T n)[2]! = UInt8.ofNat b2.val)
    (hz : z.val = 2 ^ 16 * (b2.val % 128) + 2 ^ 8 * b1.val + b0.val) :
    triAt T n = if z.val < Spec.q then some ((z.val : Nat) : Zq) else none := by
  have hb0 : b0.val < 256 := by scalar_tac
  have hb1 : b1.val < 256 := by scalar_tac
  have hb2 : b2.val < 256 := by scalar_tac
  unfold triAt
  rw [h0, h1, h2, CoeffFromThreeBytes_eq, t0 b0 hb0, t0 b1 hb1, t0 b2 hb2, ← hz]

/-! ## The lane invariant -/

/-- After the first `n` candidates of the stream `T`: the fill count `j` of the scratch `a` is the pure fold's count
(saturating at 256: `j` may run on past 256 inside a block) and the first `(stA T n).2` words are its coefficients. -/
def LaneInv (T : List UInt8) (n : Nat) (a : Array U32 312#usize) (j : Usize) : Prop :=
  j.val ≤ 311 ∧ min 256 j.val = (stA T n).2 ∧
    ∀ k, k < (stA T n).2 → (a.val[k]!).val < Spec.q ∧ (((a.val[k]!).val : Nat) : Zq) = (stA T n).1[k]!

theorem arr_get_set (a : Array U32 312#usize) (j : Usize) (z : U32) (hj : j.val < 312) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 312 := a.property
  by_cases hk : k < 312
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem vec_getElem!_set! (xs : Vector Zq 256) (i j : Nat) (x : Zq) (hj : j < 256) :
    (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  rw [set!_eq, getElem!_pos _ _ (by simpa using hj), Vector.getElem_setIfInBounds hj]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false]
    rw [getElem!_pos _ _ (by simpa using hj)]

/-- One candidate: write `z` at `a[j]` and advance `j` when `z < q`. -/
theorem laneInv_step (T : List UInt8) (n : Nat) (a a' : Array U32 312#usize) (j j' : Usize) (z : U32)
    (h : LaneInv T n a j) (hj : j.val ≤ 310)
    (htri : triAt T n = if z.val < Spec.q then some ((z.val : Nat) : Zq) else none)
    (ha' : a' = a.set j z) (hj' : j'.val = j.val + (if z.val < Spec.q then 1 else 0)) :
    LaneInv T (n + 1) a' j' := by
  obtain ⟨hj311, hmin, hk⟩ := h
  have hjl : j.val < 312 := by omega
  by_cases hq : z.val < Spec.q
  · rw [if_pos hq] at htri hj'
    by_cases hj256 : j.val < 256
    · have hs2 : (stA T n).2 = j.val := by omega
      have hst := stA_succ_some T n _ htri (by omega)
      have e1 : (stA T (n + 1)).2 = (stA T n).2 + 1 := by rw [hst]
      have e2 : ∀ k, k < 256 → (stA T (n + 1)).1[k]! = if (stA T n).2 = k then ((z.val : Nat) : Zq) else (stA T n).1[k]! := by
        intro k hk256
        rw [hst]
        exact vec_getElem!_set! _ _ _ _ hk256
      refine ⟨by omega, by omega, ?_⟩
      intro k hk'
      rw [e1] at hk'
      rw [e2 k (by omega), ha', arr_get_set a j z hjl k]
      by_cases hkj : k = j.val
      · subst hkj
        rw [if_pos rfl, if_pos hs2]
        exact ⟨hq, rfl⟩
      · have hne : ¬ j.val = k := fun h => hkj h.symm
        have hne2 : ¬ (stA T n).2 = k := by omega
        rw [if_neg hne, if_neg hne2]
        exact hk k (by omega)
    · have hs2 : (stA T n).2 = 256 := by omega
      have hst := stA_stable T n (n + 1) (by omega) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'
  · rw [if_neg hq] at htri hj'
    by_cases hj256 : j.val < 256
    · have hs2 : (stA T n).2 = j.val := by omega
      have hst := stA_succ_none T n htri (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'
    · have hs2 : (stA T n).2 = 256 := by omega
      have hst := stA_stable T n (n + 1) (by omega) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'

/-! ## The rate bytes of one lane -/

theorem arr_get_set_u8 (a : Array U8 168#usize) (j : Usize) (z : U8) (hj : j.val < 168) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 168 := a.property
  by_cases hk : k < 168
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

/-- The first `8 * k + b` bytes of `buf` are the rate bytes of state `i`. -/
def RateGood (st : St4) (i : Nat) (k b : Nat) (buf : Array U8 168#usize) : Prop :=
  ∀ p, p < 168 → (p / 8 < k ∨ (p / 8 = k ∧ p % 8 < b)) →
    UInt8.ofNat (buf.val[p]!).val = KM.sb (pj st i) p

theorem rate_inner_spec (st : St4) (si : Nat) (k : Usize) (w : U64) (hk : k.val < 21) (hi : si < 4)
    (hw : toU64 w = ln (at4 st k.val) si) (buf : Array U8 168#usize) (b : Usize) (hb : b.val ≤ 8)
    (h : RateGood st si k.val b.val buf) :
    sampling.rate_bytes_x4_loop0_loop0 buf k w b ⦃ r => RateGood st si (k.val + 1) 0 r ⦄ := by
  unfold sampling.rate_bytes_x4_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 168#usize × Usize) => 8 - p.2.val)
    (fun (p : Array U8 168#usize × Usize) => p.2.val ≤ 8 ∧ RateGood st si k.val p.2.val p.1)
  · rintro ⟨buf, b⟩ ⟨hb, hg⟩
    dsimp only at hb hg
    simp only [sampling.rate_bytes_x4_loop0_loop0.body]
    split
    · rename_i hlt
      have hb8 : b.val < 8 := by scalar_tac
      step*
      have hk25 : k.val < 25 := by omega
      have hbyte : UInt8.ofNat i4.val = KM.sb (pj st si) (8 * k.val + b.val) := by
        have h0 := read_byte w i1 i i4 b.val hb8 i_post i1_post1 i4_post
        rw [h0]
        unfold KM.sb
        have e1 : (8 * k.val + b.val) / 8 = k.val := by omega
        have e2 : (8 * k.val + b.val) % 8 = b.val := by omega
        rw [e1, e2, pj_getElem _ _ _ hk25, hw]
      refine ⟨by omega, ?_, by omega⟩
      intro p hp hcase
      have hi3 : i3.val < 168 := by omega
      rw [a_post, arr_get_set_u8 buf i3 i4 hi3 p]
      by_cases hpe : p = 8 * k.val + b.val
      · have : i3.val = p := by omega
        rw [if_pos this]
        rw [hpe]
        exact hbyte
      · have : ¬ i3.val = p := by omega
        rw [if_neg this]
        apply hg p hp
        omega
    · rename_i hge
      have : b.val = 8 := by scalar_tac
      simp only [WP.spec_ok]
      intro p hp hcase
      apply hg p hp
      omega
  · exact ⟨hb, h⟩

theorem rate_outer_spec (st : St4) (i : Usize) (hi : i.val < 4) (buf : Array U8 168#usize) (k : Usize)
    (hk : k.val ≤ 21) (h : RateGood st i.val k.val 0 buf) :
    sampling.rate_bytes_x4_loop0 st i buf k ⦃ r => RateGood st i.val 21 0 r ⦄ := by
  unfold sampling.rate_bytes_x4_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 168#usize × Usize) => 21 - p.2.val)
    (fun (p : Array U8 168#usize × Usize) => p.2.val ≤ 21 ∧ RateGood st i.val p.2.val 0 p.1)
  · rintro ⟨buf, k⟩ ⟨hk, hg⟩
    dsimp only at hk hg
    simp only [sampling.rate_bytes_x4_loop0.body]
    split
    · rename_i hlt
      have hk21 : k.val < 21 := by scalar_tac
      step*
      rename_i _ arr wv
      have e1 := ln_of_get arr i.val w wv w_post2
      have e2 : arr = at4 st k.val := at4_idx st k arr (by omega) a_post2
      rw [e2] at e1
      have hin := rate_inner_spec st i.val k wv hk21 hi e1 buf 0#usize (by simp) (by
        intro p hp hc
        have h0 : (0#usize).val = 0 := rfl
        apply hg p hp
        omega)
      step with hin
      step*
    · rename_i hge
      have : k.val = 21 := by scalar_tac
      simp only [WP.spec_ok]
      rw [this] at hg
      exact hg
  · exact ⟨hk, h⟩

theorem rate_bytes_x4_spec (st : St4) (i : Usize) (hi : i.val < 4) :
    sampling.rate_bytes_x4 st i ⦃ buf => ∀ p, p < 168 → UInt8.ofNat (buf.val[p]!).val = KM.sb (pj st i.val) p ⦄ := by
  unfold sampling.rate_bytes_x4
  have := rate_outer_spec st i hi (Array.repeat 168#usize 0#u8) 0#usize (by simp) (by
    intro p hp hc
    have h0 : (0#usize).val = 0 := rfl
    omega)
  step with this
  rename_i p
  exact buf_post1 p buf_post2 (Or.inl (by omega))

/-! ## One block of one lane -/

theorem getE8 (buf : Array U8 168#usize) (q : Nat) (hq : q < 168) (x : U8)
    (hx : x = buf.val[q]'(by rw [buf.property]; exact hq)) : buf.val[q]! = x := by
  rw [getElem!_pos buf.val q (by rw [buf.property]; exact hq)]; exact hx.symm

theorem getE_of_opt (T : List UInt8) (k : Nat) (v : UInt8) (h : T[k]? = some v) : T[k]! = v := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [getElem!_pos T k hk]

theorem tripleAt_get (T : List UInt8) (n c : Nat) (hc : c < 3) (h : 3 * n + c < T.length) :
    (tripleAt T n)[c]! = T[3 * n + c]! := by
  have h1 : c < (tripleAt T n).length := by
    simp only [tripleAt, List.length_take, List.length_drop]; omega
  rw [getElem!_pos (tripleAt T n) c h1, getElem!_pos T (3 * n + c) h]
  simp [tripleAt, List.getElem_take, List.getElem_drop]

theorem rej_ntt_block_x4_spec (T : List UInt8) (buf : Array U8 168#usize) (b : Nat)
    (hT : ∀ p < 168, T[168 * b + p]? = some (UInt8.ofNat (buf.val[p]!).val))
    (a : Array U32 312#usize) (j : Usize) (hj : j.val < 256) (h : LaneInv T (56 * b) a j) :
    sampling.rej_ntt_block_x4 buf a j ⦃ r => LaneInv T (56 * (b + 1)) r.2 r.1 ⦄ := by
  unfold sampling.rej_ntt_block_x4 sampling.rej_ntt_block_x4_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 312#usize × Usize × Usize) => 56 - p.2.2.val)
    (fun (p : Array U32 312#usize × Usize × Usize) =>
      p.2.2.val ≤ 56 ∧ p.2.1.val ≤ j.val + p.2.2.val ∧ LaneInv T (56 * b + p.2.2.val) p.1 p.2.1)
  · rintro ⟨a, jc, t⟩ ⟨ht, hjt, hinv⟩
    dsimp only at ht hjt hinv
    simp only [sampling.rej_ntt_block_x4_loop.body]
    split
    · rename_i htlt
      have ht56 : t.val < 56 := by scalar_tac
      have hP : ∀ c : Nat, c < 3 → 168 * b + 3 * t.val + c < T.length := by
        intro c hc3
        have := hT (3 * t.val + c) (by omega)
        have := (List.getElem?_eq_some_iff.mp this).1
        omega
      have hj311 : jc.val ≤ 311 := hinv.1
      step*
      · have hb1 : i6.val ≤ 1 := by rw [i6_post]; exact Bool.toNat_le _
        scalar_tac
      · have g0 := getE8 buf i.val (by omega) _ i1_post2
        have g1 := getE8 buf i2.val (by omega) _ i3_post2
        have g2 := getE8 buf i4.val (by omega) _ i5_post2
        rw [← g0, ← g1, ← g2] at z_post
        have key : ∀ (c : Nat) (hc3 : c < 3) (q : Usize), q.val = 3 * t.val + c →
            (tripleAt T (56 * b + t.val))[c]! = UInt8.ofNat (buf.val[q.val]!).val := by
          intro c hc3 q hq
          rw [tripleAt_get T _ c hc3 (by have := hP c hc3; omega), show 3 * (56 * b + t.val) + c = 168 * b + (3 * t.val + c) by omega]
          exact getE_of_opt T _ _ (by rw [hq]; exact hT (3 * t.val + c) (by omega))
        have k0 := key 0 (by omega) i (by omega)
        have k1 := key 1 (by omega) i2 (by omega)
        have k2 := key 2 (by omega) i4 (by omega)
        have htri := triAt_of_bytes T (56 * b + t.val) _ _ _ z k0 k1 k2 (by simpa using z_post)
        have hQ : (field.Q).val = 8380417 := by first | rfl | decide | simp [field.Q]
        have hzq : z < field.Q ↔ z.val < Spec.q := by
          rw [UScalar.lt_equiv, hQ]
        have hj6 : i6.val = if z.val < Spec.q then 1 else 0 := by
          rw [i6_post]
          by_cases hh : z.val < Spec.q
          · rw [if_pos hh, decide_eq_true (hzq.mpr hh)]; rfl
          · rw [if_neg hh, decide_eq_false (fun h => hh (hzq.mp h))]; rfl
        have hstep := laneInv_step T (56 * b + t.val) a a1 jc j1 z hinv (by omega) htri a1_post
          (by rw [j1_post, hj6])
        refine ⟨by omega, ?_, ?_, by omega⟩
        · rw [j1_post, hj6]; split <;> omega
        · rw [show 56 * b + t1.val = 56 * b + t.val + 1 by omega]
          exact hstep
    · rename_i htge
      have ht56 : t.val = 56 := by scalar_tac
      simp only [WP.spec_ok]
      rw [ht56] at hinv
      rw [show 56 * (b + 1) = 56 * b + 56 by ring]
      exact hinv
  · exact ⟨by simp, by simp, by simpa using h⟩

/-! ## One lane of one 4-way block -/

theorem rej_ntt_lane_x4_spec (T : List UInt8) (st : St4) (i : Usize) (b : Nat) (hi : i.val < 4)
    (hT : ∀ p < 168, T[168 * b + p]? = some (KM.sb (pj st i.val) p))
    (a : Array U32 312#usize) (j : Usize) (h : LaneInv T (56 * b) a j) :
    sampling.rej_ntt_lane_x4 st i a j ⦃ r => LaneInv T (56 * (b + 1)) r.2 r.1 ⦄ := by
  unfold sampling.rej_ntt_lane_x4
  split
  · rename_i hj
    have hj256 : j.val < 256 := by scalar_tac
    step with rate_bytes_x4_spec st i hi
    exact rej_ntt_block_x4_spec T buf b (fun p hp => by rw [hT p hp, buf_post p hp]) a j hj256 h
  · rename_i hj
    have hj256 : 256 ≤ j.val := by scalar_tac
    simp only [WP.spec_ok]
    obtain ⟨h1, h2, h3⟩ := h
    have hst := stA_stable T (56 * b) (56 * (b + 1)) (by omega) (by omega)
    refine ⟨h1, ?_, ?_⟩
    · rw [hst]; exact h2
    · intro k hk
      rw [hst] at hk ⊢
      exact h3 k hk

/-! ## The final copy -/

theorem arr_get_set_256 (a : Array U32 256#usize) (j : Usize) (z : U32) (hj : j.val < 256) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 256 := a.property
  by_cases hk : k < 256
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem getE312 (a : Array U32 312#usize) (q : Nat) (hq : q < 312) (x : U32)
    (hx : x = a.val[q]'(by rw [a.property]; exact hq)) : a.val[q]! = x := by
  rw [getElem!_pos a.val q (by rw [a.property]; exact hq)]; exact hx.symm

@[step]
theorem first_256_spec (a : Array U32 312#usize) :
    sampling.first_256 a ⦃ r => ∀ k, k < 256 → r.val[k]! = a.val[k]! ⦄ := by
  unfold sampling.first_256 sampling.first_256_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun (p : Array U32 256#usize × Usize) => p.2.val ≤ 256 ∧ ∀ m, m < p.2.val → p.1.val[m]! = a.val[m]!)
  · rintro ⟨r, k⟩ ⟨hk, hg⟩
    dsimp only at hk hg
    simp only [sampling.first_256_loop.body]
    split
    · rename_i hlt
      have hk256 : k.val < 256 := by scalar_tac
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro m hm
      rw [a1_post, arr_get_set_256 r k _ hk256 m]
      by_cases hmk : m = k.val
      · subst hmk
        rw [if_pos rfl]
        exact (getE312 a k.val (by omega) _ i_post2).symm
      · have : ¬ k.val = m := fun h => hmk h.symm
        rw [if_neg this]
        exact hg m (by omega)
    · rename_i hge
      have : k.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      intro m hm
      exact hg m (by omega)
  · exact ⟨by simp, by intro m hm; simp at hm⟩

/-! ## What a finished lane denotes -/

/-- The first 256 words of the scratch are canonical and denote the polynomial `P`. -/
def FinP (P : Poly) (a : Array U32 312#usize) : Prop :=
  (∀ k, k < 256 → (a.val[k]!).val < Spec.q) ∧ ∀ k, k < 256 → (((a.val[k]!).val : Nat) : Zq) = P[k]!

def FinL (T : List UInt8) (n : Nat) (a : Array U32 312#usize) : Prop := FinP (stA T n).1 a

theorem lane_fin (T : List UInt8) (n m : Nat) (hnm : n ≤ m) (a : Array U32 312#usize) (j : Usize)
    (h : LaneInv T n a j) (hj : 256 ≤ j.val) : FinL T m a := by
  obtain ⟨_, hmin, hk⟩ := h
  have hs : (stA T n).2 = 256 := by omega
  have hst := stA_stable T n m (by omega) hnm
  unfold FinL FinP
  rw [hst]
  exact ⟨fun k hk' => (hk k (by omega)).1, fun k hk' => (hk k (by omega)).2⟩

theorem finP_of (T : List UInt8) (n : Nat) (P : Poly) (a : Array U32 312#usize) (h : FinL T n a)
    (e : (stA T n).1 = P) : FinP P a := by
  subst e; exact h

theorem repr_of_first_256 (r : Array U32 256#usize) (a : Array U32 312#usize) (P : Poly)
    (hr : ∀ k, k < 256 → r.val[k]! = a.val[k]!) (h : FinP P a) : Repr r P := by
  obtain ⟨h1, h2⟩ := h
  have hl := len256 r
  constructor
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := List.getElem_of_mem hx
    subst hxk
    have hk' : k < 256 := by omega
    have e := hr k hk'
    rw [getElem!_pos r.val k hk] at e
    rw [e]
    exact h1 k hk'
  · apply Vector.ext
    intro k hk
    rw [toZq_get r k hk]
    have e := hr k hk
    rw [getElem!_pos r.val k (by omega)] at e
    rw [e, h2 k hk, getElem!_pos _ _ (by simpa using hk)]

end Proofs
