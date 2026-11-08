import Proofs.TrLane

/-!
# The extracted lane-3 helpers of `rej_ntt_poly_x3_tr`

`sampling.set_lane3`, `lane3_state`, `absorb_block_lane3` (lane 3 of the 4-way state), `tr_tail_lanes`, `squeeze64` and
`tr_finish_scalar` against the pure block schedule of `Proofs/TrLane.lean`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem RATE256_val : sampling.RATE256.val = 136 := by
  unfold sampling.RATE256; rfl

theorem RATE256_eq : sampling.RATE256 = 136#usize := by
  unfold sampling.RATE256; rfl

theorem len17 (a : Array U64 17#usize) : a.val.length = 17 := a.property

theorem toU64_zero : toU64 0#u64 = 0 := rfl

theorem st_ext {A B : Spec.Keccak.State} (h : ∀ k, k < 25 → A[k]! = B[k]!) : A = B := by
  apply Vector.ext
  intro k hk
  have := h k hk
  rwa [getElem!_pos _ _ (by simpa using hk), getElem!_pos _ _ (by simpa using hk)] at this

theorem repeat_getbang_zero (n : Usize) (k : Nat) (hk : k < n.val) : (Array.repeat n 0#u64).val[k]! = 0#u64 := by
  rw [getElem!_pos _ _ (by simp [hk])]
  simp only [Array.repeat_val, List.getElem_replicate]

theorem getD_drop (M : List UInt8) (b j : Nat) : (M.drop b).getD j 0 = M.getD (b + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem arr_getbang_set {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (j : Usize) (z : α) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k ∧ j.val < n.val then z else a.val[k]! := by
  have hl : a.val.length = n.val := a.property
  by_cases hk : k < n.val
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
    by_cases h : j.val = k <;> simp [h, hk]
  · have hne : ¬ (j.val = k ∧ j.val < n.val) := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

/-! ## `set_lane3` and `lane3_state` -/

theorem set_lane3_spec (st : St4) (s : Array U64 25#usize) :
    sampling.set_lane3 st s ⦃ st' => ∀ k, k < 25 → ∀ i, i < 4 →
      ln (at4 st' k) i = if i = 3 then toU64 (s.val[k]!) else ln (at4 st k) i ⦄ := by
  unfold sampling.set_lane3 sampling.set_lane3_loop
  apply loop.spec_decr_nat
    (fun (p : St4 × Usize) => 25 - p.2.val)
    (fun p => p.2.val ≤ 25 ∧ ∀ k, k < 25 → ∀ i, i < 4 →
      ln (at4 p.1 k) i = if i = 3 ∧ k < p.2.val then toU64 (s.val[k]!) else ln (at4 st k) i)
  · rintro ⟨st1, k⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.set_lane3_loop.body]
    split
    · rename_i hk
      have hk25 : k.val < 25 := by scalar_tac
      step*
      subst i_post2 a_post3 a1_post
      have ha := at4_idx st1 k a hk25 a_post2
      refine ⟨by omega, fun k' hk' i' hi' => ?_, by omega⟩
      rw [at4_set st1 k _ k' hk25]
      by_cases hkk : k.val = k'
      · subst hkk
        have hh := h2 k.val hk25 i' hi'
        have hlt : k.val < k1.val := by omega
        have hh' : ln (at4 st1 k.val) i' = ln (at4 st k.val) i' := by rw [hh]; simp
        rw [if_pos rfl, ln_set _ _ _ _ (by norm_num), ha, hh']
        by_cases hi3 : i' = 3
        · subst hi3
          rw [if_pos (by simp), if_pos ⟨rfl, hlt⟩, getElem!_pos s.val k.val (by rw [len25 s]; exact hk25)]
        · rw [if_neg (by simp; omega), if_neg (by omega)]
      · rw [if_neg hkk, h2 k' hk' i' hi']
        have : k' < k1.val ↔ k' < k.val := by omega
        simp only [this]
    · rename_i hk
      have hk25 : k.val = 25 := by scalar_tac
      simp only [WP.spec_ok]
      intro k' hk' i' hi'
      rw [h2 k' hk' i' hi']
      have : k' < k.val := by omega
      simp [this]
  · refine ⟨by simp, fun k hk i hi => ?_⟩
    simp

theorem lane3_state_spec (st : St4) : sampling.lane3_state st ⦃ s => toLanes s = pj st 3 ⦄ := by
  unfold sampling.lane3_state sampling.lane3_state_loop
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 25 - p.2.val)
    (fun p => p.2.val ≤ 25 ∧ ∀ k, k < p.2.val → toU64 (p.1.val[k]!) = ln (at4 st k) 3)
  · rintro ⟨s1, k⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.lane3_state_loop.body]
    split
    · rename_i hk
      have hk25 : k.val < 25 := by scalar_tac
      step*
      subst a1_post
      have ha := at4_idx st k _ hk25 a_post2
      refine ⟨by omega, fun k' hk' => ?_, by omega⟩
      rw [arr_getbang_set]
      by_cases hkk : k.val = k'
      · subst hkk
        rw [if_pos ⟨rfl, by simpa using hk25⟩, ln_of_get _ 3 (by simp) _ i_post2, ha]
      · rw [if_neg (by simp; omega)]
        exact h2 k' (by omega)
    · rename_i hk
      have hk25 : k.val = 25 := by scalar_tac
      simp only [WP.spec_ok]
      apply Vector.ext
      intro k' hk'
      rw [toLanes_get _ _ hk', pj_getElem' _ _ _ hk']
      have := h2 k' (by omega)
      rw [getElem!_pos _ _ (by rw [len25]; omega)] at this
      exact this
  · refine ⟨by simp, fun k hk => ?_⟩
    simp at hk

theorem squeeze64_spec (s : Array U64 25#usize) :
    sampling.squeeze64 s ⦃ out => ∀ j, j < 64 → UInt8.ofNat (out.val[j]!).val = KM.sb (toLanes s) j ⦄ := by
  unfold sampling.squeeze64 sampling.squeeze64_loop
  apply loop.spec_decr_nat
    (fun (p : Array U8 64#usize × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧ ∀ j, j < p.2.val → UInt8.ofNat (p.1.val[j]!).val = KM.sb (toLanes s) j)
  · rintro ⟨out1, j⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.squeeze64_loop.body]
    split
    · rename_i hj
      have hj64 : j.val < 64 := by scalar_tac
      step*
      subst a_post
      have hb := read_sb s j.val (by omega) i i3 _ i4 i5 (by omega) (by omega) i1_post2 (by omega) i4_post1 i5_post
      refine ⟨by omega, fun j' hj' => ?_, by omega⟩
      rw [arr_getbang_set]
      by_cases hjj : j.val = j'
      · subst hjj
        rw [if_pos ⟨rfl, by simp; omega⟩]
        exact hb
      · rw [if_neg (by simp; omega)]
        exact h2 j' (by omega)
    · rename_i hj
      have hj64 : j.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      intro j' hj'
      exact h2 j' (by omega)
  · refine ⟨by simp, fun k hk => ?_⟩
    simp at hk

/-! ## The lane word of a block -/

theorem blk_lane_spec (pk : Slice U8) (tail : Array U64 17#usize) (q t k : Usize)
    (hq : q.val = (bytes pk).length / 136) (ht : t.val ≤ q.val)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k) (hk : k.val < 17) :
    (if t < q then
        (do let i ← sampling.RATE256 * t
            let i1 ← 8#usize * k
            let i2 ← i + i1
            keccak.load_lane pk i2)
      else Array.index_usize tail k : RustM U64) ⦃ w => toU64 w = Wb (blkT (bytes pk) t.val) k.val ⦄ := by
  have hlen : (bytes pk).length = pk.val.length := by simp [bytes]
  have hmax : pk.val.length ≤ Usize.max := pk.property
  split
  · rename_i htq
    have htq' : t.val < q.val := by scalar_tac
    simp only [RATE256_eq]
    step*
    refine eq_Wb _ _ _ (fun m hm => ?_)
    rw [blkT_getD_full _ t.val (by omega) (8 * k.val + m) (by omega)]
    have h := w_post m hm
    rw [show i2.val + m = 136 * t.val + (8 * k.val + m) by simp at *; omega] at h
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  · rename_i htq
    step*
    subst w_post2
    have htq' : t.val = q.val := by scalar_tac
    rw [htq', ← htail k.val hk, getElem!_pos tail.val k.val (by rw [len17 tail]; exact hk)]

/-! ## `absorb_block_lane3` -/

theorem absorb_block_lane3_spec (st : St4) (pk : Slice U8) (tail : Array U64 17#usize) (q t : Usize)
    (hq : q.val = (bytes pk).length / 136) (ht : t.val ≤ q.val)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k) :
    sampling.absorb_block_lane3 st pk tail q t ⦃ st' =>
      (∀ i, i < 3 → pj st' i = pj st i) ∧ pj st' 3 = xor17 (pj st 3) (blkT (bytes pk) t.val) ⦄ := by
  unfold sampling.absorb_block_lane3 sampling.absorb_block_lane3_loop
  have hblk : (blkT (bytes pk) t.val).length = 136 := blkT_length _ _ (by omega)
  apply loop.spec_decr_nat
    (fun (p : St4 × Usize) => 17 - p.2.val)
    (fun p => p.2.val ≤ 17 ∧ ∀ k, k < 25 → ∀ i, i < 4 →
      ln (at4 p.1 k) i = if i = 3 ∧ k < p.2.val then ln (at4 st k) 3 ^^^ Wb (blkT (bytes pk) t.val) k
        else ln (at4 st k) i)
  · rintro ⟨st1, k⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.absorb_block_lane3_loop.body]
    split
    · rename_i hk
      have hk17 : k.val < 17 := by scalar_tac
      refine WP.spec_bind (blk_lane_spec pk tail q t k hq ht htail hk17) ?_
      intro w hw
      step*
      have hk25 : k.val < 25 := by omega
      refine ⟨by omega, fun k' hk' i' hi' => ?_, by omega⟩
      subst a1_post3
      rw [at4_set st1 k a2 k' hk25]
      by_cases hkk : k.val = k'
      · subst hkk
        have ha1 := at4_idx st1 k _ hk25 a1_post2
        have ha := at4_idx st1 k _ hk25 a_post2
        have hx := ln_of_get _ 3 (by simp) _ i_post2
        have hx1 := xor_of_bv _ _ _ i1_post2
        rw [ha] at hx
        have hlt : k.val < k1.val := by omega
        rw [if_pos rfl, a2_post, ln_set _ _ _ _ (by simp), ha1]
        by_cases hi3 : i' = 3
        · subst hi3
          have h2k := h2 k.val hk25 3 (by omega)
          rw [if_pos (by simp), hx1, hx, h2k, if_neg (by omega), hw, if_pos ⟨rfl, hlt⟩]
        · rw [if_neg (by simp; omega), h2 k.val hk25 i' hi', if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hkk, h2 k' hk' i' hi']
        have : k' < k1.val ↔ k' < k.val := by omega
        simp only [this]
    · rename_i hk
      have hk17 : k.val = 17 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨fun i hi => ?_, ?_⟩
      · apply st_ext
        intro k' hk'
        rw [pj_getElem _ _ _ hk', pj_getElem _ _ _ hk', h2 k' hk' i (by omega), if_neg (by omega)]
      · apply st_ext
        intro k' hk'
        rw [pj_getElem _ _ _ hk', xor17_getElem _ _ _ hk', pj_getElem _ _ _ hk', h2 k' hk' 3 (by omega)]
        by_cases hk17' : k' < 17
        · rw [if_pos ⟨rfl, by omega⟩, if_pos hk17']
        · rw [if_neg (by omega), if_neg hk17']
  · refine ⟨by simp, fun k hk i hi => ?_⟩
    simp

/-! ## `tr_tail_lanes` -/

theorem tail_loop_spec (pk : Slice U8) (base rem : Usize) (hb : base.val + rem.val = pk.val.length)
    (hrem : rem.val < 136) (w0 : Array U64 17#usize)
    (hw0 : ∀ k, k < 17 → ∀ m, m < 8 → KM.byteOf (toU64 (w0.val[k]!)) m = 0) :
    sampling.tr_tail_lanes_loop pk base rem w0 0#usize ⦃ w => ∀ k, k < 17 → ∀ m, m < 8 →
      KM.byteOf (toU64 (w.val[k]!)) m =
        if 8 * k + m < rem.val then (bytes pk).getD (base.val + (8 * k + m)) 0 else 0 ⦄ := by
  unfold sampling.tr_tail_lanes_loop
  apply loop.spec_decr_nat
    (fun (p : Array U64 17#usize × Usize) => rem.val - p.2.val)
    (fun p => p.2.val ≤ rem.val ∧ ∀ k, k < 17 → ∀ m, m < 8 →
      KM.byteOf (toU64 (p.1.val[k]!)) m =
        if 8 * k + m < p.2.val then (bytes pk).getD (base.val + (8 * k + m)) 0 else 0)
  · rintro ⟨w1, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.tr_tail_lanes_loop.body]
    split
    · rename_i hi
      have hi' : i.val < rem.val := by scalar_tac
      step*
      subst a_post i2_post2 i8_post2
      have hi7 : i7.val < 17 := by omega
      have hbi6 : ∀ m, m < 8 → KM.byteOf (toU64 i6) m = if m = i.val % 8 then UInt8.ofNat (pk.val[i1.val]'i2).val else 0 :=
        fun m hm => byteOf_cast_shl i3 i6 i5 _ (i.val % 8) m (by omega) hm (by omega) i3_post i6_post2
      have hg := bytes_getElem?_of pk i1.val _ (List.getElem?_eq_getElem i2)
      have hg' : (bytes pk)[base.val + i.val]? = some (UInt8.ofNat (pk.val[i1.val]'i2).val) := by
        rw [← i1_post]; exact hg
      have hget : (bytes pk).getD (base.val + i.val) 0 = UInt8.ofNat (pk.val[i1.val]'i2).val := by
        rw [List.getD_eq_getElem?_getD, hg']; rfl
      refine ⟨by omega, fun k hk m hm => ?_, by omega⟩
      rw [arr_getbang_set]
      by_cases hk7 : i7.val = k
      · rw [if_pos ⟨hk7, by simp; omega⟩, xor_of_bv _ _ _ i9_post2, KM.byteOf_xor, hbi6 m hm,
          show (w1.val[i7.val]'i8) = w1.val[k]! by rw [← hk7]; exact (getElem!_pos _ _ _).symm, h2 k hk m hm, i10_post]
        by_cases hmm : m = i.val % 8
        · have hj : 8 * k + m = i.val := by omega
          rw [if_pos hmm, hj, if_neg (lt_irrefl _), if_pos (by omega), hget]
          simp
        · have hj : 8 * k + m ≠ i.val := by omega
          rw [if_neg hmm, UInt8.xor_zero]
          have : (8 * k + m < i.val + 1) ↔ (8 * k + m < i.val) := by omega
          simp only [this]
      · rw [if_neg (by intro h; exact hk7 h.1), h2 k hk m hm, i10_post]
        have : (8 * k + m < i.val + 1) ↔ (8 * k + m < i.val) := by omega
        simp only [this]
    · rename_i hi
      have hi' : i.val = rem.val := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk m hm
      rw [h2 k hk m hm, hi']
  · refine ⟨by simp, fun k hk m hm => ?_⟩
    have h0 : (0#usize).val = 0 := rfl
    rw [h0, if_neg (by omega)]
    exact hw0 k hk m hm

theorem byteOf_const_shl (x z : U64) (n : Usize) (b : UInt8) (k m : Nat) (hk : k < 8) (hm : m < 8)
    (hn : n.val = 8 * k) (hx : toU64 x = b.toUInt64) (hz : z.bv = x.bv <<< n.val) :
    KM.byteOf (toU64 z) m = if m = k then b else 0 := by
  rw [toU64_shl x z n (by omega) hz, hx, hn]
  exact KM.byteOf_shl b k m hk hm

theorem getD_zero_of_ge (M : List UInt8) (j : Nat) (h : M.length ≤ j) : M.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem tr_tail_lanes_spec (pk : Slice U8) :
    sampling.tr_tail_lanes pk ⦃ w => ∀ k, k < 17 →
      toU64 (w.val[k]!) = Wb (blkT (bytes pk) ((bytes pk).length / 136)) k ⦄ := by
  have hlen : (bytes pk).length = pk.val.length := by simp [bytes]
  have hpl : pk.len.val = pk.val.length := by simp [Slice.len]
  unfold sampling.tr_tail_lanes
  simp only [RATE256_eq]
  step*
  have hrem : rem.val < 136 := by omega
  step with tail_loop_spec pk base rem (by omega) hrem (Array.repeat 17#usize 0#u64) (by
    intro k hk m hm
    rw [repeat_getbang_zero _ _ (by simpa using hk), toU64_zero]
    exact Proofs.byteOf_zero m) as ⟨w1, hw1⟩
  step*
  rename_i k
  have hk := w_post2
  have hrb : rem.val = (bytes pk).length % 136 := by omega
  have hbase : base.val = 136 * ((bytes pk).length / 136) := by omega
  have hc1f : toU64 31#u64 = (0x1F : UInt8).toUInt64 := by decide +kernel
  have hlen2 : (bytes pk).length = base.val + rem.val := by omega
  -- the second lane: the `0x1F` byte
  have hw2 : ∀ k, k < 17 → ∀ m, m < 8 → KM.byteOf (toU64 (w2.val[k]!)) m =
      KM.byteOf (toU64 (w1.val[k]!)) m ^^^ (if k = rem.val / 8 ∧ m = rem.val % 8 then 0x1F else 0) := by
    intro k hk m hm
    subst w2_post
    rw [arr_getbang_set]
    have hb5 := byteOf_const_shl 31#u64 i5 i4 0x1F (rem.val % 8) m (by omega) hm (by omega) hc1f i5_post2
    by_cases hk6 : i6.val = k
    · rw [if_pos ⟨hk6, by simp; omega⟩, xor_of_bv _ _ _ i8_post2, KM.byteOf_xor, hb5]
      subst i7_post2
      rw [show (w1.val[i6.val]'i7) = w1.val[k]! by rw [← hk6]; exact (getElem!_pos _ _ _).symm]
      have : (k = rem.val / 8 ∧ m = rem.val % 8) ↔ m = rem.val % 8 := by omega
      simp only [this]
    · rw [if_neg (by intro h; exact hk6 h.1), if_neg (by omega), UInt8.xor_zero]
  have hw3 : ∀ k, k < 17 → ∀ m, m < 8 → KM.byteOf (toU64 (w.val[k]!)) m =
      KM.byteOf (toU64 (w2.val[k]!)) m ^^^ (if k = 16 ∧ m = 7 then 0x80 else 0) := by
    intro k hk m hm
    subst w_post1
    rw [arr_getbang_set]
    by_cases hk6 : 16 = k
    · subst hk6
      rw [if_pos ⟨rfl, by simp⟩, xor_of_bv _ _ _ i10_post2, KM.byteOf_xor]
      subst i9_post2
      have hc : KM.byteOf (toU64 9223372036854775808#u64) m = if m = 7 then 0x80 else 0 := by
        interval_cases m <;> decide +kernel
      rw [hc, show (w2.val[16]'i9) = w2.val[16]! from (getElem!_pos _ _ _).symm]
      simp
    · rw [if_neg (by intro h; exact hk6 (by simpa using h.1)), if_neg (by omega), UInt8.xor_zero]
  refine eq_Wb _ _ _ (fun m hm => ?_)
  rw [blkT_last, KM.blk_pad_getD _ 136 ((bytes pk).length % 136) (by simp; omega) (Nat.mod_lt _ (by norm_num))
    (8 * k + m), getD_drop, hw3 k hk m hm, hw2 k hk m hm, hw1 k hk m hm, ← hbase]
  have hz : (if 8 * k + m < rem.val then (bytes pk).getD (base.val + (8 * k + m)) 0 else 0) =
      (bytes pk).getD (base.val + (8 * k + m)) 0 := by
    split_ifs with h
    · rfl
    · exact (getD_zero_of_ge _ _ (by omega)).symm
  rw [hz]
  have c1 : (k = rem.val / 8 ∧ m = rem.val % 8) ↔ 8 * k + m = (bytes pk).length % 136 := by omega
  have c2 : (k = 16 ∧ m = 7) ↔ 8 * k + m = 136 - 1 := by omega
  simp only [c1, c2]

/-! ## `tr_finish_scalar` -/

theorem fin_inner_spec (pk : Slice U8) (tail : Array U64 17#usize) (q t : Usize) (s0 : Array U64 25#usize)
    (hq : q.val = (bytes pk).length / 136) (ht : t.val ≤ q.val)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k) :
    sampling.tr_finish_scalar_loop0_loop0 pk tail q s0 t 0#usize ⦃ s =>
      toLanes s = xor17 (toLanes s0) (blkT (bytes pk) t.val) ⦄ := by
  unfold sampling.tr_finish_scalar_loop0_loop0
  have hblk : (blkT (bytes pk) t.val).length = 136 := blkT_length _ _ (by omega)
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 17 - p.2.val)
    (fun p => p.2.val ≤ 17 ∧ ∀ k, k < 25 → toU64 (p.1.val[k]!) =
      if k < p.2.val then toU64 (s0.val[k]!) ^^^ Wb (blkT (bytes pk) t.val) k else toU64 (s0.val[k]!))
  · rintro ⟨s1, k⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.tr_finish_scalar_loop0_loop0.body]
    split
    · rename_i hk
      have hk17 : k.val < 17 := by scalar_tac
      refine WP.spec_bind (blk_lane_spec pk tail q t k hq ht htail hk17) ?_
      intro w hw
      step*
      subst a_post i1_post2
      have hk25 : k.val < 25 := by omega
      have hx : toU64 (s1.val[k.val]'i1) = toU64 (s0.val[k.val]!) := by
        have := h2 k.val hk25
        rw [getElem!_pos s1.val k.val i1] at this
        simpa using this
      refine ⟨by omega, fun k' hk' => ?_, by omega⟩
      rw [arr_getbang_set]
      by_cases hkk : k.val = k'
      · subst hkk
        rw [if_pos ⟨rfl, by simpa using hk25⟩, xor_of_bv _ _ _ i2_post2, hx, hw, if_pos (by omega)]
      · rw [if_neg (by simp; omega), h2 k' hk']
        have : k' < k1.val ↔ k' < k.val := by omega
        simp only [this]
    · rename_i hk
      have hk17 : k.val = 17 := by scalar_tac
      simp only [WP.spec_ok]
      apply st_ext
      intro k' hk'
      have hh := h2 k' hk'
      rw [getElem!_pos s1.val k' (by rw [len25]; exact hk'), getElem!_pos s0.val k' (by rw [len25]; exact hk')] at hh
      rw [toLanes_getElem! _ _ (by rw [len25]; exact hk'), xor17_getElem _ _ _ hk', toLanes_getElem! s0 k' (by rw [len25]; exact hk'), hh]
      by_cases h17 : k' < 17
      · rw [if_pos (by omega), if_pos h17]
      · rw [if_neg (by omega), if_neg h17]
  · refine ⟨by simp, fun k hk => ?_⟩
    simp

theorem fin_outer_spec (pk : Slice U8) (tail : Array U64 17#usize) (q : Usize) (trs : Array U64 25#usize)
    (t0 : Usize) (hq : q.val = (bytes pk).length / 136) (ht : t0.val ≤ q.val + 1)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (hs : toLanes trs = HS (bytes pk) t0.val) :
    sampling.tr_finish_scalar_loop0 pk tail q trs t0 ⦃ s => toLanes s = HS (bytes pk) (q.val + 1) ⦄ := by
  unfold sampling.tr_finish_scalar_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => q.val + 1 - p.2.val)
    (fun p => p.2.val ≤ q.val + 1 ∧ toLanes p.1 = HS (bytes pk) p.2.val)
  · rintro ⟨s1, t⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.tr_finish_scalar_loop0.body]
    split
    · rename_i htq
      have htq' : t.val ≤ q.val := by scalar_tac
      refine WP.spec_bind (fin_inner_spec pk tail q t s1 hq htq' htail) ?_
      intro s2 hs2
      have hmax : pk.val.length ≤ Usize.max := pk.property
      have hlen : (bytes pk).length = pk.val.length := by simp [bytes]
      step*
      refine ⟨by omega, ?_, by omega⟩
      rw [s2_post, hs2, h2, t1_post, HS_succ _ _ (by omega), xorBlock_eq_xor17 _ _ (blkT_length _ _ (by omega)).le]
    · rename_i htq
      have htq' : t.val = q.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      rw [h2, htq']
  · exact ⟨ht, hs⟩

theorem tr_finish_scalar_spec (pk : Slice U8) (tail : Array U64 17#usize) (q : Usize) (trs : Array U64 25#usize)
    (t0 : Usize) (hq : q.val = (bytes pk).length / 136) (ht : t0.val ≤ q.val + 1)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (hs : toLanes trs = HS (bytes pk) t0.val) :
    sampling.tr_finish_scalar pk tail q trs t0 ⦃ out => ∀ j, j < 64 →
      UInt8.ofNat (out.val[j]!).val = KM.sb (HS (bytes pk) (q.val + 1)) j ⦄ := by
  unfold sampling.tr_finish_scalar
  step with fin_outer_spec pk tail q trs t0 hq ht htail hs as ⟨s, hs'⟩
  step with squeeze64_spec s as ⟨out, hout⟩
  rename_i j hj
  rw [hout j hj, hs']

end Proofs
