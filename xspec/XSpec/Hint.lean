import XSpec.HintModel

/-!
# Algorithms 20 and 21 (`HintBitPack`, `HintBitUnpack`)

Ours act on `Vector HintPoly k` (`HintPoly = Vector Bool 256`) and `List UInt8`; ocaml-pq's
`OcamlPq.Encoding.Hint` on `HintVec = ℕ → ℕ → ℕ` (entry `1` exactly where the hint bit is set) and `List ℕ`.
Adapter `hv H r c = 1` iff `r < k`, `c < 256` and `H[r][c]`.  `HintBitUnpack` is proved equal on every input
(including the `⊥` cases); `HintBitPack` under its precondition (weight at most `ω`, `ω < 256`; outside it the
only difference is the `UInt8` truncation of `Index`).
-/

open Spec

namespace XSpec

open OcamlPq.Encoding.Hint

/-- A hint vector as ocaml-pq's `HintVec`. -/
def hv {k : Nat} (H : Vector HintPoly k) : HintVec :=
  fun r c => if r < k ∧ c < 256 ∧ (H[r]!)[c]! = true then 1 else 0

theorem vset_get_ne {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i r : Nat) (a : α)
    (h : i ≠ r) : (v.set! i a)[r]! = v[r]! := by
  by_cases hr : r < n
  · rw [getElem!_pos _ r (by simpa using hr), getElem!_pos _ r (by simpa using hr)]
    simp [set!_eq', Vector.getElem_setIfInBounds hr, h]
  · rw [getElem!_neg _ r (by simpa using hr), getElem!_neg _ r (by simpa using hr)]

theorem vset_get_eq {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    (v.set! i a)[i]! = a := HM.vget_vset v i hi a

theorem hv_set {k : Nat} (H : Vector HintPoly k) (i b : Nat) (hi : i < k) (hb : b < 256) :
    setHint (hv H) i b = hv (H.set! i (H[i]!.set! b true)) := by
  funext r c
  unfold setHint hv
  by_cases hri : r = i
  · subst hri
    rw [vset_get_eq _ _ hi]
    by_cases hc : c = b
    · subst hc
      rw [vset_get_eq _ _ (by omega)]
      simp [hi, hb]
    · rw [vset_get_ne _ _ _ _ (fun h => hc h.symm)]
      simp [hc, hi]
  · rw [vset_get_ne _ _ _ _ (fun h => hri h.symm)]
    simp [hri]

theorem hv_set_self {k : Nat} (H : Vector HintPoly k) (i : Nat) (hi : i < k) : H.set! i H[i]! = H :=
  HM.vset_self H i hi

theorem getD_bytesN (y : List UInt8) (i : Nat) : (bytesN y).getD i 0 = (y[i]!).toNat := by
  by_cases h : i < y.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), getElem!_pos y i h]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), getElem!_neg y i h]
    rfl

theorem u8_ge_iff (a b : UInt8) : a ≥ b ↔ a.toNat ≥ b.toNat := by
  simp [GE.ge, UInt8.le_iff_toNat_le]

theorem while_corr (y : List UInt8) (i first : Nat) {k : Nat} (hi : i < k) :
    ∀ (n idx : Nat) (H : Vector HintPoly k),
      unpackWhile (bytesN y) i first (idx + n) idx (hv H) =
        (HM.rowLoop y first n idx H[i]!).map (fun row => (hv (H.set! i row), idx + n)) := by
  intro n
  induction n with
  | zero =>
    intro idx H
    rw [unpackWhile, if_neg (by omega)]
    simp [HM.rowLoop, hv_set_self H i hi]
  | succ n ih =>
    intro idx H
    rw [unpackWhile, if_pos (by omega)]
    simp only [HM.rowLoop, getD_bytesN, u8_ge_iff]
    by_cases hc : idx > first ∧ (y[idx - 1]!).toNat ≥ (y[idx]!).toNat
    · simp only [if_pos hc, Option.map_none]
    · have hb : (y[idx]!).toNat < 256 := UInt8.toNat_lt _
      simp only [if_neg hc]
      rw [hv_set H i _ hi hb, show idx + (n + 1) = idx + 1 + n by omega, ih, HM.vget_vset H _ hi]
      simp only [HM.vset_vset, show idx + 1 + n = idx + (n + 1) from by omega]

theorem rows_corr (p : Params) (y : List UInt8) :
    ∀ (m i idx : Nat) (H : Vector HintPoly p.k), i + m = p.k →
      unpackRows p.k p.ω (bytesN y) i (hv H) idx =
        match HM.efoldv (HM.gOut p y) (List.range' i m) (H, idx) with
        | .inl _ => none
        | .inr s => some (hv s.1, s.2) := by
  intro m
  induction m with
  | zero =>
    intro i idx H hm
    rw [unpackRows, if_neg (by omega)]
    simp [HM.efoldv]
  | succ m ih =>
    intro i idx H hm
    have hik : i < p.k := by omega
    rw [unpackRows, if_pos hik, List.range'_succ]
    simp only [HM.efoldv, HM.gOut, getD_bytesN]
    by_cases hc : (y[p.ω + i]!).toNat < idx ∨ (y[p.ω + i]!).toNat > p.ω
    · simp only [if_pos hc]
    · simp only [if_neg hc]
      have hle : idx ≤ (y[p.ω + i]!).toNat := by omega
      have := while_corr y i idx hik ((y[p.ω + i]!).toNat - idx) idx H
      rw [show idx + ((y[p.ω + i]!).toNat - idx) = (y[p.ω + i]!).toNat by omega] at this
      rw [this]
      rcases HM.rowLoop y idx ((y[p.ω + i]!).toNat - idx) idx H[i]! with _ | row
      · simp
      · simp only [Option.map_some]
        rw [ih (i + 1) _ _ (by omega)]

theorem trailing_corr (y : List UInt8) (ω : Nat) :
    ∀ (n i : Nat), i + n = ω → unpackTrailing ω (bytesN y) i = (List.range' i n).all (fun j => y[j]! == 0) := by
  intro n
  induction n with
  | zero => intro i h; rw [unpackTrailing, if_neg (by omega)]; simp
  | succ n ih =>
    intro i h
    rw [unpackTrailing, if_pos (by omega), List.range'_succ, List.all_cons, getD_bytesN]
    by_cases h0 : (y[i]!) = 0
    · have h1 : (y[i]!).toNat = 0 := by simp [h0]
      simp [h1, h0, ih (i + 1) (by omega)]
    · have h1 : (y[i]!).toNat ≠ 0 := fun h' => h0 (UInt8.toNat_inj.mp (by simpa using h'))
      have e : (y[i]! == 0) = false := by simpa using h0
      rw [if_pos h1, e, Bool.false_and]

theorem trailing_eq_padB (y : List UInt8) (ω idx : Nat) :
    unpackTrailing ω (bytesN y) idx = HM.padB y ω idx := by
  unfold HM.padB
  by_cases h : idx ≤ ω
  · exact trailing_corr y ω (ω - idx) idx (by omega)
  · rw [unpackTrailing, if_neg (by omega), show ω - idx = 0 by omega]
    simp

theorem hv_zero (k : Nat) : (fun (_ _ : Nat) => (0 : Nat)) = hv (Vector.replicate k (Vector.replicate 256 false)) := by
  funext r c
  unfold hv
  by_cases h : r < k ∧ c < 256
  · simp [getElem!_pos, h.1, h.2]
  · have : ¬ (r < k ∧ c < 256 ∧ ((Vector.replicate k (Vector.replicate 256 false))[r]!)[c]! = true) := by
      intro h'; exact h ⟨h'.1, h'.2.1⟩
    simp [this]

theorem gOut_inl (p : Params) (y : List UInt8) (i : Nat) (b : Vector HintPoly p.k × Nat) (r : Option (Vector HintPoly p.k))
    (h : HM.gOut p y i b = .inl r) : r = none := by
  unfold HM.gOut at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem efoldv_gOut_inl (p : Params) (y : List UInt8) :
    ∀ (l : List Nat) (b : Vector HintPoly p.k × Nat) (a : Option (Vector HintPoly p.k)),
      HM.efoldv (HM.gOut p y) l b = .inl a → a = none := by
  intro l
  induction l with
  | nil => intro b a h; simp [HM.efoldv] at h
  | cons x l ih =>
    intro b a h
    simp only [HM.efoldv] at h
    cases hg : HM.gOut p y x b with
    | inl r => rw [hg] at h; obtain rfl : r = a := Sum.inl.inj h; exact gOut_inl p y x b r hg
    | inr b' => rw [hg] at h; exact ih b' a h

/-- `HintBitUnpack` (Algorithm 21), for every input, including the malformed ones (`⊥` on both sides at
exactly the same inputs). -/
theorem hintBitUnpack_eq (p : Params) (y : List UInt8) :
    (Spec.HintBitUnpack p y).map (fun H => hv H) = hintBitUnpack p.k p.ω (bytesN y) := by
  rw [HM.unpack_eq]
  unfold HM.unpackModel hintBitUnpack
  rw [hv_zero p.k, rows_corr p y p.k 0 0 _ (by omega)]
  rcases hE : HM.efoldv (HM.gOut p y) (List.range' 0 p.k) (Vector.replicate p.k (Vector.replicate 256 false), 0)
    with a | s
  · have := efoldv_gOut_inl p y _ _ _ hE
    subst this
    simp
  · simp only [trailing_eq_padB]
    by_cases h : HM.padB y p.ω s.2 = true <;> simp [h]

/-! ## `HintBitPack` -/

/-- Relation between our `(Array UInt8, Index)` pack state and ocaml-pq's `(List ℕ, Index)`. -/
def PR (o : Array UInt8 × Nat) (t : List ℕ × Nat) : Prop :=
  t.1 = o.1.toList.map UInt8.toNat ∧ t.2 = o.2

theorem toUInt8_toNat_of_lt {j : Nat} (h : j < 256) : j.toUInt8.toNat = j := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem packRow_idx (row : HintPoly) :
    ∀ (n j : Nat) (st : Array UInt8 × Nat), j + n = 256 →
      ((List.range' j n).foldl (fun b a => HM.packRowF row a b) st).2 = st.2 + HM.cntFrom row j := by
  intro n
  induction n with
  | zero =>
    intro j st h
    have : j = 256 := by omega
    subst this
    simp [HM.cntFrom_256]
  | succ n ih =>
    intro j st h
    rw [List.range'_succ, List.foldl_cons, ih (j + 1) _ (by omega), HM.cntFrom_succ row j (by omega)]
    unfold HM.packRowF
    by_cases hb : row[j]! = true <;> simp [hb] <;> omega

theorem packRow_corr {k : Nat} (H : Vector HintPoly k) (i : Nat) (hi : i < k) :
    ∀ (n : Nat) (o : Array UInt8 × Nat) (t : List ℕ × Nat), n ≤ 256 → PR o t →
      PR ((List.range' 0 n).foldl (fun b a => HM.packRowF H[i]! a b) o)
        ((List.range n).foldl (fun (st : List ℕ × ℕ) j =>
          if hv H i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) t) := by
  intro n
  induction n with
  | zero => intro o t _ h; simpa using h
  | succ n ih =>
    intro o t hn h
    have := ih o t (by omega) h
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 0 n).foldl (fun b a => HM.packRowF H[i]! a b) o = o' at this ⊢
    generalize (List.range n).foldl (fun (st : List ℕ × ℕ) j =>
          if hv H i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) t = t' at this ⊢
    obtain ⟨h1, h2⟩ := this
    unfold HM.packRowF hv
    by_cases hb : (H[i]!)[0 + 1 * n]! = true
    · simp only [Nat.zero_add, Nat.one_mul] at hb ⊢
      have hn' : n < 256 := by omega
      simp only [hb, hi, hn', and_self, if_true, ne_eq, one_ne_zero, not_false_eq_true]
      refine ⟨?_, by simp [h2]⟩
      simp only [Array.set!, Array.toList_setIfInBounds, h1, List.map_set, h2, toUInt8_toNat_of_lt hn']
    · simp only [Nat.zero_add, Nat.one_mul] at hb ⊢
      simp only [hb]
      simp
      exact ⟨h1, h2⟩

theorem hintBitPack_eq (p : Params) (hω : p.ω < 256) (H : Vector HintPoly p.k) (hw : HintWeight H ≤ p.ω) :
    bytesN (Spec.HintBitPack p H) = hintBitPack p.k p.ω (hv H) := by
  rw [HM.pack_eq]
  unfold HM.packModel hintBitPack
  have hW := HM.hintWeight_eq H
  -- invariant over the first `m` rows
  have key : ∀ m, m ≤ p.k →
      PR ((List.range' 0 m).foldl (fun b i => HM.packRowsF p.ω H i b) (Array.replicate (p.ω + p.k) 0, 0))
        ((List.range m).foldl (fun (st : List ℕ × ℕ) i =>
          let st := (List.range 256).foldl (fun (st : List ℕ × ℕ) j =>
            if hv H i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) st
          (st.1.set (p.ω + i) st.2, st.2)) (List.replicate (p.ω + p.k) 0, 0)) ∧
      ((List.range' 0 m).foldl (fun b i => HM.packRowsF p.ω H i b)
        (Array.replicate (p.ω + p.k) 0, 0)).2 + HM.restW H m = HM.restW H 0 := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨⟨?_, rfl⟩, by simp⟩
      simp
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.range_succ (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range' 0 m).foldl (fun b i => HM.packRowsF p.ω H i b)
        (Array.replicate (p.ω + p.k) 0, 0) = o at h1 h2 ⊢
      generalize (List.range m).foldl (fun (st : List ℕ × ℕ) i =>
          let st := (List.range 256).foldl (fun (st : List ℕ × ℕ) j =>
            if hv H i j ≠ 0 then (st.1.set st.2 j, st.2 + 1) else st) st
          (st.1.set (p.ω + i) st.2, st.2)) (List.replicate (p.ω + p.k) 0, 0) = t at h1 h2 ⊢
      have hmk : m < p.k := by omega
      have hrow := packRow_corr H m hmk 256 o t le_rfl h1
      have hidx := packRow_idx H[m]! 256 0 o (by omega)
      have hrw := HM.restW_succ H m hmk
      have hpr : HM.packRow H[m]! o = (List.range' 0 256).foldl (fun b a => HM.packRowF H[m]! a b) o := rfl
      rw [← hpr] at hrow hidx
      obtain ⟨hr1, hr2⟩ := hrow
      have hidx' : (HM.packRow H[m]! o).2 < 256 := by omega
      simp only [Nat.zero_add, Nat.one_mul]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · unfold HM.packRowsF
        simp only [Array.set!, Array.toList_setIfInBounds, List.map_set, hr1, hr2,
          toUInt8_toNat_of_lt hidx']
      · unfold HM.packRowsF
        simpa using hr2
      · unfold HM.packRowsF
        simp only
        omega
  obtain ⟨h1, -⟩ := key p.k le_rfl
  exact h1.1.symm

end XSpec
