import Proofs.NTTOps
import Proofs.Rounding
import Proofs.Hint

/-!
# Refinement specs for the small helpers of KeyGen, Sign and Verify

`sign.response`, `sign.hint_step`, `keygen.vec_power2round`, `keygen.compute_t`, `verify.scale_by_2d`,
`verify.scale_vec_by_2d`, `verify.prefix_eq` and `api.ctx_prefix`. Each is stated against the exact expression of
`Spec/MLDSA.lean` that the corresponding step of Algorithms 6, 7 and 8 computes, so the composition proofs
can rewrite with them directly.

Loops over rows use the predicate `Rows a P i` ("rows `< i` of `a` exist and satisfy `P`"), which survives
`Array.update` and turns into `ReprVec` / `ReprIntVec` / `ReprHintVec` once `i = K`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Row-wise invariants -/

/-- Rows `< i` of `a` exist and satisfy `P`. -/
def Rows {α : Type} {n : Usize} (a : Array α n) (P : Nat → α → Prop) (i : Nat) : Prop :=
  ∀ r, r < i → ∃ x, a.val[r]? = some x ∧ P r x

theorem Rows.zero {α : Type} {n : Usize} (a : Array α n) (P : Nat → α → Prop) : Rows a P 0 :=
  fun r hr => absurd hr (by omega)

theorem Rows.set {α : Type} {n : Usize} {a : Array α n} {P : Nat → α → Prop} {i : Nat}
    (h : Rows a P i) (j : Usize) (hj : j.val = i) (hi : i < a.val.length) (x : α) (hx : P i x) :
    Rows (a.set j x) P (i + 1) := by
  intro r hr
  rw [Array.set_val_eq, List.getElem?_set]
  by_cases e : j.val = r
  · have hri : r = i := by omega
    subst hri
    rw [if_pos e, if_pos (by omega)]
    exact ⟨x, rfl, hx⟩
  · rw [if_neg e]
    exact h r (by omega)

theorem Rows.reprVec {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {V : Vector Poly k}
    (h : Rows a (fun r x => Repr x V[r]!) k) (hK : K.val = k) : ReprVec a V := by
  refine ⟨hK, fun i hi => ?_⟩
  obtain ⟨row, hrow, hr⟩ := h i hi
  have hl : i < a.val.length := by have := a.property; omega
  rw [List.getElem?_eq_getElem hl] at hrow
  have e := Option.some.inj hrow
  have hr' : Repr row V[i] := by rw [← vget! V i hi]; exact hr
  rw [e]
  exact hr'

theorem Rows.reprIntVec {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {V : Vector RPoly k}
    (h : Rows a (fun r x => ReprInt x V[r]!) k) (hK : K.val = k) : ReprIntVec a V := by
  refine ⟨hK, fun i hi => ?_⟩
  obtain ⟨row, hrow, hr⟩ := h i hi
  have hl : i < a.val.length := by have := a.property; omega
  rw [List.getElem?_eq_getElem hl] at hrow
  have e := Option.some.inj hrow
  have hr' : ReprInt row V[i] := by rw [← vget! V i hi]; exact hr
  rw [e]
  exact hr'

theorem Rows.reprHintVec {K : Usize} {k : Nat} {a : Array (Array Bool 256#usize) K} {V : Vector HintPoly k}
    (h : Rows a (fun r x => ReprHint x V[r]!) k) (hK : K.val = k) : ReprHintVec a V := by
  refine ⟨hK, fun i hi => ?_⟩
  obtain ⟨row, hrow, hr⟩ := h i hi
  have hl : i < a.val.length := by have := a.property; omega
  rw [List.getElem?_eq_getElem hl] at hrow
  have e := Option.some.inj hrow
  have hr' : ReprHint row V[i] := by rw [← vget! V i hi]; exact hr
  rw [e]
  exact hr'

/-- A coefficient array whose entries are, pointwise, canonical residues of `P`. -/
theorem repr_of_get? (row : Array U32 256#usize) (P : Poly)
    (h : ∀ c, c < 256 → ∃ x : U32, row.val[c]? = some x ∧ x.val < Spec.q ∧ ((x.val : Nat) : Zq) = P[c]!) :
    Repr row P := by
  have hlen := len256 row
  constructor
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨y, hy, hlt, _⟩ := h c (by omega)
    rw [List.getElem?_eq_getElem hc] at hy
    have e : row.val[c] = y := Option.some.inj hy
    rw [e]; exact hlt
  · apply Vector.ext
    intro c hc
    obtain ⟨y, hy, _, he⟩ := h c hc
    rw [List.getElem?_eq_getElem (by omega)] at hy
    have e : row.val[c] = y := Option.some.inj hy
    rw [toZq_get row c hc, e, he, vget! P c hc]

theorem reprHint_of_get? (row : Array Bool 256#usize) (H : HintPoly)
    (h : ∀ c, c < 256 → row.val[c]? = some H[c]!) : ReprHint row H := by
  apply Vector.ext
  intro c hc
  have hlen : row.val.length = 256 := row.property
  have h1 := h c hc
  rw [List.getElem?_eq_getElem (by omega), vget! H c hc] at h1
  simp only [toHint, Vector.getElem_ofFn]
  exact Option.some.inj h1

theorem ReprIntVec.index_spec' {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {v : Vector RPoly k}
    (h : ReprIntVec a v) (i : Usize) (hi : i.val < k) :
    Array.index_usize a i ⦃ x => ReprInt x v[i.val] ⦄ := by
  have hlt : i.val < a.val.length := by have := a.property; have := h.len; omega
  have e : a[i]? = some (a.val[i.val]'hlt) := by simp
  unfold Array.index_usize
  rw [e]
  simp only [WP.spec_ok]
  exact h.elt i.val hi

theorem ReprHintVec.index_spec' {K : Usize} {k : Nat} {a : Array (Array Bool 256#usize) K}
    {v : Vector HintPoly k} (h : ReprHintVec a v) (i : Usize) (hi : i.val < k) :
    Array.index_usize a i ⦃ x => ReprHint x v[i.val] ⦄ := by
  have hlt : i.val < a.val.length := by have := a.property; have := h.len; omega
  have e : a[i]? = some (a.val[i.val]'hlt) := by simp
  unfold Array.index_usize
  rw [e]
  simp only [WP.spec_ok]
  exact h.elt i.val hi

/-- `Array.index_usize` reads the `i`-th element (named result variant of `Array.index_usize_spec`). -/
theorem arr_index_spec {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val < a.val.length) :
    Array.index_usize a i ⦃ x => x = a.val[i.val] ⦄ := by
  have e : a[i]? = some (a.val[i.val]'h) := by simp
  unfold Array.index_usize
  rw [e]
  simp only [WP.spec_ok]

theorem vadd_getElem {α : Type} [Add α] {n : Nat} (x y : Vector α n) (i : Nat) (hi : i < n) :
    (x + y)[i] = x[i] + y[i] := by
  show (Vector.zipWith (· + ·) x y)[i] = _
  simp

theorem vsub_getElem {α : Type} [Sub α] {n : Nat} (x y : Vector α n) (i : Nat) (hi : i < n) :
    (x - y)[i] = x[i] - y[i] := by
  show (Vector.zipWith (· - ·) x y)[i] = _
  simp

theorem vneg_getElem {α : Type} [Neg α] {n : Nat} (x : Vector α n) (i : Nat) (hi : i < n) :
    (-x)[i] = -x[i] := by
  show (Vector.map (- ·) x)[i] = _
  simp

theorem vadd_getElem! {α : Type} [Add α] [Inhabited α] {n : Nat} (x y : Vector α n) (i : Nat) (hi : i < n) :
    (x + y)[i]! = x[i]! + y[i]! := by
  rw [vget! _ i hi, vget! x i hi, vget! y i hi, vadd_getElem _ _ _ hi]

theorem vsub_getElem! {α : Type} [Sub α] [Inhabited α] {n : Nat} (x y : Vector α n) (i : Nat) (hi : i < n) :
    (x - y)[i]! = x[i]! - y[i]! := by
  rw [vget! _ i hi, vget! x i hi, vget! y i hi, vsub_getElem _ _ _ hi]

theorem vneg_getElem! {α : Type} [Neg α] [Inhabited α] {n : Nat} (x : Vector α n) (i : Nat) (hi : i < n) :
    (-x)[i]! = -x[i]! := by
  rw [vget! _ i hi, vget! x i hi, vneg_getElem _ _ hi]

/-! ## `verify.scale_by_2d` and `verify.scale_vec_by_2d` -/

theorem scale_by_2d_loop_spec (t1 : Array U32 256#usize) (hb : ∀ x ∈ t1.val, x.val < 1024)
    (out : Array U32 256#usize) (j : Usize) (hj : j.val ≤ 256)
    (hinv : ∀ c, c < j.val → ∃ x y : U32, out.val[c]? = some x ∧ t1.val[c]? = some y ∧ x.val = y.val * 8192) :
    verify.scale_by_2d_loop t1 out j ⦃ o => ∀ c, c < 256 → ∃ x y : U32, o.val[c]? = some x ∧
      t1.val[c]? = some y ∧ x.val = y.val * 8192 ⦄ := by
  unfold verify.scale_by_2d_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ ∀ c, c < p.2.val → ∃ x y : U32, p.1.val[c]? = some x ∧
      t1.val[c]? = some y ∧ x.val = y.val * 8192)
  · rintro ⟨o, j⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [verify.scale_by_2d_loop.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := hj
      step*
      subst i_post2 a_post
      have hmem := hb _ (List.getElem_mem (l := t1.val) (n := j.val) (by simpa using i))
      have h13 : (2 : Nat) ^ 13 = 8192 := by norm_num
      have h32 : U32.size = 4294967296 := by simp [U32.size, U32.numBits]
      have e : i1.val = t1.val[j.val].val * 8192 := by
        rw [i1_post1, Nat.shiftLeft_eq, h13, h32]; omega
      refine ⟨by omega, fun c hc => ?_, by omega⟩
      rw [Array.set_val_eq, List.getElem?_set]
      by_cases hcj : j.val = c
      · subst hcj
        refine ⟨i1, t1.val[j.val], ?_, ?_, e⟩
        · rw [if_pos rfl, if_pos (by rw [len256 o]; omega)]
        · exact List.getElem?_eq_getElem (by simpa using i)
      · rw [if_neg hcj]
        exact h2 c (by omega)
    · rename_i hj
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨hj, hinv⟩

@[step]
theorem scale_by_2d_spec (sp : Spec.Params) (hd : sp.d = 13) (t1 : Array U32 256#usize) (v : RPoly)
    (hv : ReprInt t1 v) (hb : ∀ (c : Nat) (hc : c < 256), 0 ≤ v[c] ∧ v[c] < 1024) :
    verify.scale_by_2d t1 ⦃ r => Repr r ((RPoly.toZq v).map (· * (2 ^ sp.d : Zq))) ⦄ := by
  have hq : (Spec.q : Int) = 8380417 := rfl
  have hb' : ∀ x ∈ t1.val, x.val < 1024 := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
    have hc' : c < 256 := by simpa [len256 t1] using hc
    have h := hv.coeff c hc'
    have h2 := hb c hc'
    rw [hq] at h
    omega
  unfold verify.scale_by_2d
  step with scale_by_2d_loop_spec t1 hb' (Array.repeat 256#usize 0#u32) 0#usize (by simp)
    (fun c hc => absurd hc (by simp)) as ⟨o, ho⟩
  apply repr_of_get?
  intro c hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ho c hc
  have hlen := len256 t1
  have hyc : y = t1.val[c]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)] at hy
    exact (Option.some.inj hy).symm
  have hymem : y.val < 1024 := hb' y (by rw [hyc]; exact List.getElem_mem _)
  refine ⟨x, hx, by simp only [Spec.q]; omega, ?_⟩
  have hrc := hv.repr.coeff c hc
  have hmap : ((RPoly.toZq v).map (· * (2 ^ sp.d : Zq)))[c]! = (RPoly.toZq v)[c] * 2 ^ 13 := by
    rw [vget! _ c (by simpa using hc), Vector.getElem_map, hd]
  rw [hmap, hxy, Nat.cast_mul, hyc, hrc]
  norm_num

theorem scale_vec_loop_spec {N : Usize} {k : Nat} (sp : Spec.Params) (hd : sp.d = 13)
    (t1 : Array (Array U32 256#usize) N) (T1 : Vector RPoly k) (ht : ReprIntVec t1 T1)
    (hb : ∀ (r : Nat) (hr : r < k) (c : Nat) (hc : c < 256), 0 ≤ (T1[r]'hr)[c]'hc ∧ (T1[r]'hr)[c]'hc < 1024)
    (W : Vector Poly k) (hW : ∀ r (hr : r < k), W[r]! = (RPoly.toZq (T1[r]'hr)).map (· * (2 ^ sp.d : Zq)))
    (out : Array (Array U32 256#usize) N) (i : Usize) (hi : i.val ≤ N.val)
    (h : Rows out (fun r x => Repr x W[r]!) i.val) :
    verify.scale_vec_by_2d_loop t1 out i ⦃ o => Rows o (fun r x => Repr x W[r]!) N.val ⦄ := by
  have hN : N.val = k := ht.len
  unfold verify.scale_vec_by_2d_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) N × Usize) => N.val - p.2.val)
    (fun p => p.2.val ≤ N.val ∧ Rows p.1 (fun r x => Repr x W[r]!) p.2.val)
  · rintro ⟨o, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [verify.scale_vec_by_2d_loop.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < k := by omega
      step with ht.index_spec' i hik as ⟨a, ha⟩
      step with scale_by_2d_spec sp hd a T1[i.val] ha (hb i.val hik) as ⟨a1, ha1⟩
      step*
      subst a2_post
      have e : i1.val = i.val + 1 := by scalar_tac
      refine ⟨by omega, ?_, by omega⟩
      rw [e]
      refine h2.set i rfl ?_ a1 ?_
      · rw [o.property]; omega
      · rw [hW i.val hik]; exact ha1
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2
      exact h2
  · exact ⟨hi, h⟩

@[step]
theorem scale_vec_by_2d_spec {N : Usize} {k : Nat} (sp : Spec.Params) (hd : sp.d = 13)
    (t1 : Array (Array U32 256#usize) N) (T1 : Vector RPoly k) (ht : ReprIntVec t1 T1)
    (hb : ∀ (r : Nat) (hr : r < k) (c : Nat) (hc : c < 256), 0 ≤ (T1[r]'hr)[c]'hc ∧ (T1[r]'hr)[c]'hc < 1024) :
    verify.scale_vec_by_2d t1 ⦃ r =>
      ReprVec r ((T1.map RPoly.toZq).map (·.map (· * (2 ^ sp.d : Zq)))) ⦄ := by
  have hN : N.val = k := ht.len
  unfold verify.scale_vec_by_2d
  step with scale_vec_loop_spec sp hd t1 T1 ht hb ((T1.map RPoly.toZq).map (·.map (· * (2 ^ sp.d : Zq))))
    (fun r hr => by rw [vget! _ r (by simpa using hr)]; simp)
    (Array.repeat N (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) as ⟨o, ho⟩
  rw [hN] at ho
  exact ho.reprVec hN

/-! ## `verify.prefix_eq` -/

theorem u8_val_zero_iff (w : U8) : w.val = 0 ↔ w.bv = 0#_ := by
  show w.bv.toNat = 0 ↔ _
  rw [BitVec.toNat_eq]
  simp

theorem u8_bv_eq (x y : U8) : x.bv = y.bv ↔ x = y :=
  ⟨fun h => by cases x; cases y; simp_all, fun h => by rw [h]⟩

theorem u8_or_xor_zero (d x y z w : U8) (h1 : z.bv = d.bv ||| w.bv) (h2 : w.bv = x.bv ^^^ y.bv) :
    z.val = 0 ↔ d.val = 0 ∧ x = y := by
  constructor
  · intro h
    have h0 := (u8_val_zero_iff z).1 h
    obtain ⟨hd0, hw0⟩ := BitVec.or_eq_zero_iff.1 (h1.symm.trans h0)
    exact ⟨(u8_val_zero_iff d).2 hd0,
      (u8_bv_eq x y).1 (BitVec.xor_eq_zero_iff.1 (h2.symm.trans hw0))⟩
  · rintro ⟨hd, rfl⟩
    apply (u8_val_zero_iff z).2
    have hd0 := (u8_val_zero_iff d).1 hd
    rw [h1, h2, BitVec.xor_self, hd0]
    simp

theorem u8_eq_zero_iff (d : U8) : d = 0#u8 ↔ d.val = 0 :=
  ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by simpa using h)⟩

theorem take_eq_iff {α : Type} (l m : List α) (n : Nat) :
    l.take n = m.take n ↔ ∀ c, c < n → l[c]? = m[c]? := by
  constructor
  · intro h c hc
    have := congrArg (fun x => x[c]?) h
    simpa [List.getElem?_take, hc] using this
  · intro h
    apply List.ext_getElem?
    intro c
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hc
    · exact h c hc
    · rfl

theorem prefix_eq_loop_spec (a b : Array U8 64#usize) (len : Usize) (hlen : len.val ≤ 64)
    (diff : U8) (i : Usize) (hi : i.val ≤ len.val)
    (hinv : diff.val = 0 ↔ ∀ c, c < i.val → a.val[c]? = b.val[c]?) :
    verify.prefix_eq_loop a b len diff i ⦃ d => d.val = 0 ↔ ∀ c, c < len.val → a.val[c]? = b.val[c]? ⦄ := by
  unfold verify.prefix_eq_loop
  apply loop.spec_decr_nat
    (fun (p : U8 × Usize) => len.val - p.2.val)
    (fun p => p.2.val ≤ len.val ∧ (p.1.val = 0 ↔ ∀ c, c < p.2.val → a.val[c]? = b.val[c]?))
  · rintro ⟨d, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [verify.prefix_eq_loop.body]
    split
    · rename_i hj
      have hj' : i.val < len.val := hj
      step*
      subst i1_post2 i2_post2
      have hx : diff1.val = 0 ↔ d.val = 0 ∧ a.val[i.val] = b.val[i.val] := by
        exact u8_or_xor_zero d _ _ diff1 i3 diff1_post2 i3_post2
      have hcc : (∀ c, c < i.val + 1 → a.val[c]? = b.val[c]?) ↔
          (∀ c, c < i.val → a.val[c]? = b.val[c]?) ∧ a.val[i.val]? = b.val[i.val]? :=
        ⟨fun h => ⟨fun c hc => h c (by omega), h _ (by omega)⟩, fun ⟨h, h'⟩ c hc => by
          by_cases e : c = i.val
          · subst e; exact h'
          · exact h c (by omega)⟩
      have hai : a.val[i.val]? = some a.val[i.val] := List.getElem?_eq_getElem i1
      have hbi : b.val[i.val]? = some b.val[i.val] := List.getElem?_eq_getElem i2
      refine ⟨by omega, ?_, by omega⟩
      rw [i4_post, hcc, hai, hbi, ← h2, hx]
      simp
    · rename_i hj
      simp only [WP.spec_ok]
      have : i.val = len.val := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨hi, hinv⟩

theorem bytesA_take_eq_iff {n : Usize} (a b : Array U8 n) (m : Nat) :
    (bytesA a).take m = (bytesA b).take m ↔ ∀ c, c < m → a.val[c]? = b.val[c]? := by
  rw [take_eq_iff]
  unfold bytesA
  refine forall_congr' fun c => imp_congr_right fun _ => ?_
  rw [List.getElem?_map, List.getElem?_map]
  exact (Option.map_injective ofNat_val_injective).eq_iff

@[step]
theorem prefix_eq_spec (a b : Array U8 64#usize) (len : Usize) (hlen : len.val ≤ 64) :
    verify.prefix_eq a b len ⦃ r =>
      r = decide ((bytesA a).take len.val = (bytesA b).take len.val) ⦄ := by
  unfold verify.prefix_eq
  step with prefix_eq_loop_spec a b len hlen 0#u8 0#usize (by simp)
    (by simp) as ⟨d, hd⟩
  simp only [decide_eq_decide]
  rw [bytesA_take_eq_iff, u8_eq_zero_iff]
  exact hd

/-! ## `api.ctx_prefix` -/

theorem ctx_prefix_loop_spec (ctx : Slice U8) (hctx : ctx.val.length ≤ 255)
    (pre0 pre : Array U8 257#usize) (i : Usize) (hi : i.val ≤ ctx.val.length)
    (hinv : ∀ k, pre.val[k]? = if 2 ≤ k ∧ k < 2 + i.val then ctx.val[k - 2]? else pre0.val[k]?) :
    api.ctx_prefix_loop ctx pre i ⦃ o => ∀ k, o.val[k]? =
      if 2 ≤ k ∧ k < 2 + ctx.val.length then ctx.val[k - 2]? else pre0.val[k]? ⦄ := by
  unfold api.ctx_prefix_loop
  apply loop.spec_decr_nat
    (fun (p : Array U8 257#usize × Usize) => ctx.val.length - p.2.val)
    (fun p => p.2.val ≤ ctx.val.length ∧
      ∀ k, p.1.val[k]? = if 2 ≤ k ∧ k < 2 + p.2.val then ctx.val[k - 2]? else pre0.val[k]?)
  · rintro ⟨d, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [api.ctx_prefix_loop.body]
    split
    · rename_i hj
      have hj' : i.val < ctx.val.length := by simpa using hj
      step*
      refine ⟨by omega, fun k => ?_, by omega⟩
      rw [a_post, i2_post2, Array.set_val_eq, List.getElem?_set, i3_post, i4_post]
      by_cases hk : 2 + i.val = k
      · subst hk
        have hl : 2 + i.val < d.val.length := by rw [d.property]; simp; omega
        rw [if_pos rfl, if_pos hl, if_pos (by omega)]
        have : 2 + i.val - 2 = i.val := by omega
        rw [this]
        exact (List.getElem?_eq_getElem (by simpa using i2)).symm
      · rw [if_neg hk, h2 k]
        by_cases c1 : 2 ≤ k ∧ k < 2 + i.val
        · rw [if_pos c1, if_pos (by omega)]
        · rw [if_neg c1, if_neg (by omega)]
    · rename_i hj
      simp only [WP.spec_ok]
      have : i.val = ctx.val.length := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨hi, hinv⟩


open HintAux

theorem response_inner_spec {L : Usize} {ℓ : Nat} (y cs1 : Array (Array U32 256#usize) L)
    (Y CS : Vector Poly ℓ)
    (hy : ReprVec y Y) (hcs : ReprVec cs1 CS) (i : Usize) (hi : i.val < ℓ)
    (z0 z : Array (Array U32 256#usize) L) (j : Usize) (hj : j.val ≤ 256)
    (hz0 : ∀ r, r ≠ i.val → z.val[r]? = z0.val[r]?)
    (hrow : ∃ row : Array U32 256#usize, z.val[i.val]? = some row ∧ ∀ c, c < j.val → ∃ x : U32,
      row.val[c]? = some x ∧ x.val < Spec.q ∧ ((x.val : Nat) : Zq) = (Y[i.val]!)[c]! + (CS[i.val]!)[c]!) :
    sign.response_loop0_loop0 y cs1 z i j ⦃ o => (∀ r, r ≠ i.val → o.val[r]? = z0.val[r]?) ∧
      ∃ row : Array U32 256#usize, o.val[i.val]? = some row ∧ ∀ c, c < 256 → ∃ x : U32,
      row.val[c]? = some x ∧ x.val < Spec.q ∧ ((x.val : Nat) : Zq) = (Y[i.val]!)[c]! + (CS[i.val]!)[c]! ⦄ := by
  have hL : L.val = ℓ := hy.len
  unfold sign.response_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ r, r ≠ i.val → p.1.val[r]? = z0.val[r]?) ∧
      ∃ row : Array U32 256#usize, p.1.val[i.val]? = some row ∧ ∀ c, c < p.2.val → ∃ x : U32,
      row.val[c]? = some x ∧ x.val < Spec.q ∧ ((x.val : Nat) : Zq) = (Y[i.val]!)[c]! + (CS[i.val]!)[c]!)
  · rintro ⟨z, j⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [sign.response_loop0_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := hj
      step with hy.index_spec i hi as ⟨a, ha⟩
      have hl1 : j.val < a.val.length := by rw [len256 a]; exact hj'
      step with arr_index_spec a j hl1 as ⟨x1, hx1e⟩
      step with hcs.index_spec i hi as ⟨a1, ha1⟩
      have hl2 : j.val < a1.val.length := by rw [len256 a1]; exact hj'
      step with arr_index_spec a1 j hl2 as ⟨x2, hx2e⟩
      have hq1 : x1.val < 8380417 := by rw [hx1e]; exact canon_get ha.canon hl1
      have hq2 : x2.val < 8380417 := by rw [hx2e]; exact canon_get ha1.canon hl2
      step with add_zmod x1 x2 hq1 hq2 as ⟨i3, hi3a, hi3b⟩
      step*
      obtain ⟨row, hrow, hc⟩ := h3
      subst a2_post2 a3_post a2_post3
      have hzi : z.val[i.val] = row := by
        have := List.getElem?_eq_getElem (l := z.val) (i := i.val) (by simpa using a2_post1)
        rw [this] at hrow; exact Option.some.inj hrow
      rw [hzi]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · intro r hr
        rw [Array.set_val_eq, List.getElem?_set, if_neg (by omega)]
        exact h2 r hr
      · refine ⟨row.set j i3, ?_, ?_⟩
        · rw [Array.set_val_eq, List.getElem?_set, if_pos rfl, if_pos (by simpa using a2_post1)]
        · intro c hc'
          rw [Array.set_val_eq, List.getElem?_set]
          by_cases hcj : j.val = c
          · subst hcj
            refine ⟨i3, ?_, hi3a, ?_⟩
            · rw [if_pos rfl, if_pos (by rw [len256 row]; exact hj')]
            · rw [hi3b, hx1e, hx2e]
              have e1 := ha.coeff j.val hj'
              have e2 := ha1.coeff j.val hj'
              rw [e1, e2, vget! Y i.val (by omega), vget! CS i.val (by omega), vget! Y[i.val] j.val hj',
                vget! CS[i.val] j.val hj']
          · rw [if_neg hcj]
            exact hc c (by omega)
    · rename_i hj
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      obtain ⟨row, hrow, hc⟩ := h3
      rw [this] at hc
      exact ⟨h2, row, hrow, hc⟩
  · exact ⟨hj, hz0, hrow⟩

theorem response_outer_spec {L : Usize} {ℓ : Nat} (y cs1 : Array (Array U32 256#usize) L)
    (Y CS : Vector Poly ℓ) (hy : ReprVec y Y) (hcs : ReprVec cs1 CS)
    (z : Array (Array U32 256#usize) L) (i : Usize) (hi : i.val ≤ L.val)
    (h : Rows z (fun r x => Repr x (Y + CS)[r]!) i.val) :
    sign.response_loop0 y cs1 z i ⦃ o => Rows o (fun r x => Repr x (Y + CS)[r]!) L.val ⦄ := by
  have hL : L.val = ℓ := hy.len
  unfold sign.response_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Usize) => L.val - p.2.val)
    (fun p => p.2.val ≤ L.val ∧ Rows p.1 (fun r x => Repr x (Y + CS)[r]!) p.2.val)
  · rintro ⟨z, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sign.response_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < L.val := hi
      have hik : i.val < ℓ := by omega
      have hzl : i.val < z.val.length := by rw [z.property]; exact hi'
      step with response_inner_spec y cs1 Y CS hy hcs i hik z z 0#usize (by simp) (fun r _ => rfl)
        ⟨z.val[i.val], List.getElem?_eq_getElem hzl, fun c hc => absurd hc (by simp)⟩
          as ⟨z1, hrest, row, hrow, hfull⟩
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro r hr
      by_cases hri : r = i.val
      · subst hri
        refine ⟨row, hrow, ?_⟩
        apply repr_of_get?
        intro c hc
        obtain ⟨x, hx, hxq, hxe⟩ := hfull c hc
        refine ⟨x, hx, hxq, ?_⟩
        rw [hxe, vadd_getElem! _ _ _ hik, vadd_getElem! _ _ _ hc]
      · rw [hrest r hri]
        exact h2 r (by omega)
    · rename_i hi
      have hi' : i.val = L.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2
      exact h2
  · exact ⟨hi, h⟩

theorem lowBitsVec_getElem! (sp : Spec.Params) {k : Nat} (X : Vector Poly k) (i : Nat) (hi : i < k) :
    (LowBitsVec sp X)[i]! = (X[i]!).map (LowBits sp) := by
  rw [vget! _ i hi, vget! X i hi]
  simp [Spec.LowBitsVec]

theorem power2roundVec_fst_getElem! (sp : Spec.Params) {k : Nat} (X : Vector Poly k) (i : Nat) (hi : i < k) :
    ((Power2RoundVec sp X).1)[i]! = (X[i]!).map (fun c => (Power2Round sp c).1) := by
  rw [vget! _ i hi, vget! X i hi]
  simp [Spec.Power2RoundVec]

theorem power2roundVec_snd_getElem! (sp : Spec.Params) {k : Nat} (X : Vector Poly k) (i : Nat) (hi : i < k) :
    ((Power2RoundVec sp X).2)[i]! = (X[i]!).map (fun c => (Power2Round sp c).2) := by
  rw [vget! _ i hi, vget! X i hi]
  simp [Spec.Power2RoundVec]

theorem nttInvVec_getElem! {k : Nat} (X : Vector Poly k) (i : Nat) (hi : i < k) :
    (NTTInvVec X)[i]! = NTTInv (X[i]!) := by
  rw [vget! _ i hi, vget! X i hi]
  simp [Spec.NTTInvVec]

theorem response_loop1_spec {K L : Usize} {k : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp)
    (w cs2 : Array (Array U32 256#usize) K) (W CS2 : Vector Poly k) (hw : ReprVec w W)
    (hcs : ReprVec cs2 CS2)
    (wc r0 : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ K.val)
    (h1 : Rows wc (fun r x => Repr x (W - CS2)[r]!) i.val)
    (h0 : Rows r0 (fun r x => ReprInt x (LowBitsVec sp (W - CS2))[r]!) i.val) :
    sign.response_loop1 ip w cs2 wc r0 i ⦃ o => Rows o.1 (fun r x => Repr x (W - CS2)[r]!) K.val ∧
      Rows o.2 (fun r x => ReprInt x (LowBitsVec sp (W - CS2))[r]!) K.val ⦄ := by
  have hN : K.val = k := hw.len
  unfold sign.response_loop1
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Array (Array U32 256#usize) K × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ Rows p.1 (fun r x => Repr x (W - CS2)[r]!) p.2.2.val ∧
      Rows p.2.1 (fun r x => ReprInt x (LowBitsVec sp (W - CS2))[r]!) p.2.2.val)
  · rintro ⟨wc, r0, i⟩ ⟨hi1, h2, h3⟩
    dsimp only at hi1 h2 h3
    simp only [sign.response_loop1.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      have hl : i.val < wc.val.length := by rw [wc.property]; exact hi'
      have hl0 : i.val < r0.val.length := by rw [r0.property]; exact hi'
      step with hw.index_spec i hik as ⟨a, ha⟩
      step with hcs.index_spec i hik as ⟨a1, ha1⟩
      step with sub_poly_spec a a1 _ _ ha ha1 as ⟨a2, ha2⟩
      step as ⟨wc1, hwc1⟩
      step with arr_index_spec wc1 i (by rw [hwc1, Array.set_val_eq, List.length_set]; exact hl) as ⟨a3, ha3⟩
      have ha3e : a3 = a2 := by
        rw [ha3]; subst hwc1; simp [Array.set_val_eq, List.getElem_set]
      step with poly_low_bits_spec hp hg a3 (W[i.val] - CS2[i.val]) (by rw [ha3e]; exact ha2) as ⟨a4, ha4, _⟩
      step*
      have e : i1.val = i.val + 1 := i1_post
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hwc1, e]
        refine h2.set i rfl hl a2 ?_
        rw [vsub_getElem! _ _ _ hik, vget! W _ hik, vget! CS2 _ hik]; exact ha2
      · rw [a5_post, e]
        refine h3.set i rfl hl0 a4 ?_
        rw [lowBitsVec_getElem! sp _ _ hik, vsub_getElem! _ _ _ hik, vget! W _ hik, vget! CS2 _ hik]
        exact ha4
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2 h3
      exact ⟨h2, h3⟩
  · exact ⟨hi, h1, h0⟩

@[step]
theorem response_spec {K L : Usize} {k ℓ : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp)
    (y : Array (Array U32 256#usize) L) (Y : Vector Poly ℓ) (hy : ReprVec y Y)
    (c_hat : Array U32 256#usize) (C : Poly) (hc : Repr c_hat C)
    (s1_hat : Array (Array U32 256#usize) L) (S1 : Vector Poly ℓ) (hs1 : ReprVec s1_hat S1)
    (s2_hat : Array (Array U32 256#usize) K) (S2 : Vector Poly k) (hs2 : ReprVec s2_hat S2)
    (w : Array (Array U32 256#usize) K) (W : Vector Poly k) (hw : ReprVec w W) :
    sign.response ip y c_hat s1_hat s2_hat w ⦃ r =>
      ReprVec r.1 (Y + NTTInvVec (ScalarVectorNTT C S1)) ∧
      ReprVec r.2.1 (W - NTTInvVec (ScalarVectorNTT C S2)) ∧
      ReprIntVec r.2.2 (LowBitsVec sp (W - NTTInvVec (ScalarVectorNTT C S2))) ⦄ := by
  unfold sign.response
  step with scalar_vector_ntt_inverse_spec c_hat C hc s1_hat S1 hs1 as ⟨cs1, hcs1⟩
  step with scalar_vector_ntt_inverse_spec c_hat C hc s2_hat S2 hs2 as ⟨cs2, hcs2⟩
  step with response_outer_spec y cs1 Y _ hy hcs1 (Array.repeat L (Array.repeat 256#usize 0#u32)) 0#usize
    (by simp) (Rows.zero _ _) as ⟨z1, hz1⟩
  step with response_loop1_spec ip sp hp hg w cs2 W _ hw hcs2 (Array.repeat K (Array.repeat 256#usize 0#u32))
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) (Rows.zero _ _)
  have hL : L.val = ℓ := hy.len
  have hK : K.val = k := hw.len
  rw [hL] at hz1
  rw [hK] at w_cs21_post1 w_cs21_post2
  exact ⟨hz1.reprVec hL, w_cs21_post1.reprVec hK, w_cs21_post2.reprIntVec hK⟩

theorem power2round_range (sp : Spec.Params) (hd : sp.d = 13) (c : Zq) :
    0 ≤ (Spec.Power2Round sp c).1 ∧ (Spec.Power2Round sp c).1 ≤ 1023 ∧
    -4095 ≤ (Spec.Power2Round sp c).2 ∧ (Spec.Power2Round sp c).2 ≤ 4096 := by
  haveI : NeZero Spec.q := ⟨by decide⟩
  rw [Power2Round_eq, hd]
  have hc1 : (c.val : Int) < 8380417 := by exact_mod_cast ZMod.val_lt c
  have hc0 : (0 : Int) ≤ c.val := Int.natCast_nonneg _
  have hm := modPM_cases (c.val : Int) (2 ^ 13)
  generalize (c.val : Int) = x at hm hc0 hc1 ⊢
  have h8 : (2 : Nat) ^ 13 = 8192 := by norm_num
  have h8' : (2 : Int) ^ 13 = 8192 := by norm_num
  simp only [h8, h8'] at hm ⊢
  norm_num at hm
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega

theorem vec_power2round_loop_spec {K : Usize} {k : Nat} (sp : Spec.Params) (hd : sp.d = 13)
    (t : Array (Array U32 256#usize) K) (V : Vector Poly k) (ht : ReprVec t V)
    (t1 t0 : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ K.val)
    (h1 : Rows t1 (fun r x => ReprInt x ((Power2RoundVec sp V).1)[r]!) i.val)
    (h0 : Rows t0 (fun r x => ReprInt x ((Power2RoundVec sp V).2)[r]!) i.val) :
    keygen.vec_power2round_loop t t1 t0 i ⦃ o =>
      Rows o.1 (fun r x => ReprInt x ((Power2RoundVec sp V).1)[r]!) K.val ∧
      Rows o.2 (fun r x => ReprInt x ((Power2RoundVec sp V).2)[r]!) K.val ⦄ := by
  have hN : K.val = k := ht.len
  unfold keygen.vec_power2round_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Array (Array U32 256#usize) K × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ Rows p.1 (fun r x => ReprInt x ((Power2RoundVec sp V).1)[r]!) p.2.2.val ∧
      Rows p.2.1 (fun r x => ReprInt x ((Power2RoundVec sp V).2)[r]!) p.2.2.val)
  · rintro ⟨t1, t0, i⟩ ⟨hi1, h2, h3⟩
    dsimp only at hi1 h2 h3
    simp only [keygen.vec_power2round_loop.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      have hl : i.val < t1.val.length := by rw [t1.property]; exact hi'
      have hl0 : i.val < t0.val.length := by rw [t0.property]; exact hi'
      step with ht.index_spec i hik as ⟨a, ha⟩
      step with poly_power2round_spec (sp := sp) hd a V[i.val] ha as ⟨a1, b, hr1, hr2, hr3⟩
      step*
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [a2_post, i1_post]
        refine h2.set i rfl hl a1 ?_
        rw [power2roundVec_fst_getElem! sp V _ hik, vget! V _ hik]; exact hr1
      · rw [a3_post, i1_post]
        refine h3.set i rfl hl0 b ?_
        rw [power2roundVec_snd_getElem! sp V _ hik, vget! V _ hik]; exact hr2
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2 h3
      exact ⟨h2, h3⟩
  · exact ⟨hi, h1, h0⟩

@[step]
theorem vec_power2round_spec {K : Usize} {k : Nat} (sp : Spec.Params) (hd : sp.d = 13)
    (t : Array (Array U32 256#usize) K) (V : Vector Poly k) (ht : ReprVec t V) :
    keygen.vec_power2round t ⦃ r =>
      ReprIntVec r.1 (Power2RoundVec sp V).1 ∧ ReprIntVec r.2 (Power2RoundVec sp V).2 ⦄ := by
  have hK : K.val = k := ht.len
  unfold keygen.vec_power2round
  step with vec_power2round_loop_spec sp hd t V ht (Array.repeat K (Array.repeat 256#usize 0#u32))
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) (Rows.zero _ _)
  rw [hK] at r_post1 r_post2
  exact ⟨r_post1.reprIntVec hK, r_post2.reprIntVec hK⟩

theorem power2roundVec_range (sp : Spec.Params) (hd : sp.d = 13) {k : Nat} (V : Vector Poly k) :
    (∀ (r : Nat) (hr : r < k) (c : Nat) (hc : c < 256),
      0 ≤ (((Power2RoundVec sp V).1)[r]'hr)[c]'hc ∧ (((Power2RoundVec sp V).1)[r]'hr)[c]'hc ≤ 1023) ∧
    (∀ (r : Nat) (hr : r < k) (c : Nat) (hc : c < 256),
      -4095 ≤ (((Power2RoundVec sp V).2)[r]'hr)[c]'hc ∧ (((Power2RoundVec sp V).2)[r]'hr)[c]'hc ≤ 4096) := by
  constructor
  · intro r hr c hc
    have := power2round_range sp hd ((V[r]'hr)[c]'hc)
    simp only [Spec.Power2RoundVec, Vector.getElem_map]
    exact ⟨this.1, this.2.1⟩
  · intro r hr c hc
    have := power2round_range sp hd ((V[r]'hr)[c]'hc)
    simp only [Spec.Power2RoundVec, Vector.getElem_map]
    exact ⟨this.2.2.1, this.2.2.2⟩

theorem compute_t_loop_spec {K : Usize} {k : Nat} (s2 prod : Array (Array U32 256#usize) K)
    (S2 PV : Vector Poly k) (hs2 : ReprVec s2 S2) (hprod : ReprVec prod PV)
    (t : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ K.val)
    (h : Rows t (fun r x => Repr x (NTTInvVec PV + S2)[r]!) i.val) :
    keygen.compute_t_loop s2 prod t i ⦃ o => Rows o (fun r x => Repr x (NTTInvVec PV + S2)[r]!) K.val ⦄ := by
  have hN : K.val = k := hs2.len
  unfold keygen.compute_t_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Usize) => K.val - p.2.val)
    (fun p => p.2.val ≤ K.val ∧ Rows p.1 (fun r x => Repr x (NTTInvVec PV + S2)[r]!) p.2.val)
  · rintro ⟨t, i⟩ ⟨hi1, h2⟩
    dsimp only at hi1 h2
    simp only [keygen.compute_t_loop.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      have hl : i.val < t.val.length := by rw [t.property]; exact hi'
      step with hprod.index_spec i hik as ⟨a, ha⟩
      step with ntt_inverse_spec a ha.canon as ⟨a1, ha1, ha2⟩
      step with hs2.index_spec i hik as ⟨a2, ha2'⟩
      step with add_poly_add_spec a1 a2 (NTTInv PV[i.val]) S2[i.val] ⟨ha1, by rw [ha2, ha.eq]⟩ ha2' as ⟨a3, ha3⟩
      step*
      have e : i1.val = i.val + 1 := i1_post
      refine ⟨by omega, ?_, by omega⟩
      rw [a4_post, e]
      refine h2.set i rfl hl a3 ?_
      rw [vadd_getElem! _ _ _ hik, nttInvVec_getElem! _ _ hik, vget! PV _ hik, vget! S2 _ hik]
      exact ha3
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2
      exact h2
  · exact ⟨hi, h⟩

@[step]
theorem compute_t_spec {K L : Usize} {k ℓ : Nat}
    (a_hat : Array (Array (Array U32 256#usize) L) K) (M : Vector (Vector Poly ℓ) k) (hM : ReprMat a_hat M)
    (s1_hat : Array (Array U32 256#usize) L) (S1 : Vector Poly ℓ) (hs1 : ReprVec s1_hat S1)
    (s2 : Array (Array U32 256#usize) K) (S2 : Vector RPoly k) (hs2 : ReprIntVec s2 S2) :
    keygen.compute_t a_hat s1_hat s2 ⦃ t =>
      ReprVec t (NTTInvVec (MatrixVectorNTT M S1) + S2.map RPoly.toZq) ⦄ := by
  have hK : K.val = k := hM.len
  unfold keygen.compute_t
  step with matrix_vector_ntt_spec a_hat M hM s1_hat S1 hs1 as ⟨prod, hprod⟩
  step with compute_t_loop_spec s2 prod (S2.map RPoly.toZq) _ hs2.repr hprod
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) as ⟨t, ht⟩
  rw [hK] at ht
  exact ht.reprVec hK

@[step]
theorem ctx_prefix_spec (ctx : Slice U8) :
    api.ctx_prefix ctx ⦃ r => match r with
      | none => 255 < ctx.val.length
      | some a => ctx.val.length ≤ 255 ∧
          (bytesA a).take (2 + ctx.val.length) = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx ∧
          (bytesA a).drop (2 + ctx.val.length) = List.replicate (255 - ctx.val.length) 0 ⦄ := by
  unfold api.ctx_prefix
  dsimp only
  split
  · rename_i h
    simp only [WP.spec_ok]
    scalar_tac
  · rename_i h
    have hlen : ctx.val.length ≤ 255 := by scalar_tac
    step*
    step with ctx_prefix_loop_spec ctx hlen a a 0#usize (by simp)
      (fun k => by rw [if_neg (by intro hh; have : (0#usize).val = 0 := rfl; omega)]) as ⟨o, ho⟩
    have hi2 : i2.val = ctx.val.length := by
      rw [i2_post]
      have := UScalar.cast_val_eq (src_ty := UScalarTy.Usize) (tgt_ty := UScalarTy.U8) ctx.len
      rw [this]
      have : ctx.len.val = ctx.val.length := by simp
      rw [this]
      exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; omega)
    have ha : ∀ k, a.val[k]? = if k = 1 then some i2 else if k < 257 then some 0#u8 else none := by
      intro k
      rw [a_post, prefix1_post]
      have hrep : ∀ k, (Array.repeat 257#usize (0#u8)).val[k]? = if k < 257 then some 0#u8 else none := by
        intro k
        show (List.replicate 257 0#u8)[k]? = _
        rw [List.getElem?_replicate]
      simp only [Array.set_val_eq, List.getElem?_set, hrep]
      by_cases h1 : k = 1
      · subst h1; simp
      by_cases h0 : k = 0
      · subst h0; simp
      have h1' : ¬ 1 = k := fun h => h1 h.symm
      have h0' : ¬ 0 = k := fun h => h0 h.symm
      simp [h0', h1', h1]
    have hb : ∀ k, (bytesA o)[k]? = (if 2 ≤ k ∧ k < 2 + ctx.val.length then ctx.val[k-2]?
        else a.val[k]?).map (fun x => UInt8.ofNat x.val) := by
      intro k; unfold bytesA; rw [List.getElem?_map, ho k]
    refine ⟨hlen, ?_, ?_⟩
    · apply List.ext_getElem?
      intro k
      rw [List.getElem?_take, hb k]
      by_cases hk : k < 2 + ctx.val.length
      · rw [if_pos hk]
        by_cases hk2 : 2 ≤ k
        · rw [if_pos ⟨hk2, hk⟩]
          have : ([0, UInt8.ofNat ctx.val.length] ++ bytes ctx)[k]? = (bytes ctx)[k-2]? := by
            rw [List.getElem?_append_right (by simp; omega)]; simp
          rw [this]; unfold bytes; rw [List.getElem?_map]
        · rw [if_neg (by omega), ha k]
          rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
          · simp
          · simp [hi2]
      · rw [if_neg hk]
        have : ([0, UInt8.ofNat ctx.val.length] ++ bytes ctx)[k]? = none := by
          rw [List.getElem?_eq_none]; simp [bytes]; omega
        rw [this]
    · apply List.ext_getElem?
      intro k
      rw [List.getElem?_drop, hb, List.getElem?_replicate]
      rw [if_neg (by omega), ha]
      by_cases hk : k < 255 - ctx.val.length
      · rw [if_neg (by omega), if_pos (by omega), if_pos hk]; simp
      · rw [if_neg hk]
        split_ifs <;> simp_all <;> omega

theorem len256_bool (w : Array Bool 256#usize) : w.val.length = 256 := w.property

theorem cntFrom_le (row : HintPoly) (j : Nat) : cntFrom row j ≤ 256 := by
  unfold cntFrom
  calc _ ≤ (row.toList.drop j).length := List.countP_le_length
    _ ≤ 256 := by simp

theorem restW_le {k : Nat} (h : Vector HintPoly k) : ∀ n i, k - i = n → restW h i ≤ 256 * n := by
  intro n
  induction n with
  | zero =>
    intro i hi
    unfold restW
    rw [List.drop_of_length_le (by simp; omega)]
    simp
  | succ n ih =>
    intro i hi
    rw [restW_succ h i (by omega)]
    have := cntFrom_le h[i]! 0
    have := ih (i + 1) (by omega)
    omega

theorem hint_inner_spec {K L : Usize} {k : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (hK : sp.k ≤ 2 ^ 20)
    (w_cs2 ct0 : Array (Array U32 256#usize) K) (WC CT : Vector Poly k) (hw : ReprVec w_cs2 WC)
    (hct : ReprVec ct0 CT) (H : Vector HintPoly k) (i : Usize) (hik : i.val < k)
    (hH : ∀ c, c < 256 → (H[i.val]!)[c]! =
      MakeHint sp (-(CT[i.val]!)[c]!) ((WC[i.val]!)[c]! + (CT[i.val]!)[c]!))
    (hint0 hint : Array (Array Bool 256#usize) K) (ones : Usize) (j : Usize) (hj : j.val ≤ 256)
    (hz0 : ∀ r, r ≠ i.val → hint.val[r]? = hint0.val[r]?)
    (hrow : ∃ row : Array Bool 256#usize, hint.val[i.val]? = some row ∧
      ∀ c, c < j.val → row.val[c]? = some (H[i.val]!)[c]!)
    (hones : ones.val + cntFrom (H[i.val]!) j.val + restW H (i.val + 1) = restW H 0) :
    sign.hint_step_loop0_loop0 ip w_cs2 ct0 hint ones i j ⦃ o => (∀ r, r ≠ i.val → o.1.val[r]? = hint0.val[r]?) ∧
      (∃ row : Array Bool 256#usize, o.1.val[i.val]? = some row ∧
        ∀ c, c < 256 → row.val[c]? = some (H[i.val]!)[c]!) ∧
      o.2.val + restW H (i.val + 1) = restW H 0 ⦄ := by
  have hN : K.val = k := hw.len
  unfold sign.hint_step_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array Bool 256#usize) K × Usize × Usize) => 256 - p.2.2.val)
    (fun p => p.2.2.val ≤ 256 ∧ (∀ r, r ≠ i.val → p.1.val[r]? = hint0.val[r]?) ∧
      (∃ row : Array Bool 256#usize, p.1.val[i.val]? = some row ∧
        ∀ c, c < p.2.2.val → row.val[c]? = some (H[i.val]!)[c]!) ∧
      p.2.1.val + cntFrom (H[i.val]!) p.2.2.val + restW H (i.val + 1) = restW H 0)
  · rintro ⟨hint, ones, j⟩ ⟨hj1, h2, h3, h4⟩
    dsimp only at hj1 h2 h3 h4
    simp only [sign.hint_step_loop0_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := hj
      have hl1 : j.val < 256 := hj'
      step with hct.index_spec i hik as ⟨a, ha⟩
      have hla : j.val < a.val.length := by rw [len256 a]; exact hj'
      step with arr_index_spec a j hla as ⟨x1, hx1⟩
      have hq1 : x1.val < 8380417 := by rw [hx1]; exact canon_get ha.canon hla
      step with neg_zmod x1 hq1 as ⟨i2, hi2a, hi2b⟩
      step with hw.index_spec i hik as ⟨a1, ha1⟩
      have hla1 : j.val < a1.val.length := by rw [len256 a1]; exact hj'
      step with arr_index_spec a1 j hla1 as ⟨x2, hx2⟩
      have hq2 : x2.val < 8380417 := by rw [hx2]; exact canon_get ha1.canon hla1
      step with arr_index_spec a j hla as ⟨x3, hx3⟩
      have hq3 : x3.val < 8380417 := by rw [hx3]; exact canon_get ha.canon hla
      step with add_zmod x2 x3 hq2 hq3 as ⟨i5, hi5a, hi5b⟩
      step with make_hint_spec hp hg i2 i5 hi2a hi5a as ⟨b, hb⟩
      have hbnd : ones.val ≤ 256 * 2 ^ 20 := by
        have e1 := restW_le H k 0 (by omega)
        have e2 : k = sp.k := by rw [← hN, hp.K_eq]
        have := hK
        omega
      have hcs := cntFrom_succ (H[i.val]!) j.val hj'
      step*
      · have key : ∀ z : Bool, ones.val + z.toNat ≤ Usize.max := fun z => by
          have := Bool.toNat_le z
          have hm : 4294967295 ≤ Usize.max := by scalar_tac
          omega
        rw [i6_post]; exact key _
      have hCT : ((x1.val : Nat) : Zq) = (CT[i.val]!)[j.val]! := by
        rw [hx1, vget! CT _ hik, vget! _ j.val hj']; exact ha.coeff j.val hj'
      have hCT3 : ((x3.val : Nat) : Zq) = (CT[i.val]!)[j.val]! := by
        rw [hx3, vget! CT _ hik, vget! _ j.val hj']; exact ha.coeff j.val hj'
      have hWC : ((x2.val : Nat) : Zq) = (WC[i.val]!)[j.val]! := by
        rw [hx2, vget! WC _ hik, vget! _ j.val hj']; exact ha1.coeff j.val hj'
      have hbH : b = (H[i.val]!)[j.val]! := by
        rw [hb, hi2b, hi5b, hCT, hWC, hCT3]; exact (hH j.val hj').symm
      obtain ⟨row, hrow', hc⟩ := h3
      have hli : i.val < hint.val.length := by rw [hint.property]; omega
      have hzi : hint.val[i.val] = row := by
        have := List.getElem?_eq_getElem (l := hint.val) (i := i.val) hli
        rw [this] at hrow'; exact Option.some.inj hrow'
      simp only [b1_post2, a4_post2, a2_post3, a3_post, a2_post2, hzi] at i6_post
      rw [a2_post3, a3_post, a2_post2, hzi]
      have hi6 : i6.val = (if b = true then 1 else 0) := by
        rw [i6_post]
        simp [Array.set_val_eq]
        cases b <;> simp
      refine ⟨by omega, ?_, ?_, ?_, by omega⟩
      · intro r hr
        rw [Array.set_val_eq, List.getElem?_set, if_neg (by omega)]
        exact h2 r hr
      · refine ⟨row.set j b, ?_, ?_⟩
        · rw [Array.set_val_eq, List.getElem?_set, if_pos rfl, if_pos hli]
        · intro c hc'
          rw [Array.set_val_eq, List.getElem?_set]
          by_cases hcj : j.val = c
          · subst hcj
            rw [if_pos rfl, if_pos (by rw [len256_bool row]; exact hj'), hbH]
          · rw [if_neg hcj]
            exact hc c (by omega)
      · rw [← hbH] at hcs
        by_cases hbb : b = true
        · simp only [hbb, if_true] at hi6 hcs
          rw [j1_post]; omega
        · simp only [hbb, if_false] at hi6 hcs
          rw [j1_post]; omega
    · rename_i hj
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      obtain ⟨row, hrow', hc⟩ := h3
      rw [this] at hc h4
      rw [cntFrom_256] at h4
      exact ⟨h2, ⟨row, hrow', hc⟩, by omega⟩
  · exact ⟨hj, hz0, hrow, hones⟩

theorem makeHintVec_getElem! (sp : Spec.Params) {n : Nat} (Z R : Vector Poly n) (i c : Nat)
    (hi : i < n) (hc : c < 256) :
    ((MakeHintVec sp Z R)[i]!)[c]! = MakeHint sp ((Z[i]!)[c]!) ((R[i]!)[c]!) := by
  rw [vget! _ i hi, vget! Z i hi, vget! R i hi, vget! _ c hc, vget! _ c hc, vget! _ c hc]
  simp [Spec.MakeHintVec]

theorem restW_len {k : Nat} (H : Vector HintPoly k) : restW H k = 0 := by
  unfold restW
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem hint_outer_spec {K L : Usize} {k : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (hK : sp.k ≤ 2 ^ 20)
    (w_cs2 ct0 : Array (Array U32 256#usize) K) (WC CT : Vector Poly k) (hw : ReprVec w_cs2 WC)
    (hct : ReprVec ct0 CT) (H : Vector HintPoly k)
    (hH : ∀ i, i < k → ∀ c, c < 256 → (H[i]!)[c]! =
      MakeHint sp (-(CT[i]!)[c]!) ((WC[i]!)[c]! + (CT[i]!)[c]!))
    (hint : Array (Array Bool 256#usize) K) (ones i : Usize) (hi : i.val ≤ K.val)
    (h : Rows hint (fun r x => ReprHint x H[r]!) i.val)
    (hones : ones.val + restW H i.val = restW H 0) :
    sign.hint_step_loop0 ip w_cs2 ct0 hint ones i ⦃ o =>
      Rows o.1 (fun r x => ReprHint x H[r]!) K.val ∧ o.2.val + restW H K.val = restW H 0 ⦄ := by
  have hN : K.val = k := hw.len
  unfold sign.hint_step_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array Bool 256#usize) K × Usize × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ Rows p.1 (fun r x => ReprHint x H[r]!) p.2.2.val ∧
      p.2.1.val + restW H p.2.2.val = restW H 0)
  · rintro ⟨hint, ones, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [sign.hint_step_loop0.body]
    split
    · rename_i hik'
      have hik : i.val < k := by have : i.val < K.val := hik'; omega
      have hil : i.val < hint.val.length := by rw [hint.property]; omega
      have hrs := restW_succ H i.val hik
      step with hint_inner_spec ip sp hp hg hK w_cs2 ct0 WC CT hw hct H i hik (hH i.val hik) hint hint ones 0#usize
        (by simp) (fun r _ => rfl)
        ⟨hint.val[i.val], List.getElem?_eq_getElem hil, fun c hc => absurd hc (by simp)⟩
        (by have : (0#usize).val = 0 := rfl; rw [this]; omega) as ⟨o, ones1, hrest, row, hrow, hfull, hones'⟩
      step*
      refine ⟨by omega, ?_, by rw [i1_post]; omega⟩
      intro r hr
      by_cases hri : r = i.val
      · subst hri
        exact ⟨row, hrow, reprHint_of_get? row _ hfull⟩
      · rw [hrest r hri]
        exact h2 r (by omega)
    · rename_i hik'
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2 h3
      exact ⟨h2, h3⟩
  · exact ⟨hi, h, hones⟩

@[step]
theorem hint_step_spec {K L : Usize} {k : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (hK : sp.k ≤ 2 ^ 20)
    (c_hat : Array U32 256#usize) (C : Poly) (hc : Repr c_hat C)
    (t0_hat : Array (Array U32 256#usize) K) (T0 : Vector Poly k) (ht : ReprVec t0_hat T0)
    (w_cs2 : Array (Array U32 256#usize) K) (WC : Vector Poly k) (hw : ReprVec w_cs2 WC) :
    sign.hint_step ip c_hat t0_hat w_cs2 ⦃ r =>
      ReprHintVec r.1 (MakeHintVec sp (-NTTInvVec (ScalarVectorNTT C T0))
        (WC + NTTInvVec (ScalarVectorNTT C T0))) ∧
      ReprVec r.2.1 (NTTInvVec (ScalarVectorNTT C T0)) ∧
      r.2.2.val = HintWeight (MakeHintVec sp (-NTTInvVec (ScalarVectorNTT C T0))
        (WC + NTTInvVec (ScalarVectorNTT C T0))) ⦄ := by
  have hN : K.val = k := hw.len
  unfold sign.hint_step
  step with scalar_vector_ntt_inverse_spec c_hat C hc t0_hat T0 ht as ⟨ct0, hct⟩
  have hH : ∀ i, i < k → ∀ c, c < 256 →
      ((MakeHintVec sp (-NTTInvVec (ScalarVectorNTT C T0))
        (WC + NTTInvVec (ScalarVectorNTT C T0)))[i]!)[c]! =
      MakeHint sp (-(((NTTInvVec (ScalarVectorNTT C T0))[i]!)[c]!)) ((WC[i]!)[c]! +
        ((NTTInvVec (ScalarVectorNTT C T0))[i]!)[c]!) := by
    intro i hi c hc
    rw [makeHintVec_getElem! sp _ _ i c hi hc, vneg_getElem! _ i hi, vneg_getElem! _ c hc,
      vadd_getElem! _ _ i hi, vadd_getElem! _ _ c hc]
  step with hint_outer_spec ip sp hp hg hK w_cs2 ct0 WC (NTTInvVec (ScalarVectorNTT C T0)) hw hct
    (MakeHintVec sp (-NTTInvVec (ScalarVectorNTT C T0)) (WC + NTTInvVec (ScalarVectorNTT C T0))) hH
    (Array.repeat K (Array.repeat 256#usize false)) 0#usize 0#usize (by simp) (Rows.zero _ _)
    (by simp) as ⟨hint1, ones, hrows, hw'⟩
  rw [hN] at hrows
  refine ⟨hrows.reprHintVec hN, hct, ?_⟩
  rw [hN, restW_len] at hw'
  rw [hintWeight_eq]
  omega


end Proofs
