import XSpec.Pack

/-!
# Ported from `lean/Proofs/Hint.lean`: explicit models of `HintBitUnpack` and `HintBitPack`

`unpack_eq` / `pack_eq` rewrite the spec's early-exit and plain `for` loops into pure folds
(`efoldv` / `packModel`); the weight lemmas relate `HintWeight` to a recursive count.  Unchanged except for the
loop-state order of Lean 4.34 (see PORT-NOTES).
-/

open Spec
set_option maxRecDepth 8192

namespace XSpec.HM

/-- The pure value of an early-exit loop over a list: `inl r` is the early result, `inr b` the final state. -/
def efoldv {α R B : Type} (g : α → B → Sum R B) : List α → B → Sum R B
  | [], b => .inr b
  | a :: l, b => match g a b with
    | .inl r => .inl r
    | .inr b' => efoldv g l b'

theorem forIn_efoldv {α R B : Type} (g : α → B → Sum R B)
    (l : List α)
    (f : α → (Option R × B) → Id (ForInStep ((Option R × B))))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a (none, b) = pure (ForInStep.done (some r, s))
        | .inr b' => f a (none, b) = pure (ForInStep.yield (none, b'))) (b : B) :
    ∃ s : (Option R × B), forIn l ((none, b) : Option R × B) f = pure s ∧
      match efoldv g l b with
      | .inl r => s.1 = some r
      | .inr b' => s.1 = none ∧ s.2 = b' := by
  induction l generalizing b with
  | nil => exact ⟨(none, b), by simp, by simp [efoldv]⟩
  | cons a l ih =>
    have h1 := hf a (by simp) b
    simp only [efoldv]
    cases hg : g a b with
    | inl r =>
      rw [hg] at h1
      obtain ⟨s, hs⟩ := h1
      exact ⟨(some r, s), by rw [List.forIn_cons, hs]; rfl, rfl⟩
    | inr b' =>
      rw [hg] at h1
      obtain ⟨s, hs, hv⟩ := ih (fun a ha => hf a (by simp [ha])) b'
      refine ⟨s, ?_, hv⟩
      rw [List.forIn_cons, h1]
      exact hs


/-- What a consumer of an early-exit loop sees. -/
def qv {R B : Type} (s : (Option R × B)) : Sum R B :=
  match s.1 with
  | some r => .inl r
  | none => .inr s.2

theorem bind_forIn_efoldv {α R B γ : Type} (g : α → B → Sum R B) (l : List α)
    (f : α → (Option R × B) → Id (ForInStep ((Option R × B))))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a (none, b) = pure (ForInStep.done (some r, s))
        | .inr b' => f a (none, b) = pure (ForInStep.yield (none, b')))
    (K1 : Sum R B → Id γ) (K : (Option R × B) → Id γ) (hK : ∀ s, K s = K1 (qv s)) (b : B) :
    (forIn l ((none, b) : Option R × B) f >>= K) = K1 (efoldv g l b) := by
  obtain ⟨s, hs, hv⟩ := forIn_efoldv g l f hf b
  rw [hs, pure_bind, hK]
  congr 1
  unfold qv
  revert hv
  cases efoldv g l b <;> intro hv
  · simp [hv]
  · simp [hv.1, hv.2]

theorem forIn_efoldv_elim {α R B γ : Type} (g : α → B → Sum R B) (l : List α)
    (f : α → (Option R × B) → Id (ForInStep ((Option R × B))))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a (none, b) = pure (ForInStep.done (some r, s))
        | .inr b' => f a (none, b) = pure (ForInStep.yield (none, b')))
    (C : Id γ → Prop) (K : (Option R × B) → Id γ) (b : B)
    (h : ∀ s : (Option R × B), (match efoldv g l b with
        | .inl r => s.1 = some r
        | .inr b' => s.1 = none ∧ s.2 = b') → C (K s)) :
    C (forIn l ((none, b) : Option R × B) f >>= K) := by
  obtain ⟨s, hs, hv⟩ := forIn_efoldv g l f hf b
  rw [hs, pure_bind]
  exact h s hv

theorem vset_vset {α : Type} {n : Nat} (h : Vector α n) (i : Nat) (a b : α) :
    (h.set! i a).set! i b = h.set! i b := by
  apply Vector.ext; intro j hj
  simp [Vector.set!]

theorem vget_vset {α : Type} [Inhabited α] {n : Nat} (h : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    (h.set! i a)[i]! = a := by
  rw [getElem!_pos _ i (by simpa using hi)]
  rw [XSpec.set!_eq', Vector.getElem_setIfInBounds hi]
  simp

theorem vset_self {α : Type} [Inhabited α] {n : Nat} (h : Vector α n) (i : Nat) (hi : i < n) :
    h.set! i h[i]! = h := by
  apply Vector.ext; intro j hj
  rw [XSpec.set!_eq', Vector.getElem_setIfInBounds hj]
  by_cases hij : i = j
  · subst hij; simp; exact getElem!_pos _ _ (by simpa using hj)
  · simp [hij]

def rowLoop (y : List UInt8) (first : Nat) : Nat → Nat → HintPoly → Option HintPoly
  | 0, _, row => some row
  | n+1, idx, row =>
    if idx > first ∧ y[idx-1]! ≥ y[idx]! then none
    else rowLoop y first n (idx+1) (row.set! (y[idx]!).toNat true)

def gIn {k : Nat} (y : List UInt8) (first i : Nat) (_x : Nat) (b : Vector HintPoly k × Nat) :
    Sum (Option (Vector HintPoly k)) (Vector HintPoly k × Nat) :=
  if b.2 > first ∧ y[b.2-1]! ≥ y[b.2]! then .inl none
  else .inr (b.1.set! i (b.1[i]!.set! (y[b.2]!).toNat true), b.2+1)

theorem efoldv_gIn {k : Nat} (y : List UInt8) (first i : Nat) (hi : i < k) :
    ∀ (n c idx : Nat) (h : Vector HintPoly k),
    efoldv (gIn y first i) (List.range' c n) (h, idx) =
      match rowLoop y first n idx h[i]! with
      | none => .inl none
      | some row => .inr (h.set! i row, idx + n) := by
  intro n
  induction n with
  | zero => intro c idx h; simp [efoldv, rowLoop, vset_self _ _ hi]
  | succ n ih =>
    intro c idx h
    rw [List.range'_succ]
    simp only [efoldv, gIn, rowLoop]
    by_cases hc : idx > first ∧ y[idx-1]! ≥ y[idx]!
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      dsimp only
      rw [ih, vget_vset _ _ hi]
      rcases rowLoop y first n (idx + 1) (Vector.set! h[i]! y[idx]!.toNat true) with _ | row
      · rfl
      · simp only [vset_vset]
        rw [show idx + 1 + n = idx + (n + 1) by omega]

def gOut (sp : Params) (y : List UInt8) (i : Nat) (b : Vector HintPoly sp.k × Nat) :
    Sum (Option (Vector HintPoly sp.k)) (Vector HintPoly sp.k × Nat) :=
  if (y[sp.ω+i]!).toNat < b.2 ∨ (y[sp.ω+i]!).toNat > sp.ω then .inl none
  else match rowLoop y b.2 ((y[sp.ω+i]!).toNat - b.2) b.2 b.1[i]! with
    | none => .inl none
    | some row => .inr (b.1.set! i row, (y[sp.ω+i]!).toNat)

def gPad {R : Type} (y : List UInt8) (j : Nat) (_u : PUnit) : Sum (Option R) PUnit :=
  if y[j]! ≠ 0 then .inl none else .inr PUnit.unit

def padB (y : List UInt8) (ω idx : Nat) : Bool :=
  (List.range' idx (ω - idx)).all fun j => y[j]! == 0

theorem efoldv_gPad {R : Type} (y : List UInt8) : ∀ (n c : Nat),
    efoldv (gPad (R := R) y) (List.range' c n) PUnit.unit =
      if (List.range' c n).all (fun j => y[j]! == 0) then .inr PUnit.unit else .inl none := by
  intro n
  induction n with
  | zero => intro c; simp [efoldv]
  | succ n ih =>
    intro c
    rw [List.range'_succ]
    by_cases h0 : y[c]! = 0
    · have e : (y[c]! == 0) = true := beq_iff_eq.2 h0
      simp only [efoldv, gPad, List.all_cons, e, Bool.true_and]
      rw [if_neg (by simpa using h0)]
      exact ih (c + 1)
    · have e : (y[c]! == 0) = false := by simpa using h0
      simp only [efoldv, gPad, List.all_cons, e, Bool.false_and]
      rw [if_pos h0]
      simp

abbrev OutSt (k : Nat) := Option (Option (Vector HintPoly k)) × (Vector HintPoly k × Nat)

def unpackModel (sp : Params) (y : List UInt8) : Option (Vector HintPoly sp.k) :=
  match efoldv (gOut sp y) (List.range' 0 sp.k)
      (Vector.replicate sp.k (Vector.replicate 256 false), 0) with
  | .inl a => a
  | .inr s => if padB y sp.ω s.2 = true then some s.1 else none

theorem unpack_eq (sp : Params) (y : List UInt8) : HintBitUnpack sp y = unpackModel sp y := by
  unfold HintBitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine forIn_efoldv_elim (gOut sp y) (List.range' 0 sp.k) _ ?hf
    (fun X => Id.run X = unpackModel sp y) _ _ ?main
  case hf =>
    intro i hi b
    obtain ⟨h, idx⟩ := b
    have hik : i < sp.k := by simpa using hi
    unfold gOut
    by_cases hc : (y[sp.ω+i]!).toNat < idx ∨ (y[sp.ω+i]!).toNat > sp.ω
    · simp only [hc, if_true]
      exact ⟨_, rfl⟩
    · simp only [hc, if_false]
      have hc' : idx ≤ (y[sp.ω+i]!).toNat := by omega
      rcases hrl : rowLoop y idx ((y[sp.ω+i]!).toNat - idx) idx h[i]! with _ | row
      · simp only [pure_bind]
        refine forIn_efoldv_elim (gIn y idx i) (List.range' idx _) _ ?hf1
          (fun X => ∃ s : Vector HintPoly sp.k × Nat, X =
            (pure (ForInStep.done (some none, s)) : Id (ForInStep (OutSt sp.k)))) _ (h, idx) ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          simp only at hs
          rw [hs]
          exact ⟨_, rfl⟩
        case hf1 =>
          intro x hx b
          obtain ⟨hh, j⟩ := b
          unfold gIn
          by_cases hj : j > idx
          · by_cases hge : y[j-1]! ≥ y[j]!
            · rw [if_pos ⟨hj, hge⟩]
              dsimp only
              rw [if_pos hj, if_pos hge]
              exact ⟨_, rfl⟩
            · rw [if_neg (fun h => hge h.2)]
              dsimp only
              rw [if_pos hj, if_neg hge]
          · rw [if_neg (fun h => hj h.1)]
            dsimp only
            rw [if_neg hj]
      · dsimp only
        refine forIn_efoldv_elim (gIn y idx i) (List.range' idx _) _ ?hf1
          (fun X => X = (pure (ForInStep.yield (none, (h.set! i row, (y[sp.ω+i]!).toNat))) :
            Id (ForInStep (OutSt sp.k)))) _ (h, idx) ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          rcases s with ⟨o, hh, a⟩
          simp only [Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          simp only
          have : idx + ((y[sp.ω+i]!).toNat - idx) = (y[sp.ω+i]!).toNat := by omega
          rw [this]
        case hf1 =>
          intro x hx b
          obtain ⟨hh, j⟩ := b
          unfold gIn
          by_cases hj : j > idx
          · by_cases hge : y[j-1]! ≥ y[j]!
            · rw [if_pos ⟨hj, hge⟩]
              dsimp only
              rw [if_pos hj, if_pos hge]
              exact ⟨_, rfl⟩
            · rw [if_neg (fun h => hge h.2)]
              dsimp only
              rw [if_pos hj, if_neg hge]
          · rw [if_neg (fun h => hj h.1)]
            dsimp only
            rw [if_neg hj]
  case main =>
    intro s hs
    unfold unpackModel
    rcases hE : efoldv (gOut sp y) (List.range' 0 sp.k)
      (Vector.replicate sp.k (Vector.replicate 256 false), 0) with a | b'
    · rw [hE] at hs
      simp only at hs ⊢
      rw [hs]; rfl
    · rw [hE] at hs
      rcases s with ⟨o, hh, a⟩
      simp only at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [pure_bind]
      refine forIn_efoldv_elim (gPad y) (List.range' a (sp.ω - a)) _ ?hf2
        (fun X => Id.run X = if padB y sp.ω a = true then some hh else none) _ PUnit.unit ?main2
      case main2 =>
        intro s2 hs'
        rw [efoldv_gPad] at hs'
        by_cases hp : (List.range' a (sp.ω - a)).all (fun j => y[j]! == 0) = true
        · rw [if_pos hp] at hs'
          simp only at hs'
          rw [hs'.1]
          have : padB y sp.ω a = true := hp
          rw [if_pos this]
          rfl
        · rw [if_neg hp] at hs'
          simp only at hs'
          rw [hs']
          have : ¬ padB y sp.ω a = true := hp
          rw [if_neg this]
          rfl
      case hf2 =>
        intro j hj u
        cases u
        unfold gPad
        by_cases h0 : y[j]! ≠ 0
        · simp only [h0, if_true, ne_eq, not_false_eq_true]
          exact ⟨PUnit.unit, trivial⟩
        · simp only [h0, if_false]


theorem bind_forIn_foldl {α β γ : Type} (l : List α) (f : α → β → Id (ForInStep β)) (F : α → β → β)
    (hf : ∀ a, a ∈ l → ∀ b, f a b = pure (ForInStep.yield (F a b))) (K : β → Id γ) (b : β) :
    (forIn l b f >>= K) = K (l.foldl (fun b a => F a b) b) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hf a (by simp) b]
    simp only [pure_bind, List.foldl_cons]
    exact ih (fun a ha => hf a (by simp [ha])) _

def packRowF (row : HintPoly) (j : Nat) (st : Array UInt8 × Nat) : Array UInt8 × Nat :=
  if row[j]! = true then (st.1.set! st.2 j.toUInt8, st.2 + 1) else st

def packRow (row : HintPoly) (st : Array UInt8 × Nat) : Array UInt8 × Nat :=
  (List.range' 0 256).foldl (fun b a => packRowF row a b) st

def packRowsF (ω : Nat) {k : Nat} (h : Vector HintPoly k) (i : Nat) (st : Array UInt8 × Nat) :
    Array UInt8 × Nat :=
  ((packRow h[i]! st).1.set! (ω + i) (packRow h[i]! st).2.toUInt8, (packRow h[i]! st).2)

def packModel (sp : Params) (h : Vector HintPoly sp.k) : List UInt8 :=
  ((List.range' 0 sp.k).foldl (fun b i => packRowsF sp.ω h i b)
    (Array.replicate (sp.ω + sp.k) 0, 0)).1.toList

theorem pack_eq (sp : Params) (h : Vector HintPoly sp.k) : HintBitPack sp h = packModel sp h := by
  unfold HintBitPack packModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [bind_forIn_foldl (List.range' 0 sp.k) _ (fun i st => packRowsF sp.ω h i st) ?hf]
  case hf =>
    intro i hi st
    rw [bind_forIn_foldl (List.range' 0 256) _ (fun j st => packRowF h[i]! j st) ?hf2]
    · rfl
    · intro j hj r
      unfold packRowF
      by_cases hb : (h[i]!)[j]! = true
      · simp [hb]
      · simp [hb]
  rfl



def cntFrom (row : HintPoly) (j : Nat) : Nat := (row.toList.drop j).countP (fun b => b)

def restW {k : Nat} (h : Vector HintPoly k) (i : Nat) : Nat :=
  ((h.toList.drop i).map (fun r => r.toList.countP (fun b => b))).sum

theorem cntFrom_succ (row : HintPoly) (j : Nat) (hj : j < 256) :
    cntFrom row j = (if row[j]! = true then 1 else 0) + cntFrom row (j + 1) := by
  have hl : j < row.toList.length := by simpa using hj
  unfold cntFrom
  rw [List.drop_eq_getElem_cons hl, List.countP_cons, getElem!_pos _ _ (by simpa using hj)]
  simp only [Vector.getElem_toList]
  by_cases hb : row[j] = true <;> simp [hb] <;> omega

theorem cntFrom_256 (row : HintPoly) : cntFrom row 256 = 0 := by
  unfold cntFrom
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem restW_succ {k : Nat} (h : Vector HintPoly k) (i : Nat) (hi : i < k) :
    restW h i = cntFrom h[i]! 0 + restW h (i + 1) := by
  have hl : i < h.toList.length := by simpa using hi
  unfold restW cntFrom
  rw [List.drop_eq_getElem_cons hl, List.map_cons, List.sum_cons, getElem!_pos _ _ (by simpa using hi)]
  simp only [Vector.getElem_toList, List.drop_zero]

theorem foldl_add_sum {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega

theorem vcountP {n : Nat} (xs : Vector Bool n) : xs.countP (fun b => b) = xs.toList.countP (fun b => b) := by
  rcases xs with ⟨⟨l⟩, hl⟩
  simp [Vector.countP, Vector.toList]

theorem hintWeight_eq {k : Nat} (h : Vector HintPoly k) : HintWeight h = restW h 0 := by
  unfold HintWeight restW
  rw [← Vector.foldl_toList, List.drop_zero]
  simp only [vcountP]
  rw [foldl_add_sum (fun r : HintPoly => r.toList.countP (fun b => b))]
  simp


end XSpec.HM
