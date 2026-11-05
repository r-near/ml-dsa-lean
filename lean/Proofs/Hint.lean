import Proofs.Repr
import Spec.Encode

/-!
# HintBitPack and HintBitUnpack (FIPS 204 Algorithms 20 and 21)

* `hint_bit_unpack_spec`: for **every** byte string `y` of length `ω + k` (no condition on the content),
  `Impl.encode.hint_bit_unpack` returns `none` exactly when `Spec.HintBitUnpack` returns `none` (`⊥`), and
  otherwise the hint vectors agree (`ReprHintVec`). It is assembled from the specs of the three extracted
  helpers (`hint_bit_unpack_row_spec`, `hint_bit_unpack_rows_spec`, `hint_bit_unpack_padding_spec`).
* `hint_bit_pack_spec`: for a hint of weight at most `ω` (what Sign guarantees) and an output slice of length
  `ω + k`, `Impl.encode.hint_bit_pack` writes exactly `Spec.HintBitPack`.

Method. The spec writes Algorithm 21 with `for` loops that `return none` early. `unpack_eq` rewrites it, with the
generic lemma `forIn_efoldv` (an early-exit loop over a list in the `Id` monad is the pure fold
`efoldv`), into an explicit model: `gOut` (one row, steps 4-14), `rowLoop` (steps 7-14 on the row), `padB`
(steps 16-20). The Rust loops are then proved against that model by loop invariants of the form "the model run
from the current state equals the model run from the start" (`loop.spec_decr_nat`). `pack_eq` does the same for
Algorithm 20 (`packModel`, no early exits; the weight bound `HintWeight h ≤ ω` keeps every write in bounds).
All helper lemmas live in `Proofs.HintAux`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace HintAux

/-- The pure value of an early-exit loop over a list: `inl r` is the early result, `inr b` the final state. -/
def efoldv {α R B : Type} (g : α → B → Sum R B) : List α → B → Sum R B
  | [], b => .inr b
  | a :: l, b => match g a b with
    | .inl r => .inl r
    | .inr b' => efoldv g l b'

theorem forIn_efoldv {α R B : Type} (g : α → B → Sum R B)
    (l : List α)
    (f : α → MProd (Option R) B → Id (ForInStep (MProd (Option R) B)))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a ⟨none, b⟩ = pure (ForInStep.done ⟨some r, s⟩)
        | .inr b' => f a ⟨none, b⟩ = pure (ForInStep.yield ⟨none, b'⟩)) (b : B) :
    ∃ s : MProd (Option R) B, forIn l (⟨none, b⟩ : MProd (Option R) B) f = pure s ∧
      match efoldv g l b with
      | .inl r => s.fst = some r
      | .inr b' => s.fst = none ∧ s.snd = b' := by
  induction l generalizing b with
  | nil => exact ⟨⟨none, b⟩, by simp, by simp [efoldv]⟩
  | cons a l ih =>
    have h1 := hf a (by simp) b
    simp only [efoldv]
    cases hg : g a b with
    | inl r =>
      rw [hg] at h1
      obtain ⟨s, hs⟩ := h1
      exact ⟨⟨some r, s⟩, by rw [List.forIn_cons, hs]; rfl, rfl⟩
    | inr b' =>
      rw [hg] at h1
      obtain ⟨s, hs, hv⟩ := ih (fun a ha => hf a (by simp [ha])) b'
      refine ⟨s, ?_, hv⟩
      rw [List.forIn_cons, h1]
      exact hs


theorem forIn_efoldv_elim {α R B γ : Type} (g : α → B → Sum R B) (l : List α)
    (f : α → MProd (Option R) B → Id (ForInStep (MProd (Option R) B)))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a ⟨none, b⟩ = pure (ForInStep.done ⟨some r, s⟩)
        | .inr b' => f a ⟨none, b⟩ = pure (ForInStep.yield ⟨none, b'⟩))
    (C : Id γ → Prop) (K : MProd (Option R) B → Id γ) (b : B)
    (h : ∀ s : MProd (Option R) B, (match efoldv g l b with
        | .inl r => s.fst = some r
        | .inr b' => s.fst = none ∧ s.snd = b') → C (K s)) :
    C (forIn l (⟨none, b⟩ : MProd (Option R) B) f >>= K) := by
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
  rw [set!_eq', Vector.getElem_setIfInBounds hi]
  simp

theorem vset_self {α : Type} [Inhabited α] {n : Nat} (h : Vector α n) (i : Nat) (_hi : i < n) :
    h.set! i h[i]! = h := by
  apply Vector.ext; intro j hj
  rw [set!_eq', Vector.getElem_setIfInBounds hj]
  by_cases hij : i = j
  · subst hij; simp; exact getElem!_pos _ _ (by simpa using hj)
  · simp [hij]

def rowLoop (y : List UInt8) (first : Nat) : Nat → Nat → HintPoly → Option HintPoly
  | 0, _, row => some row
  | n+1, idx, row =>
    if idx > first ∧ y[idx-1]! ≥ y[idx]! then none
    else rowLoop y first n (idx+1) (row.set! (y[idx]!).toNat true)

def gIn {k : Nat} (y : List UInt8) (first i : Nat) (_x : Nat) (b : MProd Nat (Vector HintPoly k)) :
    Sum (Option (Vector HintPoly k)) (MProd Nat (Vector HintPoly k)) :=
  if b.fst > first ∧ y[b.fst-1]! ≥ y[b.fst]! then .inl none
  else .inr ⟨b.fst+1, b.snd.set! i (b.snd[i]!.set! (y[b.fst]!).toNat true)⟩

theorem efoldv_gIn {k : Nat} (y : List UInt8) (first i : Nat) (hi : i < k) :
    ∀ (n c idx : Nat) (h : Vector HintPoly k),
    efoldv (gIn y first i) (List.range' c n) ⟨idx, h⟩ =
      match rowLoop y first n idx h[i]! with
      | none => .inl none
      | some row => .inr ⟨idx + n, h.set! i row⟩ := by
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

def gOut (sp : Params) (y : List UInt8) (i : Nat) (b : MProd Nat (Vector HintPoly sp.k)) :
    Sum (Option (Vector HintPoly sp.k)) (MProd Nat (Vector HintPoly sp.k)) :=
  if (y[sp.ω+i]!).toNat < b.fst ∨ (y[sp.ω+i]!).toNat > sp.ω then .inl none
  else match rowLoop y b.fst ((y[sp.ω+i]!).toNat - b.fst) b.fst b.snd[i]! with
    | none => .inl none
    | some row => .inr ⟨(y[sp.ω+i]!).toNat, b.snd.set! i row⟩

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

abbrev OutSt (k : Nat) := MProd (Option (Option (Vector HintPoly k))) (MProd Nat (Vector HintPoly k))

def unpackModel (sp : Params) (y : List UInt8) : Option (Vector HintPoly sp.k) :=
  match efoldv (gOut sp y) (List.range' 0 sp.k)
      ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ with
  | .inl a => a
  | .inr s => if padB y sp.ω s.fst = true then some s.snd else none

theorem unpack_eq (sp : Params) (y : List UInt8) : HintBitUnpack sp y = unpackModel sp y := by
  unfold HintBitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine forIn_efoldv_elim (gOut sp y) (List.range' 0 sp.k) _ ?hf
    (fun X => Id.run X = unpackModel sp y) _ _ ?main
  case hf =>
    intro i hi b
    obtain ⟨idx, h⟩ := b
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
          (fun X => ∃ s : MProd Nat (Vector HintPoly sp.k), X =
            (pure (ForInStep.done ⟨some none, s⟩) : Id (ForInStep (OutSt sp.k)))) _ ⟨idx, h⟩ ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          simp only at hs
          rw [hs]
          exact ⟨_, rfl⟩
        case hf1 =>
          intro x hx b
          obtain ⟨j, hh⟩ := b
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
        simp only [pure_bind]
        refine forIn_efoldv_elim (gIn y idx i) (List.range' idx _) _ ?hf1
          (fun X => X = (pure (ForInStep.yield ⟨none, ⟨(y[sp.ω+i]!).toNat, h.set! i row⟩⟩) :
            Id (ForInStep (OutSt sp.k)))) _ ⟨idx, h⟩ ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          rcases s with ⟨o, a, hh⟩
          simp only [MProd.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          simp only
          have : idx + ((y[sp.ω+i]!).toNat - idx) = (y[sp.ω+i]!).toNat := by omega
          rw [this]
        case hf1 =>
          intro x hx b
          obtain ⟨j, hh⟩ := b
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
      ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ with a | b'
    · rw [hE] at hs
      simp only at hs ⊢
      rw [hs]; rfl
    · rw [hE] at hs
      rcases s with ⟨o, a, hh⟩
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

/-! ## Rust side: padding -/

theorem bytes_getElem!' (y : Slice U8) (i : Nat) (hi : i < y.val.length) :
    (bytes y)[i]! = UInt8.ofNat (y.val[i]).val := by
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp [bytes]

theorem padB_of_le (y : List UInt8) (ω idx : Nat) (h : ω ≤ idx) : padB y ω idx = true := by
  simp [padB, Nat.sub_eq_zero_of_le h]

theorem padB_step (y : List UInt8) (ω idx : Nat) (h : idx < ω) :
    padB y ω idx = ((y[idx]! == 0) && padB y ω (idx + 1)) := by
  unfold padB
  obtain ⟨n, hn⟩ : ∃ n, ω - idx = n + 1 := ⟨ω - idx - 1, by omega⟩
  rw [hn, List.range'_succ, List.all_cons, show ω - (idx + 1) = n by omega]

theorem u8_ne_zero_iff (x : U8) : (x != 0#u8) = true ↔ x.val ≠ 0 := by
  constructor
  · intro h h0
    have : x = 0#u8 := UScalar.eq_of_val_eq (by simpa using h0)
    subst this
    simp at h
  · intro h
    simp only [bne_iff_ne, ne_eq]
    intro h0
    exact h (by rw [h0]; rfl)

theorem ofNat_val_eq_zero_iff (x : U8) : UInt8.ofNat x.val = 0 ↔ x.val = 0 := by
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    rwa [toNat_ofNat_val] at this
  · intro h; rw [h]; rfl

theorem hint_bit_unpack_padding_loop_spec (ip : Impl.params.Params) (ω : Nat) (hω : ip.omega.val = ω)
    (y : Slice U8) (hy : ω ≤ y.val.length) (j0 : Usize) :
    encode.hint_bit_unpack_padding_loop ip y j0 ⦃ b => b = padB (bytes y) ω j0.val ⦄ := by
  unfold encode.hint_bit_unpack_padding_loop
  apply loop.spec_decr_nat (fun j : Usize => ω - j.val)
    (fun j => padB (bytes y) ω j.val = padB (bytes y) ω j0.val)
  · intro j hj
    simp only [encode.hint_bit_unpack_padding_loop.body]
    split
    · rename_i hjω
      have hj' : j.val < ω := by have : j.val < ip.omega.val := hjω; omega
      step*
      · rename_i x hne
        have hjl := i
        have hx := i_post2
        have hne' := (u8_ne_zero_iff x).1 hne
        have hb : ((bytes y)[j.val]! == 0) = false := by
          rw [bytes_getElem!' y j.val hjl, beq_eq_false_iff_ne, ne_eq, ofNat_val_eq_zero_iff]
          rw [hx] at hne'
          exact hne'
        rw [← hj, padB_step _ _ _ hj', hb]
        rfl
      · rename_i _ x hne
        have hjl := i
        have hx := i_post2
        have hj1 := j1_post
        have hz : x.val = 0 := by
          by_contra hh
          exact hne ((u8_ne_zero_iff x).2 hh)
        have hb : ((bytes y)[j.val]! == 0) = true := by
          rw [bytes_getElem!' y j.val hjl, beq_iff_eq, ofNat_val_eq_zero_iff]
          rw [hx] at hz
          exact hz
        refine ⟨?_, by omega⟩
        rw [← hj, padB_step _ _ _ hj', hb, hj1]
        rfl
    · rename_i hjω
      have hj' : ¬ j.val < ω := by intro h; exact hjω (by show j.val < ip.omega.val; omega)
      simp only [WP.spec_ok]
      rw [← hj, padB_of_le _ _ _ (by omega)]
  · rfl


/-! ## Rust side: one row -/

theorem toHint_set (a : Array Bool 256#usize) (i : Usize) (x : Bool) (_hi : i.val < 256) :
    toHint (a.set i x) = (toHint a).set! i.val x := by
  apply Vector.ext
  intro k hk
  rw [set!_eq', Vector.getElem_setIfInBounds hk]
  simp only [toHint, Vector.getElem_ofFn, Array.set_val_eq]
  by_cases h : i.val = k
  · subst h
    simp
  · simp [h]

theorem rowLoop_succ (y : List UInt8) (first n idx : Nat) (rm : HintPoly) :
    rowLoop y first (n + 1) idx rm =
      if idx > first ∧ y[idx-1]! ≥ y[idx]! then none
      else rowLoop y first n (idx + 1) (rm.set! (y[idx]!).toNat true) := rfl

theorem bytes_get_of_eq (y : Slice U8) (i : Usize) (x : U8) (hi : i.val < y.val.length)
    (h : x = y.val[i.val]) (m : Nat) (hm : i.val = m) : (bytes y)[m]! = UInt8.ofNat x.val := by
  subst hm
  rw [bytes_getElem!' y _ hi, h]

theorem u8_ge (a b : U8) (h : a ≥ b) : UInt8.ofNat a.val ≥ UInt8.ofNat b.val := by
  rw [ge_iff_le, UInt8.le_iff_toNat_le, toNat_ofNat_val, toNat_ofNat_val]
  scalar_tac

theorem u8_not_ge (a b : U8) (h : ¬ a ≥ b) : ¬ UInt8.ofNat a.val ≥ UInt8.ofNat b.val := by
  rw [ge_iff_le, UInt8.le_iff_toNat_le, toNat_ofNat_val, toNat_ofNat_val]
  scalar_tac

theorem hint_bit_unpack_row_loop_spec (y : Slice U8) (first «end» : Usize)
    (hend : «end».val ≤ y.val.length) (hfe : first.val ≤ «end».val)
    (row0 : Array Bool 256#usize) (rm0 : HintPoly) (hrow : ReprHint row0 rm0) :
    encode.hint_bit_unpack_row_loop y first «end» row0 first ⦃ r =>
      match rowLoop (bytes y) first.val («end».val - first.val) first.val rm0 with
      | none => r.1 = false
      | some rm => r.1 = true ∧ ReprHint r.2 rm ⦄ := by
  unfold encode.hint_bit_unpack_row_loop
  apply loop.spec_decr_nat (fun p : Array Bool 256#usize × Usize => «end».val - p.2.val)
    (fun p => first.val ≤ p.2.val ∧ p.2.val ≤ «end».val ∧ ∃ rm, ReprHint p.1 rm ∧
      rowLoop (bytes y) first.val («end».val - p.2.val) p.2.val rm =
        rowLoop (bytes y) first.val («end».val - first.val) first.val rm0)
  · rintro ⟨row, idx⟩ ⟨h1, h2, rm, hr, h3⟩
    dsimp only at h1 h2 hr h3
    simp only [encode.hint_bit_unpack_row_loop.body]
    split
    · rename_i hlt
      have hlt' : idx.val < «end».val := hlt
      step*
      · subst i1_post2 i2_post2
        have hgt0 := ‹idx > first›
        have hgt : idx.val > first.val := hgt0
        have hge := ‹(_ : U8) ≥ _›
        have e1 := bytes_get_of_eq y i _ i1 rfl (idx.val - 1) (by omega)
        have e2 := bytes_get_of_eq y idx _ i2 rfl idx.val rfl
        have hc : idx.val > first.val ∧ (bytes y)[idx.val-1]! ≥ (bytes y)[idx.val]! :=
          ⟨hgt, by rw [e1, e2]; exact u8_ge _ _ hge⟩
        rw [show «end».val - idx.val = («end».val - idx.val - 1) + 1 by omega, rowLoop_succ,
          if_pos hc] at h3
        rw [← h3]
        trivial
      · subst i1_post2 i2_post2
        have hnge := ‹¬(_ : U8) ≥ _›
        have e1 := bytes_get_of_eq y i _ i1 rfl (idx.val - 1) (by omega)
        have e2 := bytes_get_of_eq y idx _ i2 rfl idx.val rfl
        have hnc : ¬ (idx.val > first.val ∧ (bytes y)[idx.val-1]! ≥ (bytes y)[idx.val]!) :=
          fun hc => u8_not_ge _ _ hnge (by rw [e1, e2] at hc; exact hc.2)
        have hi3 : i3.val = (y.val[idx.val]'i2).val := by rw [i3_post]; simp
        have hxb : ((bytes y)[idx.val]!).toNat = (y.val[idx.val]'i2).val := by
          rw [e2]; exact toNat_ofNat_val _
        rw [show «end».val - idx.val = («end».val - index1.val) + 1 by omega, rowLoop_succ,
          if_neg hnc, hxb, show idx.val + 1 = index1.val by omega] at h3
        refine ⟨by omega, by omega, ⟨rm.set! (y.val[idx.val]'i2).val true, ?_, h3⟩, by omega⟩
        show toHint a = _
        have hlt256 : i3.val < 256 := by rw [hi3]; scalar_tac
        rw [a_post, toHint_set _ _ _ hlt256, hi3]
        unfold ReprHint at hr
        rw [hr]
      · subst i_post2
        have hnc : ¬ (idx.val > first.val ∧ (bytes y)[idx.val-1]! ≥ (bytes y)[idx.val]!) :=
          fun hc => ‹¬ idx > first› hc.1
        have e2 := bytes_get_of_eq y idx _ i rfl idx.val rfl
        have hi3 : i3.val = (y.val[idx.val]'i).val := by rw [i3_post]; simp
        have hxb : ((bytes y)[idx.val]!).toNat = (y.val[idx.val]'i).val := by
          rw [e2]; exact toNat_ofNat_val _
        rw [show «end».val - idx.val = («end».val - index1.val) + 1 by omega, rowLoop_succ,
          if_neg hnc, hxb, show idx.val + 1 = index1.val by omega] at h3
        refine ⟨by omega, by omega, ⟨rm.set! (y.val[idx.val]'i).val true, ?_, h3⟩, by omega⟩
        show toHint a = _
        have hlt256 : i3.val < 256 := by rw [hi3]; scalar_tac
        rw [a_post, toHint_set _ _ _ hlt256, hi3]
        unfold ReprHint at hr
        rw [hr]
    · rename_i hlt
      have hlt' : ¬ idx.val < «end».val := hlt
      have hidx : idx.val = «end».val := by omega
      simp only [WP.spec_ok]
      rw [hidx, Nat.sub_self] at h3
      rw [rowLoop] at h3
      rw [← h3]
      exact ⟨trivial, hr⟩
  · exact ⟨le_refl _, hfe, rm0, hrow, rfl⟩


end HintAux
open HintAux

@[step]
theorem hint_bit_unpack_row_spec (y : Slice U8) (first «end» : Usize)
    (hend : «end».val ≤ y.val.length) (hfe : first.val ≤ «end».val)
    (row0 : Array Bool 256#usize) :
    encode.hint_bit_unpack_row y first «end» row0 ⦃ r =>
      match rowLoop (bytes y) first.val («end».val - first.val) first.val (toHint row0) with
      | none => r.1 = false
      | some rm => r.1 = true ∧ ReprHint r.2 rm ⦄ :=
  hint_bit_unpack_row_loop_spec y first «end» hend hfe row0 (toHint row0) rfl

namespace HintAux


end HintAux

@[step]
theorem hint_bit_unpack_padding_spec (ip : Impl.params.Params)
    (y : Slice U8) (hy : ip.omega.val ≤ y.val.length) (index : Usize) :
    encode.hint_bit_unpack_padding ip y index ⦃ b => b = padB (bytes y) ip.omega.val index.val ⦄ :=
  hint_bit_unpack_padding_loop_spec ip ip.omega.val rfl y hy index

namespace HintAux


/-! ## Rust side: all rows -/

theorem reprHintVec_set {K : Usize} {k : Nat} {a : Array (Array Bool 256#usize) K}
    {hm : Vector HintPoly k} (h : ReprHintVec a hm) (i : Usize) (x : Array Bool 256#usize)
    (r : HintPoly) (hx : ReprHint x r) : ReprHintVec (a.set i x) (hm.set! i.val r) := by
  refine ⟨h.len, fun j hj => ?_⟩
  have hlt : j < a.val.length := by have := a.property; have := h.len; omega
  rw [set!_eq', Vector.getElem_setIfInBounds hj]
  simp only [Array.set_val_eq]
  by_cases hij : i.val = j
  · subst hij; simpa using hx
  · simpa [hij, List.getElem_set] using h.elt j hj

theorem reprHintVec_get {K : Usize} {k : Nat} {a : Array (Array Bool 256#usize) K}
    {hm : Vector HintPoly k} (h : ReprHintVec a hm) (i : Usize) (hi : i.val < K.val) :
    ReprHint (a.val[i.val]'(by have := a.property; omega)) hm[i.val]! := by
  have hik : i.val < k := by have := h.len; omega
  rw [getElem!_pos _ _ (by simpa using hik)]
  exact h.elt i.val hik

theorem rows_unfold (sp : Params) (ys : List UInt8) (i idx : Nat) (hm : Vector HintPoly sp.k)
    (hik : i < sp.k) :
    efoldv (gOut sp ys) (List.range' i (sp.k - i)) ⟨idx, hm⟩ =
      match gOut sp ys i ⟨idx, hm⟩ with
      | .inl r => .inl r
      | .inr b' => efoldv (gOut sp ys) (List.range' (i + 1) (sp.k - (i + 1))) b' := by
  obtain ⟨n, hn⟩ : ∃ n, sp.k - i = n + 1 := ⟨sp.k - i - 1, by omega⟩
  rw [hn, List.range'_succ, show sp.k - (i + 1) = n by omega]
  simp only [efoldv]
  cases gOut sp ys i ⟨idx, hm⟩ <;> rfl

theorem rows_step_none (sp : Params) (ys : List UInt8) (i idx : Nat) (hm : Vector HintPoly sp.k)
    (hik : i < sp.k) (hc : (ys[sp.ω + i]!).toNat < idx ∨ (ys[sp.ω + i]!).toNat > sp.ω) :
    efoldv (gOut sp ys) (List.range' i (sp.k - i)) ⟨idx, hm⟩ = .inl none := by
  rw [rows_unfold sp ys i idx hm hik]
  unfold gOut
  rw [if_pos hc]

theorem rows_step_none' (sp : Params) (ys : List UInt8) (i idx : Nat) (hm : Vector HintPoly sp.k)
    (hik : i < sp.k) (hc : ¬ ((ys[sp.ω + i]!).toNat < idx ∨ (ys[sp.ω + i]!).toNat > sp.ω))
    (hrl : rowLoop ys idx ((ys[sp.ω + i]!).toNat - idx) idx hm[i]! = none) :
    efoldv (gOut sp ys) (List.range' i (sp.k - i)) ⟨idx, hm⟩ = .inl none := by
  rw [rows_unfold sp ys i idx hm hik]
  unfold gOut
  rw [if_neg hc, hrl]

theorem rows_step_ok (sp : Params) (ys : List UInt8) (i idx : Nat) (hm : Vector HintPoly sp.k)
    (hik : i < sp.k) (hc : ¬ ((ys[sp.ω + i]!).toNat < idx ∨ (ys[sp.ω + i]!).toNat > sp.ω))
    (rm : HintPoly)
    (hrl : rowLoop ys idx ((ys[sp.ω + i]!).toNat - idx) idx hm[i]! = some rm) :
    efoldv (gOut sp ys) (List.range' i (sp.k - i)) ⟨idx, hm⟩ =
      efoldv (gOut sp ys) (List.range' (i + 1) (sp.k - (i + 1))) ⟨(ys[sp.ω + i]!).toNat, hm.set! i rm⟩ := by
  rw [rows_unfold sp ys i idx hm hik]
  unfold gOut
  rw [if_neg hc, hrl]

theorem hint_bit_unpack_rows_loop_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (y : Slice U8) (hy : y.val.length = sp.ω + sp.k)
    (h0 : Array (Array Bool 256#usize) K) (hm0 : Vector HintPoly sp.k) (hh0 : ReprHintVec h0 hm0) :
    encode.hint_bit_unpack_rows_loop ip y h0 0#usize 0#usize ⦃ r =>
      match efoldv (gOut sp (bytes y)) (List.range' 0 sp.k) ⟨0, hm0⟩ with
      | .inl _ => r.1 = none
      | .inr s => ∃ idx : Usize, r.1 = some idx ∧ idx.val = s.fst ∧ ReprHintVec r.2 s.snd ⦄ := by
  unfold encode.hint_bit_unpack_rows_loop
  apply loop.spec_decr_nat
    (fun p : Array (Array Bool 256#usize) K × Usize × Usize => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ ∃ hm, ReprHintVec p.1 hm ∧
      efoldv (gOut sp (bytes y)) (List.range' p.2.2.val (sp.k - p.2.2.val)) ⟨p.2.1.val, hm⟩ =
        efoldv (gOut sp (bytes y)) (List.range' 0 sp.k) ⟨0, hm0⟩)
  · rintro ⟨h, idx, i⟩ ⟨h1, hm, hr, h3⟩
    dsimp only at h1 hr h3
    simp only [encode.hint_bit_unpack_rows_loop.body]
    have hω := hp.omega
    have hKk := hp.K_eq
    split
    · rename_i hlt
      have hlt' : i.val < K.val := hlt
      have hik : i.val < sp.k := by omega
      have hyl := y.property
      have hrowi := reprHintVec_get hr i hlt'
      step*
      · have hyi := bytes_get_of_eq y i1 _ i2 i2_post2 (sp.ω + i.val) (by omega)
        have hyi' : ((bytes y)[sp.ω + i.val]!).toNat = «end».val := by
          rw [hyi, toNat_ofNat_val, end_post]; simp
        have hc : ((bytes y)[sp.ω + i.val]!).toNat < idx.val ∨ ((bytes y)[sp.ω + i.val]!).toNat > sp.ω :=
          Or.inl (by rw [hyi']; exact ‹«end» < idx›)
        rw [← h3, rows_step_none sp _ _ _ hm hik hc]
        trivial
      · have hyi := bytes_get_of_eq y i1 _ i2 i2_post2 (sp.ω + i.val) (by omega)
        have hyi' : ((bytes y)[sp.ω + i.val]!).toNat = «end».val := by
          rw [hyi, toNat_ofNat_val, end_post]; simp
        have hc : ((bytes y)[sp.ω + i.val]!).toNat < idx.val ∨ ((bytes y)[sp.ω + i.val]!).toNat > sp.ω :=
          Or.inr (by rw [hyi']; have : «end».val > ip.omega.val := ‹«end» > ip.omega›; omega)
        rw [← h3, rows_step_none sp _ _ _ hm hik hc]
        trivial
      · have hyi := bytes_get_of_eq y i1 _ i2 i2_post2 (sp.ω + i.val) (by omega)
        have hyi' : ((bytes y)[sp.ω + i.val]!).toNat = «end».val := by
          rw [hyi, toNat_ofNat_val, end_post]; simp
        have hnc : ¬ (((bytes y)[sp.ω + i.val]!).toNat < idx.val ∨
            ((bytes y)[sp.ω + i.val]!).toNat > sp.ω) := by
          rw [hyi']
          have h1' : ¬ «end».val < idx.val := ‹¬«end» < idx›
          have h2' : ¬ «end».val > ip.omega.val := ‹¬«end» > ip.omega›
          omega
        have ea : toHint a = hm[i.val]! := by rw [a_post2]; exact hrowi
        rw [ea] at b_post
        rcases hrl : rowLoop (bytes y) idx.val («end».val - idx.val) idx.val hm[i.val]! with _ | rm
        · rw [hrl] at b_post
          have hb : b = true := ‹b = true›
          rw [b_post] at hb
          exact absurd hb (by simp)
        · rw [hrl] at b_post
          refine ⟨by omega, ⟨hm.set! i.val rm, ?_, ?_⟩, by omega⟩
          · rw [a_post3]
            exact reprHintVec_set hr i a1 rm b_post.2
          · rw [← h3, rows_step_ok sp _ _ _ hm hik hnc rm (by rw [hyi']; exact hrl), hyi', i3_post]
      · have hyi := bytes_get_of_eq y i1 _ i2 i2_post2 (sp.ω + i.val) (by omega)
        have hyi' : ((bytes y)[sp.ω + i.val]!).toNat = «end».val := by
          rw [hyi, toNat_ofNat_val, end_post]; simp
        have hnc : ¬ (((bytes y)[sp.ω + i.val]!).toNat < idx.val ∨
            ((bytes y)[sp.ω + i.val]!).toNat > sp.ω) := by
          rw [hyi']
          have h1' : ¬ «end».val < idx.val := ‹¬«end» < idx›
          have h2' : ¬ «end».val > ip.omega.val := ‹¬«end» > ip.omega›
          omega
        have ea : toHint a = hm[i.val]! := by rw [a_post2]; exact hrowi
        rw [ea] at b_post
        rcases hrl : rowLoop (bytes y) idx.val («end».val - idx.val) idx.val hm[i.val]! with _ | rm
        · rw [hrl] at b_post
          rw [← h3, rows_step_none' sp _ _ _ hm hik hnc (by rw [hyi']; exact hrl)]
          trivial
        · rw [hrl] at b_post
          exact absurd b_post.1 ‹¬b = true›
    · rename_i hlt
      have hlt' : ¬ i.val < K.val := hlt
      have hik : i.val = sp.k := by omega
      simp only [WP.spec_ok]
      rw [hik, Nat.sub_self] at h3
      rw [← h3]
      exact ⟨idx, rfl, rfl, hr⟩
  · refine ⟨by simp, hm0, hh0, ?_⟩
    simp


theorem efoldv_gOut_inl (sp : Params) (ys : List UInt8) :
    ∀ (l : List Nat) (b : MProd Nat (Vector HintPoly sp.k)) (a : Option (Vector HintPoly sp.k)),
      efoldv (gOut sp ys) l b = .inl a → a = none := by
  intro l
  induction l with
  | nil => intro b a h; simp [efoldv] at h
  | cons i l ih =>
    intro b a h
    simp only [efoldv] at h
    unfold gOut at h
    by_cases hc : (ys[sp.ω + i]!).toNat < b.fst ∨ (ys[sp.ω + i]!).toNat > sp.ω
    · rw [if_pos hc] at h
      simp only [Sum.inl.injEq] at h
      exact h.symm
    · rw [if_neg hc] at h
      rcases hrl : rowLoop ys b.fst ((ys[sp.ω + i]!).toNat - b.fst) b.fst b.snd[i]! with _ | row
      · rw [hrl] at h
        simp only [Sum.inl.injEq] at h
        exact h.symm
      · rw [hrl] at h
        exact ih _ a h

theorem toHint_repeat_false :
    toHint (Array.repeat 256#usize false) = Vector.replicate 256 false := by
  apply Vector.ext
  intro k hk
  simp only [toHint, Vector.getElem_ofFn, Array.repeat_val, List.getElem_replicate,
    Vector.getElem_replicate]

theorem reprHintVec_repeat (K : Usize) :
    ReprHintVec (Array.repeat K (Array.repeat 256#usize false))
      (Vector.replicate K.val (Vector.replicate 256 false)) := by
  refine ⟨rfl, fun i hi => ?_⟩
  unfold ReprHint
  simp [Array.repeat_val, toHint_repeat_false]

end HintAux

@[step]
theorem hint_bit_unpack_rows_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (y : Slice U8) (hy : y.val.length = sp.ω + sp.k)
    (h0 : Array (Array Bool 256#usize) K) (hm0 : Vector HintPoly sp.k) (hh0 : ReprHintVec h0 hm0) :
    encode.hint_bit_unpack_rows ip y h0 ⦃ r =>
      match efoldv (gOut sp (bytes y)) (List.range' 0 sp.k) ⟨0, hm0⟩ with
      | .inl _ => r.1 = none
      | .inr s => ∃ idx : Usize, r.1 = some idx ∧ idx.val = s.fst ∧ ReprHintVec r.2 s.snd ⦄ :=
  hint_bit_unpack_rows_loop_spec ip sp hp y hy h0 hm0 hh0

namespace HintAux


end HintAux

theorem hint_bit_unpack_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (y : Slice U8) (hy : y.length = sp.ω + sp.k) :
    encode.hint_bit_unpack K ip y ⦃ r =>
      match r, Spec.HintBitUnpack sp (bytes y) with
      | none, none => True
      | some h, some h' => ReprHintVec h h'
      | _, _ => False ⦄ := by
  have hy' : y.val.length = sp.ω + sp.k := hy
  have hrep : ReprHintVec (Array.repeat K (Array.repeat 256#usize false))
      (Vector.replicate sp.k (Vector.replicate 256 false)) := by
    have := reprHintVec_repeat K
    rw [hp.K_eq] at this
    exact this
  have hrows := hint_bit_unpack_rows_spec ip sp hp y hy' _ _ hrep
  rw [unpack_eq]
  unfold unpackModel
  unfold encode.hint_bit_unpack
  step with hrows
  generalize hT : efoldv (gOut sp (bytes y)) (List.range' 0 sp.k)
    ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ = T at r_post ⊢
  rcases T with a | s
  · simp only at r_post
    rw [r_post]
    have := efoldv_gOut_inl sp _ _ _ a hT
    rw [this]
    simp only [WP.spec_ok]
  · obtain ⟨idx, hr, hidx, hrv⟩ := r_post
    rw [hr]
    simp only
    have hωy : ip.omega.val ≤ y.val.length := by rw [hp.omega]; omega
    step*
    · have hb : b = true := ‹b = true›
      rw [hb] at b_post
      have hp' : padB (bytes y) sp.ω s.fst = true := by
        rw [← hidx, ← hp.omega]; exact b_post.symm
      rw [if_pos hp']
      exact hrv
    · have hbt : ¬ b = true := ‹¬ b = true›
      have hp' : ¬ padB (bytes y) sp.ω s.fst = true := by
        rw [← hidx, ← hp.omega, ← b_post]; exact hbt
      rw [if_neg hp']
      trivial

namespace HintAux



/-! ## HintBitPack: the spec as an explicit fold -/

theorem bind_forIn_foldl {α β γ : Type} (l : List α) (f : α → β → Id (ForInStep β)) (F : α → β → β)
    (hf : ∀ a, a ∈ l → ∀ b, f a b = pure (ForInStep.yield (F a b))) (K : β → Id γ) (b : β) :
    (forIn l b f >>= K) = K (l.foldl (fun b a => F a b) b) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hf a (by simp) b]
    simp only [pure_bind, List.foldl_cons]
    exact ih (fun a ha => hf a (by simp [ha])) _

def packRowF (row : HintPoly) (j : Nat) (st : MProd Nat (Array UInt8)) : MProd Nat (Array UInt8) :=
  if row[j]! = true then ⟨st.fst + 1, st.snd.set! st.fst j.toUInt8⟩ else st

def packRow (row : HintPoly) (st : MProd Nat (Array UInt8)) : MProd Nat (Array UInt8) :=
  (List.range' 0 256).foldl (fun b a => packRowF row a b) st

def packRowsF (ω : Nat) {k : Nat} (h : Vector HintPoly k) (i : Nat) (st : MProd Nat (Array UInt8)) :
    MProd Nat (Array UInt8) :=
  ⟨(packRow h[i]! st).fst, (packRow h[i]! st).snd.set! (ω + i) (packRow h[i]! st).fst.toUInt8⟩

def packModel (sp : Params) (h : Vector HintPoly sp.k) : List UInt8 :=
  ((List.range' 0 sp.k).foldl (fun b i => packRowsF sp.ω h i b)
    ⟨0, Array.replicate (sp.ω + sp.k) 0⟩).snd.toList

theorem pack_eq (sp : Params) (h : Vector HintPoly sp.k) : HintBitPack sp h = packModel sp h := by
  unfold HintBitPack packModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine congrArg Id.run ?_
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


/-! ## HintBitPack: weights -/

def cntFrom (row : HintPoly) (j : Nat) : Nat := (row.toList.drop j).countP (fun b => b)

def restW {k : Nat} (h : Vector HintPoly k) (i : Nat) : Nat :=
  ((h.toList.drop i).map (fun r => r.toList.countP (fun b => b))).sum

theorem cntFrom_succ (row : HintPoly) (j : Nat) (hj : j < 256) :
    cntFrom row j = (if row[j]! = true then 1 else 0) + cntFrom row (j + 1) := by
  have hl : j < row.toList.length := by simpa using hj
  unfold cntFrom
  rw [List.drop_eq_getElem_cons hl, List.countP_cons, getElem!_pos _ _ (by simpa using hj)]
  simp only [Vector.getElem_toList]
  by_cases hb : row[j] = true <;> simp [hb]; omega

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

theorem vcountP (xs : Vector Bool n) : xs.countP (fun b => b) = xs.toList.countP (fun b => b) := by
  rcases xs with ⟨⟨l⟩, hl⟩
  simp [Vector.countP, Vector.toList]

theorem hintWeight_eq {k : Nat} (h : Vector HintPoly k) : HintWeight h = restW h 0 := by
  unfold HintWeight restW
  rw [← Vector.foldl_toList, List.drop_zero]
  simp only [vcountP]
  rw [foldl_add_sum (fun r : HintPoly => r.toList.countP (fun b => b))]
  simp


/-! ## Rust side: HintBitPack -/

/-- The model state read off a Rust output slice and write index. -/
def stOf (out : Slice U8) (index : Usize) : MProd Nat (Array UInt8) :=
  ⟨index.val, (bytes out).toArray⟩

theorem toHint_get (a : Array Bool 256#usize) (j : Nat) (hj : j < a.val.length) (hj' : j < 256) :
    (toHint a)[j]! = a.val[j] := by
  rw [getElem!_pos _ _ (by simpa using hj')]
  simp [toHint]

theorem foldl_range'_step {β : Type} (f : β → Nat → β) (j : Nat) (hj : j < 256) (b : β) :
    (List.range' j (256 - j)).foldl f b = (List.range' (j + 1) (256 - (j + 1))).foldl f (f b j) := by
  obtain ⟨n, hn⟩ : ∃ n, 256 - j = n + 1 := ⟨256 - j - 1, by omega⟩
  rw [hn, List.range'_succ, List.foldl_cons, show 256 - (j + 1) = n by omega]

theorem stOf_pack_true (o1 o' : Slice U8) (idx1 x : Usize) (c : U8) (j : Nat) (hc : c.val = j)
    (ho' : o' = o1.set idx1 c) (hx : x.val = idx1.val + 1) :
    stOf o' x = ⟨(stOf o1 idx1).fst + 1, (stOf o1 idx1).snd.set! (stOf o1 idx1).fst j.toUInt8⟩ := by
  unfold stOf
  subst ho'
  simp only [MProd.mk.injEq]
  refine ⟨hx, ?_⟩
  apply Array.ext'
  simp [bytes_set, hc, Nat.toUInt8]

theorem pack_inner_spec {K : Usize} {k : Nat} (h : Array (Array Bool 256#usize) K)
    (hm : Vector HintPoly k) (hr : ReprHintVec h hm) (i : Usize) (hi : i.val < K.val)
    (out : Slice U8) (index j : Usize) (hj : j.val ≤ 256)
    (hw : index.val + cntFrom hm[i.val]! j.val + restW hm (i.val + 1) ≤ out.val.length) :
    encode.hint_bit_pack_loop1_loop0 h out index i j ⦃ r =>
      bytes r.1 = ((List.range' j.val (256 - j.val)).foldl
        (fun b a => packRowF hm[i.val]! a b) (stOf out index)).snd.toList ∧
      r.2.val = ((List.range' j.val (256 - j.val)).foldl
        (fun b a => packRowF hm[i.val]! a b) (stOf out index)).fst ∧
      r.1.val.length = out.val.length ∧
      r.2.val + restW hm (i.val + 1) ≤ out.val.length ⦄ := by
  unfold encode.hint_bit_pack_loop1_loop0
  have hrowi := reprHintVec_get hr i hi
  apply loop.spec_decr_nat (fun p : Slice U8 × Usize × Usize => 256 - p.2.2.val)
    (fun p => p.2.2.val ≤ 256 ∧ p.1.val.length = out.val.length ∧
      p.2.1.val + cntFrom hm[i.val]! p.2.2.val + restW hm (i.val + 1) ≤ out.val.length ∧
      (List.range' p.2.2.val (256 - p.2.2.val)).foldl (fun b a => packRowF hm[i.val]! a b)
        (stOf p.1 p.2.1) =
      (List.range' j.val (256 - j.val)).foldl (fun b a => packRowF hm[i.val]! a b) (stOf out index))
  · rintro ⟨o1, idx1, jj⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simp only [encode.hint_bit_pack_loop1_loop0.body]
    split
    · rename_i hlt
      have hlt' : jj.val < 256 := hlt
      have hik : i.val < k := by have := hr.len; omega
      step*
      rename_i xb
      have e : toHint (h.val[i.val]'a) = hm[i.val]! := hrowi
      have hrb : (hm[i.val]!)[jj.val]! = xb := by
        rw [← e, ← a_post2, toHint_get _ _ b hlt', ← b_post2]
      have hcs := cntFrom_succ hm[i.val]! jj.val hlt'
      rw [hrb] at hcs
      have hstep := foldl_range'_step (fun b a => packRowF hm[i.val]! a b) jj.val hlt' (stOf o1 idx1)
      have hl1 : o1.length = o1.val.length := rfl
      by_cases hb : xb = true
      · have hcs' : cntFrom hm[i.val]! jj.val = 1 + cntFrom hm[i.val]! (jj.val + 1) := by
          rw [hb] at hcs; simpa using hcs
        have hidx : idx1.val < o1.length := by omega
        simp only [hb, if_true]
        step*
        rename_i _ c _ hcdef o2 _ _
        have hl2 : o2.length = o2.val.length := rfl
        have hc : c.val = jj.val := by
          rw [hcdef]; simp; omega
        have hst := stOf_pack_true o1 o2 idx1 x c jj.val hc x_post2 x_post
        have hstep2 : packRowF hm[i.val]! jj.val (stOf o1 idx1) = stOf o2 x := by
          rw [hst]; unfold packRowF; rw [hrb, hb]; simp
        rw [hstep2] at hstep
        have hlen2 : o2.val.length = o1.val.length := by rw [x_post2]; simp [Slice.set]
        refine ⟨by omega, by omega, ?_, ?_, by omega⟩
        · rw [j1_post]; omega
        · rw [j1_post, ← hstep]; exact h4
      · simp only [hb, Bool.false_eq_true, if_false]
        step*
        have hb' : xb = false := by simpa using hb
        have hcs' : cntFrom hm[i.val]! jj.val = cntFrom hm[i.val]! (jj.val + 1) := by
          rw [hb'] at hcs; simpa using hcs
        have hstep2 : packRowF hm[i.val]! jj.val (stOf o1 idx1) = stOf o1 idx1 := by
          unfold packRowF; rw [hrb, hb']; simp
        rw [hstep2] at hstep
        refine ⟨by omega, h2, ?_, ?_, by omega⟩
        · rw [j1_post]; omega
        · rw [j1_post, ← hstep]; exact h4
    · rename_i hlt
      have hlt' : ¬ jj.val < 256 := hlt
      have hj1 : jj.val = 256 := by omega
      simp only [WP.spec_ok]
      rw [hj1, Nat.sub_self] at h4
      rw [← h4]
      have h3' := h3
      rw [hj1, cntFrom_256] at h3'
      exact ⟨by simp [stOf], by simp [stOf], h2, by omega⟩
  · exact ⟨hj, rfl, hw, rfl⟩


theorem foldl_range'_stepn {β : Type} (f : β → Nat → β) (n j : Nat) (hj : j < n) (b : β) :
    (List.range' j (n - j)).foldl f b = (List.range' (j + 1) (n - (j + 1))).foldl f (f b j) := by
  obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
  rw [hm, List.range'_succ, List.foldl_cons, show n - (j + 1) = m by omega]

theorem stOf_row_end (out2 s : Slice U8) (index2 i3 : Usize) (c : U8) (st' : MProd Nat (Array UInt8))
    (hb : bytes out2 = st'.snd.toList) (hi : index2.val = st'.fst) (hc : c.val = index2.val % 256)
    (hs : s = out2.set i3 c) :
    stOf s index2 = ⟨st'.fst, st'.snd.set! i3.val st'.fst.toUInt8⟩ := by
  unfold stOf
  subst hs
  simp only [MProd.mk.injEq]
  refine ⟨hi, ?_⟩
  apply Array.ext'
  simp only [bytes_set, hb, _root_.Array.set!_eq_setIfInBounds,
    _root_.Array.toList_setIfInBounds, hc]
  congr 1
  rw [← hi, Nat.toUInt8]
  exact UInt8.ofNat_mod_size


theorem pack_outer_spec {K : Usize} {k : Nat} (off : Usize) (h : Array (Array Bool 256#usize) K)
    (hm : Vector HintPoly k) (hr : ReprHintVec h hm) (ω : Nat) (hoff : off.val = ω)
    (out : Slice U8) (hlen : out.val.length = ω + k) (index i1 : Usize) (hi1 : i1.val ≤ K.val)
    (hw : index.val + restW hm i1.val ≤ out.val.length) :
    encode.hint_bit_pack_loop1 off h out index i1 ⦃ out' =>
      bytes out' = ((List.range' i1.val (k - i1.val)).foldl
        (fun b i => packRowsF ω hm i b) (stOf out index)).snd.toList ⦄ := by
  unfold encode.hint_bit_pack_loop1
  have hKk : K.val = k := hr.len
  have hylen := out.property
  apply loop.spec_decr_nat (fun p : Slice U8 × Usize × Usize => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ p.1.val.length = out.val.length ∧
      p.2.1.val + restW hm p.2.2.val ≤ out.val.length ∧
      (List.range' p.2.2.val (k - p.2.2.val)).foldl (fun b i => packRowsF ω hm i b) (stOf p.1 p.2.1) =
      (List.range' i1.val (k - i1.val)).foldl (fun b i => packRowsF ω hm i b) (stOf out index))
  · rintro ⟨o1, idx1, ii⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simp only [encode.hint_bit_pack_loop1.body]
    split
    · rename_i hlt
      have hlt' : ii.val < K.val := hlt
      have hik : ii.val < k := by omega
      have hrs := restW_succ hm ii.val hik
      have hin := pack_inner_spec h hm hr ii hlt' o1 idx1 0#usize (by simp) (by simp; omega)
      step with hin
      have hbound : off.val + ii.val < o1.val.length := by omega
      step*
      have hst := stOf_row_end out1 s index1 i2 i3
        (packRow hm[ii.val]! (stOf o1 idx1)) (by simpa [packRow] using out1_post1)
        (by simpa [packRow] using out1_post2) (by rw [i3_post]; simp) s_post2
      have hrow : packRowsF ω hm ii.val (stOf o1 idx1) = stOf s index1 := by
        rw [hst]; unfold packRowsF; rw [i2_post, hoff]
      have hfs := foldl_range'_stepn (fun b i => packRowsF ω hm i b) k ii.val hik (stOf o1 idx1)
      rw [hrow] at hfs
      have hls : s.val.length = o1.val.length := by
        rw [s_post2]; simp [Slice.set]; exact out1_post3
      refine ⟨by omega, by omega, ?_, ?_, by omega⟩
      · rw [i4_post]; omega
      · rw [i4_post, ← hfs]
        exact h4
    · rename_i hlt
      have hlt' : ¬ ii.val < K.val := hlt
      have hii : ii.val = k := by omega
      simp only [WP.spec_ok]
      rw [hii, Nat.sub_self] at h4
      rw [← h4]
      simp [stOf]
  · exact ⟨hi1, rfl, hw, rfl⟩


theorem pack_zero_spec (K : Usize) (ip : Impl.params.Params) (out : Slice U8)
    (hlen : out.val.length = ip.omega.val + K.val) :
    encode.hint_bit_pack_loop0 K ip out 0#usize ⦃ r =>
      r.1 = ip.omega ∧ bytes r.2 = List.replicate (ip.omega.val + K.val) 0 ⦄ := by
  unfold encode.hint_bit_pack_loop0
  have hylen := out.property
  apply loop.spec_decr_nat (fun p : Slice U8 × Usize => ip.omega.val + K.val - p.2.val)
    (fun p => p.2.val ≤ ip.omega.val + K.val ∧ p.1.val.length = out.val.length ∧
      ∀ m (hm : m < (bytes p.1).length), m < p.2.val → (bytes p.1)[m] = 0)
  · rintro ⟨o1, ii⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.hint_bit_pack_loop0.body]
    step*
    · have hlt'' : ii.val < i1.val := ‹ii < i1›
      have hlt' : ii.val < ip.omega.val + K.val := by omega
      have hb : bytes s = (bytes o1).set ii.val (UInt8.ofNat (0#u8).val) := by
        rw [s_post2, bytes_set]
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [s_post2]; simp [Slice.set, h2]
      · intro m hm hmi
        simp only [hb, List.getElem_set]
        by_cases hmm : ii.val = m
        · simp [hmm]
        · simp only [hmm, if_false]
          have hm' := hm
          simp only [bytes_length] at hm'
          have hls : s.val.length = o1.val.length := by rw [s_post2]; simp [Slice.set]
          exact h3 m (by simp only [bytes_length]; omega) (by omega)
    · have hnl : ¬ ii.val < i1.val := ‹¬ ii < i1›
      have hii : ii.val = ip.omega.val + K.val := by omega
      apply List.ext_getElem
      · simp only [bytes_length, List.length_replicate]; omega
      · intro m hm1 hm2
        rw [List.getElem_replicate]
        have hm1' := hm1
        simp only [bytes_length] at hm1'
        exact h3 m hm1 (by omega)
  · exact ⟨by simp, rfl, fun m _ hm => by simp at hm⟩


end HintAux

theorem hint_bit_pack_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (h : Array (Array Bool 256#usize) K) (h' : Vector HintPoly sp.k)
    (hr : ReprHintVec h h') (hw : HintWeight h' ≤ sp.ω) (out : Slice U8)
    (hout : out.length = sp.ω + sp.k) :
    encode.hint_bit_pack ip h out ⦃ out' => bytes out' = Spec.HintBitPack sp h' ⦄ := by
  have hout' : out.val.length = ip.omega.val + K.val := by
    rw [hp.omega, hp.K_eq]; exact hout
  have hz := pack_zero_spec K ip out hout'
  unfold encode.hint_bit_pack
  step with hz
  have hk : K.val = sp.k := hp.K_eq
  have hlen1 : out1.val.length = sp.ω + sp.k := by
    have := congrArg List.length i_post2
    simp only [bytes_length, List.length_replicate] at this
    rw [this, hp.omega, hk]
  have hbyt : bytes out1 = List.replicate (sp.ω + sp.k) 0 := by
    rw [i_post2, hp.omega, hk]
  have hst : stOf out1 0#usize = ⟨0, Array.replicate (sp.ω + sp.k) 0⟩ := by
    unfold stOf
    simp only [MProd.mk.injEq]
    refine ⟨rfl, ?_⟩
    apply Array.ext'
    simp [hbyt]
  have hweight : (0#usize).val + restW h' 0 ≤ out1.val.length := by
    rw [← hintWeight_eq]; simp; omega
  have hout2 := pack_outer_spec i h h' hr sp.ω (by rw [i_post1, hp.omega]) out1 hlen1 0#usize 0#usize
    (by simp) hweight
  step with hout2
  rw [pack_eq]
  unfold packModel
  rw [hst] at out'_post
  simpa using out'_post

namespace HintAux


end HintAux

end Proofs
