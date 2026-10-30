import Spec.Sampling
import Proofs.Keccak
import Proofs.Encode

/-!
# SampleInBall (FIPS 204 Algorithm 29): the extracted `sample_in_ball` equals the spec

`Spec.SampleInBall p fuel ρ` squeezes `8 + fuel` bytes of `SHAKE256 ρ`, takes the first 8 as sign bits and, for
`i = 256 - τ .. 255`, reads bytes until one is `≤ i`. The Rust inner `while j > i` is unbounded.

## Termination

The theorem is conditional on `Spec.SampleInBall sp fuel (bytes ρ) = some c`. Part A rewrites the spec's nested
`forIn` loops into pure functions (`sibFind`, `sibStep`, `sibRun`; `SampleInBall_eq`). From the `some` run, the
inner search `sibFind S i k pos j` succeeds for some budget `k`; the Rust inner loop is proved with
`loop.spec_decr_nat` and the measure `Nat.find` of the least such `k` (a function of the loop state, via
classical choice), which decreases at every iteration. The Rust never reads past the `8 + fuel` bytes the spec
reads.

## Hypotheses
`hτ : τ ≤ 64` (the Rust sign word is a `u64`; `ML_DSA_*_tau` for the standard sets), `Params.Valid`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Part A: the spec's loops as pure functions -/

abbrev SibState := MProd (Option (Option RPoly)) (MProd RPoly Ctx)
abbrev InnerState := MProd (Option (Option RPoly)) (MProd Ctx Nat)

/-- `forIn` over `List.range' s k` in `Id`, for a body that is a pure transition function. -/
def iterT {σ : Type} (t : Nat → σ → ForInStep σ) : Nat → Nat → σ → σ
  | _, 0, st => st
  | s, k + 1, st =>
    match t s st with
    | .done st' => st'
    | .yield st' => iterT t (s + 1) k st'

theorem forIn_range'_iterT {σ : Type} (t : Nat → σ → ForInStep σ) (f : Nat → σ → Id (ForInStep σ))
    (hf : ∀ x st, f x st = pure (t x st)) :
    ∀ (k s : Nat) (st : σ), forIn (m := Id) (List.range' s k) st f = iterT t s k st := by
  intro k
  induction k with
  | zero => intro s st; rfl
  | succ k ih =>
    intro s st
    rw [List.range'_succ, List.forIn_cons, hf]
    cases h : t s st <;> simp [iterT, h, ih] <;> try rfl

/-- The body of the spec's inner loop (Algorithm 29, steps 8-10). -/
def innerT (i : Nat) : Nat → InnerState → ForInStep InnerState := fun _ r =>
  if r.snd.snd ≤ i then ForInStep.done ⟨none, r.snd.fst, r.snd.snd⟩
  else
    match H.Squeeze r.snd.fst 1 with
    | some (ctx', s₁) => ForInStep.yield ⟨none, ctx', (s₁[0]?.getD default).toNat⟩
    | x => ForInStep.done ⟨some none, r.snd.fst, r.snd.snd⟩

/-- The inner search: read bytes from position `pos` of the stream until one is `≤ i`, with `k` reads allowed. -/
def sibFind (S : List UInt8) (i : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, pos, j => if j ≤ i then some (j, pos) else none
  | k + 1, pos, j =>
    if j ≤ i then some (j, pos)
    else if pos + 1 ≤ S.length then sibFind S i k (pos + 1) ((S[pos]?.getD default).toNat) else none

theorem sibFind_le (S : List UInt8) (i : Nat) : ∀ k pos j j' pos', sibFind S i k pos j = some (j', pos') → j' ≤ i := by
  intro k
  induction k with
  | zero =>
    intro pos j j' pos' h
    simp only [sibFind] at h
    split at h
    · simp at h; omega
    · simp at h
  | succ k ih =>
    intro pos j j' pos' h
    simp only [sibFind] at h
    split at h
    · simp at h; omega
    · split at h
      · exact ih _ _ _ _ h
      · simp at h

theorem inner_iter (S : List UInt8) (i : Nat) : ∀ (k s pos j : Nat),
    (∃ j' pos', sibFind S i k pos j = some (j', pos') ∧
        iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩ = ⟨none, ⟨S, pos'⟩, j'⟩) ∨
    (sibFind S i k pos j = none ∧
        ((iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).fst = some none ∨
         ((iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).fst = none ∧
          i < (iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).snd.snd))) := by
  intro k
  induction k with
  | zero =>
    intro s pos j
    by_cases h : j ≤ i
    · left; exact ⟨j, pos, by simp [sibFind, h], by simp [iterT]⟩
    · right; refine ⟨by simp [sibFind, h], Or.inr ⟨by simp [iterT], ?_⟩⟩; simp [iterT]; omega
  | succ k ih =>
    intro s pos j
    by_cases h : j ≤ i
    · left; exact ⟨j, pos, by simp [sibFind, h], by simp [iterT, innerT, h]⟩
    · by_cases hp : pos + 1 ≤ S.length
      · have e : iterT (innerT i) s (k + 1) ⟨none, ⟨S, pos⟩, j⟩ =
            iterT (innerT i) (s + 1) k ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩ := by
          simp [iterT, innerT, h, H.Squeeze, Ctx.Squeeze, hp]
        have e2 : sibFind S i (k + 1) pos j = sibFind S i k (pos + 1) ((S[pos]?.getD default).toNat) := by
          simp [sibFind, h, hp]
        rw [e, e2]
        exact ih (s + 1) (pos + 1) _
      · right
        refine ⟨by simp [sibFind, h, hp], Or.inl ?_⟩
        simp [iterT, innerT, h, H.Squeeze, Ctx.Squeeze, hp]

/-- The body of the spec's outer loop (Algorithm 29, steps 7-12). -/
def outerT (hb : List Bool) (τ fuel : Nat) : Nat → SibState → ForInStep SibState := fun i r =>
  match H.Squeeze r.snd.snd 1 with
  | some (ctx', s₁) =>
    let r_1 := iterT (innerT i) 0 fuel ⟨none, ctx', (s₁[0]?.getD default).toNat⟩
    match r_1.fst with
    | none =>
      if i < r_1.2.snd then ForInStep.done ⟨some none, r.snd.fst, r_1.2.fst⟩
      else
        ForInStep.yield
          ⟨none, (Vector.set! r.snd.fst i r.snd.fst[r_1.2.snd]!).set! r_1.2.snd
            (if hb[i + τ - 256]?.getD false = true then -1 else 1), r_1.2.fst⟩
    | some a => ForInStep.done ⟨some a, r.snd.fst, r_1.2.fst⟩
  | x => ForInStep.done ⟨some none, r.snd.fst, r.snd.snd⟩

/-- One iteration of the outer loop as a function of `(c, pos)`. -/
def sibStep (S : List UInt8) (hb : List Bool) (τ fuel : Nat) (st : RPoly × Nat) (i : Nat) :
    Option (RPoly × Nat) :=
  if st.2 + 1 ≤ S.length then
    match sibFind S i fuel (st.2 + 1) ((S[st.2]?.getD default).toNat) with
    | none => none
    | some (j, pos') =>
      some ((st.1.set! i st.1[j]!).set! j (if hb[i + τ - 256]?.getD false = true then -1 else 1), pos')
  else none

theorem outerT_step (S : List UInt8) (hb : List Bool) (τ fuel i : Nat) (c : RPoly) (pos : Nat) :
    (∀ c' pos', sibStep S hb τ fuel (c, pos) i = some (c', pos') →
      outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ = ForInStep.yield ⟨none, c', ⟨S, pos'⟩⟩) ∧
    (sibStep S hb τ fuel (c, pos) i = none →
      ∃ st : SibState, outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ = ForInStep.done st ∧ st.fst = some none) := by
  by_cases hp : pos + 1 ≤ S.length
  · have e : outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ =
        (let r_1 := iterT (innerT i) 0 fuel ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩
         match r_1.fst with
         | none =>
           if i < r_1.2.snd then ForInStep.done ⟨some none, c, r_1.2.fst⟩
           else ForInStep.yield ⟨none, (Vector.set! c i c[r_1.2.snd]!).set! r_1.2.snd
              (if hb[i + τ - 256]?.getD false = true then -1 else 1), r_1.2.fst⟩
         | some a => ForInStep.done ⟨some a, c, r_1.2.fst⟩) := by
      simp [outerT, H.Squeeze, Ctx.Squeeze, hp]
    rw [e]
    rcases inner_iter S i fuel 0 (pos + 1) ((S[pos]?.getD default).toNat) with
      ⟨j', pos', h1, h2⟩ | ⟨h1, h2⟩
    · have hj := sibFind_le S i _ _ _ _ _ h1
      simp only [h2]
      refine ⟨fun c' pos'' h => ?_, fun h => ?_⟩
      · simp only [sibStep, hp, if_true, h1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [show ¬ i < j' by omega]
      · simp [sibStep, hp, h1] at h
    · generalize iterT (innerT i) 0 fuel ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩ = R at h2 ⊢
      obtain ⟨f, cx, jx⟩ := R
      refine ⟨fun c' pos'' h => ?_, fun h => ?_⟩
      · simp only [sibStep, hp, if_true, h1] at h
        simp at h
      · cases f with
        | none =>
          simp at h2
          exact ⟨⟨some none, c, cx⟩, by simp [h2], by simp⟩
        | some a =>
          simp at h2
          subst h2
          exact ⟨⟨some none, c, cx⟩, by simp, by simp⟩
  · constructor
    · intro c' pos' h
      simp [sibStep, hp] at h
    · intro _
      exact ⟨⟨some none, c, ⟨S, pos⟩⟩, by simp [outerT, H.Squeeze, Ctx.Squeeze, hp], by simp⟩

theorem outer_iter (S : List UInt8) (hb : List Bool) (τ fuel : Nat) : ∀ (n s : Nat) (c : RPoly) (pos : Nat),
    (∃ c' pos', (List.range' s n).foldlM (sibStep S hb τ fuel) (c, pos) = some (c', pos') ∧
        iterT (outerT hb τ fuel) s n ⟨none, c, ⟨S, pos⟩⟩ = ⟨none, c', ⟨S, pos'⟩⟩) ∨
    ((List.range' s n).foldlM (sibStep S hb τ fuel) (c, pos) = none ∧
        (iterT (outerT hb τ fuel) s n ⟨none, c, ⟨S, pos⟩⟩).fst = some none) := by
  intro n
  induction n with
  | zero =>
    intro s c pos
    left; exact ⟨c, pos, by simp, by simp [iterT]⟩
  | succ n ih =>
    intro s c pos
    obtain ⟨hy, hd⟩ := outerT_step S hb τ fuel s c pos
    cases hst : sibStep S hb τ fuel (c, pos) s with
    | none =>
      right
      obtain ⟨st, h1, h2⟩ := hd hst
      refine ⟨by simp [List.range'_succ, hst], ?_⟩
      simp [iterT, h1, h2]
    | some r =>
      obtain ⟨c', pos'⟩ := r
      have h1 := hy c' pos' hst
      have e : iterT (outerT hb τ fuel) s (n + 1) ⟨none, c, ⟨S, pos⟩⟩ =
          iterT (outerT hb τ fuel) (s + 1) n ⟨none, c', ⟨S, pos'⟩⟩ := by
        simp [iterT, h1]
      rw [e]
      have e2 : (List.range' s (n + 1)).foldlM (sibStep S hb τ fuel) (c, pos) =
          (List.range' (s + 1) n).foldlM (sibStep S hb τ fuel) (c', pos') := by
        simp [List.range'_succ, hst]
      rw [e2]
      exact ih (s + 1) c' pos'

/-- The model of Algorithm 29 on the stream `S = H ρ (8 + fuel)`. -/
def sibRun (S : List UInt8) (τ fuel : Nat) : Option (RPoly × Nat) :=
  (List.range' (256 - τ) τ).foldlM (sibStep S (BytesToBits (S.take 8)) τ fuel) (Vector.replicate 256 0, 8)

theorem SampleInBall_eq (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) :
    Spec.SampleInBall p fuel ρ = (sibRun (H ρ (8 + fuel)) p.τ fuel).map Prod.fst := by
  unfold Spec.SampleInBall
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hsq : H.Squeeze (H.InitAbsorb (8 + fuel) ρ) 8 =
      some (⟨H ρ (8 + fuel), 8⟩, ((H ρ (8 + fuel)).drop 0).take 8) := by
    have hl : (H ρ (8 + fuel)).length = 8 + fuel := SHAKE256_length _ _
    simp [H.Squeeze, Ctx.Squeeze, H.InitAbsorb, hl]
  simp [hsq]
  unfold sibRun
  generalize H ρ (8 + fuel) = S
  rw [Nat.sub_sub_self hτ]
  rw [forIn_range'_iterT (outerT (BytesToBits (S.take 8)) p.τ fuel) _ ?hF]
  · rcases outer_iter S (BytesToBits (S.take 8)) p.τ fuel p.τ (256 - p.τ) (Vector.replicate 256 0) 8 with
      ⟨c', pos', h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; rfl
    · rw [h1]
      generalize iterT (outerT (BytesToBits (S.take 8)) p.τ fuel) (256 - p.τ) p.τ
        ⟨none, Vector.replicate 256 0, ⟨S, 8⟩⟩ = R at h2 ⊢
      obtain ⟨f, c, ctx⟩ := R
      simp at h2
      subst h2
      rfl
  · intro i r
    simp only [outerT]
    cases hq : H.Squeeze r.snd.snd 1 with
    | none => rfl
    | some v =>
      obtain ⟨ctx', s₁⟩ := v
      dsimp only
      rw [forIn_range'_iterT (innerT i) _ ?hI]
      · rfl
      · intro x r'
        simp only [innerT]
        split_ifs with hh
        · rfl
        · cases hq' : H.Squeeze r'.snd.fst 1 with
          | none => rfl
          | some v' => obtain ⟨a, b⟩ := v'; rfl

/-! ## Consequences of the model -/

theorem SampleInBall_model (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) (c : RPoly)
    (hs : Spec.SampleInBall p fuel ρ = some c) :
    ∃ pos, sibRun (H ρ (8 + fuel)) p.τ fuel = some (c, pos) := by
  rw [SampleInBall_eq p hτ] at hs
  cases h : sibRun (H ρ (8 + fuel)) p.τ fuel with
  | none => rw [h] at hs; simp at hs
  | some r =>
    rw [h] at hs
    obtain ⟨c', pos⟩ := r
    simp at hs
    subst hs
    exact ⟨pos, rfl⟩

/-- Every coefficient is in `{-1, 0, 1}`. -/
def Ternary (c : RPoly) : Prop := ∀ k (hk : k < 256), c[k] = -1 ∨ c[k] = 0 ∨ c[k] = 1

theorem set!_getElem (c : RPoly) (i : Nat) (x : Int) (k : Nat) (hk : k < 256) :
    (c.set! i x)[k] = if i = k then x else c[k] := by
  rw [set!_eq']; exact Vector.getElem_setIfInBounds hk

theorem Ternary.set {c : RPoly} (h : Ternary c) (i : Nat) (x : Int) (hx : x = -1 ∨ x = 0 ∨ x = 1) :
    Ternary (c.set! i x) := by
  intro k hk
  rw [set!_getElem _ _ _ _ hk]
  split
  · exact hx
  · exact h k hk

theorem Ternary.getElem! {c : RPoly} (h : Ternary c) (j : Nat) (hj : j < 256) :
    c[j]! = -1 ∨ c[j]! = 0 ∨ c[j]! = 1 := by
  rw [getElem!_pos _ _ (by simpa using hj)]
  exact h j hj

theorem sibStep_ternary (S : List UInt8) (hb : List Bool) (τ fuel i : Nat) (hi : i < 256) (st st' : RPoly × Nat)
    (hst : Ternary st.1) (h : sibStep S hb τ fuel st i = some st') : Ternary st'.1 := by
  unfold sibStep at h
  split at h
  · cases hf : sibFind S i fuel (st.2 + 1) ((S[st.2]?.getD default).toNat) with
    | none => rw [hf] at h; simp at h
    | some r =>
      obtain ⟨j, pos'⟩ := r
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      have hj := sibFind_le S i _ _ _ _ _ hf
      refine Ternary.set (Ternary.set hst _ _ (hst.getElem! j (by omega))) _ _ ?_
      split <;> simp
  · simp at h

theorem foldlM_ternary (S : List UInt8) (hb : List Bool) (τ fuel : Nat) :
    ∀ (l : List Nat), (∀ i ∈ l, i < 256) → ∀ (st st' : RPoly × Nat), Ternary st.1 →
      l.foldlM (sibStep S hb τ fuel) st = some st' → Ternary st'.1 := by
  intro l
  induction l with
  | nil => intro _ st st' h hf; simp at hf; subst hf; exact h
  | cons a l ih =>
    intro hl st st' h hf
    rw [List.foldlM_cons] at hf
    cases h1 : sibStep S hb τ fuel st a with
    | none => rw [h1] at hf; simp at hf
    | some st1 =>
      rw [h1] at hf
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) st1 st'
        (sibStep_ternary S hb τ fuel a (hl a (List.mem_cons_self ..)) st st1 h h1) hf

theorem ternary_replicate : Ternary (Vector.replicate 256 (0 : Int)) := by
  intro k hk; right; left; simp

/-- **Coefficients of `SampleInBall`** (no premise besides the spec's fuel sufficing): `c` has coefficients in
`{-1, 0, 1}`. -/
theorem SampleInBall_ternary (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) (c : RPoly)
    (hs : Spec.SampleInBall p fuel ρ = some c) : ∀ k (hk : k < 256), c[k] = -1 ∨ c[k] = 0 ∨ c[k] = 1 := by
  obtain ⟨pos, h⟩ := SampleInBall_model p hτ fuel ρ c hs
  have := foldlM_ternary (H ρ (8 + fuel)) (BytesToBits ((H ρ (8 + fuel)).take 8)) p.τ fuel
    (List.range' (256 - p.τ) p.τ) (fun i hi => by
      rw [List.mem_range'_1] at hi; omega) _ (c, pos) ternary_replicate h
  exact this

/-! ## Part B: the sign word `h` -/

theorem testBit_byte_shift (b : Nat) (hb : b < 256) (k t : Nat) :
    (b <<< (8 * k)).testBit t = (decide (8 * k ≤ t) && b.testBit (t - 8 * k)) := by
  rw [Nat.testBit_shiftLeft]

theorem byte_testBit_high (b : Nat) (hb : b < 256) (u : Nat) (hu : 8 ≤ u) : b.testBit u = false := by
  apply Nat.testBit_eq_false_of_lt
  calc b < 2 ^ 8 := by omega
    _ ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) hu

theorem byteBit_testBit (v : List UInt8) (k u : Nat) (hu : u < 8) :
    (v[k]?.getD default).toNat.testBit u = decide (byteBit v (8 * k + u) = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold byteBit
  have e1 : (8 * k + u) / 8 = k := by omega
  have e2 : (8 * k + u) % 8 = u := by omega
  rw [e1, e2]

theorem h_loop_spec (s : Array U8 8#usize) :
    sampling.sample_in_ball_loop0 s 0#u64 0#usize ⦃ h => ∀ t, t < 64 →
      h.val.testBit t = decide (byteBit (bytesA s) t = 1) ⦄ := by
  unfold sampling.sample_in_ball_loop0
  apply loop.spec_decr_nat
    (fun (p : U64 × Usize) => 8 - p.2.val)
    (fun p => p.2.val ≤ 8 ∧ ∀ t, p.1.val.testBit t = (decide (t < 8 * p.2.val) && decide (byteBit (bytesA s) t = 1)))
  · rintro ⟨h, k⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.sample_in_ball_loop0.body]
    split
    · rename_i hk
      have hk' : k.val < 8 := by scalar_tac
      step*
      have hk8 : k.val < s.val.length := i
      have hb : (s.val[k.val]'hk8).val < 256 := by scalar_tac
      have hi1 : i1.val = (s.val[k.val]'hk8).val := by
        rw [i1_post, UScalar.cast_val_eq, i_post2]
        exact Nat.mod_eq_of_lt (by have : (2:Nat) ^ UScalarTy.U64.numBits = 2 ^ 64 := rfl
                                   omega)
      have hx : ((bytesA s)[k.val]?.getD default).toNat = (s.val[k.val]'hk8).val := by
        simp [bytesA, List.getElem?_eq_getElem hk8, toNat_ofNat_val]
      have hi3 : i3.val = (s.val[k.val]'hk8).val <<< (8 * k.val) := by
        rw [i3_post1, hi1, i2_post]
        apply Nat.mod_eq_of_lt
        rw [Nat.shiftLeft_eq]
        have h64 : U64.size = 2 ^ 64 := by
          first | scalar_tac | simp [U64.size, U64.numBits]
        rw [h64]
        calc (s.val[k.val]'hk8).val * 2 ^ (8 * k.val) < 2 ^ 8 * 2 ^ (8 * k.val) :=
              Nat.mul_lt_mul_of_pos_right hb (by positivity)
          _ = 2 ^ (8 + 8 * k.val) := by rw [← pow_add]
          _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨by omega, ?_, by omega⟩
      intro t
      have hh1 : h1.val = h.val ||| i3.val := by rw [h1_post1]; rfl
      rw [hh1, Nat.testBit_or, h2 t, hi3, Nat.testBit_shiftLeft]
      by_cases c1 : t < 8 * k.val
      · have : ¬ (8 * k.val ≤ t) := by omega
        simp [c1, this, k1_post, show t < 8 * (k.val + 1) by omega]
      · by_cases c2 : t < 8 * k.val + 8
        · have hu : t - 8 * k.val < 8 := by omega
          have h3 := byteBit_testBit (bytesA s) k.val (t - 8 * k.val) hu
          rw [show 8 * k.val + (t - 8 * k.val) = t by omega, hx] at h3
          simp [c1, c2, h3, k1_post, show 8 * k.val ≤ t by omega, show t < 8 * (k.val + 1) by omega]
        · rw [byte_testBit_high _ hb _ (by omega)]
          simp [c1, k1_post, show ¬ t < 8 * (k.val + 1) by omega]
    · rename_i hk
      have hk' : k.val = 8 := by scalar_tac
      simp only [WP.spec_ok]
      intro t ht
      rw [h2 t, hk']
      simp [ht]
  · refine ⟨by simp, fun t => by simp⟩

/-! ## Part C: the Rust loops -/

theorem byte1 (S : List UInt8) (pos : Nat) (hp : pos < S.length) (s1 : Slice U8)
    (h : bytes s1 = (S.drop pos).take 1) :
    s1.val.map (fun x => x.val) = [(S[pos]?.getD default).toNat] := by
  have hl : s1.val.length = 1 := by
    have := congrArg List.length h
    simp [bytes] at this
    omega
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hl
  unfold bytes at h
  rw [hb] at h ⊢
  simp at h
  have h3 := congrArg (fun l => l[0]?) h
  simp at h3
  first | simp [← h3, toNat_ofNat_val] | simp [h3, toNat_ofNat_val]

def bv0 (j : Array U8 1#usize) : Option Nat := j.val[0]?.map (fun x : U8 => x.val)

theorem inner_loop_spec (M : List UInt8) (N : Nat) (i : Usize) (jf posf : Nat)
    (ctx : keccak.Shake) (j : Array U8 1#usize)
    (h0 : ∃ k pos jcur, ShakeSqz ctx 136 M pos ∧ pos ≤ N ∧ bv0 j = some jcur ∧
      sibFind (Spec.SHAKE256 M N) i.val k pos jcur = some (jf, posf)) :
    sampling.sample_in_ball_loop1_loop0 ctx i j ⦃ r =>
      ShakeSqz r.1 136 M posf ∧ bv0 r.2 = some jf ⦄ := by
  classical
  unfold sampling.sample_in_ball_loop1_loop0
  let P : keccak.Shake × Array U8 1#usize → Nat → Prop := fun x k => ∃ pos jcur,
    ShakeSqz x.1 136 M pos ∧ pos ≤ N ∧ bv0 x.2 = some jcur ∧
      sibFind (Spec.SHAKE256 M N) i.val k pos jcur = some (jf, posf)
  apply loop.spec_decr_nat (fun x => if h : ∃ k, P x k then Nat.find h else 0) (fun x => ∃ k, P x k)
    (fun r : keccak.Shake × Array U8 1#usize => ShakeSqz r.1 136 M posf ∧ bv0 r.2 = some jf)
  · rintro ⟨ctx, j⟩ hex
    simp only [sampling.sample_in_ball_loop1_loop0.body]
    obtain ⟨pos, jcur, hS, hpos, hj, hk⟩ := Nat.find_spec hex
    have hSN : (Spec.SHAKE256 M N).length = N := SHAKE256_length _ _
    step*
    · -- continue
      have hgt : i2 > i := ‹i2 > i›
      have hj' : j.val[0]? = some (j.val[0]'i1) := List.getElem?_eq_getElem i1
      have hjc : (j.val[0]'i1).val = jcur := by
        have := hj; simp only [bv0] at this; rw [hj'] at this; simpa using this
      have hi2 : i2.val = jcur := by
        rw [i2_post, U8.cast_Usize_val_eq, i1_post2, hjc]
      have hgt' : i.val < jcur := by have : i < i2 := hgt; scalar_tac
      rcases hkm : Nat.find hex with _ | k'
      · rw [hkm] at hk
        simp [sibFind, show ¬ jcur ≤ i.val by omega] at hk
      · rw [hkm] at hk
        simp only [sibFind, show ¬ jcur ≤ i.val by omega, if_false] at hk
        split at hk
        · rename_i hp1
          have hlen1 : s.val.length = 1 := by rw [s_post1]; simpa using j.property
          have hN1 : pos + 1 ≤ N := by omega
          have hb1 : bytes s1 = ((Spec.SHAKE256 M N).drop pos).take 1 := by
            rw [ctx1_post2, hlen1]
            exact sponge_window 136 (by norm_num) M pos 1 N hN1
          have hbyte := byte1 (Spec.SHAKE256 M N) pos (by omega) s1 hb1
          have hlens1 : s1.val.length = 1 := by
            have := congrArg List.length hbyte; simpa using this
          have hback : (to_slice_mut_back s1).val = s1.val := by
            rw [s_post2]; exact Array.from_slice_val j s1 hlens1
          have hP : P (ctx1, to_slice_mut_back s1) k' := by
            refine ⟨pos + 1, _, ?_, hN1, ?_, hk⟩
            · rw [hlen1] at ctx1_post1; exact ctx1_post1
            · simp only [bv0, hback]
              obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlens1
              rw [hb] at hbyte ⊢
              simp at hbyte ⊢
              exact hbyte
          have hex' : ∃ k, P (ctx1, to_slice_mut_back s1) k := ⟨k', hP⟩
          refine ⟨hex', ?_⟩
          rw [dif_pos hex', dif_pos hex, hkm]
          have := Nat.find_min' hex' hP
          omega
        · simp at hk
    · -- done
      have hle : ¬ i2 > i := ‹¬ i2 > i›
      have hj' : j.val[0]? = some (j.val[0]'i1) := List.getElem?_eq_getElem i1
      have hjc : (j.val[0]'i1).val = jcur := by
        have := hj; simp only [bv0] at this; rw [hj'] at this; simpa using this
      have hi2 : i2.val = jcur := by
        rw [i2_post, U8.cast_Usize_val_eq, i1_post2, hjc]
      have hle' : jcur ≤ i.val := by have : i2 ≤ i := not_lt.mp hle; scalar_tac
      have hs : sibFind (Spec.SHAKE256 M N) i.val (Nat.find hex) pos jcur = some (jcur, pos) := by
        cases Nat.find hex <;> simp [sibFind, hle']
      rw [hs] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨hS, hj⟩
  · exact h0

theorem bit_cond (v : List UInt8) (t : Nat) : ((BytesToBits v)[t]?.getD false = true) ↔ byteBit v t = 1 := by
  have h := bitv_BytesToBits v t
  unfold bitv at h
  cases hh : ((BytesToBits v)[t]?.getD false) <;> simp_all

theorem outer_loop_spec (ip : Impl.params.Params) (hτ : ip.tau.val ≤ 64) (M : List UInt8) (fuel : Nat)
    (cfin : RPoly) (posfin : Nat) (h : U64)
    (hh : ∀ t, t < 64 → h.val.testBit t = decide (byteBit ((Spec.SHAKE256 M (8 + fuel)).take 8) t = 1))
    (c0 : Array U32 256#usize) (ctx0 : keccak.Shake) (i0 : Usize)
    (cm0 : RPoly) (pos0 : Nat) (hi0 : 256 - ip.tau.val = i0.val) (hrep0 : ReprInt c0 cm0)
    (hS0 : ShakeSqz ctx0 136 M pos0)
    (hfold0 : (List.range' i0.val (256 - i0.val)).foldlM
      (sibStep (Spec.SHAKE256 M (8 + fuel)) (BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))
        ip.tau.val fuel) (cm0, pos0) = some (cfin, posfin)) :
    sampling.sample_in_ball_loop1 ip.tau c0 ctx0 h i0 ⦃ r => ReprInt r cfin ⦄ := by
  unfold sampling.sample_in_ball_loop1
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × keccak.Shake × Usize) => 256 - p.2.2.val)
    (fun p => 256 - ip.tau.val ≤ p.2.2.val ∧ p.2.2.val ≤ 256 ∧ ∃ cm pos, ReprInt p.1 cm ∧
      ShakeSqz p.2.1 136 M pos ∧
      (List.range' p.2.2.val (256 - p.2.2.val)).foldlM
        (sibStep (Spec.SHAKE256 M (8 + fuel)) (BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))
          ip.tau.val fuel) (cm, pos) = some (cfin, posfin))
  · rintro ⟨c, ctx, i1⟩ ⟨hlo, hhi, cm, pos, hrep, hS, hfold⟩
    dsimp only at hlo hhi hrep hS hfold
    simp only [sampling.sample_in_ball_loop1.body]
    split
    · rename_i hlt
      have hi' : i1.val < 256 := by scalar_tac
      have hSN : (Spec.SHAKE256 M (8 + fuel)).length = 8 + fuel := SHAKE256_length _ _
      obtain ⟨n, hn⟩ : ∃ n, 256 - i1.val = n + 1 := ⟨255 - i1.val, by omega⟩
      rw [hn, List.range'_succ, List.foldlM_cons] at hfold
      cases hst : sibStep (Spec.SHAKE256 M (8 + fuel)) (BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))
          ip.tau.val fuel (cm, pos) i1.val with
      | none => rw [hst] at hfold; simp at hfold
      | some r =>
        obtain ⟨cm', pos'⟩ := r
        rw [hst] at hfold
        try simp only [Option.bind_some] at hfold
        unfold sibStep at hst
        split at hst
        · rename_i hp1
          cases hf : sibFind (Spec.SHAKE256 M (8 + fuel)) i1.val fuel (pos + 1)
              (((Spec.SHAKE256 M (8 + fuel))[pos]?.getD default).toNat) with
          | none => rw [hf] at hst; simp at hst
          | some r2 =>
            obtain ⟨jf, pos2⟩ := r2
            rw [hf] at hst
            simp only [Option.some.injEq, Prod.mk.injEq] at hst
            obtain ⟨hcm', hpos'⟩ := hst
            have hjf := sibFind_le _ _ _ _ _ _ _ hf
            step*
            have hfold' : List.foldlM (sibStep (Spec.SHAKE256 M (8 + fuel))
                (BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8)) ip.tau.val fuel) (cm', pos')
                (List.range' (i1.val + 1) n) = some (cfin, posfin) := hfold
            have hlen1 : s.val.length = 1 := by rw [s_post1]; simp
            have hN1 : pos + 1 ≤ 8 + fuel := by
              have : pos + 1 ≤ (Spec.SHAKE256 M (8 + fuel)).length := hp1
              omega
            have hb1 : bytes s1 = ((Spec.SHAKE256 M (8 + fuel)).drop pos).take 1 := by
              rw [ctx1_post2, hlen1]
              exact sponge_window 136 (by norm_num) M pos 1 (8 + fuel) hN1
            have hbyte := byte1 (Spec.SHAKE256 M (8 + fuel)) pos (by omega) s1 hb1
            have hlens1 : s1.val.length = 1 := by
              have := congrArg List.length hbyte; simpa using this
            have hback : (to_slice_mut_back s1).val = s1.val := by
              rw [s_post2]; exact Array.from_slice_val _ s1 hlens1
            have hS1 : ShakeSqz ctx1 136 M (pos + 1) := by
              rw [hlen1] at ctx1_post1; exact ctx1_post1
            have hbv : bv0 (to_slice_mut_back s1) =
                some ((Spec.SHAKE256 M (8 + fuel))[pos]?.getD default).toNat := by
              simp only [bv0, hback]
              obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlens1
              rw [hb] at hbyte ⊢
              simp at hbyte ⊢
              exact hbyte
            refine WP.spec_bind (inner_loop_spec M (8 + fuel) i1 jf pos2 ctx1 (to_slice_mut_back s1)
              ⟨fuel, pos + 1, _, hS1, hN1, hbv, hf⟩) ?_
            rintro ⟨ctx2, j2⟩ ⟨hS2, hj2⟩
            dsimp only at hS2 hj2
            step*
            have hxj : (j2.val[0]'i2).val = jf := by
              have hj' : j2.val[0]? = some (j2.val[0]'i2) := List.getElem?_eq_getElem i2
              have := hj2; simp only [bv0] at this; rw [hj'] at this; simpa using this
            have hjj : jj.val = jf := by rw [jj_post, U8.cast_Usize_val_eq, i2_post2, hxj]
            subst hjj
            subst i3_post2 c1_post
            have hjj256 : jj.val < 256 := by omega
            have hXc := hrep.coeff jj.val hjj256
            have hXe : (c.val[jj.val]'i3) = c.val[jj.val]'(by rw [len256 c]; exact hjj256) := rfl
            have hXq : (c.val[jj.val]'i3).val < Spec.q := canon_get hrep.1 _
            have hxc : (((c.val[jj.val]'i3).val : Nat) : Zq) = ((cm[jj.val]! : Int) : Zq) := by
              rw [getElem!_pos _ _ (by simpa using hjj256)]
              have h1 : (((c.val[jj.val]'i3).val : Nat) : Zq) = ((((c.val[jj.val]'i3).val : Nat) : Int) : Zq) := by
                simp
              rw [h1, hXc]
              exact ZMod.intCast_mod _ _
            have hr1 := hrep.set i1 (c.val[jj.val]'i3) (cm[jj.val]!) hi' hXq hxc
            have hbitv : bit.val = 1 ↔ byteBit ((Spec.SHAKE256 M (8 + fuel)).take 8) (i1.val + ip.tau.val - 256) = 1 := by
              have hb1 : bit.val = (h.val >>> i5.val) &&& 1 := by
                rw [bit_post1, UScalar.val_and, i6_post1]; rfl
              have h5 : i5.val = i1.val + ip.tau.val - 256 := by omega
              have hh5 := hh i5.val i6_post3
              rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow] at hh5
              rw [hb1, Nat.and_one_is_mod, ← h5]
              exact decide_eq_decide.mp hh5
            have hQ : field.Q.val = 8380417 := by first | rfl | decide | simp [field.Q]
            have hq1 : (((Spec.q - 1 : Nat)) : Zq) = ((-1 : Int) : Zq) := by
              rw [Nat.cast_sub (by decide : 1 ≤ Spec.q)]
              simp [ZMod.natCast_self]
            have hcond : ((BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))[i1.val + ip.tau.val - 256]?.getD false = true)
                ↔ bit.val = 1 := by
              rw [bit_cond, hbitv]
            by_cases hbit : bit = 1#u64
            · simp only [hbit, if_true]
              step*
              have hbit1 : bit.val = 1 := by rw [hbit]; rfl
              have hc : (BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))[i1.val + ip.tau.val - 256]?.getD false = true :=
                hcond.mpr hbit1
              have hi7 : i7.val = 8380416 := by rw [i7_post1]; omega
              refine ⟨by omega, by omega, ⟨cm', pos', ?_, by rw [← hpos']; exact hS2, ?_⟩, by omega⟩
              · rw [a_post, ← hcm', if_pos hc]
                exact hr1.set jj i7 (-1) hjj256 (by rw [hi7]; decide) (by rw [hi7]; exact hq1)
              · have : 256 - i8.val = n := by omega
                rw [this, i8_post]; exact hfold'
            · simp only [hbit, if_false]
              step*
              have hcf : ¬ ((BytesToBits ((Spec.SHAKE256 M (8 + fuel)).take 8))[i1.val + ip.tau.val - 256]?.getD false = true) := by
                intro h
                have h1 := hcond.mp h
                exact hbit (UScalar.eq_of_val_eq (by simpa using h1))
              refine ⟨by omega, by omega, ⟨cm', pos', ?_, by rw [← hpos']; exact hS2, ?_⟩, by omega⟩
              · rw [a_post, ← hcm', if_neg hcf]
                exact hr1.set jj 1#u32 1 hjj256 (by decide) (by simp)
              · have : 256 - i8.val = n := by omega
                rw [this, i8_post]; exact hfold'
        · simp at hst
    · rename_i hlt
      have hi' : i1.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at hfold
      simp at hfold
      obtain ⟨rfl, -⟩ := hfold
      exact hrep
  · dsimp only
    refine ⟨by omega, by omega, cm0, pos0, hrep0, hS0, ?_⟩
    exact hfold0

/-- **`sample_in_ball` is `SampleInBall`** (Algorithm 29), for every `ρ` and every `fuel` for which the spec
returns `some c` (the Rust loop is unbounded; on such inputs it terminates after reading at most `8 + fuel`
bytes of the stream). `hτ : τ ≤ 64` is needed by the Rust code (the sign word is a `u64`). -/
theorem sample_in_ball_spec {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hτ : sp.τ ≤ 64) (ρ : Slice U8) (c : RPoly) (fuel : Nat)
    (hs : Spec.SampleInBall sp fuel (bytes ρ) = some c) :
    sampling.sample_in_ball ip ρ ⦃ r => ReprInt r c ⦄ := by
  obtain ⟨pos, hmodel⟩ := SampleInBall_model sp (by omega) fuel (bytes ρ) c hs
  unfold sampling.sample_in_ball
  step*
  simp only [List.nil_append] at *
  have hτ' : ip.tau.val ≤ 64 := by rw [hp.tau]; exact hτ
  have hτ256 : sp.τ ≤ 256 := by omega
  have hl1 : s1.val.length = 8 := by rw [s1_post1]; simp
  have hSN : (Spec.SHAKE256 (bytes ρ) (8 + fuel)).length = 8 + fuel := SHAKE256_length _ _
  have hb2 : bytes s2 = (Spec.SHAKE256 (bytes ρ) (8 + fuel)).take 8 := by
    rw [ctx3_post2, hl1]
    have := sponge_window 136 (by norm_num) (bytes ρ) 0 8 (8 + fuel) (by omega)
    show _ = List.take 8 (Keccak.sponge 136 (bytes ρ) (8 + fuel))
    simpa using this
  have hl2 : s2.val.length = 8 := by
    have := congrArg List.length hb2
    unfold bytes at this
    rw [List.length_map, List.length_take, SHAKE256_length] at this
    omega
  have hb3 : bytesA (to_slice_mut_back s2) = (Spec.SHAKE256 (bytes ρ) (8 + fuel)).take 8 := by
    rw [s1_post2, bytesA_from_slice _ _ hl2, hb2]
  refine WP.spec_bind (h_loop_spec (to_slice_mut_back s2)) ?_
  intro h hh
  rw [hb3] at hh
  step*
  rw [hl1] at ctx3_post1
  refine outer_loop_spec ip hτ' (bytes ρ) fuel c pos h hh _ ctx3 i (Vector.replicate 256 0) 8
    (by rw [i_post1, hp.tau]) reprInt_zero (by simpa using ctx3_post1) ?_
  have e : 256 - i.val = sp.τ := by rw [i_post1, hp.tau]; omega
  rw [e, i_post1, hp.tau]
  unfold sibRun at hmodel
  exact hmodel

theorem ML_DSA_44_tau : Spec.ML_DSA_44.τ ≤ 64 := by decide +kernel
theorem ML_DSA_65_tau : Spec.ML_DSA_65.τ ≤ 64 := by decide +kernel
theorem ML_DSA_87_tau : Spec.ML_DSA_87.τ ≤ 64 := by decide +kernel

end Proofs
