import XSpec.Samplers

/-!
# `SampleInBall` (Algorithm 29)

Ours: `Spec.SampleInBall p F ρ` reads `8 + F` bytes of `SHAKE256 ρ`: 8 sign bytes, then for each `i = 256 - τ .. 255`
a byte and up to `F` further bytes until one is `≤ i`.  Theirs: `SampleInBallReturns τ s c` says that
`sampleInBallFuel τ s f = some c` for some `f`, on the infinite stream `s`, where each search `findLE s i f pos`
tests at most `f` bytes and the stream is unbounded.

Fuel: our search over a stream of `8 + F` bytes with `F` extra reads is their `findLE` with fuel `F + 1`
(the first byte read is a test of its own), restricted to positions below `8 + F`.  Part A (the loops of
`Spec.SampleInBall` as pure functions) is ported from `lean/Proofs/SampleBall.lean` (Lean 4.34: `Prod` states
instead of `MProd`; names carry a `b` prefix to stay clear of ocaml-pq's `sibStep`).
-/

open Spec

namespace XSpec

open OcamlPq.MLDSAAlg
open OcamlPq.EndToEnd.MLDSA

namespace SB


/-! ## Part A: the spec's loops as pure functions -/

abbrev BState := Prod (Option (Option RPoly)) (Prod RPoly Ctx)
abbrev BInner := Prod (Option (Option RPoly)) (Prod Ctx Nat)

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
def innerT (i : Nat) : Nat → BInner → ForInStep BInner := fun _ r =>
  if r.snd.snd ≤ i then ForInStep.done ⟨none, r.snd.fst, r.snd.snd⟩
  else
    match H.Squeeze r.snd.fst 1 with
    | some (ctx', s₁) => ForInStep.yield ⟨none, ctx', (s₁[0]?.getD default).toNat⟩
    | x => ForInStep.done ⟨some none, r.snd.fst, r.snd.snd⟩

/-- The inner search: read bytes from position `pos` of the stream until one is `≤ i`, with `k` reads allowed. -/
def bFind (S : List UInt8) (i : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, pos, j => if j ≤ i then some (j, pos) else none
  | k + 1, pos, j =>
    if j ≤ i then some (j, pos)
    else if pos + 1 ≤ S.length then bFind S i k (pos + 1) ((S[pos]?.getD default).toNat) else none

theorem sibFind_le (S : List UInt8) (i : Nat) : ∀ k pos j j' pos', bFind S i k pos j = some (j', pos') → j' ≤ i := by
  intro k
  induction k with
  | zero =>
    intro pos j j' pos' h
    simp only [bFind] at h
    split at h
    · simp at h; omega
    · simp at h
  | succ k ih =>
    intro pos j j' pos' h
    simp only [bFind] at h
    split at h
    · simp at h; omega
    · split at h
      · exact ih _ _ _ _ h
      · simp at h

theorem b_inner_iter (S : List UInt8) (i : Nat) : ∀ (k s pos j : Nat),
    (∃ j' pos', bFind S i k pos j = some (j', pos') ∧
        iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩ = ⟨none, ⟨S, pos'⟩, j'⟩) ∨
    (bFind S i k pos j = none ∧
        ((iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).fst = some none ∨
         ((iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).fst = none ∧
          i < (iterT (innerT i) s k ⟨none, ⟨S, pos⟩, j⟩).snd.snd))) := by
  intro k
  induction k with
  | zero =>
    intro s pos j
    by_cases h : j ≤ i
    · left; exact ⟨j, pos, by simp [bFind, h], by simp [iterT]⟩
    · right; refine ⟨by simp [bFind, h], Or.inr ⟨by simp [iterT], ?_⟩⟩; simp [iterT]; omega
  | succ k ih =>
    intro s pos j
    by_cases h : j ≤ i
    · left; exact ⟨j, pos, by simp [bFind, h], by simp [iterT, innerT, h]⟩
    · by_cases hp : pos + 1 ≤ S.length
      · have e : iterT (innerT i) s (k + 1) ⟨none, ⟨S, pos⟩, j⟩ =
            iterT (innerT i) (s + 1) k ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩ := by
          simp [iterT, innerT, h, H.Squeeze, Ctx.Squeeze, hp]
        have e2 : bFind S i (k + 1) pos j = bFind S i k (pos + 1) ((S[pos]?.getD default).toNat) := by
          simp [bFind, h, hp]
        rw [e, e2]
        exact ih (s + 1) (pos + 1) _
      · right
        refine ⟨by simp [bFind, h, hp], Or.inl ?_⟩
        simp [iterT, innerT, h, H.Squeeze, Ctx.Squeeze, hp]

/-- The body of the spec's outer loop (Algorithm 29, steps 7-12). -/
def outerT (hb : List Bool) (τ fuel : Nat) : Nat → BState → ForInStep BState := fun i r =>
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
def bStep (S : List UInt8) (hb : List Bool) (τ fuel : Nat) (st : RPoly × Nat) (i : Nat) :
    Option (RPoly × Nat) :=
  if st.2 + 1 ≤ S.length then
    match bFind S i fuel (st.2 + 1) ((S[st.2]?.getD default).toNat) with
    | none => none
    | some (j, pos') =>
      some ((st.1.set! i st.1[j]!).set! j (if hb[i + τ - 256]?.getD false = true then -1 else 1), pos')
  else none

theorem outerT_step (S : List UInt8) (hb : List Bool) (τ fuel i : Nat) (c : RPoly) (pos : Nat) :
    (∀ c' pos', bStep S hb τ fuel (c, pos) i = some (c', pos') →
      outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ = ForInStep.yield ⟨none, c', ⟨S, pos'⟩⟩) ∧
    (bStep S hb τ fuel (c, pos) i = none →
      ∃ st : BState, outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ = ForInStep.done st ∧ st.fst = some none) := by
  by_cases hp : pos + 1 ≤ S.length
  · have e : outerT hb τ fuel i ⟨none, c, ⟨S, pos⟩⟩ =
        (let r_1 := iterT (innerT i) 0 fuel ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩
         match r_1.fst with
         | none =>
           if i < r_1.2.snd then ForInStep.done ⟨some none, c, r_1.2.fst⟩
           else ForInStep.yield ⟨none, (Vector.set! c i (c)[r_1.2.snd]!).set! r_1.2.snd
              (if hb[i + τ - 256]?.getD false = true then -1 else 1), r_1.2.fst⟩
         | some a => ForInStep.done ⟨some a, c, r_1.2.fst⟩) := by
      simp [outerT, H.Squeeze, Ctx.Squeeze, hp]
    rw [e]
    rcases b_inner_iter S i fuel 0 (pos + 1) ((S[pos]?.getD default).toNat) with
      ⟨j', pos', h1, h2⟩ | ⟨h1, h2⟩
    · have hj := sibFind_le S i _ _ _ _ _ h1
      simp only [h2]
      refine ⟨fun c' pos'' h => ?_, fun h => ?_⟩
      · simp only [bStep, hp, if_true, h1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [show ¬ i < j' by omega]
      · simp [bStep, hp, h1] at h
    · generalize iterT (innerT i) 0 fuel ⟨none, ⟨S, pos + 1⟩, (S[pos]?.getD default).toNat⟩ = R at h2 ⊢
      obtain ⟨f, cx, jx⟩ := R
      refine ⟨fun c' pos'' h => ?_, fun h => ?_⟩
      · simp only [bStep, hp, if_true, h1] at h
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
      simp [bStep, hp] at h
    · intro _
      exact ⟨⟨some none, c, ⟨S, pos⟩⟩, by simp [outerT, H.Squeeze, Ctx.Squeeze, hp], by simp⟩

theorem b_outer_iter (S : List UInt8) (hb : List Bool) (τ fuel : Nat) : ∀ (n s : Nat) (c : RPoly) (pos : Nat),
    (∃ c' pos', (List.range' s n).foldlM (bStep S hb τ fuel) (c, pos) = some (c', pos') ∧
        iterT (outerT hb τ fuel) s n ⟨none, c, ⟨S, pos⟩⟩ = ⟨none, c', ⟨S, pos'⟩⟩) ∨
    ((List.range' s n).foldlM (bStep S hb τ fuel) (c, pos) = none ∧
        (iterT (outerT hb τ fuel) s n ⟨none, c, ⟨S, pos⟩⟩).fst = some none) := by
  intro n
  induction n with
  | zero =>
    intro s c pos
    left; exact ⟨c, pos, by simp, by simp [iterT]⟩
  | succ n ih =>
    intro s c pos
    obtain ⟨hy, hd⟩ := outerT_step S hb τ fuel s c pos
    cases hst : bStep S hb τ fuel (c, pos) s with
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
      have e2 : (List.range' s (n + 1)).foldlM (bStep S hb τ fuel) (c, pos) =
          (List.range' (s + 1) n).foldlM (bStep S hb τ fuel) (c', pos') := by
        simp [List.range'_succ, hst]
      rw [e2]
      exact ih (s + 1) c' pos'

/-- The model of Algorithm 29 on the stream `S = H ρ (8 + fuel)`. -/
def bRun (S : List UInt8) (τ fuel : Nat) : Option (RPoly × Nat) :=
  (List.range' (256 - τ) τ).foldlM (bStep S (BytesToBits (S.take 8)) τ fuel) (Vector.replicate 256 0, 8)

theorem SampleInBall_eq (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) :
    Spec.SampleInBall p fuel ρ = (bRun (H ρ (8 + fuel)) p.τ fuel).map Prod.fst := by
  unfold Spec.SampleInBall
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hsq : H.Squeeze (H.InitAbsorb (8 + fuel) ρ) 8 =
      some (⟨H ρ (8 + fuel), 8⟩, ((H ρ (8 + fuel)).drop 0).take 8) := by
    have hl : (H ρ (8 + fuel)).length = 8 + fuel := SHAKE256_length _ _
    simp [H.Squeeze, Ctx.Squeeze, H.InitAbsorb, hl]
  simp [hsq]
  unfold bRun
  generalize H ρ (8 + fuel) = S
  rw [Nat.sub_sub_self hτ]
  rw [forIn_range'_iterT (outerT (BytesToBits (S.take 8)) p.τ fuel) _ ?hF]
  · rcases b_outer_iter S (BytesToBits (S.take 8)) p.τ fuel p.τ (256 - p.τ) (Vector.replicate 256 0) 8 with
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
      · generalize iterT (innerT i) 0 fuel ⟨none, ctx', (s₁[0]?.getD default).toNat⟩ = R
        obtain ⟨f, cx, jx⟩ := R
        rcases f with _ | a <;> rfl
      · intro x r'
        simp only [innerT]
        split_ifs with hh
        · rfl
        · cases hq' : H.Squeeze r'.snd.fst 1 with
          | none => rfl
          | some v' => obtain ⟨a, b⟩ := v'; rfl

/-! ## Ours against theirs -/

theorem bFind_zero (S : List UInt8) (i pos j : ℕ) : bFind S i 0 pos j = if j ≤ i then some (j, pos) else none := rfl

theorem bFind_succ (S : List UInt8) (i k pos j : ℕ) :
    bFind S i (k + 1) pos j = if j ≤ i then some (j, pos)
      else if pos + 1 ≤ S.length then bFind S i k (pos + 1) ((S[pos]?.getD default).toNat) else none := rfl

theorem findLE_zero' (s : ℕ → Byte) (i p : ℕ) : findLE s i 0 p = none := rfl

theorem findLE_succ' (s : ℕ → Byte) (i f p : ℕ) :
    findLE s i (f + 1) p = if (s p).val ≤ i then some p else findLE s i f (p + 1) := rfl

/-- Our bounded search is their `findLE` with one more unit of fuel, cut off at the end of the stream. -/
theorem bFind_eq (S : List UInt8) (s : ℕ → Byte)
    (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (i : ℕ) :
    ∀ k q, q < S.length →
      bFind S i k (q + 1) ((S[q]?.getD default).toNat) =
        match findLE s i (k + 1) q with
        | some p' => if p' < S.length then some ((s p').val, p' + 1) else none
        | none => none := by
  intro k
  induction k with
  | zero =>
    intro q hq
    have h0 := hs q hq
    rw [bFind_zero, findLE_succ']
    by_cases h : (S[q]?.getD default).toNat ≤ i
    · have h' : (s q).val ≤ i := by rw [h0]; exact h
      rw [if_pos h, if_pos h']
      simp only [hq, if_true]
      rw [h0]
    · have h' : ¬ (s q).val ≤ i := by rw [h0]; exact h
      rw [if_neg h, if_neg h', findLE_zero']
  | succ k ih =>
    intro q hq
    have h0 := hs q hq
    rw [bFind_succ, findLE_succ']
    by_cases h : (S[q]?.getD default).toNat ≤ i
    · have h' : (s q).val ≤ i := by rw [h0]; exact h
      rw [if_pos h, if_pos h']
      simp only [hq, if_true]
      rw [h0]
    · have h' : ¬ (s q).val ≤ i := by rw [h0]; exact h
      rw [if_neg h, if_neg h']
      by_cases hq1 : q + 1 < S.length
      · rw [if_pos (show q + 1 + 1 ≤ S.length from hq1)]
        exact ih (q + 1) hq1
      · rw [if_neg (show ¬ (q + 1 + 1 ≤ S.length) from hq1)]
        cases hf : findLE s i (k + 1) (q + 1) with
        | none => rfl
        | some p' =>
          have := findLE_ge hf
          have hn : ¬ p' < S.length := by omega
          simp only [hn, if_false]

theorem sign_eq (S : List UInt8) (s : ℕ → Byte) (h8 : 8 ≤ S.length)
    (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (k : ℕ) (hk : k < 64) :
    (((if (BytesToBits (S.take 8))[k]?.getD false = true then -1 else 1 : ℤ)) =
      (-1 : ℤ) ^ bytesToBits ((List.range 8).map s) k) := by
  have hl : (S.take 8).length = 8 := by simp; omega
  have h1 : (BytesToBits (S.take 8))[k]? = some (EB.byteBit (S.take 8) k == 1) := by
    rw [EB.BytesToBits_eq]
    simp [hl, hk]
  have hb : bytesToBits ((List.range 8).map s) k = EB.byteBit (S.take 8) k := by
    unfold bytesToBits EB.byteBit
    have hk8 : k / 8 < 8 := by omega
    rw [List.getD_eq_getElem?_getD]
    simp only [List.getElem?_map, List.getElem?_range, hk8, if_true, Option.map_some, Option.getD_some]
    rw [hs (k / 8) (by omega)]
    simp [List.getElem?_take, hk8]
  rw [h1, hb]
  have hle := EB.byteBit_le (S.take 8) k
  rcases (by omega : EB.byteBit (S.take 8) k = 0 ∨ EB.byteBit (S.take 8) k = 1) with h | h <;> simp [h]

section Fold

variable (τ F : ℕ) (S : List UInt8) (s : ℕ → Byte)

/-- The sign of coefficient `i`. -/
abbrev sgn (S : List UInt8) (τ i : ℕ) : ℤ :=
  if (BytesToBits (S.take 8))[i + τ - 256]?.getD false = true then -1 else 1

/-- One step of our loop, in terms of `findLE`. -/
theorem bStep_eq (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (i : ℕ) (c : RPoly)
    (pos : ℕ) (hpos : pos < S.length) :
    bStep S (BytesToBits (S.take 8)) τ F (c, pos) i =
      match findLE s i (F + 1) pos with
      | some p' => if p' < S.length then
          some (((c.set! i (c)[(s p').val]!).set! (s p').val (sgn S τ i)), p' + 1) else none
      | none => none := by
  unfold bStep
  dsimp only
  rw [if_pos (by omega), bFind_eq S s hs i F pos hpos]
  cases findLE s i (F + 1) pos with
  | none => rfl
  | some p' =>
    dsimp only
    split_ifs <;> rfl

/-- Their step, in terms of `findLE`. -/
theorem absStep_eq (i : ℕ) (c : ℕ → ℤ) (pos : ℕ) :
    absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p) (some (pos, c)) i =
      (findLE s i (F + 1) pos).map fun p' =>
        (p' + 1, Function.update (Function.update c i (c (s p').val)) (s p').val
          ((-1 : ℤ) ^ bytesToBits ((List.range 8).map s) (i + τ - 256))) := rfl

theorem step_rel (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (h8 : 8 ≤ S.length)
    (hτ : τ ≤ 64) (i : ℕ) (hi1 : 256 - τ ≤ i) (hi : i < 256) (c : RPoly) (pos : ℕ) (hpos : pos < S.length) :
    (bStep S (BytesToBits (S.take 8)) τ F (c, pos) i).map (fun x => (x.2, rfn x.1)) =
      (absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p)
        (some (pos, rfn c)) i).filter (fun x => x.1 ≤ S.length) := by
  rw [bStep_eq τ F S s hs i c pos hpos, absStep_eq]
  cases hf : findLE s i (F + 1) pos with
  | none => rfl
  | some p' =>
    have hj := findLE_le hf
    have hjl : (s p').val < 256 := by omega
    simp only [Option.map_some]
    by_cases hp' : p' < S.length
    · rw [if_pos hp']
      simp only [Option.map_some, Option.filter_some, show p' + 1 ≤ S.length from hp', decide_true, if_true]
      congr 1
      rw [RB.rfn_set _ _ hjl, RB.rfn_set _ _ hi]
      have hsg := sign_eq S s h8 hs (i + τ - 256) (by omega)
      rw [← hsg]
      simp only [rfn]
    · rw [if_neg hp']
      have hn : ¬ (p' + 1 ≤ S.length) := by omega
      simp only [Option.map_some, Option.filter_some, hn, decide_false]
      rfl

theorem fold_fwd (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (h8 : 8 ≤ S.length)
    (hτ : τ ≤ 64) :
    ∀ (l : List ℕ), (∀ i ∈ l, 256 - τ ≤ i ∧ i < 256) → ∀ (c : RPoly) (pos : ℕ) (c' : RPoly) (pos' : ℕ),
      l.foldlM (bStep S (BytesToBits (S.take 8)) τ F) (c, pos) = some (c', pos') →
      l.foldl (absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p))
        (some (pos, rfn c)) = some (pos', rfn c') := by
  intro l
  induction l with
  | nil =>
    intro _ c pos c' pos' h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a l ih =>
    intro hl c pos c' pos' h
    rw [List.foldlM_cons] at h
    have ha := hl a (List.mem_cons_self ..)
    cases h1 : bStep S (BytesToBits (S.take 8)) τ F (c, pos) a with
    | none => rw [h1] at h; simp at h
    | some st1 =>
      obtain ⟨c1, pos1⟩ := st1
      rw [h1] at h
      try simp only [Option.bind_some] at h
      have hposS : pos < S.length := by
        by_contra hc
        unfold bStep at h1
        simp only at h1
        rw [if_neg (by omega)] at h1
        cases h1
      have hr := step_rel τ F S s hs h8 hτ a ha.1 ha.2 c pos hposS
      rw [h1] at hr
      simp only [Option.map_some] at hr
      have hr' : absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p)
          (some (pos, rfn c)) a = some (pos1, rfn c1) := by
        cases hh : absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p)
          (some (pos, rfn c)) a with
        | none => rw [hh] at hr; simp at hr
        | some x =>
          rw [hh] at hr
          simp only [Option.filter] at hr
          split_ifs at hr with hx
          · simp only [Option.some.injEq] at hr
            rw [hr]
      rw [List.foldl_cons, hr']
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) c1 pos1 c' pos' h

theorem fold_bwd (hs : ∀ q < S.length, (s q).val = (S[q]?.getD default).toNat) (h8 : 8 ≤ S.length)
    (hτ : τ ≤ 64) :
    ∀ (l : List ℕ), (∀ i ∈ l, 256 - τ ≤ i ∧ i < 256) → ∀ (c : RPoly) (pos pos' : ℕ) (cc : ℕ → ℤ),
      l.foldl (absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p))
        (some (pos, rfn c)) = some (pos', cc) → pos' ≤ S.length →
      ∃ c', l.foldlM (bStep S (BytesToBits (S.take 8)) τ F) (c, pos) = some (c', pos') ∧ rfn c' = cc := by
  intro l
  induction l with
  | nil =>
    intro _ c pos pos' cc h _
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, rfl, rfl⟩
  | cons a l ih =>
    intro hl c pos pos' cc h hp
    have ha := hl a (List.mem_cons_self ..)
    rw [List.foldl_cons] at h
    cases h1 : absStep τ s (bytesToBits ((List.range 8).map s)) (fun i p => findLE s i (F + 1) p)
        (some (pos, rfn c)) a with
    | none => rw [h1, absFold_none] at h; simp at h
    | some st1 =>
      obtain ⟨pos1, cc1⟩ := st1
      rw [h1] at h
      have hle := absFold_pos_le τ s (bytesToBits ((List.range 8).map s))
        (fun i p => findLE s i (F + 1) p) (fun i p p' h => findLE_ge h) l _ _ h
      simp only at hle
      have hposS : pos < S.length := by
        rw [absStep_eq] at h1
        cases hf : findLE s a (F + 1) pos with
        | none => rw [hf] at h1; simp at h1
        | some p' =>
          rw [hf] at h1
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
          have := findLE_ge hf
          omega
      have hr := step_rel τ F S s hs h8 hτ a ha.1 ha.2 c pos hposS
      rw [h1] at hr
      simp only [Option.filter, show pos1 ≤ S.length by omega, decide_true, if_true] at hr
      cases hb : bStep S (BytesToBits (S.take 8)) τ F (c, pos) a with
      | none => rw [hb] at hr; simp at hr
      | some st2 =>
        obtain ⟨c1, pos2⟩ := st2
        rw [hb] at hr
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨c', hb2, hr2⟩ := ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) c1 pos2 pos' cc h hp
        refine ⟨c', ?_, hr2⟩
        rw [List.foldlM_cons, hb]
        exact hb2

end Fold

theorem stream_facts (ρ : List UInt8) (L : ℕ) :
    ∀ q < (H ρ L).length, (oursShake256 (u8ToBytes ρ) q).val = ((H ρ L)[q]?.getD default).toNat := by
  intro q hq
  have hL : (H ρ L).length = L := SHAKE256_length _ _
  rw [oursShake256_val ρ L q (by omega)]
  simp [List.getD_eq_getElem?_getD, H]
  rfl

end SB

theorem Std3.tau_le {p : Spec.Params} (hp : Std3 p) : p.τ ≤ 64 := by
  rcases hp with rfl | rfl | rfl <;> decide

namespace SB

/-- **Ours implies theirs.**  The fuel is `F + 1`. -/
theorem sampleInBall_ours_to_theirs {p : Spec.Params} (hp : Std3 p) (ρ : List UInt8) (F : ℕ) (c : RPoly)
    (h : Spec.SampleInBall p F ρ = some c) :
    SampleInBallReturns p.τ (oursShake256 (u8ToBytes ρ)) (rfn c) := by
  have hτ := hp.tau_le
  rw [SampleInBall_eq p (by omega) F ρ] at h
  obtain ⟨⟨c', pos'⟩, hq, hc⟩ := Option.map_eq_some_iff.mp h
  simp only at hc
  subst hc
  have hL : (H ρ (8 + F)).length = 8 + F := SHAKE256_length _ _
  refine ⟨F + 1, ?_⟩
  unfold sampleInBallFuel
  rw [sibStep_eq]
  have := fold_fwd p.τ F (H ρ (8 + F)) (oursShake256 (u8ToBytes ρ)) (stream_facts ρ (8 + F)) (by omega) hτ
    (List.range' (256 - p.τ) p.τ) (by
      intro i hi
      rw [List.mem_range'_1] at hi
      omega) (Vector.replicate 256 0) 8 c' pos' hq
  rw [RB.rfn_replicate] at this
  rw [this]
  rfl

/-- **Theirs implies ours, for all large enough fuel.** -/
theorem sampleInBall_theirs_to_ours {p : Spec.Params} (hp : Std3 p) (ρ : List UInt8) (b : ℕ → ℤ)
    (h : SampleInBallReturns p.τ (oursShake256 (u8ToBytes ρ)) b) :
    ∃ F0, ∀ F, F0 ≤ F → ∃ c, Spec.SampleInBall p F ρ = some c ∧ rfn c = b := by
  have hτ := hp.tau_le
  obtain ⟨f, hf⟩ := h
  unfold sampleInBallFuel at hf
  rw [sibStep_eq] at hf
  obtain ⟨⟨pe, cc⟩, hq, hc⟩ := Option.map_eq_some_iff.mp hf
  simp only at hc
  subst hc
  refine ⟨max f pe, fun F hF => ?_⟩
  have hL : (H ρ (8 + F)).length = 8 + F := SHAKE256_length _ _
  have hq' := absFold_transfer p.τ (oursShake256 (u8ToBytes ρ)) (bytesToBits ((List.range 8).map (oursShake256 (u8ToBytes ρ))))
    (fun i p => findLE (oursShake256 (u8ToBytes ρ)) i f p)
    (fun i p => findLE (oursShake256 (u8ToBytes ρ)) i (F + 1) p) (fun i p p' h => findLE_ge h)
    (List.range' (256 - p.τ) p.τ) (8, fun _ => 0) (pe, cc) hq (by
      intro i q q' h1 h2
      exact findLE_fuel h1 (by simp only at h2; omega))
  rw [← RB.rfn_replicate] at hq'
  have hpe := absFold_pos_le p.τ (oursShake256 (u8ToBytes ρ)) (bytesToBits ((List.range 8).map (oursShake256 (u8ToBytes ρ))))
    (fun i p => findLE (oursShake256 (u8ToBytes ρ)) i (F + 1) p) (fun i p p' h => findLE_ge h)
    (List.range' (256 - p.τ) p.τ) _ _ hq'
  obtain ⟨c', hb, hr⟩ := fold_bwd p.τ F (H ρ (8 + F)) (oursShake256 (u8ToBytes ρ)) (stream_facts ρ (8 + F))
    (by omega) hτ (List.range' (256 - p.τ) p.τ) (by
      intro i hi
      rw [List.mem_range'_1] at hi
      omega) (Vector.replicate 256 0) 8 pe cc hq' (by omega)
  refine ⟨c', ?_, hr⟩
  rw [SampleInBall_eq p (by omega) F ρ]
  unfold bRun
  rw [hb]
  rfl

end SB

end XSpec
