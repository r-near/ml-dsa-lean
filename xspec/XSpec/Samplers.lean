import XSpec.Hash
import XSpec.Arith
import XSpec.Coeff

/-!
# `RejNTTPoly` and `RejBoundedPoly` (Algorithms 30 and 31)

Ours: `Spec.RejNTTPoly fuel rho` runs `fuel` iterations of the `while j < 256` loop on the first `3 * fuel`
bytes of `SHAKE128 rho`; `none` means the fuel ran out.  Theirs: `RejNTTPolyReturns s a` says that some
fuel makes `rejNTTPolyLoop s fuel 0 0 (fun _ => 0)` return `some a` on the (infinite) SHAKE128 stream `s`.

The bridge is exact up to an off-by-one: ours returns after the iteration that fills the 256th coefficient;
theirs needs one further call to observe `j = 256`.  So ours at fuel `F` corresponds to theirs at fuel `F + 1`.
`RejBoundedPoly` (namespace `RB`) is bridged the same way, against `RejBoundedReturns`.  ocaml-pq's stream is
`oursShake128 (u8ToBytes rho)` resp. `oursShake256 ...` (our SHAKE through ocaml-pq's `keccakXOF`), see `Hash.lean`.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

namespace RN

abbrev RejSt := Option (Option Poly) × Poly × Nat × Ctx

def tripleAt (T : List UInt8) (i : Nat) : List UInt8 := (T.drop (3 * i)).take 3

def triAt (T : List UInt8) (i : Nat) : Option Zq :=
  CoeffFromThreeBytes (tripleAt T i)[0]! (tripleAt T i)[1]! (tripleAt T i)[2]!

def stepA (T : List UInt8) (s : Poly × Nat) (i : Nat) : Poly × Nat :=
  if 256 ≤ s.2 then s else
  match triAt T i with
  | some v => (s.1.set! s.2 v, s.2 + 1)
  | none => s

def rejBody (_ : Nat) (r : RejSt) : Id (ForInStep RejSt) :=
  have a := r.2.1
  have j := r.2.2.1
  have ctx := r.2.2.2
  if j ≥ 256 then pure (ForInStep.done (none, a, j, ctx))
  else
    match G.Squeeze ctx 3 with
    | some (ctx', s) =>
      match CoeffFromThreeBytes s[0]! s[1]! s[2]! with
      | some v => pure (ForInStep.yield (none, Vector.set! a j v, j + 1, ctx'))
      | none => pure (ForInStep.yield (none, a, j, ctx'))
    | x => pure (ForInStep.done (some none, a, j, ctx))

/-- What `RejNTTPoly` does with the final loop state. -/
def tailFn (r : RejSt) : Option Poly :=
  match r.1 with
  | some a => a
  | none => if r.2.2.1 < 256 then none else some r.2.1

theorem rej_unfold (fuel : Nat) (ρ : List UInt8) :
    Spec.RejNTTPoly fuel ρ =
      tailFn (forIn (m := Id) (List.range' 0 fuel) ((none, Poly.zero, 0, G.InitAbsorb (3 * fuel) ρ) : RejSt) rejBody) := by
  obtain ⟨f, k, h1, h2, h3⟩ : ∃ (f : Nat → RejSt → Id (ForInStep RejSt)) (k : RejSt → Id (Option Poly)),
      (∀ x s, f x s = rejBody x s) ∧ (∀ s, k s = tailFn s) ∧
      Spec.RejNTTPoly fuel ρ = Id.run (do
        let __s ← forIn (m := Id) (List.range' 0 fuel) ((none, Poly.zero, 0, G.InitAbsorb (3 * fuel) ρ) : RejSt) f
        k __s) := by
    refine' ⟨_, _, ?h1, ?h2, ?h3⟩
    case h3 =>
      unfold Spec.RejNTTPoly
      have hs : [:fuel].size = fuel := by simp [Std.Legacy.Range.size]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs]
      rfl
    case h1 =>
      intro x s
      unfold rejBody
      by_cases hj : s.2.2.1 ≥ 256
      · simp only [hj, if_true]
      · simp only [hj, if_false]
        rcases hq : G.Squeeze s.2.2.2 3 with _ | ⟨ctx', t⟩
        · simp only [hq]
        · simp only [hq]
          generalize CoeffFromThreeBytes t[0]! t[1]! t[2]! = c
          cases c <;> rfl
    case h2 =>
      intro s
      unfold tailFn
      rcases s with ⟨_ | r, a, j, c⟩ <;> rfl
  have : f = rejBody := funext fun x => funext fun s => h1 x s
  have hk : k = fun s => pure (tailFn s) := funext fun s => by rw [h2]; rfl
  subst this
  rw [h3, hk]
  rfl

theorem foldl_stepA_stable (T : List UInt8) (l : List Nat) (p : Poly × Nat) (h : 256 ≤ p.2) :
    l.foldl (stepA T) p = p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.foldl_cons, stepA, h, ih]

theorem rej_loop (T : List UInt8) (fuel : Nat) (hT : T.length = 3 * fuel) :
    ∀ n s (a : Poly) j, s + n ≤ fuel → ∃ c, forIn (m := Id) (List.range' s n) ((none, a, j, ⟨T, 3 * s⟩) : RejSt) rejBody =
      (none, ((List.range' s n).foldl (stepA T) (a, j)).1, ((List.range' s n).foldl (stepA T) (a, j)).2, c) := by
  intro n
  induction n with
  | zero => intro s a j _; exact ⟨_, rfl⟩
  | succ n ih =>
    intro s a j hn
    rw [List.range'_succ, List.forIn_cons]
    by_cases hj : 256 ≤ j
    · have e : stepA T (a, j) s = (a, j) := by simp [stepA, hj]
      simp only [rejBody, hj, ge_iff_le, if_true, pure_bind]
      rw [List.foldl_cons, e, foldl_stepA_stable T _ _ hj]
      exact ⟨_, rfl⟩
    · have hlen : 3 * s + 3 ≤ T.length := by omega
      have e3 : 3 * (s + 1) = 3 * s + 3 := by omega
      obtain ⟨c, hc⟩ := ih (s + 1) a j (by omega)
      simp only [rejBody, hj, ge_iff_le, if_false, pure_bind, Ctx.Squeeze, hlen, if_true]
      rw [List.foldl_cons]
      have hCT : CoeffFromThreeBytes (List.take 3 (List.drop (3 * s) T))[0]!
          (List.take 3 (List.drop (3 * s) T))[1]! (List.take 3 (List.drop (3 * s) T))[2]! = triAt T s := rfl
      rw [hCT]
      rcases h : triAt T s with _ | v
      · have e : stepA T (a, j) s = (a, j) := by simp [stepA, hj, h]
        simp only [h, pure_bind]
        rw [e]
        rw [e3] at hc
        rw [hc]
        exact ⟨c, rfl⟩
      · obtain ⟨c, hc⟩ := ih (s + 1) (a.set! j v) (j + 1) (by omega)
        have e : stepA T (a, j) s = (a.set! j v, j + 1) := by simp [stepA, hj, h]
        simp only [h, pure_bind]
        rw [e]
        rw [e3] at hc
        rw [hc]
        exact ⟨c, rfl⟩

/-- State of the pure model after `n` iterations. -/
def stA (T : List UInt8) (n : Nat) : Poly × Nat := (List.range' 0 n).foldl (stepA T) (Poly.zero, 0)

theorem stA_succ (T : List UInt8) (n : Nat) : stA T (n + 1) = stepA T (stA T n) n := by
  simp [stA, List.range'_concat]

theorem stA_stable (T : List UInt8) (m n : Nat) (h : 256 ≤ (stA T m).2) (hmn : m ≤ n) : stA T n = stA T m := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [← Nat.add_assoc, stA_succ, ih (by omega)]
    simp [stepA, h]

theorem rej_eq_some (fuel : Nat) (ρ : List UInt8) (a : Poly) (h : Spec.RejNTTPoly fuel ρ = some a) :
    256 ≤ (stA (SHAKE128 ρ (3 * fuel)) fuel).2 ∧ (stA (SHAKE128 ρ (3 * fuel)) fuel).1 = a := by
  rw [rej_unfold] at h
  obtain ⟨c, hc⟩ := rej_loop (SHAKE128 ρ (3 * fuel)) fuel (SHAKE128_length _ _) fuel 0 Poly.zero 0 (by omega)
  have hc' : forIn (m := Id) (List.range' 0 fuel) ((none, Poly.zero, 0, G.InitAbsorb (3 * fuel) ρ) : RejSt) rejBody =
      (none, (stA (SHAKE128 ρ (3 * fuel)) fuel).1, (stA (SHAKE128 ρ (3 * fuel)) fuel).2, c) := hc
  simp only [hc', tailFn] at h
  by_cases h2 : (stA (SHAKE128 ρ (3 * fuel)) fuel).2 < 256
  · simp [h2] at h
  · simp [h2] at h
    exact ⟨by omega, h⟩

theorem rej_some_of_fin (ρ : List UInt8) (fuel : Nat) (hfin : 256 ≤ (stA (SHAKE128 ρ (3 * fuel)) fuel).2) :
    Spec.RejNTTPoly fuel ρ = some (stA (SHAKE128 ρ (3 * fuel)) fuel).1 := by
  rw [rej_unfold]
  obtain ⟨c, hc⟩ := rej_loop (SHAKE128 ρ (3 * fuel)) fuel (SHAKE128_length _ _) fuel 0 Poly.zero 0 (by omega)
  have hc' : forIn (m := Id) (List.range' 0 fuel) ((none, Poly.zero, 0, G.InitAbsorb (3 * fuel) ρ) : RejSt) rejBody =
      (none, (stA (SHAKE128 ρ (3 * fuel)) fuel).1, (stA (SHAKE128 ρ (3 * fuel)) fuel).2, c) := hc
  simp only [hc', tailFn]
  have h2 : ¬ (stA (SHAKE128 ρ (3 * fuel)) fuel).2 < 256 := by omega
  simp [h2]

/-! ## ocaml-pq's `rejNTTPolyLoop` as a fold -/

/-- One call of `rejNTTPolyLoop` that does work, as a state transformer; `i` indexes the triple at `p + 3 i`. -/
def stepS (s : ℕ → OcamlPq.MLDSAAlg.Byte) (p : ℕ) (st : (ℕ → ℤ) × ℕ) (i : ℕ) : (ℕ → ℤ) × ℕ :=
  if 256 ≤ st.2 then st else
  match OcamlPq.MLDSAAlg.coeffFromThreeBytes (s (p + 3 * i)).val (s (p + 3 * i + 1)).val
      (s (p + 3 * i + 2)).val with
  | some z => (Function.update st.1 st.2 (z : ℤ), st.2 + 1)
  | none => st

def foldS (s : ℕ → OcamlPq.MLDSAAlg.Byte) (p n : ℕ) (st : (ℕ → ℤ) × ℕ) : (ℕ → ℤ) × ℕ :=
  (List.range' 0 n).foldl (stepS s p) st

theorem foldl_range'_shift {α : Type} (f : α → ℕ → α) (k n : ℕ) (st : α) :
    (List.range' (k + 1) n).foldl f st = (List.range' k n).foldl (fun st i => f st (i + 1)) st := by
  induction n generalizing k st with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.range'_succ, List.foldl_cons, List.foldl_cons]
    exact ih (k + 1) _

theorem foldS_succ (s : ℕ → OcamlPq.MLDSAAlg.Byte) (p n : ℕ) (st : (ℕ → ℤ) × ℕ) :
    foldS s p (n + 1) st = foldS s (p + 3) n (stepS s p st 0) := by
  unfold foldS
  rw [List.range'_succ, List.foldl_cons, foldl_range'_shift _ 0 n]
  congr 1
  funext st i
  unfold stepS
  have h1 : p + 3 * (i + 1) = p + 3 + 3 * i := by omega
  simp only [h1]

theorem foldS_stable (s : ℕ → OcamlPq.MLDSAAlg.Byte) (p n : ℕ) (st : (ℕ → ℤ) × ℕ) (h : 256 ≤ st.2) :
    foldS s p n st = st := by
  induction n generalizing p st with
  | zero => rfl
  | succ n ih => rw [foldS_succ]; simp [stepS, h, ih]

theorem loop_eq_foldS (s : ℕ → OcamlPq.MLDSAAlg.Byte) :
    ∀ f p j (a : ℕ → ℤ), OcamlPq.MLDSAAlg.rejNTTPolyLoop s (f + 1) p j a =
      if 256 ≤ (foldS s p f (a, j)).2 then some (foldS s p f (a, j)).1 else none := by
  intro f
  induction f with
  | zero =>
    intro p j a
    by_cases hj : j < 256
    · have : ¬ 256 ≤ j := by omega
      simp only [OcamlPq.MLDSAAlg.rejNTTPolyLoop, hj, if_true, foldS, List.range'_zero, List.foldl_nil, this,
        if_false]
      cases OcamlPq.MLDSAAlg.coeffFromThreeBytes (s p).val (s (p + 1)).val (s (p + 2)).val <;> rfl
    · have : 256 ≤ j := by omega
      simp [OcamlPq.MLDSAAlg.rejNTTPolyLoop, hj, foldS, this]
  | succ f ih =>
    intro p j a
    by_cases hj : j < 256
    · have hn : ¬ 256 ≤ j := by omega
      rw [OcamlPq.MLDSAAlg.rejNTTPolyLoop, if_pos hj, foldS_succ]
      unfold stepS
      simp only [hn, if_false, Nat.mul_zero, Nat.add_zero]
      cases OcamlPq.MLDSAAlg.coeffFromThreeBytes (s p).val (s (p + 1)).val (s (p + 2)).val with
      | none => exact ih _ _ _
      | some z => exact ih _ _ _
    · have hn : 256 ≤ j := by omega
      rw [OcamlPq.MLDSAAlg.rejNTTPolyLoop, if_neg hj, foldS_stable _ _ _ _ (by simpa using hn)]
      simp [hn]

/-! ## Ours against theirs -/

theorem poly_ge (A : Poly) (i : ℕ) (hi : ¬ i < 256) : A[i]! = 0 := by
  rw [getElem!_neg A i (by simpa using hi)]; rfl

theorem canon_zero : canon Poly.zero = fun _ => (0 : ℤ) := by
  funext i
  by_cases hi : i < 256
  · simp [canon, Poly.zero, vget! _ i hi]
  · simp [canon, poly_ge _ i hi]

theorem canon_set (A : Poly) (j : ℕ) (hj : j < 256) (v : Zq) :
    canon (A.set! j v) = Function.update (canon A) j (v.val : ℤ) := by
  funext i
  by_cases h : i = j
  · subst h
    simp [canon, set!_eq', Function.update, vget! _ i hj]
  · by_cases hi : i < 256
    · simp [canon, set!_eq', Function.update, h, vget! _ i hi, Vector.getElem_setIfInBounds, Ne.symm h]
    · have : (A.set! j v)[i]! = 0 := poly_ge _ i hi
      simp [canon, Function.update, h, poly_ge _ i hi, this]

theorem coeffFromThreeBytes_lt {b0 b1 b2 z : ℕ} (h : OcamlPq.MLDSAAlg.coeffFromThreeBytes b0 b1 b2 = some z) :
    z < Spec.q := by
  have hq : OcamlPq.MLDSAAlg.q = Spec.q := rfl
  unfold OcamlPq.MLDSAAlg.coeffFromThreeBytes at h
  simp only [hq] at h
  split_ifs at h <;> simp_all

theorem foldS_snoc (s : ℕ → OcamlPq.MLDSAAlg.Byte) (p n : ℕ) (st : (ℕ → ℤ) × ℕ) :
    foldS s p (n + 1) st = stepS s p (foldS s p n st) n := by
  simp [foldS, List.range'_concat]

theorem tripleAt_get (T : List UInt8) (n i : ℕ) (hi : i < 3) (hT : 3 * n + 3 ≤ T.length) :
    (tripleAt T n)[i]! = T.getD (3 * n + i) 0 := by
  have h1 : (tripleAt T n).length = 3 := by simp [tripleAt]; omega
  rw [getElem!_pos _ i (by simp [h1]; exact hi)]
  simp only [tripleAt, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega)]
  simp

theorem rel_step (ρ : List UInt8) (F n : ℕ) (hn : n < F) (A : Poly) (j : ℕ) :
    stepS (oursShake128 (u8ToBytes ρ)) 0 (canon A, j) n =
      ((stepA (SHAKE128 ρ (3 * F)) (A, j) n).1 |> canon, (stepA (SHAKE128 ρ (3 * F)) (A, j) n).2) := by
  have hT := Spec.SHAKE128_length ρ (3 * F)
  by_cases hj : 256 ≤ j
  · simp [stepS, stepA, hj]
  · have v0 := oursShake128_val ρ (3 * F) (0 + 3 * n) (by omega)
    have v1 := oursShake128_val ρ (3 * F) (0 + 3 * n + 1) (by omega)
    have v2 := oursShake128_val ρ (3 * F) (0 + 3 * n + 2) (by omega)
    rw [Nat.zero_add] at v0 v1 v2
    have hc : triAt (SHAKE128 ρ (3 * F)) n =
        Option.map (Nat.cast : Nat → Zq) (OcamlPq.MLDSAAlg.coeffFromThreeBytes
          ((SHAKE128 ρ (3 * F)).getD (3 * n) 0).toNat ((SHAKE128 ρ (3 * F)).getD (3 * n + 1) 0).toNat
          ((SHAKE128 ρ (3 * F)).getD (3 * n + 2) 0).toNat) := by
      unfold triAt
      rw [coeffFromThreeBytes_eq, tripleAt_get _ n 0 (by omega) (by omega), tripleAt_get _ n 1 (by omega) (by omega),
        tripleAt_get _ n 2 (by omega) (by omega)]
      rfl
    unfold stepS stepA
    rw [if_neg (by simpa using hj), if_neg (by simpa using hj)]
    simp only [Nat.zero_add]
    rw [v0, v1, v2, hc]
    rcases h : OcamlPq.MLDSAAlg.coeffFromThreeBytes ((SHAKE128 ρ (3 * F)).getD (3 * n) 0).toNat
        ((SHAKE128 ρ (3 * F)).getD (3 * n + 1) 0).toNat ((SHAKE128 ρ (3 * F)).getD (3 * n + 2) 0).toNat with _ | z
    · simp
    · have hz := coeffFromThreeBytes_lt h
      have hjl : j < 256 := by omega
      simp only [Option.map_some]
      show (Function.update (canon A) j (z : ℤ), j + 1) = (canon (A.set! j (z : Zq)), j + 1)
      rw [canon_set A j hjl]
      simp [ZMod.val_natCast_of_lt (show z < Spec.q from hz)]

theorem rel_fold (ρ : List UInt8) (F : ℕ) :
    ∀ n ≤ F, foldS (oursShake128 (u8ToBytes ρ)) 0 n ((fun _ => (0 : ℤ)), 0) =
      (canon (stA (SHAKE128 ρ (3 * F)) n).1, (stA (SHAKE128 ρ (3 * F)) n).2) := by
  intro n
  induction n with
  | zero => intro _; simp [foldS, stA, canon_zero]
  | succ n ih =>
    intro hn
    rw [foldS_snoc, ih (by omega), stA_succ]
    exact rel_step ρ F n (by omega) _ _

/-- **Ours implies theirs.**  If `RejNTTPoly F ρ = some a`, ocaml-pq's `RejNTTPoly` on the SHAKE128 stream of `ρ`
(with our SHAKE) returns `canon a`; the fuel is `F + 1` (one extra call observes `j = 256`). -/
theorem rejNTT_ours_to_theirs (ρ : List UInt8) (F : ℕ) (a : Poly) (h : Spec.RejNTTPoly F ρ = some a) :
    OcamlPq.MLDSAAlg.RejNTTPolyReturns (oursShake128 (u8ToBytes ρ)) (canon a) := by
  obtain ⟨hfin, rfl⟩ := rej_eq_some F ρ a h
  refine ⟨F + 1, ?_⟩
  rw [loop_eq_foldS, rel_fold ρ F F le_rfl]
  simp [hfin]

/-- **Theirs implies ours.**  If ocaml-pq's `RejNTTPoly` returns `b` on the SHAKE128 stream of `ρ`, then some
fuel makes ours return `some a` with `canon a = b`. -/
theorem rejNTT_theirs_to_ours (ρ : List UInt8) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.RejNTTPolyReturns (oursShake128 (u8ToBytes ρ)) b) :
    ∃ F a, Spec.RejNTTPoly F ρ = some a ∧ canon a = b := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := by
    cases f with
    | zero => simp [OcamlPq.MLDSAAlg.rejNTTPolyLoop] at hf
    | succ F => exact ⟨F, rfl⟩
  rw [loop_eq_foldS, rel_fold ρ F F le_rfl] at hf
  by_cases hfin : 256 ≤ (stA (SHAKE128 ρ (3 * F)) F).2
  · rw [if_pos hfin] at hf
    exact ⟨F, _, rej_some_of_fin ρ F hfin, Option.some.inj hf⟩
  · rw [if_neg hfin] at hf; cases hf

end RN

namespace RB

/-- One iteration of Algorithm 31 after the squeeze: `z` is the byte, `st = (a, j)`. -/
def rbStep (η : Nat) (st : RPoly × Nat) (z : Nat) : RPoly × Nat :=
  let s1 : RPoly × Nat :=
    match CoeffFromHalfByte η (z % 16) with
    | some v => (st.1.set! st.2 v, st.2 + 1)
    | none => st
  match CoeffFromHalfByte η (z / 16) with
  | some v => if s1.2 < 256 then (s1.1.set! s1.2 v, s1.2 + 1) else s1
  | none => s1

/-- `n` iterations of the `while j < 256` loop, reading stream bytes `s, s+1, ...`. -/
def rbRun (η : Nat) (stream : List UInt8) : RPoly × Nat → Nat → Nat → RPoly × Nat
  | st, _, 0 => st
  | st, s, n + 1 =>
    if st.2 ≥ 256 then st else rbRun η stream (rbStep η st (stream[s]!).toNat) (s + 1) n

theorem rbRun_stop (η : Nat) (stream : List UInt8) (st : RPoly × Nat) (h : st.2 ≥ 256) (s n : Nat) :
    rbRun η stream st s n = st := by
  cases n with
  | zero => rfl
  | succ n => simp [rbRun, h]

abbrev RBState := Option (Option RPoly) × RPoly × Nat × Ctx

def rbBody (p : Spec.Params) (_ : Nat) (r : RBState) : Id (ForInStep RBState) :=
  if r.2.2.1 ≥ 256 then pure (ForInStep.done (none, r.2.1, r.2.2.1, r.2.2.2))
  else match H.Squeeze r.2.2.2 1 with
    | some (ctx', s) =>
      let t := rbStep p.η (r.2.1, r.2.2.1) (s[0]!).toNat
      pure (ForInStep.yield (none, t.1, t.2, ctx'))
    | none => pure (ForInStep.done (some none, r.2.1, r.2.2.1, r.2.2.2))

theorem RejBoundedPoly_eq_forIn (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.RejBoundedPoly p fuel ρ =
      (let r := (forIn (m := Id) (List.range' 0 fuel) ((none, Vector.replicate 256 0, 0, H.InitAbsorb fuel ρ) : RBState)
          (rbBody p)).run
       match r.1 with
       | none => if r.2.2.1 < 256 then none else some r.2.1
       | some a => a) := by
  obtain ⟨f, k, h1, h2, h3⟩ : ∃ (f : Nat → RBState → Id (ForInStep RBState)) (k : RBState → Id (Option RPoly)),
      (∀ x r, f x r = rbBody p x r) ∧
      (∀ r, k r = (match r.1 with
        | none => if r.2.2.1 < 256 then none else some r.2.1
        | some a => a)) ∧
      Spec.RejBoundedPoly p fuel ρ = Id.run (do
        let __s ← forIn (m := Id) (List.range' 0 fuel) ((none, Vector.replicate 256 0, 0, H.InitAbsorb fuel ρ) : RBState) f
        k __s) := by
    refine' ⟨_, _, ?h1, ?h2, ?h3⟩
    case h3 =>
      unfold Spec.RejBoundedPoly
      have hs : [:fuel].size = fuel := by simp [Std.Legacy.Range.size]
      simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs]
      rfl
    case h1 =>
      intro x r
      obtain ⟨b, a, j, ctx⟩ := r
      simp only [rbBody, rbStep]
      by_cases hj : j ≥ 256
      · simp [hj]
      · simp only [hj, if_false, pure_bind]
        rcases hs : H.Squeeze ctx 1 with _ | ⟨ctx', s⟩
        · simp [hs]
        · simp only [hs]
          rcases h0 : CoeffFromHalfByte p.η (s[0]!.toNat % 16) with _ | v
          · rcases h1 : CoeffFromHalfByte p.η (s[0]!.toNat / 16) with _ | w <;> simp [h0, h1] <;>
              (split_ifs <;> simp_all)
          · rcases h1 : CoeffFromHalfByte p.η (s[0]!.toNat / 16) with _ | w <;> simp [h0, h1] <;>
              (split_ifs <;> simp_all)
    case h2 =>
      intro r
      rcases r with ⟨_ | _ | a', _⟩ <;> rfl
  have : f = rbBody p := funext fun x => funext fun s => h1 x s
  have hk : k = fun s => pure (match s.1 with
        | none => if s.2.2.1 < 256 then none else some s.2.1
        | some a => a) := funext fun s => by rw [h2]; rfl
  subst this
  rw [h3, hk]
  rfl

theorem drop_take_one_get (l : List UInt8) (s : Nat) (h : s < l.length) :
    ((l.drop s).take 1)[0]! = l[s]! := by
  rw [List.drop_eq_getElem_cons h]
  simp [getElem!_pos, h]

theorem stream_length (fuel : Nat) (ρ : List UInt8) : (H.InitAbsorb fuel ρ).stream.length = fuel := by
  simp [H.InitAbsorb, H, SHAKE256_length]

theorem forIn_rbBody (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (n : Nat) :
    ∀ (s : Nat) (a : RPoly) (j : Nat), s + n ≤ fuel → ∃ ctx' : Ctx,
      forIn (m := Id) (List.range' s n) ((none, a, j, ⟨(H.InitAbsorb fuel ρ).stream, s⟩) : RBState) (rbBody p)
        = ((none, (rbRun p.η (H.InitAbsorb fuel ρ).stream (a, j) s n).1,
            (rbRun p.η (H.InitAbsorb fuel ρ).stream (a, j) s n).2, ctx') : RBState) := by
  induction n with
  | zero => intro s a j _; exact ⟨_, rfl⟩
  | succ n ih =>
    intro s a j hs
    by_cases hj : j ≥ 256
    · refine ⟨⟨(H.InitAbsorb fuel ρ).stream, s⟩, ?_⟩
      rw [rbRun_stop _ _ (a, j) hj]
      simp [List.range'_succ, List.forIn_cons, rbBody, hj]
      rfl
    · have hlen : s < (H.InitAbsorb fuel ρ).stream.length := by rw [stream_length]; omega
      have hsq : H.Squeeze ⟨(H.InitAbsorb fuel ρ).stream, s⟩ 1 =
          some (⟨(H.InitAbsorb fuel ρ).stream, s + 1⟩, ((H.InitAbsorb fuel ρ).stream.drop s).take 1) := by
        simp only [H.Squeeze, Ctx.Squeeze]
        rw [if_pos (by omega)]
      obtain ⟨ctx', h⟩ := ih (s + 1) (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).1
        (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).2 (by omega)
      refine ⟨ctx', ?_⟩
      rw [List.range'_succ, List.forIn_cons]
      have hb : rbBody p s (none, a, j, ⟨(H.InitAbsorb fuel ρ).stream, s⟩) = pure (ForInStep.yield
          (none, (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).1,
            (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).2,
            ⟨(H.InitAbsorb fuel ρ).stream, s + 1⟩)) := by
        simp only [rbBody]
        rw [if_neg hj, hsq]
        simp only [drop_take_one_get _ _ hlen]
      rw [hb, pure_bind]
      dsimp only
      rw [h]
      simp only [rbRun, if_neg hj]

theorem RejBoundedPoly_eq (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.RejBoundedPoly p fuel ρ =
      (if (rbRun p.η (H ρ fuel) (Vector.replicate 256 0, 0) 0 fuel).2 < 256 then none
       else some (rbRun p.η (H ρ fuel) (Vector.replicate 256 0, 0) 0 fuel).1) := by
  rw [RejBoundedPoly_eq_forIn]
  simp only [Id.run]
  obtain ⟨ctx', h⟩ := forIn_rbBody p fuel ρ fuel 0 (Vector.replicate 256 0) 0 (by omega)
  have e : ((none, Vector.replicate 256 0, 0, H.InitAbsorb fuel ρ) : RBState) =
      (none, Vector.replicate 256 0, 0, ⟨(H.InitAbsorb fuel ρ).stream, 0⟩) := rfl
  rw [e, h]
  rfl

/-! ## Ours against theirs -/

theorem rfn_replicate : rfn (Vector.replicate 256 (0 : ℤ)) = fun _ => (0 : ℤ) := by
  funext i
  by_cases hi : i < 256
  · simp [rfn, vget! _ i hi]
  · have : ((Vector.replicate 256 (0 : ℤ)))[i]! = 0 := by
      rw [getElem!_neg (Vector.replicate 256 (0 : ℤ)) i (by simpa using hi)]; rfl
    simp [rfn, this]

theorem rfn_set (w : RPoly) (j : ℕ) (hj : j < 256) (v : ℤ) :
    rfn (w.set! j v) = Function.update (rfn w) j v := by
  funext i
  by_cases h : i = j
  · subst h
    simp [rfn, set!_eq', Function.update, vget! _ i hj]
  · by_cases hi : i < 256
    · simp [rfn, set!_eq', Function.update, h, vget! _ i hi, Ne.symm h]
    · have h1 : (w.set! j v)[i]! = 0 := by
        rw [getElem!_neg _ i (by simpa using hi)]; rfl
      have h2 : w[i]! = 0 := by
        rw [getElem!_neg w i (by simpa using hi)]; rfl
      simp [rfn, Function.update, h, h1, h2]

theorem bodyRel (η : ℕ) (st : RPoly × ℕ) (z : ℕ) (hst : st.2 < 256) :
    OcamlPq.MLDSAAlg.rejBoundedBody η (st.2, rfn st.1) z = ((rbStep η st z).2, rfn (rbStep η st z).1) := by
  unfold OcamlPq.MLDSAAlg.rejBoundedBody rbStep
  have e0 : CoeffFromHalfByte η (z % 16) = OcamlPq.MLDSAAlg.coeffFromHalfByte η (z % 16) := rfl
  have e1 : CoeffFromHalfByte η (z / 16) = OcamlPq.MLDSAAlg.coeffFromHalfByte η (z / 16) := rfl
  rw [e0, e1]
  rcases OcamlPq.MLDSAAlg.coeffFromHalfByte η (z % 16) with _ | v <;>
    rcases OcamlPq.MLDSAAlg.coeffFromHalfByte η (z / 16) with _ | w
  case none.none => rfl
  case none.some =>
    simp only [if_pos hst, rfn_set _ _ hst]
  case some.none =>
    simp only [rfn_set _ _ hst]
  case some.some =>
    by_cases h2 : st.2 + 1 < 256
    · simp only [if_pos h2, rfn_set _ _ h2, rfn_set _ _ hst]
    · simp only [if_neg h2, rfn_set _ _ hst]

theorem loopB_eq (η : ℕ) (S : ℕ → OcamlPq.MLDSAAlg.Byte) (T : List UInt8) :
    ∀ n s (st : RPoly × ℕ), (∀ i, s ≤ i → i < s + n → (S i).val = (T[i]!).toNat) →
      OcamlPq.MLDSAAlg.rejBoundedLoop η S (n + 1) s (st.2, rfn st.1) =
        if 256 ≤ (rbRun η T st s n).2 then some (rfn (rbRun η T st s n).1) else none := by
  intro n
  induction n with
  | zero =>
    intro s st _
    by_cases h : st.2 < 256
    · have h' : ¬ 256 ≤ st.2 := by omega
      simp [OcamlPq.MLDSAAlg.rejBoundedLoop, rbRun, h, h']
    · have h' : 256 ≤ st.2 := by omega
      simp [OcamlPq.MLDSAAlg.rejBoundedLoop, rbRun, h, h']
  | succ n ih =>
    intro s st hS
    by_cases h : st.2 < 256
    · have hn : ¬ st.2 ≥ 256 := by omega
      rw [OcamlPq.MLDSAAlg.rejBoundedLoop, if_pos h, rbRun, if_neg hn, hS s le_rfl (by omega), bodyRel _ _ _ h]
      exact ih (s + 1) _ (fun i hi1 hi2 => hS i (by omega) (by omega))
    · have hn : st.2 ≥ 256 := by omega
      rw [OcamlPq.MLDSAAlg.rejBoundedLoop, if_neg h, rbRun_stop _ _ _ hn]
      simp [hn]

theorem bang_getD (T : List UInt8) (i : ℕ) (h : i < T.length) : (T[i]!).toNat = (T.getD i 0).toNat := by
  rw [getElem!_pos T i h, List.getD_eq_getElem _ _ h]

theorem rejBounded_ours_to_theirs (p : Spec.Params) (ρ : List UInt8) (F : ℕ) (a : RPoly)
    (h : Spec.RejBoundedPoly p F ρ = some a) :
    OcamlPq.MLDSAAlg.RejBoundedReturns p.η (oursShake256 (u8ToBytes ρ)) (rfn a) := by
  rw [RejBoundedPoly_eq] at h
  have hT : (Spec.H ρ F).length = F := Spec.SHAKE256_length ρ F
  split at h
  · cases h
  · rename_i hlt
    cases h
    refine ⟨F + 1, ?_⟩
    have := loopB_eq p.η (oursShake256 (u8ToBytes ρ)) (Spec.H ρ F) F 0 (Vector.replicate 256 0, 0) (by
      intro i _ hi
      rw [oursShake256_val ρ F i (by omega), bang_getD _ i (by omega)]
      rfl)
    simp only [rfn_replicate] at this
    rw [this, if_pos (by omega)]

theorem rejBounded_theirs_to_ours (p : Spec.Params) (ρ : List UInt8) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.RejBoundedReturns p.η (oursShake256 (u8ToBytes ρ)) b) :
    ∃ F a, Spec.RejBoundedPoly p F ρ = some a ∧ rfn a = b := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := by
    cases f with
    | zero => simp [OcamlPq.MLDSAAlg.rejBoundedLoop] at hf
    | succ F => exact ⟨F, rfl⟩
  have hT : (Spec.H ρ F).length = F := Spec.SHAKE256_length ρ F
  have := loopB_eq p.η (oursShake256 (u8ToBytes ρ)) (Spec.H ρ F) F 0 (Vector.replicate 256 0, 0) (by
    intro i _ hi
    rw [oursShake256_val ρ F i (by omega), bang_getD _ i (by omega)]
    rfl)
  simp only [rfn_replicate] at this
  rw [this] at hf
  by_cases hfin : 256 ≤ (rbRun p.η (Spec.H ρ F) (Vector.replicate 256 0, 0) 0 F).2
  · rw [if_pos hfin] at hf
    refine ⟨F, _, ?_, Option.some.inj hf⟩
    rw [RejBoundedPoly_eq, if_neg (by omega)]
  · rw [if_neg hfin] at hf; cases hf

end RB

end XSpec
