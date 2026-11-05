import Proofs.Keccak
import Proofs.Coeff
import Proofs.Repr
import Proofs.NTTOps

/-!
# RejNTTPoly and ExpandA (FIPS 204 Algorithms 30 and 32)

Premise (named `RejTerm`, docs/assurance.md): the spec returns `some` at some fuel. The Rust loop is unbounded, so
termination is derived from the spec's run.

* Spec side: `RejNTTPoly fuel ρ` is a `forIn` over `List.range' 0 fuel`; `rej_loop` shows it equals the pure
  fold `stA T fuel` (`stepA`: skip when `j ≥ 256`, else accept/reject the next 3-byte window of
  `T = SHAKE128 ρ (3 * fuel)`). `rej_eq_some` : `some a` means `256 ≤ j` and `a` is the fold's polynomial.
  `ExpandA` equals a `foldlM` in `Option` (`expandA_eq`).
* Rust side: loop invariant `RejInv` carries the iteration count `n` as a ghost (`ShakeSqz ctx 168 ρ (3 * n)`).
  The count is not a function of the state (the sponge state does not determine `n`), so `loop.spec_decr_nat`
  does not apply; `rej_loop_spec` unfolds `loop` and does induction on `fuel - n`. The body spec shows that with
  `j < 256` we have `n < fuel` (otherwise the fold would have `j < 256` at `n = fuel`), so the loop exits before
  the fuel runs out.
* `expand_a_spec`: nested loops with invariants `foldlM … (range' 0 s) = some B ∧ ReprMat a B`.
-/
open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192
namespace Proofs
open Impl
namespace SampleA

abbrev RejSt := MProd (Option (Option Poly)) (MProd Poly (MProd Ctx Nat))

def tripleAt (T : List UInt8) (i : Nat) : List UInt8 := (T.drop (3 * i)).take 3

def triAt (T : List UInt8) (i : Nat) : Option Zq :=
  CoeffFromThreeBytes (tripleAt T i)[0]! (tripleAt T i)[1]! (tripleAt T i)[2]!

def stepA (T : List UInt8) (s : Poly × Nat) (i : Nat) : Poly × Nat :=
  if 256 ≤ s.2 then s else
  match triAt T i with
  | some v => (s.1.set! s.2 v, s.2 + 1)
  | none => s

def rejBody (_ : Nat) (r : RejSt) : Id (ForInStep RejSt) :=
  have r := r.snd
  have a := r.fst
  have x := r.snd
  have ctx := x.fst
  have j := x.snd
  have __do_jp := fun a ctx j (_ : PUnit) =>
    match G.Squeeze ctx 3 with
    | some (ctx', s) =>
      have ctx := ctx'
      match CoeffFromThreeBytes s[0]! s[1]! s[2]! with
      | some v =>
        have a := Vector.set! a j v
        have j := j + 1
        pure (ForInStep.yield ⟨none, a, ctx, j⟩)
      | none => 
        pure (ForInStep.yield ⟨none, a, ctx, j⟩)
    | x => pure (ForInStep.done ⟨some none, a, ctx, j⟩)
  if j ≥ 256 then pure (ForInStep.done ⟨none, a, ctx, j⟩)
  else do
    let y ← pure PUnit.unit
    __do_jp a ctx j y

theorem rej_unfold (fuel : Nat) (ρ : List UInt8) :
    Spec.RejNTTPoly fuel ρ =
      (let r := forIn (m := Id) (List.range' 0 fuel) (⟨none, Poly.zero, G.InitAbsorb (3 * fuel) ρ, 0⟩ : RejSt) rejBody
       match r.fst with
       | none => if r.2.2.snd < 256 then none else some r.2.fst
       | some a => a) := by
  unfold Spec.RejNTTPoly
  have hs : [:fuel].size = fuel := by simp [Std.Legacy.Range.size]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs]
  rfl

theorem foldl_stepA_stable (T : List UInt8) (l : List Nat) (p : Poly × Nat) (h : 256 ≤ p.2) :
    l.foldl (stepA T) p = p := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.foldl_cons, stepA, h, ih]

theorem rej_loop (T : List UInt8) (fuel : Nat) (hT : T.length = 3 * fuel) :
    ∀ n s (a : Poly) j, s + n ≤ fuel → ∃ c, forIn (m := Id) (List.range' s n) (⟨none, a, ⟨T, 3 * s⟩, j⟩ : RejSt) rejBody =
      ⟨none, ((List.range' s n).foldl (stepA T) (a, j)).1, c, ((List.range' s n).foldl (stepA T) (a, j)).2⟩ := by
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
  have hc' : forIn (m := Id) (List.range' 0 fuel) (⟨none, Poly.zero, G.InitAbsorb (3 * fuel) ρ, 0⟩ : RejSt) rejBody =
      ⟨none, (stA (SHAKE128 ρ (3 * fuel)) fuel).1, c, (stA (SHAKE128 ρ (3 * fuel)) fuel).2⟩ := hc
  simp only [hc'] at h
  by_cases h2 : (stA (SHAKE128 ρ (3 * fuel)) fuel).2 < 256
  · simp [h2] at h
  · simp [h2] at h
    exact ⟨by omega, h⟩


theorem stA_succ_none (T : List UInt8) (i : Nat) (h : triAt T i = none) (hj : (stA T i).2 < 256) :
    stA T (i + 1) = stA T i := by
  rw [stA_succ]; simp [stepA, h, Nat.not_le.mpr hj]

theorem stA_succ_some (T : List UInt8) (i : Nat) (v : Zq) (h : triAt T i = some v) (hj : (stA T i).2 < 256) :
    stA T (i + 1) = ((stA T i).1.set! (stA T i).2 v, (stA T i).2 + 1) := by
  rw [stA_succ]; simp [stepA, h, Nat.not_le.mpr hj]

theorem triple_bytes (ρ : List UInt8) (fuel i : Nat) (hif : i < fuel) (s1 s2 : Slice U8) (hs1 : s1.val.length = 3)
    (h : bytes s2 = List.drop (3 * i) (Keccak.sponge 168 ρ (3 * i + s1.val.length))) :
    s2.val.length = 3 ∧ bytes s2 = tripleAt (SHAKE128 ρ (3 * fuel)) i := by
  rw [hs1] at h
  have hw := sponge_window 168 (by omega) ρ (3 * i) 3 (3 * fuel) (by omega)
  rw [hw] at h
  have : (tripleAt (SHAKE128 ρ (3 * fuel)) i).length = 3 := by
    simp [tripleAt, SHAKE128_length]; omega
  refine ⟨?_, h.trans rfl⟩
  have h2 := congrArg List.length h
  simp only [bytes_length] at h2
  rw [h2]; exact this

theorem tmb_byte (s2 : Slice U8) (hl : s2.val.length = 3) (W : List UInt8) (hW : bytes s2 = W) (k : Nat)
    (hk : k < ((Array.repeat 3#usize 0#u8).from_slice s2).val.length) :
    UInt8.ofNat (((Array.repeat 3#usize 0#u8).from_slice s2).val[k]).val = W[k]! := by
  have e := Array.from_slice_val (Array.repeat 3#usize 0#u8) s2 (by simpa using hl)
  have hk' : k < s2.val.length := by rw [← e]; exact hk
  have : ((Array.repeat 3#usize 0#u8).from_slice s2).val[k] = s2.val[k]'hk' := by simp only [e]
  rw [this, ← hW]
  have hk'' : k < (bytes s2).length := by simpa using hk'
  rw [getElem!_pos (bytes s2) k hk'', bytes_getElem]

/-- Loop invariant of `rej_ntt_poly_loop` after `i` iterations. -/
def RejInv (ρ : List UInt8) (fuel i : Nat) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) : Prop :=
  Canonical a ∧ toZq a = (stA (SHAKE128 ρ (3 * fuel)) i).1 ∧ j.val = (stA (SHAKE128 ρ (3 * fuel)) i).2 ∧
    ShakeSqz ctx 168 ρ (3 * i)

theorem rej_body_spec (ρ : List UInt8) (fuel n : Nat) (hi : n ≤ fuel)
    (hfin : 256 ≤ (stA (SHAKE128 ρ (3 * fuel)) fuel).2)
    (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) (h : RejInv ρ fuel n a ctx j) :
    sampling.rej_ntt_poly_loop.body a ctx j ⦃ r =>
      match r with
      | .done y => Canonical y ∧ toZq y = (stA (SHAKE128 ρ (3 * fuel)) fuel).1
      | .cont (a', ctx', j') => n < fuel ∧ RejInv ρ fuel (n + 1) a' ctx' j' ⦄ := by
  obtain ⟨hc, ha, hj, hs⟩ := h
  unfold sampling.rej_ntt_poly_loop.body
  split
  · rename_i hlt
    have hj256 : j.val < 256 := by scalar_tac
    have hlt' : (stA (SHAKE128 ρ (3 * fuel)) n).2 < 256 := by omega
    have hif : n < fuel := by
      by_contra hcon
      have : n = fuel := by omega
      subst this; omega
    step*
    all_goals
      have hs1 : s1.val.length = 3 := by rw [s1_post1]; simp
      have hsq : ShakeSqz ctx1 168 ρ (3 * (n + 1)) := by
        have := ctx1_post1; rw [hs1] at this; exact this
      obtain ⟨hl2, hW⟩ := triple_bytes ρ fuel n hif s1 s2 hs1 ctx1_post2
      subst s1_post2 i_post2 i1_post2 i2_post2
      rw [tmb_byte s2 hl2 _ hW 0 i, tmb_byte s2 hl2 _ hW 1 i1, tmb_byte s2 hl2 _ hW 2 i2] at o_post
      have ho : Option.map (fun x => x.val) o = Option.map ZMod.val (triAt (SHAKE128 ρ (3 * fuel)) n) := o_post
    · have hon : o = none := ‹o = none›
      subst hon
      have htri : triAt (SHAKE128 ρ (3 * fuel)) n = none := by simpa using ho.symm
      have hst := stA_succ_none _ n htri hlt'
      refine ⟨hif, hc, ?_, ?_, hsq⟩
      · rw [hst]; exact ha
      · rw [hst]; exact hj
    · have hon : o = some x := ‹o = some x›
      subst hon
      obtain ⟨v, htri, hxv⟩ : ∃ v, triAt (SHAKE128 ρ (3 * fuel)) n = some v ∧ x.val = v.val := by
        revert ho
        rcases h : triAt (SHAKE128 ρ (3 * fuel)) n with _ | v
        · simp
        · simp only [Option.map_some, Option.some.injEq]
          intro h; exact ⟨v, rfl, h⟩
      have hst := stA_succ_some _ n v htri hlt'
      have hxq : x.val < Spec.q := by rw [hxv]; exact ZMod.val_lt v
      have hxz : ((x.val : Nat) : Zq) = v := by rw [hxv]; exact ZMod.natCast_zmod_val v
      have hjlt : j.val < 256 := hj256
      refine ⟨hif, ?_, ?_, ?_, hsq⟩
      · rw [a1_post]; exact canonical_set a j x hc hxq
      · rw [a1_post, toZq_set a j x hjlt, ha, hst, hj, hxz]
      · rw [j1_post, hst, hj]
  · rename_i hlt
    have hj256 : 256 ≤ j.val := by scalar_tac
    simp only [WP.spec_ok]
    have := stA_stable (SHAKE128 ρ (3 * fuel)) n fuel (by omega) hi
    refine ⟨hc, ?_⟩
    rw [ha, this]


theorem rej_loop_spec (ρ : List UInt8) (fuel : Nat) (hfin : 256 ≤ (stA (SHAKE128 ρ (3 * fuel)) fuel).2) :
    ∀ k n, fuel - n = k → n ≤ fuel → ∀ (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize),
      RejInv ρ fuel n a ctx j →
      sampling.rej_ntt_poly_loop a ctx j ⦃ r =>
        Canonical r ∧ toZq r = (stA (SHAKE128 ρ (3 * fuel)) fuel).1 ⦄ := by
  intro k
  induction k with
  | zero =>
    intro n hk hn a ctx j h
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (rej_body_spec ρ fuel n hn hfin a ctx j h)
    unfold sampling.rej_ntt_poly_loop
    rw [loop]
    dsimp only
    rw [hr]
    cases r with
    | cont x' =>
      obtain ⟨a', ctx', j'⟩ := x'
      have := hp.1; omega
    | done y => simpa using hp
  | succ k ih =>
    intro n hk hn a ctx j h
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (rej_body_spec ρ fuel n hn hfin a ctx j h)
    unfold sampling.rej_ntt_poly_loop
    rw [loop]
    dsimp only
    rw [hr]
    cases r with
    | cont x' =>
      obtain ⟨a', ctx', j'⟩ := x'
      have hp' := hp
      have := ih (n + 1) (by omega) (by omega) a' ctx' j' hp.2
      exact this
    | done y => simpa using hp

theorem rej_ntt_poly_spec_aux (ρ : Array U8 34#usize) (a : Spec.Poly) (fuel : Nat)
    (hs : Spec.RejNTTPoly fuel (bytesA ρ) = some a) :
    sampling.rej_ntt_poly ρ ⦃ r => Repr r a ⦄ := by
  obtain ⟨hfin, hA⟩ := rej_eq_some fuel (bytesA ρ) a hs
  unfold sampling.rej_ntt_poly
  step*
  subst s_post
  rw [bytes_to_slice, List.nil_append] at ctx2_post
  apply WP.spec_mono (rej_loop_spec (bytesA ρ) fuel hfin fuel 0 (by omega) (by omega) _ ctx2 0#usize ?_)
  · rintro r ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, hA]⟩
  · refine ⟨canonical_repeat_zero, ?_, ?_, ?_⟩
    · rw [toZq_repeat_zero]; rfl
    · show (0#usize).val = 0; rfl
    · simpa using ctx2_post


/-! ## ExpandA -/

theorem integerToBytes_one (x : Nat) : IntegerToBytes x 1 = [(x % 256).toUInt8] := by
  unfold IntegerToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- A `forIn` whose body either yields (`some`) or exits early (`none`) is a `foldlM` in `Option`. -/
theorem forIn_opt {α β γ : Type} (f : β → α → Option β)
    (g : α → MProd (Option (Option γ)) β → Id (ForInStep (MProd (Option (Option γ)) β)))
    (hg1 : ∀ x st b, f st.snd x = some b → g x st = pure (ForInStep.yield ⟨none, b⟩))
    (hg2 : ∀ x st, f st.snd x = none → ∃ junk, g x st = pure (ForInStep.done ⟨some none, junk⟩)) :
    ∀ (l : List α) (init : β),
      (∀ b, l.foldlM f init = some b → forIn (m := Id) l (⟨none, init⟩ : MProd (Option (Option γ)) β) g = ⟨none, b⟩) ∧
      (l.foldlM f init = none → (forIn (m := Id) l (⟨none, init⟩ : MProd (Option (Option γ)) β) g).fst = some none) := by
  intro l
  induction l with
  | nil => intro init; exact ⟨fun b hb => by simp at hb; subst hb; rfl, fun h => by simp at h⟩
  | cons x l ih =>
    intro init
    rcases hf : f init x with _ | b0
    · obtain ⟨junk, hj⟩ := hg2 x ⟨none, init⟩ hf
      refine ⟨fun b hb => by simp [hf] at hb, fun _ => ?_⟩
      rw [List.forIn_cons, hj]
      rfl
    · have hj := hg1 x ⟨none, init⟩ b0 hf
      obtain ⟨ih1, ih2⟩ := ih b0
      refine ⟨fun b hb => ?_, fun hb => ?_⟩
      · rw [List.forIn_cons, hj]
        simp only [pure_bind]
        exact ih1 b (by simpa [hf] using hb)
      · rw [List.forIn_cons, hj]
        simp only [pure_bind]
        exact ih2 (by simpa [hf] using hb)


abbrev ESt (p : Spec.Params) :=
  MProd (Option (Option (Vector (Vector Poly p.ℓ) p.k))) (Vector (Vector Poly p.ℓ) p.k)

/-- The seed `ρ ‖ s ‖ r` of entry `(r, s)`. -/
def pSeed (ρ : List UInt8) (r s : Nat) : List UInt8 := ρ ++ IntegerToBytes s 1 ++ IntegerToBytes r 1

def innerF (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r : Nat) (A : Vector (Vector Poly p.ℓ) p.k)
    (s : Nat) : Option (Vector (Vector Poly p.ℓ) p.k) :=
  match Spec.RejNTTPoly fuel (pSeed ρ r s) with
  | some a => some (A.set! r (A[r]!.set! s a))
  | none => none

def outerF (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k) (r : Nat) :
    Option (Vector (Vector Poly p.ℓ) p.k) :=
  (List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A

def eIn (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r s : Nat) (st : ESt p) : Id (ForInStep (ESt p)) :=
  match Spec.RejNTTPoly fuel (pSeed ρ r s) with
  | some a => pure (ForInStep.yield ⟨none, st.snd.set! r (st.snd[r]!.set! s a)⟩)
  | _ => pure (ForInStep.done ⟨some none, st.snd⟩)

def eOut (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r : Nat) (st : ESt p) : Id (ForInStep (ESt p)) := do
  let r' ← forIn (m := Id) (List.range' 0 p.ℓ) (⟨none, st.snd⟩ : ESt p) (eIn p fuel ρ r)
  match r'.fst with
  | none => pure (ForInStep.yield ⟨none, r'.snd⟩)
  | some a => pure (ForInStep.done ⟨some a, r'.snd⟩)

theorem expandA_unfold (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandA p fuel ρ =
      (let r := forIn (m := Id) (List.range' 0 p.k)
          (⟨none, Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)⟩ : ESt p) (eOut p fuel ρ)
       match r.fst with
       | none => some r.snd
       | some a => a) := by
  unfold Spec.ExpandA
  have hs1 : [:p.k].size = p.k := by simp [Std.Legacy.Range.size]
  have hs2 : [:p.ℓ].size = p.ℓ := by simp [Std.Legacy.Range.size]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs1, hs2]
  rfl

theorem expandA_eq (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandA p fuel ρ =
      (List.range' 0 p.k).foldlM (outerF p fuel ρ) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) := by
  have hin : ∀ r (A : Vector (Vector Poly p.ℓ) p.k),
      (∀ b, (List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A = some b →
        forIn (m := Id) (List.range' 0 p.ℓ) (⟨none, A⟩ : ESt p) (eIn p fuel ρ r) = ⟨none, b⟩) ∧
      ((List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A = none →
        (forIn (m := Id) (List.range' 0 p.ℓ) (⟨none, A⟩ : ESt p) (eIn p fuel ρ r)).fst = some none) := by
    intro r A
    refine forIn_opt (innerF p fuel ρ r) (eIn p fuel ρ r) ?_ ?_ (List.range' 0 p.ℓ) A
    · intro s st b h
      unfold innerF at h
      unfold eIn
      rcases hr : Spec.RejNTTPoly fuel (pSeed ρ r s) with _ | a
      · simp [hr] at h
      · simp only [hr, Option.some.injEq] at h
        simp only [hr, h]
    · intro s st h
      unfold innerF at h
      unfold eIn
      rcases hr : Spec.RejNTTPoly fuel (pSeed ρ r s) with _ | a
      · exact ⟨st.snd, by simp only [hr]⟩
      · simp [hr] at h
  rw [expandA_unfold]
  have hout := forIn_opt (γ := Vector (Vector Poly p.ℓ) p.k) (outerF p fuel ρ) (eOut p fuel ρ) ?_ ?_
    (List.range' 0 p.k) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero))
  · rcases hf : (List.range' 0 p.k).foldlM (outerF p fuel ρ) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) with _ | b
    · simp only [hout.2 hf]
    · simp only [hout.1 b hf]
  · intro r st b h
    unfold outerF at h
    unfold eOut
    rw [(hin r st.snd).1 b h]
    rfl
  · intro r st h
    unfold outerF at h
    unfold eOut
    have := (hin r st.snd).2 h
    rcases hI : forIn (m := Id) (List.range' 0 p.ℓ) (⟨none, st.snd⟩ : ESt p) (eIn p fuel ρ r) with ⟨f1, s1⟩
    rw [hI] at this
    simp only at this
    subst this
    exact ⟨s1, rfl⟩

theorem foldlM_isSome {α β : Type} (f : α → β → Option α) (l : List β) (A : α)
    (h : ∀ x ∈ l, ∀ B, (f B x).isSome = true) : (l.foldlM f A).isSome = true := by
  induction l generalizing A with
  | nil => simp
  | cons x l ih =>
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp (h x (List.mem_cons_self) A)
    rw [List.foldlM_cons, hB]
    exact ih B (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- `ExpandA` succeeds as soon as each of its `k · ℓ` calls to `RejNTTPoly` does. -/
theorem expandA_isSome (p : Spec.Params) (fuel : Nat) (ρ : List UInt8)
    (h : ∀ r, r < p.k → ∀ s, s < p.ℓ → (Spec.RejNTTPoly fuel (pSeed ρ r s)).isSome = true) :
    (Spec.ExpandA p fuel ρ).isSome = true := by
  rw [expandA_eq]
  apply foldlM_isSome
  intro r hr A
  have hr' : r < p.k := by simpa using hr
  unfold outerF
  apply foldlM_isSome
  intro s hs B
  have hs' : s < p.ℓ := by simpa using hs
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h r hr' s hs')
  unfold innerF
  rw [ha]
  rfl

/-! ## Rust side of ExpandA -/

theorem ReprMat.set' {K L : Usize} {k ℓ : Nat} {a : Array (Array (Array U32 256#usize) L) K}
    {m : Vector (Vector Poly ℓ) k} (h : ReprMat a m) (r : Usize) (row : Array (Array U32 256#usize) L)
    (v : Vector Poly ℓ) (hrow : ReprVec row v) (_hr : r.val < k) :
    ReprMat (a.set r row) (m.set! r.val v) := by
  refine ⟨h.len, fun j hj => ?_⟩
  have hlt : j < a.val.length := by have := a.property; have := h.len; omega
  rw [set!_eq', Vector.getElem_setIfInBounds hj]
  simp only [Array.set_val_eq]
  by_cases hij : r.val = j
  · subst hij; simpa using hrow
  · simpa [hij, List.getElem_set] using h.elt j hj

theorem ReprMat_repeat_zero (K L : Usize) (k ℓ : Nat) (hK : K.val = k) (hL : L.val = ℓ) :
    ReprMat (Array.repeat K (Array.repeat L (Array.repeat 256#usize 0#u32)))
      (Vector.replicate k (Vector.replicate ℓ Poly.zero)) := by
  refine ⟨hK, fun i hi => ?_⟩
  simp only [Array.repeat_val, List.getElem_replicate, Vector.getElem_replicate]
  exact ReprVec_repeat_zero L ℓ hL

theorem prefix_foldlM {α : Type} (f : α → Nat → Option α) (A X : α) (n m : Nat)
    (h : (List.range' 0 n).foldlM f A = some X) (hmn : m ≤ n) :
    ∃ Y, (List.range' 0 m).foldlM f A = some Y := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hr : List.range' 0 m ++ List.range' (0 + m) e = List.range' 0 (m + e) := List.range'_append_1
  rw [← hr, zero_add] at h
  rw [List.foldlM_append] at h
  cases hm : (List.range' 0 m).foldlM f A with
  | none => simp [hm] at h
  | some Y => exact ⟨Y, rfl⟩

theorem step_foldlM {α : Type} (f : α → Nat → Option α) (A X B : α) (n s : Nat) (hs : s < n)
    (h : (List.range' 0 n).foldlM f A = some X) (hB : (List.range' 0 s).foldlM f A = some B) :
    ∃ B', f B s = some B' ∧ (List.range' 0 (s + 1)).foldlM f A = some B' := by
  obtain ⟨Y, hY⟩ := prefix_foldlM f A X n (s + 1) h hs
  have e : (List.range' 0 (s + 1)).foldlM f A = f B s := by
    rw [List.range'_concat, List.foldlM_append, hB]; simp
  rw [e] at hY
  refine ⟨Y, hY, ?_⟩
  rw [e]; exact hY


theorem set_take_replicate (l : List UInt8) (b : Nat) (hb : b < l.length) (m : Nat) (hm : 0 < m) (v : UInt8)
    (hv : l[b]? = some v) :
    (l.take b ++ List.replicate m 0).set b v = l.take (b + 1) ++ List.replicate (m - 1) 0 := by
  have hlen : (l.take b).length = b := by simp; omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.set_append_right _ _ (by omega), hlen, Nat.sub_self, List.take_add_one, hv]
  simp [List.replicate_succ]

@[step]
theorem seed_loop_spec (rho : Array U8 32#usize) (seed : Array U8 34#usize) (b : Usize) (hb : b.val ≤ 32)
    (h : bytesA seed = (bytesA rho).take b.val ++ List.replicate (34 - b.val) 0) :
    sampling.expand_a_loop0_loop0_loop0 rho seed b ⦃ x => bytesA x = bytesA rho ++ [0, 0] ⦄ := by
  unfold sampling.expand_a_loop0_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 34#usize × Usize) => 32 - p.2.val)
    (fun p => p.2.val ≤ 32 ∧ bytesA p.1 = (bytesA rho).take p.2.val ++ List.replicate (34 - p.2.val) 0)
  · rintro ⟨sd, n⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.expand_a_loop0_loop0_loop0.body]
    split
    · rename_i hi
      have hi' : n.val < 32 := by scalar_tac
      step*
      subst i_post2
      refine ⟨by omega, ?_, by omega⟩
      have hv : (bytesA rho)[n.val]? = some (UInt8.ofNat (rho.val[n.val]'i).val) := by
        rw [List.getElem?_eq_getElem (by simp [bytesA, rho.property]; omega)]
        simp [bytesA]
      have := set_take_replicate (bytesA rho) n.val (by simp [bytesA, rho.property]; omega) (34 - n.val)
        (by omega) _ hv
      rw [a_post, bytesA_set, h2, this, b1_post, show 34 - (n.val + 1) = 34 - n.val - 1 by omega]
    · rename_i hi
      have : n.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      rw [h2, this]
      simp [List.take_of_length_le]
  · exact ⟨hb, h⟩


theorem inner_body_spec (sp : Spec.Params) (fuel : Nat) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (r : Usize) (hr : r.val < sp.k)
    (A Af : Vector (Vector Poly sp.ℓ) sp.k) (hall : outerF sp fuel (bytesA rho) A r.val = some Af)
    (a : Array (Array (Array U32 256#usize) L) K) (s : Usize) (hs : s.val ≤ sp.ℓ)
    (B : Vector (Vector Poly sp.ℓ) sp.k) (hB : (List.range' 0 s.val).foldlM (innerF sp fuel (bytesA rho) r.val) A = some B)
    (ha : ReprMat a B) :
    sampling.expand_a_loop0_loop0.body rho r a s ⦃ x =>
      match x with
      | .done y => ReprMat y Af
      | .cont (a', s') => s'.val ≤ sp.ℓ ∧ ∃ B', (List.range' 0 s'.val).foldlM (innerF sp fuel (bytesA rho) r.val) A = some B' ∧
          ReprMat a' B' ∧ L.val - s'.val < L.val - s.val ⦄ := by
  unfold sampling.expand_a_loop0_loop0.body
  split
  · rename_i hlt
    have hs' : s.val < sp.ℓ := by have : s.val < L.val := hlt; omega
    have hseed0 : bytesA (Array.repeat 34#usize 0#u8) = (bytesA rho).take (0#usize).val ++ List.replicate (34 - (0#usize).val) 0 := by
      simp [bytesA_repeat_zero]
    step*
    have hl : (bytesA rho).length = 32 := by simp
    have hseed3 : bytesA seed3 = pSeed (bytesA rho) r.val s.val := by
      rw [seed3_post, bytesA_set, seed2_post, bytesA_set, seed1_post, i_post, i1_post]
      unfold pSeed
      rw [integerToBytes_one, integerToBytes_one,
        List.set_append_right _ _ (by simp [hl]), List.set_append_right _ _ (by simp [hl])]
      simp [hl, UScalar.cast_val_eq, List.set]
    obtain ⟨B', hf, hB'⟩ := step_foldlM (innerF sp fuel (bytesA rho) r.val) A Af B sp.ℓ s.val hs' hall hB
    unfold innerF at hf
    rcases hrej : Spec.RejNTTPoly fuel (pSeed (bytesA rho) r.val s.val) with _ | a'
    · simp [hrej] at hf
    · simp only [hrej, Option.some.injEq] at hf
      apply WP.spec_bind (rej_ntt_poly_spec_aux seed3 a' fuel (by rw [hseed3]; exact hrej))
      intro a1 ha1
      step*
      have hrk : r.val < sp.k := hr
      have hrow : ReprVec a2 B[r.val] := by
        rw [a2_post2]; exact ha.elt r.val hrk
      have hrow' : ReprVec a3 (B[r.val]!.set! s.val a') := by
        rw [a3_post, getElem!_pos B r.val (by simpa using hrk)]
        exact ReprVec.set hrow s a1 a' ha1 hs'
      refine ⟨by omega, B', by rw [s1_post]; exact hB', ?_, by omega⟩
      rw [a2_post3, ← hf]
      exact ReprMat.set' ha r a3 _ hrow' hrk
  · rename_i hlt
    have hs' : s.val = sp.ℓ := by have : ¬ s.val < L.val := hlt; omega
    simp only [WP.spec_ok]
    rw [hs'] at hB
    unfold outerF at hall
    rw [hB] at hall
    cases hall
    exact ha

theorem inner_loop_spec (sp : Spec.Params) (fuel : Nat) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (r : Usize) (hr : r.val < sp.k)
    (A Af : Vector (Vector Poly sp.ℓ) sp.k) (hall : outerF sp fuel (bytesA rho) A r.val = some Af)
    (a : Array (Array (Array U32 256#usize) L) K) (ha : ReprMat a A) :
    sampling.expand_a_loop0_loop0 rho a r 0#usize ⦃ x => ReprMat x Af ⦄ := by
  unfold sampling.expand_a_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array (Array U32 256#usize) L) K × Usize) => L.val - p.2.val)
    (fun p => p.2.val ≤ sp.ℓ ∧ ∃ B, (List.range' 0 p.2.val).foldlM (innerF sp fuel (bytesA rho) r.val) A = some B ∧
      ReprMat p.1 B)
  · rintro ⟨a', s'⟩ ⟨h1, B, hB, hR⟩
    dsimp only at h1 hB hR
    apply WP.spec_mono (inner_body_spec sp fuel hK hL rho r hr A Af hall a' s' h1 B hB hR)
    rintro (⟨a'', s''⟩ | y) h
    · obtain ⟨h1, B', hB', hR', hlt⟩ := h
      exact ⟨⟨h1, B', hB', hR'⟩, hlt⟩
    · exact h
  · exact ⟨by simp, A, by simp, ha⟩

theorem outer_body_spec (sp : Spec.Params) (fuel : Nat) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (Afin : Vector (Vector Poly sp.ℓ) sp.k)
    (hExp : (List.range' 0 sp.k).foldlM (outerF sp fuel (bytesA rho)) (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some Afin)
    (a : Array (Array (Array U32 256#usize) L) K) (r : Usize) (hr : r.val ≤ sp.k)
    (B : Vector (Vector Poly sp.ℓ) sp.k)
    (hB : (List.range' 0 r.val).foldlM (outerF sp fuel (bytesA rho)) (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some B)
    (ha : ReprMat a B) :
    sampling.expand_a_loop0.body rho a r ⦃ x =>
      match x with
      | .done y => ReprMat y Afin
      | .cont (a', r') => r'.val ≤ sp.k ∧ ∃ B', (List.range' 0 r'.val).foldlM (outerF sp fuel (bytesA rho)) (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some B' ∧
          ReprMat a' B' ∧ K.val - r'.val < K.val - r.val ⦄ := by
  unfold sampling.expand_a_loop0.body
  split
  · rename_i hlt
    have hr' : r.val < sp.k := by have : r.val < K.val := hlt; omega
    obtain ⟨B', hf, hB'⟩ := step_foldlM (outerF sp fuel (bytesA rho)) _ Afin B sp.k r.val hr' hExp hB
    apply WP.spec_bind (inner_loop_spec sp fuel hK hL rho r hr' B B' hf a ha)
    intro a1 ha1
    step*
  · rename_i hlt
    have hr' : r.val = sp.k := by have : ¬ r.val < K.val := hlt; omega
    simp only [WP.spec_ok]
    rw [hr'] at hB
    rw [hB] at hExp
    cases hExp
    exact ha

theorem expand_a_loop0_spec (sp : Spec.Params) (fuel : Nat) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (Afin : Vector (Vector Poly sp.ℓ) sp.k)
    (hExp : (List.range' 0 sp.k).foldlM (outerF sp fuel (bytesA rho)) (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some Afin)
    (a : Array (Array (Array U32 256#usize) L) K)
    (ha : ReprMat a (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero))) :
    sampling.expand_a_loop0 rho a 0#usize ⦃ x => ReprMat x Afin ⦄ := by
  unfold sampling.expand_a_loop0
  apply loop.spec_decr_nat
    (fun (p : Array (Array (Array U32 256#usize) L) K × Usize) => K.val - p.2.val)
    (fun p => p.2.val ≤ sp.k ∧ ∃ B, (List.range' 0 p.2.val).foldlM (outerF sp fuel (bytesA rho))
      (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some B ∧ ReprMat p.1 B)
  · rintro ⟨a', r'⟩ ⟨h1, B, hB, hR⟩
    dsimp only at h1 hB hR
    apply WP.spec_mono (outer_body_spec sp fuel hK hL rho Afin hExp a' r' h1 B hB hR)
    rintro (⟨a'', s''⟩ | y) h
    · obtain ⟨h1, B', hB', hR', hlt⟩ := h
      exact ⟨⟨h1, B', hB', hR'⟩, hlt⟩
    · exact h
  · exact ⟨by simp, _, by simp, ha⟩

/-- **ExpandA** (Algorithm 32). -/
theorem expand_a_spec_aux (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (A : Vector (Vector Poly sp.ℓ) sp.k) (fuel : Nat)
    (hs : Spec.ExpandA sp fuel (bytesA rho) = some A) :
    sampling.expand_a K L rho ⦃ r => ReprMat r A ⦄ := by
  rw [expandA_eq] at hs
  unfold sampling.expand_a
  simp only []
  exact expand_a_loop0_spec sp fuel hK hL rho A hs _ (ReprMat_repeat_zero K L sp.k sp.ℓ hK hL)


end SampleA

/-- **RejNTTPoly** (Algorithm 30): if the spec returns `some a` at some fuel, the Rust function returns the
array representing `a` (in particular it terminates). -/
theorem rej_ntt_poly_spec (ρ : Array U8 34#usize) (a : Spec.Poly) (fuel : Nat)
    (hs : Spec.RejNTTPoly fuel (bytesA ρ) = some a) :
    sampling.rej_ntt_poly ρ ⦃ r => Repr r a ⦄ :=
  SampleA.rej_ntt_poly_spec_aux ρ a fuel hs

/-- **ExpandA** (Algorithm 32), with the const generics tied to the spec parameters. -/
theorem expand_a_spec (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (ρ : Array U8 32#usize) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (fuel : Nat)
    (hs : Spec.ExpandA sp fuel (bytesA ρ) = some A) :
    sampling.expand_a K L ρ ⦃ r => ReprMat r A ⦄ :=
  SampleA.expand_a_spec_aux sp K L hK hL ρ A fuel hs

/-- `expand_a_spec` with the `Params.Valid` premise used elsewhere. -/
theorem expand_a_spec_valid {ip : params.Params} {K L : Usize} {sp : Spec.Params} (hp : Params.Valid ip K L sp)
    (ρ : Array U8 32#usize) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (fuel : Nat)
    (hs : Spec.ExpandA sp fuel (bytesA ρ) = some A) :
    sampling.expand_a K L ρ ⦃ r => ReprMat r A ⦄ :=
  expand_a_spec sp K L hp.K_eq hp.L_eq ρ A fuel hs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Satisfiability of the `RejNTTPoly` premise: the all-zero seed with fuel 512 succeeds (kernel evaluation of
SHAKE128, about 40 s, 4M heartbeats). -/
theorem rej_ntt_poly_satisfiable : ∃ A, Spec.RejNTTPoly 512 (List.replicate 34 0) = some A := by
  have : (Spec.RejNTTPoly 512 (List.replicate 34 0)).isSome = true := by decide +kernel
  exact Option.isSome_iff_exists.mp this

/-- The premise of `rej_ntt_poly_spec` is satisfiable for the extracted type: a 34-byte array of zeros. -/
theorem rej_ntt_poly_premise_satisfiable :
    ∃ (ρ : Array U8 34#usize) (a : Spec.Poly) (fuel : Nat), Spec.RejNTTPoly fuel (bytesA ρ) = some a := by
  obtain ⟨A, hA⟩ := rej_ntt_poly_satisfiable
  refine ⟨Array.repeat 34#usize 0#u8, A, 512, ?_⟩
  rw [bytesA_repeat_zero]
  exact hA

end Proofs
