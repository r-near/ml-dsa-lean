import Proofs.Coeff
import Proofs.Keccak
import Spec.Sampling

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## A loop rule with a ghost iteration counter -/

theorem loop_spec_ghost {α β : Type} (B : Nat) (Inv : Nat → α → Prop) (post : β → Prop)
    (body : α → RustM (ControlFlow α β)) (x : α)
    (hBody : ∀ k x, k ≤ B → Inv k x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => k < B ∧ Inv (k + 1) x' ⦄)
    (h0 : Inv 0 x) : loop body x ⦃ post ⦄ := by
  classical
  let S : α → Set Nat := fun x => {m | ∃ k, k ≤ B ∧ Inv k x ∧ m = B - k}
  apply loop.spec (fun x => sInf (S x)) (fun x => (S x).Nonempty) post body x
  · intro x hx
    have hmem := Nat.sInf_mem hx
    obtain ⟨k, hk, hI, hm⟩ := hmem
    apply WP.spec_mono (hBody k x hk hI)
    intro r hr
    cases r with
    | done y => exact hr
    | cont x' =>
      obtain ⟨hlt, hI'⟩ := hr
      have hne : (S x').Nonempty := ⟨B - (k + 1), k + 1, by omega, hI', rfl⟩
      refine ⟨hne, ?_⟩
      have := Nat.sInf_le (s := S x') (m := B - (k + 1)) ⟨k + 1, by omega, hI', rfl⟩
      show sInf (S x') < sInf (S x)
      rw [hm]
      omega
  · exact ⟨B - 0, 0, Nat.zero_le _, h0, rfl⟩


/-! ## The pure model of RejBoundedPoly -/

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

theorem rbRun_snoc (η : Nat) (stream : List UInt8) (n : Nat) :
    ∀ (st : RPoly × Nat) (s : Nat), rbRun η stream st s (n + 1) =
      (if (rbRun η stream st s n).2 ≥ 256 then rbRun η stream st s n
       else rbStep η (rbRun η stream st s n) (stream[s + n]!).toNat) := by
  induction n with
  | zero => intro st s; simp [rbRun]
  | succ n ih =>
    intro st s
    by_cases h : st.2 ≥ 256
    · have h' : 256 ≤ st.2 := h
      simp only [rbRun_stop η stream st h, ge_iff_le, h', if_true]
    · rw [rbRun, if_neg h, ih]
      conv_rhs => rw [rbRun, if_neg h]
      have : s + 1 + n = s + (n + 1) := by omega
      rw [this]

/-- The loop of Algorithm 31 as a `forIn` body over the model. -/
abbrev RBState := MProd (Option (Option RPoly)) (MProd RPoly (MProd Ctx Nat))

def rbBody (p : Params) (_ : Nat) (r : RBState) : Id (ForInStep RBState) :=
  if r.snd.snd.snd ≥ 256 then pure (ForInStep.done ⟨none, r.snd.fst, r.snd.snd.fst, r.snd.snd.snd⟩)
  else match H.Squeeze r.snd.snd.fst 1 with
    | some (ctx', s) =>
      let t := rbStep p.η (r.snd.fst, r.snd.snd.snd) (s[0]!).toNat
      pure (ForInStep.yield ⟨none, t.1, ctx', t.2⟩)
    | none => pure (ForInStep.done ⟨some none, r.snd.fst, r.snd.snd.fst, r.snd.snd.snd⟩)

theorem RejBoundedPoly_eq_forIn (p : Params) (fuel : Nat) (ρ : List UInt8) :
    RejBoundedPoly p fuel ρ =
      (let r := (forIn (m := Id) [:fuel] (⟨none, Vector.replicate 256 0, H.InitAbsorb fuel ρ, 0⟩ : RBState)
          (rbBody p)).run
       match r.fst with
       | none => if r.snd.snd.snd < 256 then none else some r.snd.fst
       | some a => a) := by
  unfold RejBoundedPoly
  have key : ∀ (init : RBState) (F : Nat → RBState → Id (ForInStep RBState)),
      (∀ x r, F x r = rbBody p x r) → forIn (m := Id) [:fuel] init F = forIn (m := Id) [:fuel] init (rbBody p) := by
    intro init F h
    rw [show F = rbBody p from funext fun x => funext (h x)]
  dsimp only
  generalize hR : forIn (m := Id) [:fuel]
    (⟨none, Vector.replicate 256 0, H.InitAbsorb fuel ρ, 0⟩ : RBState) (rbBody p) = R
  rw [key _ _ ?side]
  case side =>
    intro x r
    obtain ⟨b, a, ctx, j⟩ := r
    simp only [rbBody, rbStep]
    by_cases hj : j ≥ 256
    · simp [hj]
    · simp only [hj, if_false, pure_bind]
      rcases hs : H.Squeeze ctx 1 with _ | ⟨ctx', s⟩
      · simp
      · simp only
        rcases h0 : CoeffFromHalfByte p.η (s[0]!.toNat % 16) with _ | v
        · rcases h1 : CoeffFromHalfByte p.η (s[0]!.toNat / 16) with _ | w <;> simp;
            (split_ifs <;> simp_all)
        · rcases h1 : CoeffFromHalfByte p.η (s[0]!.toNat / 16) with _ | w <;> simp;
            (split_ifs <;> simp_all)
  rw [hR]
  rcases R with ⟨b, a, ctx, j⟩
  rcases b with _ | _ | a' <;> rfl


theorem drop_take_one_get (l : List UInt8) (s : Nat) (h : s < l.length) :
    ((l.drop s).take 1)[0]! = l[s]! := by
  rw [List.drop_eq_getElem_cons h]
  simp [getElem!_pos, h]

theorem stream_length (fuel : Nat) (ρ : List UInt8) : (H.InitAbsorb fuel ρ).stream.length = fuel := by
  simp [H.InitAbsorb, H, SHAKE256_length]

theorem forIn_rbBody (p : Params) (fuel : Nat) (ρ : List UInt8) (n : Nat) :
    ∀ (s : Nat) (a : RPoly) (j : Nat), s + n ≤ fuel → ∃ ctx' : Ctx,
      forIn (m := Id) (List.range' s n) (⟨none, a, ⟨(H.InitAbsorb fuel ρ).stream, s⟩, j⟩ : RBState) (rbBody p)
        = (⟨none, (rbRun p.η (H.InitAbsorb fuel ρ).stream (a, j) s n).1, ctx',
            (rbRun p.η (H.InitAbsorb fuel ρ).stream (a, j) s n).2⟩ : RBState) := by
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
      have hb : rbBody p s ⟨none, a, ⟨(H.InitAbsorb fuel ρ).stream, s⟩, j⟩ = pure (ForInStep.yield
          ⟨none, (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).1,
            ⟨(H.InitAbsorb fuel ρ).stream, s + 1⟩,
            (rbStep p.η (a, j) ((H.InitAbsorb fuel ρ).stream[s]!).toNat).2⟩) := by
        simp only [rbBody]
        rw [if_neg hj, hsq]
        simp only [drop_take_one_get _ _ hlen]
      rw [hb, pure_bind]
      dsimp only
      rw [h]
      simp only [rbRun, if_neg hj]

theorem RejBoundedPoly_eq (p : Params) (fuel : Nat) (ρ : List UInt8) :
    RejBoundedPoly p fuel ρ =
      (if (rbRun p.η (H ρ fuel) (Vector.replicate 256 0, 0) 0 fuel).2 < 256 then none
       else some (rbRun p.η (H ρ fuel) (Vector.replicate 256 0, 0) 0 fuel).1) := by
  rw [RejBoundedPoly_eq_forIn]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  obtain ⟨ctx', h⟩ := forIn_rbBody p fuel ρ fuel 0 (Vector.replicate 256 0) 0 (by omega)
  have e : (⟨none, Vector.replicate 256 0, H.InitAbsorb fuel ρ, 0⟩ : RBState) =
      ⟨none, Vector.replicate 256 0, ⟨(H.InitAbsorb fuel ρ).stream, 0⟩, 0⟩ := rfl
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [e, h]
  rfl


/-! ## Ranges -/

/-- Every coefficient is at most `η` in absolute value. -/
def Bounded (η : Nat) (a : RPoly) : Prop := ∀ (i : Nat) (hi : i < 256), (a[i]'hi).natAbs ≤ η

theorem Bounded.set {η : Nat} {a : RPoly} (h : Bounded η a) (k : Nat) (v : Int) (hv : v.natAbs ≤ η) :
    Bounded η (a.set! k v) := by
  intro i hi
  rw [set!_eq', Vector.getElem_setIfInBounds hi]
  split
  · exact hv
  · exact h i hi

theorem Bounded.zero (η : Nat) : Bounded η (Vector.replicate 256 0) := by
  intro i hi
  simp

theorem coeffHalf_bound (η b : Nat) (v : Int) (h : CoeffFromHalfByte η b = some v) : v.natAbs ≤ η := by
  unfold CoeffFromHalfByte at h
  split_ifs at h with h1 h2
  · obtain ⟨rfl, hb⟩ := h1
    simp only [Option.some.injEq] at h
    subst h
    omega
  · obtain ⟨rfl, hb⟩ := h2
    simp only [Option.some.injEq] at h
    subst h
    omega

theorem rbStep_bounded (η : Nat) (st : RPoly × Nat) (z : Nat) (h : Bounded η st.1) :
    Bounded η (rbStep η st z).1 := by
  unfold rbStep
  rcases h0 : CoeffFromHalfByte η (z % 16) with _ | v <;> rcases h1 : CoeffFromHalfByte η (z / 16) with _ | w <;>
    simp only
  · exact h
  · split
    · exact Bounded.set h _ _ (coeffHalf_bound _ _ _ h1)
    · exact h
  · exact Bounded.set h _ _ (coeffHalf_bound _ _ _ h0)
  · split
    · exact Bounded.set (Bounded.set h _ _ (coeffHalf_bound _ _ _ h0)) _ _ (coeffHalf_bound _ _ _ h1)
    · exact Bounded.set h _ _ (coeffHalf_bound _ _ _ h0)

theorem rbRun_bounded (η : Nat) (stream : List UInt8) (n : Nat) :
    ∀ (st : RPoly × Nat) (s : Nat), Bounded η st.1 → Bounded η (rbRun η stream st s n).1 := by
  induction n with
  | zero => intro st s h; exact h
  | succ n ih =>
    intro st s h
    simp only [rbRun]
    split
    · exact h
    · exact ih _ _ (rbStep_bounded η st _ h)

theorem rbRun_add (η : Nat) (stream : List UInt8) (k : Nat) :
    ∀ (st : RPoly × Nat) (s m : Nat), rbRun η stream st s (k + m) =
      rbRun η stream (rbRun η stream st s k) (s + k) m := by
  induction k with
  | zero => intro st s m; simp [rbRun]
  | succ k ih =>
    intro st s m
    by_cases h : st.2 ≥ 256
    · rw [rbRun_stop η stream st h, rbRun_stop η stream st h]
      rw [rbRun_stop η stream st h]
    · have e : k + 1 + m = (k + m) + 1 := by omega
      rw [e]
      simp only [rbRun, if_neg h]
      rw [ih]
      have : s + 1 + k = s + (k + 1) := by omega
      rw [this]

/-- The model state after `k` iterations. -/
def rbS (η fuel : Nat) (ρ : List UInt8) (k : Nat) : RPoly × Nat :=
  rbRun η (H ρ fuel) (Vector.replicate 256 0, 0) 0 k

theorem rbS_succ (η fuel : Nat) (ρ : List UInt8) (k : Nat) :
    rbS η fuel ρ (k + 1) =
      (if (rbS η fuel ρ k).2 ≥ 256 then rbS η fuel ρ k
       else rbStep η (rbS η fuel ρ k) ((H ρ fuel)[k]!).toNat) := by
  unfold rbS
  rw [rbRun_snoc, Nat.zero_add]

theorem rbS_stable (η fuel : Nat) (ρ : List UInt8) (k m : Nat) (h : (rbS η fuel ρ k).2 ≥ 256) :
    rbS η fuel ρ (k + m) = rbS η fuel ρ k := by
  unfold rbS at *
  rw [rbRun_add, rbRun_stop _ _ _ h]

theorem rbS_bounded (η fuel : Nat) (ρ : List UInt8) (k : Nat) : Bounded η (rbS η fuel ρ k).1 :=
  rbRun_bounded η _ k _ 0 (Bounded.zero η)

theorem RejBoundedPoly_some (p : Params) (fuel : Nat) (ρ : List UInt8) (a : RPoly)
    (h : RejBoundedPoly p fuel ρ = some a) :
    a = (rbS p.η fuel ρ fuel).1 ∧ 256 ≤ (rbS p.η fuel ρ fuel).2 := by
  rw [RejBoundedPoly_eq] at h
  change (if (rbS p.η fuel ρ fuel).2 < 256 then none else some (rbS p.η fuel ρ fuel).1) = some a at h
  split at h
  · exact absurd h (by simp)
  · exact ⟨(Option.some.inj h).symm, by omega⟩

/-- The range of a successful `RejBoundedPoly`. -/
theorem RejBoundedPoly_bounded (p : Params) (fuel : Nat) (ρ : List UInt8) (a : RPoly)
    (h : RejBoundedPoly p fuel ρ = some a) : Bounded p.η a := by
  obtain ⟨rfl, -⟩ := RejBoundedPoly_some p fuel ρ a h
  exact rbS_bounded _ _ _ _


/-! ## The Rust loop -/

theorem rbStep_cases (η : Nat) (st : RPoly × Nat) (z : Nat) :
    (CoeffFromHalfByte η (z % 16) = none → CoeffFromHalfByte η (z / 16) = none → rbStep η st z = st) ∧
    (∀ c, CoeffFromHalfByte η (z % 16) = none → CoeffFromHalfByte η (z / 16) = some c →
      rbStep η st z = if st.2 < 256 then (st.1.set! st.2 c, st.2 + 1) else st) ∧
    (∀ c, CoeffFromHalfByte η (z % 16) = some c → CoeffFromHalfByte η (z / 16) = none →
      rbStep η st z = (st.1.set! st.2 c, st.2 + 1)) ∧
    (∀ c d, CoeffFromHalfByte η (z % 16) = some c → CoeffFromHalfByte η (z / 16) = some d →
      rbStep η st z = if st.2 + 1 < 256 then ((st.1.set! st.2 c).set! (st.2 + 1) d, st.2 + 1 + 1)
        else (st.1.set! st.2 c, st.2 + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0 h1; simp [rbStep, h0, h1]
  · intro c h0 h1; simp [rbStep, h0, h1]
  · intro c h0 h1; simp [rbStep, h0, h1]
  · intro c d h0 h1; simp [rbStep, h0, h1]

theorem optCoeff_none {o : Option Int} (h : OptCoeff none o) : o = none := by
  cases o <;> simp_all [OptCoeff]

theorem optCoeff_some {x : U32} {o : Option Int} (h : OptCoeff (some x) o) : ∃ c, o = some c ∧ CoeffRel x c := by
  cases o with
  | none => exact h.elim
  | some c => exact ⟨c, rfl, h⟩

theorem byte_of (tb : Array U8 1#usize) (s1 : Slice U8) (x : U8) (stream : List UInt8) (k : Nat)
    (hx : x = tb.val[0]) (ht : tb = Array.from_slice (Array.repeat 1#usize 0#u8) s1)
    (hb : bytes s1 = (stream.drop k).take 1) (hk : k < stream.length) :
    x.val = (stream[k]!).toNat := by
  have hl : s1.val.length = 1 := by
    have := congrArg List.length hb
    simp [bytes] at this
    omega
  have h1 : bytesA tb = bytes s1 := by
    rw [ht]; exact bytesA_from_slice _ _ (by simpa using hl)
  have h2 : UInt8.ofNat x.val = ((stream.drop k).take 1)[0]! := by
    have h3 : (bytesA tb)[0]! = UInt8.ofNat x.val := by
      subst hx
      simp [bytesA]
    rw [← h3, h1, hb]
  rw [drop_take_one_get _ _ hk] at h2
  have := toNat_ofNat_val x
  rw [h2] at this
  exact this.symm

theorem rej_bounded_poly_loop_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : List UInt8) (fuel : Nat)
    (hfull : 256 ≤ (rbS sp.η fuel ρ fuel).2) (a0 : Array U32 256#usize) (ctx0 : keccak.Shake)
    (ha0 : ReprInt a0 (Vector.replicate 256 0)) (hc0 : ShakeSqz ctx0 136 ρ 0) :
    sampling.rej_bounded_poly_loop ip a0 ctx0 0#usize ⦃ r => ReprInt r (rbS sp.η fuel ρ fuel).1 ⦄ := by
  unfold sampling.rej_bounded_poly_loop
  apply loop_spec_ghost fuel
    (fun k (x : Array U32 256#usize × keccak.Shake × Usize) =>
      ShakeSqz x.2.1 136 ρ k ∧ ReprInt x.1 (rbS sp.η fuel ρ k).1 ∧ x.2.2.val = (rbS sp.η fuel ρ k).2)
  · rintro k ⟨a, ctx, j⟩ hk ⟨hS, hR, hj⟩
    dsimp only at hS hR hj
    simp only [sampling.rej_bounded_poly_loop.body]
    split
    · rename_i hj256
      have hj256' : j.val < 256 := by scalar_tac
      have hkf : k < fuel := by
        by_contra hcon
        have : k = fuel := by omega
        subst this
        omega
      have hlen : k < (H ρ fuel).length := by simp [H, SHAKE256_length]; exact hkf
      step*
      have hs1 : (↑s : List U8).length = 1 := by simp [s_post1]
      rw [hs1] at ctx1_post1 ctx1_post2
      have hw := sponge_window 136 (by omega) ρ k 1 fuel (by omega)
      have hb : bytes s1 = ((H ρ fuel).drop k).take 1 := by rw [ctx1_post2]; exact hw
      have hxv := byte_of _ s1 _ (H ρ fuel) k i_post2 (by rw [s_post2]) hb hlen
      have hi1 : i1.val = (H ρ fuel)[k]!.toNat % 16 := by
        rw [i1_post1, UScalar.val_and, hxv]
        show _ &&& 15 = _
        have := Nat.and_two_pow_sub_one_eq_mod (H ρ fuel)[k]!.toNat 4
        simpa using this
      have hi2 : i2.val = (H ρ fuel)[k]!.toNat / 16 := by
        rw [i2_post1, hxv, Nat.shiftRight_eq_div_pow]
      rw [hi1] at z0_post
      rw [hi2] at z1_post
      have hnext := rbS_succ sp.η fuel ρ k
      rw [if_neg (by omega)] at hnext
      obtain ⟨c1, c2, c3, c4⟩ := rbStep_cases sp.η (rbS sp.η fuel ρ k) (H ρ fuel)[k]!.toNat
      rcases z0 with _ | x0 <;> rcases z1 with _ | y0
      · have e0 := optCoeff_none z0_post
        have e1 := optCoeff_none z1_post
        have hn : rbS sp.η fuel ρ (k + 1) = rbS sp.η fuel ρ k := by rw [hnext]; exact c1 e0 e1
        refine (WP.spec_ok _).mpr ?_
        show k < fuel ∧ _
        rw [hn]
        exact ⟨hkf, ctx1_post1, hR, hj⟩
      · have e0 := optCoeff_none z0_post
        obtain ⟨d, e1, hrel⟩ := optCoeff_some z1_post
        have hn : rbS sp.η fuel ρ (k + 1) =
            (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 d, (rbS sp.η fuel ρ k).2 + 1) := by
          rw [hnext, c2 d e0 e1, if_pos (by omega)]
        have hset := ReprInt.set hR j y0 d hj256' hrel.1 hrel.2
        step*
      · obtain ⟨c, e0, hrel⟩ := optCoeff_some z0_post
        have e1 := optCoeff_none z1_post
        have hn : rbS sp.η fuel ρ (k + 1) =
            (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c, (rbS sp.η fuel ρ k).2 + 1) := by
          rw [hnext, c3 c e0 e1]
        have hset := ReprInt.set hR j x0 c hj256' hrel.1 hrel.2
        step*
      · obtain ⟨c, e0, hr0⟩ := optCoeff_some z0_post
        obtain ⟨d, e1, hr1⟩ := optCoeff_some z1_post
        have hset := ReprInt.set hR j x0 c hj256' hr0.1 hr0.2
        have hn4 : rbS sp.η fuel ρ (k + 1) =
            (if (rbS sp.η fuel ρ k).2 + 1 < 256 then
              ((Vector.set! (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c)
                ((rbS sp.η fuel ρ k).2 + 1) d), (rbS sp.η fuel ρ k).2 + 1 + 1)
             else (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c, (rbS sp.η fuel ρ k).2 + 1)) := by
          rw [hnext, c4 c d e0 e1]
        step*
        subst_vars
        all_goals
            (have hxlt : x.val < 256 := by scalar_tac
             have hlt : (rbS sp.η fuel ρ k).2 + 1 < 256 := by omega
             have hset2 := ReprInt.set hset x y0 d hxlt hr1.1 hr1.2
             refine ⟨hkf, ctx1_post1, ?_, ?_⟩
             · rw [hn4, if_pos hlt, ← hj]
               rw [x_post] at hset2
               exact hset2
             · rw [hn4, if_pos hlt, ← hj, j2_post, x_post])
    · rename_i hjn
      have h256 : (rbS sp.η fuel ρ k).2 ≥ 256 := by
        have : 256 ≤ j.val := by scalar_tac
        omega
      have hst := rbS_stable sp.η fuel ρ k (fuel - k) h256
      rw [show k + (fuel - k) = fuel by omega] at hst
      refine (WP.spec_ok _).mpr ?_
      show ReprInt a _
      rw [hst]; exact hR
  · exact ⟨hc0, ha0, rfl⟩


theorem rej_bounded_poly_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : Array U8 66#usize) (a : RPoly)
    (fuel : Nat) (hs : Spec.RejBoundedPoly sp fuel (bytesA ρ) = some a) :
    sampling.rej_bounded_poly ip ρ ⦃ r =>
      ReprInt r a ∧ ∀ (i : Nat) (hi : i < 256), (a[i]'hi).natAbs ≤ sp.η ⦄ := by
  have hb := RejBoundedPoly_bounded sp fuel _ a hs
  obtain ⟨rfl, hfull⟩ := RejBoundedPoly_some sp fuel _ a hs
  unfold sampling.rej_bounded_poly
  step*
  subst s_post
  have hc : ShakeSqz ctx2 136 (bytesA ρ) 0 := by
    rw [List.nil_append, bytes_to_slice] at ctx2_post
    exact ctx2_post
  exact WP.spec_mono (rej_bounded_poly_loop_spec hp hη (bytesA ρ) fuel hfull _ _ reprInt_zero hc)
    (fun r hr => ⟨hr, hb⟩)


/-! ## ExpandS: the spec side -/

theorem ITB_two_s (x : Nat) :
    IntegerToBytes x 2 = [(x % 256).toUInt8, (x / 256 % 256).toUInt8] := by
  unfold IntegerToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ]

abbrev FS (β : Type) (n : Nat) := MProd (Option (Option β)) (Vector RPoly n)

def fillBody {β : Type} {n : Nat} (f : Nat → Option RPoly) (r : Nat) (st : FS β n) :
    Id (ForInStep (FS β n)) :=
  match f r with
  | some a => pure (ForInStep.yield ⟨none, st.snd.set! r a⟩)
  | none => pure (ForInStep.done ⟨some none, st.snd⟩)

theorem fill_forIn {β : Type} {n : Nat} (f : Nat → Option RPoly) (m : Nat) :
    ∀ (s : Nat) (v : Vector RPoly n), ∃ w : Vector RPoly n,
      ((forIn (m := Id) (List.range' s m) (⟨none, v⟩ : FS β n) (fillBody f) = ⟨none, w⟩ ∧
        (∀ i, i < m → ∀ (hi : s + i < n), f (s + i) = some (w[s + i]'hi)) ∧
        (∀ t (ht : t < n), (t < s ∨ s + m ≤ t) → w[t] = v[t])) ∨
       forIn (m := Id) (List.range' s m) (⟨none, v⟩ : FS β n) (fillBody f) = ⟨some none, w⟩) := by
  induction m with
  | zero => intro s v; exact ⟨v, Or.inl ⟨rfl, by intro i hi; omega, fun _ _ _ => rfl⟩⟩
  | succ m ih =>
    intro s v
    cases hf : f s with
    | none =>
      refine ⟨v, Or.inr ?_⟩
      simp [List.range'_succ, List.forIn_cons, fillBody, hf]
      try rfl
    | some a =>
      obtain ⟨w, hw⟩ := ih (s + 1) (v.set! s a)
      have e : forIn (m := Id) (List.range' s (m + 1)) (⟨none, v⟩ : FS β n) (fillBody f) =
          forIn (m := Id) (List.range' (s + 1) m) (⟨none, v.set! s a⟩ : FS β n) (fillBody f) := by
        simp [List.range'_succ, List.forIn_cons, fillBody, hf]
        try rfl
      refine ⟨w, ?_⟩
      rcases hw with ⟨h1, h2, h3⟩ | h1
      · left
        rw [e]
        refine ⟨h1, ?_, ?_⟩
        · intro i hi hlt
          cases i with
          | zero =>
            have := h3 s (by simpa using hlt) (Or.inl (by omega))
            simp only [Nat.add_zero]
            rw [this, hf, set!_eq', Vector.getElem_setIfInBounds (by simpa using hlt)]
            simp
          | succ i =>
            have := h2 i (by omega) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
        · intro t ht hcase
          rw [h3 t ht (by omega), set!_eq', Vector.getElem_setIfInBounds ht]
          rw [if_neg (by omega)]
      · right; rw [e]; exact h1

/-- `ExpandS` as two `fillBody` loops. -/
def expandSModel (p : Params) (fuel : Nat) (ρ : List UInt8) :
    Option (Vector RPoly p.ℓ × Vector RPoly p.k) :=
  let r1 := forIn (m := Id) [:p.ℓ]
    (⟨none, Vector.replicate p.ℓ (Vector.replicate 256 0)⟩ : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.ℓ)
    (fillBody fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2))
  match r1.fst with
  | none =>
    let r2 := forIn (m := Id) [:p.k]
      (⟨none, Vector.replicate p.k (Vector.replicate 256 0)⟩ : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.k)
      (fillBody fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2))
    match r2.fst with
    | none => some (r1.snd, r2.snd)
    | some a => a
  | some a => a

theorem ExpandS_eq (p : Params) (fuel : Nat) (ρ : List UInt8) :
    ExpandS p fuel ρ = expandSModel p fuel ρ := by
  have key : ∀ {n : Nat} (m : Nat) (init : FS (Vector RPoly p.ℓ × Vector RPoly p.k) n)
      (F : Nat → FS (Vector RPoly p.ℓ × Vector RPoly p.k) n → Id (ForInStep (FS (Vector RPoly p.ℓ × Vector RPoly p.k) n)))
      (f : Nat → Option RPoly), (∀ x r, F x r = fillBody f x r) →
      forIn (m := Id) [:m] init F = forIn (m := Id) [:m] init (fillBody f) := by
    intro n m init F f h
    rw [show F = fillBody f from funext fun x => funext (h x)]
  unfold ExpandS expandSModel
  dsimp only
  generalize hA : forIn (m := Id) [:p.ℓ]
    (⟨none, Vector.replicate p.ℓ (Vector.replicate 256 0)⟩ : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.ℓ)
    (fillBody fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) = A
  generalize hB : forIn (m := Id) [:p.k]
    (⟨none, Vector.replicate p.k (Vector.replicate 256 0)⟩ : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.k)
    (fillBody fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) = B
  rw [key p.ℓ _ _ (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) ?s1,
    key p.k _ _ (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) ?s2]
  case s1 =>
    intro x r
    obtain ⟨b, v⟩ := r
    simp only [fillBody]
    rcases h : RejBoundedPoly p fuel (ρ ++ IntegerToBytes x 2) with _ | a <;> simp
  case s2 =>
    intro x r
    obtain ⟨b, v⟩ := r
    simp only [fillBody]
    rcases h : RejBoundedPoly p fuel (ρ ++ IntegerToBytes (x + p.ℓ) 2) with _ | a <;> simp
  rw [hA, hB]
  rcases A with ⟨a1, v1⟩
  rcases B with ⟨b1, v2⟩
  rcases a1 with _ | _ | x <;> rcases b1 with _ | _ | y <;> rfl

theorem ExpandS_some (p : Params) (fuel : Nat) (ρ : List UInt8) (s₁ : Vector RPoly p.ℓ)
    (s₂ : Vector RPoly p.k) (h : ExpandS p fuel ρ = some (s₁, s₂)) :
    (∀ (i : Nat) (hi : i < p.ℓ), RejBoundedPoly p fuel (ρ ++ IntegerToBytes i 2) = some s₁[i]) ∧
    (∀ (i : Nat) (hi : i < p.k), RejBoundedPoly p fuel (ρ ++ IntegerToBytes (i + p.ℓ) 2) = some s₂[i]) := by
  rw [ExpandS_eq] at h
  unfold expandSModel at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one] at h
  obtain ⟨w1, hw1⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0))
  obtain ⟨w2, hw2⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0))
  rcases hw1 with ⟨e1, q1, -⟩ | e1
  · rcases hw2 with ⟨e2, q2, -⟩ | e2
    · rw [e1, e2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun i hi => by simpa using q1 i hi (by simpa using hi),
             fun i hi => by simpa using q2 i hi (by simpa using hi)⟩
    · rw [e1, e2] at h
      simp at h
  · rw [e1] at h
    simp at h


/-- The success counterpart of `fill_forIn`: when `f` succeeds at every index of the range, the loop never exits early. -/
theorem fill_forIn_ok {β : Type} {n : Nat} (f : Nat → Option RPoly) (m : Nat) :
    ∀ (s : Nat) (v : Vector RPoly n), (∀ i, i < m → (f (s + i)).isSome = true) →
      ∃ w : Vector RPoly n,
        forIn (m := Id) (List.range' s m) (⟨none, v⟩ : FS β n) (fillBody f) = ⟨none, w⟩ := by
  induction m with
  | zero => intro s v _; exact ⟨v, rfl⟩
  | succ m ih =>
    intro s v h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h 0 (by omega))
    obtain ⟨w, hw⟩ := ih (s + 1) (v.set! s a) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show s + (i + 1) = s + 1 + i by omega] at this)
    refine ⟨w, ?_⟩
    rw [Nat.add_zero] at ha
    simp [List.range'_succ, List.forIn_cons, fillBody, ha]
    exact hw

/-- `ExpandS` succeeds as soon as each of its `ℓ + k` calls to `RejBoundedPoly` does. This is what lets the
satisfiability witnesses evaluate the calls one at a time, each in its own kernel check, instead of the whole `ExpandS`
in one (the memory of one kernel check grows with the work it does). -/
theorem ExpandS_isSome (p : Params) (fuel : Nat) (ρ : List UInt8)
    (h : ∀ i, i < p.ℓ + p.k → (RejBoundedPoly p fuel (ρ ++ IntegerToBytes i 2)).isSome = true) :
    (ExpandS p fuel ρ).isSome = true := by
  rw [ExpandS_eq]
  unfold expandSModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  obtain ⟨w1, e1⟩ := fill_forIn_ok (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0)) (fun i hi => by simpa using h i (by omega))
  obtain ⟨w2, e2⟩ := fill_forIn_ok (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0)) (fun i hi => by simpa [Nat.add_comm] using h (i + p.ℓ) (by omega))
  rw [e1, e2]
  rfl

/-! ## ExpandS: the seed buffer -/

theorem seed_set (seed : Array U8 66#usize) (ρ0 : List UInt8) (hρ : ρ0.length = 64)
    (hP : ∀ i, i < 64 → (bytesA seed)[i]? = ρ0[i]?) (x y : U8) :
    bytesA ((seed.set 64#usize x).set 65#usize y) = ρ0 ++ [UInt8.ofNat x.val, UInt8.ofNat y.val] := by
  have hl : (bytesA seed).length = 66 := by simp
  apply List.ext_getElem?
  intro i
  rw [bytesA_set, bytesA_set, List.getElem?_set, List.getElem?_set]
  rcases (by omega : i < 64 ∨ i = 64 ∨ i = 65 ∨ 66 ≤ i) with h | h | h | h
  · have h1 : ¬ ((65#usize).val = i) := by simp; omega
    have h2 : ¬ ((64#usize).val = i) := by simp; omega
    rw [if_neg h1, if_neg h2, hP i h, List.getElem?_append_left (by omega)]
  · subst h
    simp [hρ, hl]
  · subst h
    simp [hρ, hl]
  · have h1 : ¬ ((65#usize).val = i) := by simp; omega
    have h2 : ¬ ((64#usize).val = i) := by simp; omega
    rw [if_neg h1, if_neg h2, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp [hρ]; omega)]

theorem seed_set_P (seed : Array U8 66#usize) (ρ0 : List UInt8) (hρ : ρ0.length = 64)
    (hP : ∀ i, i < 64 → (bytesA seed)[i]? = ρ0[i]?) (x y : U8) :
    ∀ i, i < 64 → (bytesA ((seed.set 64#usize x).set 65#usize y))[i]? = ρ0[i]? := by
  intro i hi
  rw [seed_set seed ρ0 hρ hP x y, List.getElem?_append_left (by omega)]

theorem expand_s_loop0_spec (rho : Array U8 64#usize) (seed : Array U8 66#usize) :
    sampling.expand_s_loop0 rho seed 0#usize ⦃ r =>
      ∀ i, i < 64 → (bytesA r)[i]? = (bytesA rho)[i]? ⦄ := by
  unfold sampling.expand_s_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 66#usize × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧ ∀ i, i < 64 → i < p.2.val → (bytesA p.1)[i]? = (bytesA rho)[i]?)
  · rintro ⟨sd, b⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.expand_s_loop0.body]
    split
    · rename_i hb
      have hb' : b.val < 64 := by scalar_tac
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj hjb
      subst_vars
      rw [bytesA_set, List.getElem?_set]
      by_cases hjb' : b.val = j
      · subst hjb'
        rw [if_pos rfl, if_pos (by simp [bytesA_length]; omega)]
        simp [bytesA, *]
      · rw [if_neg hjb']
        exact h2 j hj (by scalar_tac)
    · rename_i hb
      have : b.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      intro i hi
      exact h2 i hi (by omega)
  · exact ⟨by simp, fun i _ hi => by simp at hi⟩


theorem ofNat_nonce (r : Nat) (hr : r < 256) :
    IntegerToBytes r 2 = [UInt8.ofNat r, UInt8.ofNat 0] := by
  rw [ITB_two_s]
  simp [Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr]
  try rfl

theorem expand_s_loop1_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) (fuel : Nat) (s₁ : Vector RPoly sp.ℓ)
    (hrej : ∀ (i : Nat) (hi : i < sp.ℓ), RejBoundedPoly sp fuel (bytesA ρ ++ IntegerToBytes i 2) = some s₁[i])
    (s1 : Array (Array U32 256#usize) L) (seed : Array U8 66#usize)
    (hseed : ∀ i, i < 64 → (bytesA seed)[i]? = (bytesA ρ)[i]?) :
    sampling.expand_s_loop1 ip s1 seed 0#usize ⦃ r =>
      (∀ (i : Nat) (hi : i < sp.ℓ), ∃ q, r.1.val[i]? = some q ∧ ReprInt q s₁[i]) ∧
      ∀ i, i < 64 → (bytesA r.2)[i]? = (bytesA ρ)[i]? ⦄ := by
  have hρl : (bytesA ρ).length = 64 := by simp
  have hLl := hp.L_eq
  unfold sampling.expand_s_loop1
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Array U8 66#usize × Usize) => L.val - p.2.2.val)
    (fun p => p.2.2.val ≤ L.val ∧ (∀ i, i < 64 → (bytesA p.2.1)[i]? = (bytesA ρ)[i]?) ∧
      ∀ (i : Nat), i < p.2.2.val → ∃ q, p.1.val[i]? = some q ∧ ∃ h : i < sp.ℓ, ReprInt q s₁[i])
  · rintro ⟨s1', sd, r⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [sampling.expand_s_loop1.body]
    split
    · rename_i hr
      have hr' : r.val < L.val := by scalar_tac
      have hrl : r.val < sp.ℓ := by omega
      have hrlt : r.val < 256 := by omega
      step*
      have hi : i.val = r.val := by rw [i_post]; simp [UScalar.cast_val_eq]; omega
      have hbytes : bytesA seed2 = bytesA ρ ++ IntegerToBytes r.val 2 := by
        rw [seed2_post, seed1_post, seed_set sd _ hρl h2, ofNat_nonce _ hrlt, hi]
        rfl
      have hspec := rej_bounded_poly_spec hp hη seed2 s₁[r.val] fuel (by rw [hbytes]; exact hrej r.val hrl)
      refine WP.spec_bind hspec ?_
      rintro a ⟨ha, -⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [seed2_post, seed1_post]
        exact seed_set_P sd _ hρl h2 _ _
      · intro j hj
        have hlen : s1'.val.length = L.val := s1'.property
        rw [a1_post, Array.set_val_eq, List.getElem?_set]
        by_cases hjr : r.val = j
        · subst hjr
          rw [if_pos rfl, if_pos (by omega)]
          exact ⟨a, rfl, hrl, ha⟩
        · rw [if_neg hjr]
          exact h3 j (by scalar_tac)
    · rename_i hr
      have : r.val = L.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨fun i hi => ?_, h2⟩
      obtain ⟨q, hq, _, hrq⟩ := h3 i (by omega)
      exact ⟨q, hq, hrq⟩
  · exact ⟨by simp, hseed, fun i hi => by simp at hi⟩


theorem expand_s_loop2_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) (fuel : Nat) (s₂ : Vector RPoly sp.k)
    (hrej : ∀ (i : Nat) (hi : i < sp.k),
      RejBoundedPoly sp fuel (bytesA ρ ++ IntegerToBytes (i + sp.ℓ) 2) = some s₂[i])
    (s2 : Array (Array U32 256#usize) K) (seed : Array U8 66#usize)
    (hseed : ∀ i, i < 64 → (bytesA seed)[i]? = (bytesA ρ)[i]?) :
    sampling.expand_s_loop2 L ip s2 seed 0#usize ⦃ r =>
      ∀ (i : Nat) (hi : i < sp.k), ∃ q, r.val[i]? = some q ∧ ReprInt q s₂[i] ⦄ := by
  have hρl : (bytesA ρ).length = 64 := by simp
  have hKk := hp.K_eq
  have hLl := hp.L_eq
  unfold sampling.expand_s_loop2
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Array U8 66#usize × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ (∀ i, i < 64 → (bytesA p.2.1)[i]? = (bytesA ρ)[i]?) ∧
      ∀ (i : Nat), i < p.2.2.val → ∃ q, p.1.val[i]? = some q ∧ ∃ h : i < sp.k, ReprInt q s₂[i])
  · rintro ⟨s2', sd, r⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [sampling.expand_s_loop2.body]
    split
    · rename_i hr
      have hr' : r.val < K.val := by scalar_tac
      have hrl : r.val < sp.k := by omega
      have hrlt : r.val + L.val < 256 := by omega
      step*
      have hi : i1.val = r.val + sp.ℓ := by
        rw [i1_post]; simp [UScalar.cast_val_eq]; omega
      have hbytes : bytesA seed2 = bytesA ρ ++ IntegerToBytes (r.val + sp.ℓ) 2 := by
        rw [seed2_post, seed1_post, seed_set sd _ hρl h2, ofNat_nonce _ (by omega), hi]
        rfl
      have hspec := rej_bounded_poly_spec hp hη seed2 s₂[r.val] fuel (by rw [hbytes]; exact hrej r.val hrl)
      refine WP.spec_bind hspec ?_
      rintro a ⟨ha, -⟩
      step*
      refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · rw [seed2_post, seed1_post]
        exact seed_set_P sd _ hρl h2 _ _
      · intro j hj
        have hlen : s2'.val.length = K.val := s2'.property
        rw [a1_post, Array.set_val_eq, List.getElem?_set]
        by_cases hjr : r.val = j
        · subst hjr
          rw [if_pos rfl, if_pos (by omega)]
          exact ⟨a, rfl, hrl, ha⟩
        · rw [if_neg hjr]
          exact h3 j (by scalar_tac)
    · rename_i hr
      have : r.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      intro i hi
      obtain ⟨q, hq, _, hrq⟩ := h3 i (by omega)
      exact ⟨q, hq, hrq⟩
  · exact ⟨by simp, hseed, fun i hi => by simp at hi⟩


theorem getElem_of_getElem?_eq {α : Type} {l : List α} {i : Nat} {q : α} (hi : i < l.length)
    (h : l[i]? = some q) : l[i]'hi = q := by
  obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.mp h
  exact e

theorem expand_s_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k) (fuel : Nat)
    (hs : Spec.ExpandS sp fuel (bytesA ρ) = some (s₁, s₂)) :
    sampling.expand_s K L ip ρ ⦃ r =>
      ReprIntVec r.1 s₁ ∧ ReprIntVec r.2 s₂ ∧
      (∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), ((s₁[i])[j]'hj).natAbs ≤ sp.η) ∧
      (∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), ((s₂[i])[j]'hj).natAbs ≤ sp.η) ⦄ := by
  obtain ⟨hr1, hr2⟩ := ExpandS_some sp fuel _ s₁ s₂ hs
  have hb1 : ∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), ((s₁[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp fuel _ _ (hr1 i hi)
  have hb2 : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), ((s₂[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp fuel _ _ (hr2 i hi)
  unfold sampling.expand_s
  refine WP.spec_bind (expand_s_loop0_spec ρ _) ?_
  intro seed1 hseed1
  refine WP.spec_bind (expand_s_loop1_spec hp hη hKL ρ fuel s₁ hr1 _ seed1 hseed1) ?_
  rintro ⟨s11, seed2⟩ ⟨h1, h2⟩
  refine WP.spec_bind (expand_s_loop2_spec hp hη hKL ρ fuel s₂ hr2 _ seed2 h2) ?_
  intro s21 h3
  refine (WP.spec_ok _).mpr ?_
  refine ⟨⟨hp.L_eq, fun i hi => ?_⟩, ⟨hp.K_eq, fun i hi => ?_⟩, hb1, hb2⟩
  · obtain ⟨q, hq, hr⟩ := h1 i hi
    have hlt : i < s11.val.length := by have := s11.property; have := hp.L_eq; omega
    show ReprInt (s11.val[i]'hlt) _
    rw [getElem_of_getElem?_eq hlt hq]
    exact hr
  · obtain ⟨q, hq, hr⟩ := h3 i hi
    have hlt : i < s21.val.length := by have := s21.property; have := hp.K_eq; omega
    show ReprInt (s21.val[i]'hlt) _
    rw [getElem_of_getElem?_eq hlt hq]
    exact hr


/-! ## Satisfiability of the premises (kernel evaluation of SHAKE256) -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `RejBoundedPoly` premise holds for the all-zero seed, ML-DSA-44, fuel 512. -/
theorem rej_bounded_poly_satisfiable :
    ∃ a, Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 66 0) = some a := by
  have : (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 66 0)).isSome = true := by decide +kernel
  exact Option.isSome_iff_exists.mp this

/-- The premise of `rej_bounded_poly_spec` is satisfiable for the extracted type. -/
theorem rej_bounded_poly_premise_satisfiable :
    ∃ (ρ : Array U8 66#usize) (a : RPoly) (fuel : Nat), Spec.RejBoundedPoly Spec.ML_DSA_44 fuel (bytesA ρ) = some a := by
  obtain ⟨A, hA⟩ := rej_bounded_poly_satisfiable
  refine ⟨Array.repeat 66#usize 0#u8, A, 512, ?_⟩
  rw [bytesA_repeat_zero]
  exact hA

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 0 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 0 2`. -/
theorem rej_bounded_44_0 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 0 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 1 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 1 2`. -/
theorem rej_bounded_44_1 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 1 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 2 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 2 2`. -/
theorem rej_bounded_44_2 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 2 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 3 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 3 2`. -/
theorem rej_bounded_44_3 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 3 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 4 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 4 2`. -/
theorem rej_bounded_44_4 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 4 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 5 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 5 2`. -/
theorem rej_bounded_44_5 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 5 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 6 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 6 2`. -/
theorem rej_bounded_44_6 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 6 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Call 7 of `ExpandS` (ML-DSA-44, all-zero seed, fuel 512): `RejBoundedPoly` succeeds on `ρ ‖ IntegerToBytes 7 2`. -/
theorem rej_bounded_44_7 :
    (Spec.RejBoundedPoly Spec.ML_DSA_44 512 (List.replicate 64 0 ++ IntegerToBytes 7 2)).isSome = true := by
  decide +kernel

/-- The `ExpandS` premise holds for the all-zero seed, ML-DSA-44, fuel 512 (8 kernel evaluations of SHAKE256 +
`RejBoundedPoly`, each its own declaration, assembled by `ExpandS_isSome`). -/
theorem expand_s_satisfiable :
    ∃ r, Spec.ExpandS Spec.ML_DSA_44 512 (List.replicate 64 0) = some r := by
  have : (Spec.ExpandS Spec.ML_DSA_44 512 (List.replicate 64 0)).isSome = true := by
    apply ExpandS_isSome
    have h8 : Spec.ML_DSA_44.ℓ + Spec.ML_DSA_44.k = 8 := by decide +kernel
    rw [h8]
    intro i hi
    match i, hi with
    | 0, _ => exact rej_bounded_44_0
    | 1, _ => exact rej_bounded_44_1
    | 2, _ => exact rej_bounded_44_2
    | 3, _ => exact rej_bounded_44_3
    | 4, _ => exact rej_bounded_44_4
    | 5, _ => exact rej_bounded_44_5
    | 6, _ => exact rej_bounded_44_6
    | 7, _ => exact rej_bounded_44_7
    | i + 8, h => exact absurd h (by omega)
  exact Option.isSome_iff_exists.mp this

/-- The premise of `expand_s_spec` is satisfiable for the extracted type. -/
theorem expand_s_premise_satisfiable :
    ∃ (ρ : Array U8 64#usize) (s₁ : Vector RPoly Spec.ML_DSA_44.ℓ) (s₂ : Vector RPoly Spec.ML_DSA_44.k) (fuel : Nat),
      Spec.ExpandS Spec.ML_DSA_44 fuel (bytesA ρ) = some (s₁, s₂) := by
  obtain ⟨⟨s₁, s₂⟩, h⟩ := expand_s_satisfiable
  refine ⟨Array.repeat 64#usize 0#u8, s₁, s₂, 512, ?_⟩
  rw [bytesA_repeat_zero]
  exact h

end Proofs
