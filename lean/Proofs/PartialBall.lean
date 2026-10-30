import Proofs.Partial
import Proofs.SampleBall

/-!
# Partial correctness of SampleInBall (FIPS 204 Algorithm 29)

See `Proofs/Partial.lean` for the technique. The result is `sample_in_ball_partial`: the Rust `sample_in_ball`
never panics, and if it returns `r` then `r` represents the spec's answer at some fuel.

* Spec side: the stream of `SHAKE256 M N` is a prefix of the stream for every larger `N`
  (`shake256_take`, `shake256_prefix`), so `sibFind`/`sibStep`/`sibRun` are monotone in the budget and the stream
  (`sibFind_mono`, `sibStep_mono`), and a run of the outer loop at fuel `F` stays valid at every `F' ≥ F`
  (`SampleInBall_mono`).
* Inner loop (`while j > i`): ghost `(pos, j)`; the result relates to `sibFind` at *some* stream length and budget
  (`inner_loop_partial`, `loop.dspec_ghost`).
* Outer loop: the invariant carries the spec's run so far at some fuel `F`; one more iteration needs the fuel
  `max F (max N k)` for the stream length `N` and budget `k` the inner search used (`outer_loop_partial`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Spec-side lemmas -/

theorem shake256_take (M : List UInt8) (n N : Nat) (h : n ≤ N) : (Spec.SHAKE256 M N).take n = Spec.SHAKE256 M n := by
  have hw := sponge_window 136 (by omega) M 0 n N (by omega)
  simp only [List.drop_zero, Nat.zero_add] at hw
  exact hw.symm

theorem shake256_prefix (M : List UInt8) (n N : Nat) (h : n ≤ N) : Spec.SHAKE256 M n <+: Spec.SHAKE256 M N := by
  rw [← shake256_take M n N h]
  exact List.take_prefix _ _

/-- The byte at position `pos` of the SHAKE256 stream (any stream long enough gives the same byte). -/
def byteAt (M : List UInt8) (pos : Nat) : Nat := ((Spec.SHAKE256 M (pos + 1))[pos]?.getD default).toNat

theorem byteAt_eq (M : List UInt8) (pos N : Nat) (h : pos < N) :
    ((Spec.SHAKE256 M N)[pos]?.getD default).toNat = byteAt M pos := by
  have hw := sponge_window 136 (by omega) M pos 1 N (by omega)
  have h0 := congrArg (fun l => l[0]?) hw
  simp only [List.getElem?_drop, List.getElem?_take] at h0
  unfold byteAt
  have : (Spec.SHAKE256 M N)[pos]? = (Spec.SHAKE256 M (pos + 1))[pos]? := by
    simpa [Spec.SHAKE256] using h0.symm
  rw [this]

theorem sibFind_mono (S S' : List UInt8) (i : Nat) (hp : S <+: S') :
    ∀ k k' pos j r, k ≤ k' → sibFind S i k pos j = some r → sibFind S' i k' pos j = some r := by
  obtain ⟨t, rfl⟩ := hp
  intro k
  induction k with
  | zero =>
    intro k' pos j r _ h
    simp only [sibFind] at h
    split at h
    · rename_i hj
      simp only [Option.some.injEq] at h
      subst h
      cases k' <;> simp [sibFind, hj]
    · simp at h
  | succ k ih =>
    intro k' pos j r hk h
    simp only [sibFind] at h
    split at h
    · rename_i hj
      simp only [Option.some.injEq] at h
      subst h
      cases k' <;> simp [sibFind, hj]
    · rename_i hj
      split at h
      · rename_i hpos
        obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
        have hpos' : pos + 1 ≤ (S ++ t).length := by simp; omega
        have hget : (S ++ t)[pos]? = S[pos]? := List.getElem?_append_left (by omega)
        simp only [sibFind, hj, if_false, hpos', if_true, hget]
        exact ih k'' _ _ _ (by omega) h
      · simp at h

theorem sibStep_mono (S S' : List UInt8) (hb : List Bool) (τ : Nat) (hp : S <+: S') (F F' : Nat) (hF : F ≤ F')
    (st : RPoly × Nat) (i : Nat) (y : RPoly × Nat) (h : sibStep S hb τ F st i = some y) :
    sibStep S' hb τ F' st i = some y := by
  unfold sibStep at h ⊢
  split at h
  · rename_i hlen
    have hlen' : st.2 + 1 ≤ S'.length := le_trans hlen hp.length_le
    rw [if_pos hlen']
    cases hf : sibFind S i F (st.2 + 1) ((S[st.2]?.getD default).toNat) with
    | none => rw [hf] at h; simp at h
    | some r =>
      rw [hf] at h
      obtain ⟨t, rfl⟩ := hp
      have hget : (S ++ t)[st.2]? = S[st.2]? := List.getElem?_append_left (by omega)
      rw [hget, sibFind_mono S (S ++ t) i ⟨t, rfl⟩ F F' _ _ r hF hf]
      exact h
  · simp at h

/-- The state of the spec's outer loop after the steps `256 - τ ≤ s < i`, at fuel `F`. -/
def runTo (M : List UInt8) (τ F i : Nat) : Option (RPoly × Nat) :=
  (List.range' (256 - τ) (i - (256 - τ))).foldlM
    (sibStep (Spec.SHAKE256 M (8 + F)) (BytesToBits (Spec.SHAKE256 M 8)) τ F) (Vector.replicate 256 0, 8)

theorem runTo_mono (M : List UInt8) (τ F F' i : Nat) (hF : F ≤ F') (y : RPoly × Nat)
    (h : runTo M τ F i = some y) : runTo M τ F' i = some y := by
  unfold runTo at h ⊢
  exact foldlM_fuel_mono (fun F => sibStep (Spec.SHAKE256 M (8 + F)) (BytesToBits (Spec.SHAKE256 M 8)) τ F)
    (fun F F' x i y hF h => sibStep_mono _ _ _ _ (shake256_prefix M _ _ (by omega)) F F' hF x i y h) _ _ y F F' hF h


theorem SampleInBall_of_runTo (p : Spec.Params) (hτ : p.τ ≤ 256) (ρ : List UInt8) (F : Nat) (c : RPoly) (pos : Nat)
    (h : runTo ρ p.τ F 256 = some (c, pos)) : Spec.SampleInBall p F ρ = some c := by
  rw [SampleInBall_eq p hτ]
  unfold runTo at h
  have e : 256 - (256 - p.τ) = p.τ := by omega
  rw [e] at h
  unfold sibRun
  have hb : BytesToBits ((H ρ (8 + F)).take 8) = BytesToBits (Spec.SHAKE256 ρ 8) := by
    rw [show H ρ (8 + F) = Spec.SHAKE256 ρ (8 + F) from rfl, shake256_take ρ 8 (8 + F) (by omega)]
  rw [hb, show H ρ (8 + F) = Spec.SHAKE256 ρ (8 + F) from rfl, h]
  rfl

/-! ## The inner loop -/

/-- Ghost `(pos, j)`: the sponge is at stream position `pos` and the byte buffer holds `j`. -/
def InnerG (M : List UInt8) (ctx : keccak.Shake) (j : Array U8 1#usize) (g : Nat × Nat) : Prop :=
  ShakeSqz ctx 136 M g.1 ∧ bv0 j = some g.2

/-- The inner search from `(pos, j)` finds `jf` at stream position `posf`, within some stream length and budget. -/
def InnerPost (M : List UInt8) (i : Nat) (g : Nat × Nat) (r : keccak.Shake × Array U8 1#usize) : Prop :=
  ∃ N k jf posf, g.1 ≤ posf ∧ posf ≤ N ∧ sibFind (Spec.SHAKE256 M N) i k g.1 g.2 = some (jf, posf) ∧
    ShakeSqz r.1 136 M posf ∧ bv0 r.2 = some jf

theorem inner_body_partial (M : List UInt8) (i : Usize) (g : Nat × Nat) (ctx : keccak.Shake)
    (j : Array U8 1#usize) (h : InnerG M ctx j g) :
    sampling.sample_in_ball_loop1_loop0.body i ctx j ⦃ c =>
      match c with
      | .done r => InnerPost M i.val g r
      | .cont s' => ∃ g', InnerG M s'.1 s'.2 g' ∧ ∀ r, InnerPost M i.val g' r → InnerPost M i.val g r ⦄ := by
  obtain ⟨pos, jcur⟩ := g
  obtain ⟨hS, hj⟩ := h
  dsimp only at hS hj
  simp only [sampling.sample_in_ball_loop1_loop0.body]
  step*
  · -- continue
    have hgt : i2 > i := ‹i2 > i›
    have hj' : j.val[0]? = some (j.val[0]'i1) := List.getElem?_eq_getElem i1
    have hjc : (j.val[0]'i1).val = jcur := by
      have := hj; simp only [bv0] at this; rw [hj'] at this; simpa using this
    have hi2 : i2.val = jcur := by
      rw [i2_post, U8.cast_Usize_val_eq, i1_post2, hjc]
    have hgt' : i.val < jcur := by have : i < i2 := hgt; scalar_tac
    have hlen1 : s.val.length = 1 := by rw [s_post1]; simpa using j.property
    have hb1 : bytes s1 = ((Spec.SHAKE256 M (pos + 1)).drop pos).take 1 := by
      rw [ctx1_post2, hlen1]
      exact sponge_window 136 (by norm_num) M pos 1 (pos + 1) le_rfl
    have hSN : (Spec.SHAKE256 M (pos + 1)).length = pos + 1 := SHAKE256_length _ _
    have hbyte := byte1 (Spec.SHAKE256 M (pos + 1)) pos (by omega) s1 hb1
    have hlens1 : s1.val.length = 1 := by
      have := congrArg List.length hbyte; simpa using this
    have hback : (to_slice_mut_back s1).val = s1.val := by
      rw [s_post2]; exact Array.from_slice_val j s1 hlens1
    have hG' : InnerG M ctx1 (to_slice_mut_back s1) (pos + 1, byteAt M pos) := by
      refine ⟨?_, ?_⟩
      · show ShakeSqz ctx1 136 M (pos + 1)
        rw [hlen1] at ctx1_post1; exact ctx1_post1
      · show bv0 (to_slice_mut_back s1) = some (byteAt M pos)
        simp only [bv0, hback]
        obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlens1
        rw [hb] at hbyte ⊢
        simp at hbyte ⊢
        exact hbyte
    refine ⟨(pos + 1, byteAt M pos), hG', ?_⟩
    rintro r ⟨N, k, jf, posf, hle, hN, hf, hS2, hj2⟩
    dsimp only at hle hf
    refine ⟨N, k + 1, jf, posf, by omega, hN, ?_, hS2, hj2⟩
    have hl : (Spec.SHAKE256 M N).length = N := SHAKE256_length _ _
    show sibFind (Spec.SHAKE256 M N) i.val (k + 1) pos jcur = some (jf, posf)
    unfold sibFind
    rw [if_neg (by omega), if_pos (by omega), byteAt_eq M pos N (by omega)]
    exact hf
  · -- done
    have hle : ¬ i2 > i := ‹¬ i2 > i›
    have hj' : j.val[0]? = some (j.val[0]'i1) := List.getElem?_eq_getElem i1
    have hjc : (j.val[0]'i1).val = jcur := by
      have := hj; simp only [bv0] at this; rw [hj'] at this; simpa using this
    have hi2 : i2.val = jcur := by
      rw [i2_post, U8.cast_Usize_val_eq, i1_post2, hjc]
    have hle' : jcur ≤ i.val := by have : i2 ≤ i := not_lt.mp hle; scalar_tac
    exact ⟨pos, 0, jcur, pos, le_rfl, le_rfl, by simp [sibFind, hle'], hS, hj⟩

theorem inner_loop_partial (M : List UInt8) (i : Usize) (g : Nat × Nat) (ctx : keccak.Shake)
    (j : Array U8 1#usize) (h : InnerG M ctx j g) :
    sampling.sample_in_ball_loop1_loop0 ctx i j ⦃ r => InnerPost M i.val g r ⦄div := by
  unfold sampling.sample_in_ball_loop1_loop0
  refine loop.dspec_ghost _ (fun g (s : keccak.Shake × Array U8 1#usize) => InnerG M s.1 s.2 g)
    (fun g r => InnerPost M i.val g r) ?_ g (ctx, j) h
  rintro g ⟨ctx', j'⟩ hI
  dsimp only at hI ⊢
  apply WP.spec_dspec
  refine WP.spec_mono (inner_body_partial M i g ctx' j' hI) ?_
  rintro (⟨c1, j1⟩ | r) h
  · exact h
  · exact h

theorem runTo_succ (M : List UInt8) (τ F i : Nat) (cm : RPoly) (pos : Nat) (y : RPoly × Nat) (hi : 256 - τ ≤ i)
    (h : runTo M τ F i = some (cm, pos))
    (hs : sibStep (Spec.SHAKE256 M (8 + F)) (BytesToBits (Spec.SHAKE256 M 8)) τ F (cm, pos) i = some y) :
    runTo M τ F (i + 1) = some y := by
  unfold runTo at h ⊢
  have e : i + 1 - (256 - τ) = (i - (256 - τ)) + 1 := by omega
  have e2 : 256 - τ + (i - (256 - τ)) = i := by omega
  rw [e, List.range'_concat, List.foldlM_append, h, Nat.one_mul, e2]
  simpa using hs

/-! ## The outer loop -/

/-- Outer-loop invariant: iterations `256 - τ ≤ s < i` are done, and the spec's run so far (at some fuel `F`)
is the Rust state. -/
def OuterInvB (τ : Nat) (M : List UInt8) (c : Array U32 256#usize) (ctx : keccak.Shake) (i : Usize) : Prop :=
  256 - τ ≤ i.val ∧ i.val ≤ 256 ∧ ∃ cm pos F, ReprInt c cm ∧ ShakeSqz ctx 136 M pos ∧ pos ≤ 8 + F ∧
    runTo M τ F i.val = some (cm, pos)

theorem outer_body_partial (ip : Impl.params.Params) (hτ : ip.tau.val ≤ 64) (M : List UInt8) (h : U64)
    (hh : ∀ t, t < 64 → h.val.testBit t = decide (byteBit (Spec.SHAKE256 M 8) t = 1))
    (c : Array U32 256#usize) (ctx : keccak.Shake) (i1 : Usize) (hI : OuterInvB ip.tau.val M c ctx i1) :
    sampling.sample_in_ball_loop1.body ip.tau h c ctx i1 ⦃ r =>
      match r with
      | .done y => ∃ F cfin pos', runTo M ip.tau.val F 256 = some (cfin, pos') ∧ ReprInt y cfin
      | .cont (c', ctx', i') => OuterInvB ip.tau.val M c' ctx' i' ⦄div := by
  obtain ⟨hlo, hhi, cm, pos, F, hrep, hS, hposF, hrun⟩ := hI
  simp only [sampling.sample_in_ball_loop1.body]
  split
  · rename_i hlt
    have hi' : i1.val < 256 := by scalar_tac
    step*
    obtain ⟨s, tsmb⟩ := s
    dsimp only at to_slice_mut_back s_post2 ⊢
    step*
    obtain ⟨ctx1, sl⟩ := ctx1
    dsimp only at s1 ctx1_post2 ⊢
    have hlen1 : s.val.length = 1 := by rw [to_slice_mut_back]; simp
    have hSN : (Spec.SHAKE256 M (pos + 1)).length = pos + 1 := SHAKE256_length _ _
    have hb1 : bytes sl = ((Spec.SHAKE256 M (pos + 1)).drop pos).take 1 := by
      rw [ctx1_post2, hlen1]
      exact sponge_window 136 (by norm_num) M pos 1 (pos + 1) le_rfl
    have hbyte := byte1 (Spec.SHAKE256 M (pos + 1)) pos (by omega) sl hb1
    have hlens1 : sl.val.length = 1 := by
      have := congrArg List.length hbyte; simpa using this
    have hback : (tsmb sl).val = sl.val := by
      rw [s_post2]; exact Array.from_slice_val _ sl hlens1
    have hS1 : ShakeSqz ctx1 136 M (pos + 1) := by
      have := s1; rw [hlen1] at this; exact this
    have hG' : InnerG M ctx1 (tsmb sl) (pos + 1, byteAt M pos) := by
      refine ⟨hS1, ?_⟩
      show bv0 (tsmb sl) = some (byteAt M pos)
      simp only [bv0, hback]
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlens1
      rw [hb] at hbyte ⊢
      simp at hbyte ⊢
      exact hbyte
    refine WP.dspec_bind' (inner_loop_partial M i1 (pos + 1, byteAt M pos) ctx1 (tsmb sl) hG') ?_
    rintro ⟨ctx2, j2⟩ ⟨N, k, jf, posf, hle, hN, hf, hS2, hj2⟩
    dsimp only at hle hf hS2 hj2 ⊢
    step*
    have hjf := sibFind_le _ _ _ _ _ _ _ hf
    have hxj : (j2.val[0]'i2).val = jf := by
      have hj' : j2.val[0]? = some (j2.val[0]'i2) := List.getElem?_eq_getElem i2
      have := hj2; simp only [bv0] at this; rw [hj'] at this; simpa using this
    have hjj : jj.val = jf := by rw [jj_post, U8.cast_Usize_val_eq, i2_post2, hxj]
    -- the fuel for the new iteration
    have hF'1 : F ≤ max F (max N k) := le_max_left _ _
    have hF'N : N ≤ max F (max N k) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hF'k : k ≤ max F (max N k) := le_trans (le_max_right _ _) (le_max_right _ _)
    have hrun' := runTo_mono M ip.tau.val F (max F (max N k)) i1.val hF'1 _ hrun
    have hfind : sibFind (Spec.SHAKE256 M (8 + max F (max N k))) i1.val (max F (max N k)) (pos + 1)
        (byteAt M pos) = some (jf, posf) :=
      sibFind_mono _ _ _ (shake256_prefix M N _ (by omega)) k _ _ _ _ hF'k hf
    have hstep : sibStep (Spec.SHAKE256 M (8 + max F (max N k))) (BytesToBits (Spec.SHAKE256 M 8)) ip.tau.val
        (max F (max N k)) (cm, pos) i1.val =
        some ((cm.set! i1.val cm[jf]!).set! jf
          (if (BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true then -1 else 1), posf) := by
      have hl : (Spec.SHAKE256 M (8 + max F (max N k))).length = 8 + max F (max N k) := SHAKE256_length _ _
      unfold sibStep
      dsimp only
      rw [if_pos (by omega), byteAt_eq M pos _ (by omega), hfind]
    have hrunNew := runTo_succ M ip.tau.val _ i1.val cm pos _ hlo hrun' hstep
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
    have hbitv : bit.val = 1 ↔ byteBit (Spec.SHAKE256 M 8) (i1.val + ip.tau.val - 256) = 1 := by
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
    have hcond : ((BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true)
        ↔ bit.val = 1 := by
      rw [bit_cond, hbitv]
    have hposF' : posf ≤ 8 + max F (max N k) := by omega
    by_cases hbit : bit = 1#u64
    · simp only [hbit, if_true]
      step*
      have hbit1 : bit.val = 1 := by rw [hbit]; rfl
      have hc : (BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true :=
        hcond.mpr hbit1
      have hi7 : i7.val = 8380416 := by rw [i7_post1]; omega
      refine ⟨by omega, by omega, ((cm.set! i1.val cm[jj.val]!).set! jj.val (if (BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true then -1 else 1)), posf, max F (max N k), ?_, hS2, hposF', ?_⟩
      · rw [a_post, if_pos hc]
        exact hr1.set jj i7 (-1) hjj256 (by rw [hi7]; decide) (by rw [hi7]; exact hq1)
      · rw [i8_post]; exact hrunNew
    · simp only [hbit, if_false]
      step*
      have hcf : ¬ ((BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true) := by
        intro h
        have h1 := hcond.mp h
        exact hbit (UScalar.eq_of_val_eq (by simpa using h1))
      refine ⟨by omega, by omega, ((cm.set! i1.val cm[jj.val]!).set! jj.val (if (BytesToBits (Spec.SHAKE256 M 8))[i1.val + ip.tau.val - 256]?.getD false = true then -1 else 1)), posf, max F (max N k), ?_, hS2, hposF', ?_⟩
      · rw [a_post, if_neg hcf]
        exact hr1.set jj 1#u32 1 hjj256 (by decide) (by simp)
      · rw [i8_post]; exact hrunNew
  · rename_i hlt
    have hi' : i1.val = 256 := by scalar_tac
    simp only [WP.dspec_ok]
    rw [hi'] at hrun
    exact ⟨F, cm, pos, hrun, hrep⟩

theorem outer_loop_partial (ip : Impl.params.Params) (hτ : ip.tau.val ≤ 64) (M : List UInt8) (h : U64)
    (hh : ∀ t, t < 64 → h.val.testBit t = decide (byteBit (Spec.SHAKE256 M 8) t = 1))
    (c0 : Array U32 256#usize) (ctx0 : keccak.Shake) (i0 : Usize) (hI : OuterInvB ip.tau.val M c0 ctx0 i0) :
    sampling.sample_in_ball_loop1 ip.tau c0 ctx0 h i0 ⦃ r =>
      ∃ F cfin pos', runTo M ip.tau.val F 256 = some (cfin, pos') ∧ ReprInt r cfin ⦄div := by
  unfold sampling.sample_in_ball_loop1
  refine loop.dspec_inv _
    (fun p : Array U32 256#usize × keccak.Shake × Usize => OuterInvB ip.tau.val M p.1 p.2.1 p.2.2) _ ?_
    (c0, ctx0, i0) hI
  rintro ⟨c, ctx, i1⟩ hI
  dsimp only at hI ⊢
  refine WP.dspec_mono' (outer_body_partial ip hτ M h hh c ctx i1 hI) ?_
  rintro (⟨c', ctx', i'⟩ | y) h
  · exact h
  · exact h

/-- **`sample_in_ball`, partial correctness** (Algorithm 29). The Rust function never panics, and if it returns `r`
then `r` represents the spec's `SampleInBall` at some fuel. -/
theorem sample_in_ball_partial {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hτ : sp.τ ≤ 64) (ρ : Slice U8) :
    sampling.sample_in_ball ip ρ ⦃ r =>
      ∃ (c : RPoly) (F : Nat), Spec.SampleInBall sp F (bytes ρ) = some c ∧ ReprInt r c ⦄div := by
  have hτ' : ip.tau.val ≤ 64 := by rw [hp.tau]; exact hτ
  unfold sampling.sample_in_ball
  step*
  obtain ⟨s1, tsmb⟩ := s1
  dsimp only at to_slice_mut_back s1_post2 ⊢
  step*
  obtain ⟨ctx3, sl2⟩ := ctx3
  dsimp only at ctx3_post2 ⊢
  simp only [List.nil_append] at *
  have hl1 : s1.val.length = 8 := by rw [to_slice_mut_back]; simp
  have hb2 : bytes sl2 = Spec.SHAKE256 (bytes ρ) 8 := by
    rw [ctx3_post2, hl1]
    simp [Spec.SHAKE256]
  have hl2 : sl2.val.length = 8 := by
    have := congrArg List.length hb2
    unfold bytes at this
    rw [List.length_map, SHAKE256_length] at this
    omega
  have hb3 : bytesA (tsmb sl2) = Spec.SHAKE256 (bytes ρ) 8 := by
    rw [s1_post2, bytesA_from_slice _ _ hl2, hb2]
  refine WP.dspec_bind' (WP.spec_dspec _ _ _ (h_loop_spec (tsmb sl2))) ?_
  intro h hh
  rw [hb3] at hh
  step*
  rw [hl1] at s2
  refine WP.dspec_mono' (outer_loop_partial ip hτ' (bytes ρ) h hh _ ctx3 i
    ⟨by omega, by omega, Vector.replicate 256 0, 8, 0, reprInt_zero,
      by simpa using s2, by omega, ?_⟩) ?_
  · unfold runTo
    have e : i.val = 256 - ip.tau.val := i_post1
    rw [e, Nat.sub_self]
    rfl
  · rintro r ⟨F, cfin, pos', hrun, hr⟩
    exact ⟨cfin, F, SampleInBall_of_runTo sp (by omega) (bytes ρ) F cfin pos' (by rw [← hp.tau]; exact hrun), hr⟩

end Proofs
