import Proofs.TrLaneRust

/-!
# `rej_ntt_poly_x3_tr`: three ExpandA entries and `H(pk)` in the fourth lane of the same permutations

The loop invariant `GInv3` is `GInv` of `Proofs/Sample4.lean` for lanes 0 to 2 (the SHAKE128 samplers of the three
entries) plus `T3` for lane 3: the SHAKE256 sponge of `pk`. `T3` says: after `b` permutations of the group the block counter
is `t = min (t0 + b) (q + 1)`; while `t <= q` lane 3 of the state is the sponge after `t` blocks (`HS M t`); once
`t = q + 1` the saved state `trs` is the sponge after the last block.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

/-! ## The lane-3 sponge invariant -/

def T3 (M : List UInt8) (q t0 b : Nat) (st : St4) (trs : Array U64 25#usize) (t : Usize) : Prop :=
  t.val = min (t0 + b) (q + 1) ∧ (t.val ≤ q → pj st 3 = HS M t.val) ∧
    (t.val = q + 1 → toLanes trs = HS M (q + 1))

theorem T3_succ_le (M : List UInt8) (q t0 b : Nat) (st st2 : St4) (trs trs' : Array U64 25#usize) (t t2 : Usize)
    (h : T3 M q t0 b st trs t) (htq : t.val ≤ q) (ht2 : t2.val = t.val + 1)
    (hp3 : pj st2 3 = HS M (t.val + 1))
    (htrs : t2.val = q + 1 → toLanes trs' = pj st2 3) :
    T3 M q t0 (b + 1) st2 trs' t2 := by
  obtain ⟨h1, _, _⟩ := h
  refine ⟨by omega, fun _ => by rw [ht2]; exact hp3, fun hh => ?_⟩
  rw [htrs hh, hp3]
  congr 1
  omega

theorem T3_succ_gt (M : List UInt8) (q t0 b : Nat) (st st2 : St4) (trs : Array U64 25#usize) (t : Usize)
    (h : T3 M q t0 b st trs t) (htq : ¬ t.val ≤ q) : T3 M q t0 (b + 1) st2 trs t := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨by omega, fun hh => absurd hh htq, fun _ => h3 (by omega)⟩

/-- The `if t <= q` of the loop body: block `t` is XORed into lane 3 while `t <= q`. -/
theorem absorb_if_spec (st : St4) (pk : Slice U8) (tail : Array U64 17#usize) (q t : Usize)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k) :
    (if t <= q then sampling.absorb_block_lane3 st pk tail q t else ok st : RustM St4) ⦃ st1 =>
      (∀ i, i < 3 → pj st1 i = pj st i) ∧ (t.val ≤ q.val → pj st1 3 = xor17 (pj st 3) (blkT (bytes pk) t.val)) ∧
      (¬ t.val ≤ q.val → st1 = st) ⦄ := by
  split
  · rename_i h
    have h' : t.val ≤ q.val := by scalar_tac
    apply WP.spec_mono (absorb_block_lane3_spec st pk tail q t hq h' htail)
    intro st1 ⟨a, b⟩
    exact ⟨a, fun _ => b, fun hh => absurd h' hh⟩
  · rename_i h
    have h' : ¬ t.val ≤ q.val := by scalar_tac
    simp only [WP.spec_ok]
    simp [h']

/-! ## The loop invariant -/

def GCore3 (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat) (M : List UInt8) (q t0 : Nat) (st : St4)
    (trs : Array U64 25#usize) (t : Usize) (p0 p1 p2 : Array U32 312#usize) (j0 j1 j2 : Usize) : Prop :=
  (∀ i, i < 3 → pj st i = Spec.KeccakF1600^[b] (padSt (Mi rho s r i))) ∧
  LaneInv (Tn rho s r N 0) (56 * b) p0 j0 ∧ LaneInv (Tn rho s r N 1) (56 * b) p1 j1 ∧
  LaneInv (Tn rho s r N 2) (56 * b) p2 j2 ∧ T3 M q t0 b st trs t

def MoreIff3 (j0 j1 j2 : Usize) (more : Bool) : Prop :=
  more = true ↔ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256)

abbrev X3 := St4 × Array U64 25#usize × Usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
  Usize × Usize × Usize × Bool

def GInv3 (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat) (M : List UInt8) (q t0 : Nat) (x : X3) : Prop :=
  GCore3 rho s r N b M q t0 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 ∧
  MoreIff3 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2

/-! ## One iteration -/

/-- The tail of the loop body: `more` for the next iteration, from the three fill counts. -/
theorem more_tail_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat) (M : List UInt8) (q t0 : Nat)
    (st2 : St4) (trs1 : Array U64 25#usize) (t1 : Usize) (p01 p11 p21 : Array U32 312#usize) (j01 j11 j21 : Usize)
    (st : St4) (trs : Array U64 25#usize) (t : Usize) (p0 p1 p2 : Array U32 312#usize) (more : Bool)
    (hm : more = true)
    (hcore : GCore3 rho s r N (b + 1) M q t0 st2 trs1 t1 p01 p11 p21 j01 j11 j21) :
    (if j01 < 256#usize then ok (ControlFlow.cont (st2, trs1, t1, p01, p11, p21, j01, j11, j21, true))
      else
        if j11 < 256#usize then ok (ControlFlow.cont (st2, trs1, t1, p01, p11, p21, j01, j11, j21, true))
        else ok (ControlFlow.cont (st2, trs1, t1, p01, p11, p21, j01, j11, j21, decide (j21 < 256#usize)))
      : RustM (ControlFlow X3 (St4 × Array U64 25#usize × Usize × Array U32 312#usize × Array U32 312#usize ×
        Array U32 312#usize))) ⦃ c =>
      match c with
      | .done y => more = false ∧ y = (st, trs, t, p0, p1, p2)
      | .cont x' => more = true ∧ GInv3 rho s r N (b + 1) M q t0 x' ⦄ := by
  split
  · rename_i hj
    simp only [WP.spec_ok]
    exact ⟨hm, hcore, fun _ => Or.inl (by scalar_tac), fun _ => rfl⟩
  split
  · rename_i hj0 hj
    simp only [WP.spec_ok]
    exact ⟨hm, hcore, fun _ => Or.inr (Or.inl (by scalar_tac)), fun _ => rfl⟩
  · rename_i hj0 hj1
    simp only [WP.spec_ok]
    refine ⟨hm, hcore, ?_, ?_⟩
    · intro hh
      have h2 : j21 < 256#usize := of_decide_eq_true hh
      right; right; scalar_tac
    · intro hh
      rcases hh with hh | hh | hh
      · exfalso; scalar_tac
      · exfalso; scalar_tac
      · have h2 : j21.val < 256 := hh
        show decide (j21 < 256#usize) = true
        exact decide_eq_true (by scalar_tac)


theorem rej3_body_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8)
    (tail : Array U64 17#usize) (q : Usize) (t0 N b : Nat) (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (st : St4) (trs : Array U64 25#usize) (t : Usize) (p0 p1 p2 : Array U32 312#usize) (j0 j1 j2 : Usize) (more : Bool)
    (hb : more = true → 56 * (b + 1) ≤ N)
    (h : GInv3 rho s r N b (bytes pk) q.val t0 (st, trs, t, p0, p1, p2, j0, j1, j2, more)) :
    sampling.rej_ntt_poly_x3_tr_loop.body pk tail q st trs t p0 p1 p2 j0 j1 j2 more ⦃ c =>
      match c with
      | .done y => more = false ∧ y = (st, trs, t, p0, p1, p2)
      | .cont x' => more = true ∧ GInv3 rho s r N (b + 1) (bytes pk) q.val t0 x' ⦄ := by
  obtain ⟨⟨hst, hl0, hl1, hl2, hT⟩, hmore⟩ := h
  have hT' := hT
  obtain ⟨hT1, hT2, hT3⟩ := hT'
  simp only [sampling.rej_ntt_poly_x3_tr_loop.body]
  split
  · rename_i hm
    refine WP.spec_bind (absorb_if_spec st pk tail q t hq htail) ?_
    rintro st1 ⟨h1a, h1b, h1c⟩
    step with keccak_f1600_x4_spec
    have hst2 : ∀ i, i < 3 → pj st2 i = Spec.KeccakF1600^[b + 1] (padSt (Mi rho s r i)) := by
      intro i hi
      rw [st2_post i (by omega), h1a i hi, hst i hi, Function.iterate_succ_apply']
    have hTn : ∀ (i : Nat), i < 3 → ∀ p < 168, (Tn rho s r N i)[168 * b + p]? = some (KM.sb (pj st2 i) p) := by
      intro i hi p hp
      rw [hst2 i hi]
      have hb' := hb hm
      exact shake_stream _ (Mi_length rho s r i) N b p hp (by omega)
    have b0 := rej_ntt_lane_x4_spec (Tn rho s r N 0) st2 0#usize b (by simp) (hTn 0 (by omega)) p0 j0 hl0
    have b1 := rej_ntt_lane_x4_spec (Tn rho s r N 1) st2 1#usize b (by simp) (hTn 1 (by omega)) p1 j1 hl1
    have b2 := rej_ntt_lane_x4_spec (Tn rho s r N 2) st2 2#usize b (by simp) (hTn 2 (by omega)) p2 j2 hl2
    step with b0
    step with b1
    step with b2
    have hmax : pk.val.length ≤ Usize.max := pk.property
    have hlen : (bytes pk).length = pk.val.length := by simp [bytes]
    have hcore0 : ∀ (j01 j11 j21 : Usize) (p01 p11 p21 : Array U32 312#usize),
        LaneInv (Tn rho s r N 0) (56 * (b + 1)) p01 j01 → LaneInv (Tn rho s r N 1) (56 * (b + 1)) p11 j11 →
        LaneInv (Tn rho s r N 2) (56 * (b + 1)) p21 j21 → ∀ (trs1 : Array U64 25#usize) (t1 : Usize),
        T3 (bytes pk) q.val t0 (b + 1) st2 trs1 t1 →
        GCore3 rho s r N (b + 1) (bytes pk) q.val t0 st2 trs1 t1 p01 p11 p21 j01 j11 j21 :=
      fun j01 j11 j21 p01 p11 p21 a1 a2 a3 trs1 t1 a4 => ⟨hst2, a1, a2, a3, a4⟩
    by_cases htq : t ≤ q
    · have htq' : t.val ≤ q.val := by scalar_tac
      have hp3 : pj st2 3 = HS (bytes pk) (t.val + 1) := by
        rw [st2_post 3 (by omega), h1b htq', hT2 htq', HS_succ _ _ (by omega),
          xorBlock_eq_xor17 _ _ (blkT_length _ _ (by omega)).le]
      rw [if_pos htq]
      step as ⟨t2, ht2⟩
      step as ⟨i2, hi2⟩
      by_cases he : t2 = i2
      · rw [if_pos he]
        step with lane3_state_spec st2 as ⟨a, ha⟩
        exact more_tail_spec rho s r N b (bytes pk) q.val t0 st2 a t2 p01 p11 p21 j01 j11 j21 st trs t p0 p1 p2 more hm
          (hcore0 _ _ _ _ _ _ j01_post j11_post j21_post a t2
            (T3_succ_le _ _ _ _ _ _ _ _ _ _ hT htq' ht2 hp3 (fun _ => ha)))
      · rw [if_neg he]
        simp only [Std.bind_tc_ok]
        exact more_tail_spec rho s r N b (bytes pk) q.val t0 st2 trs t2 p01 p11 p21 j01 j11 j21 st trs t p0 p1 p2 more hm
          (hcore0 _ _ _ _ _ _ j01_post j11_post j21_post trs t2
            (T3_succ_le _ _ _ _ _ _ _ _ _ _ hT htq' ht2 hp3
              (fun hh => absurd (UScalar.eq_of_val_eq (by omega)) he)))
    · rw [if_neg htq]
      simp only [Std.bind_tc_ok]
      have htq' : ¬ t.val ≤ q.val := by scalar_tac
      exact more_tail_spec rho s r N b (bytes pk) q.val t0 st2 trs t p01 p11 p21 j01 j11 j21 st trs t p0 p1 p2 more hm
        (hcore0 _ _ _ _ _ _ j01_post j11_post j21_post trs t (T3_succ_gt _ _ _ _ _ _ _ _ hT htq'))
  · rename_i hm
    have hmf : more = false := by simpa using hm
    simp only [WP.spec_ok]
    exact ⟨hmf, trivial⟩


/-! ## The loop -/

def runLoop3 (pk : Slice U8) (tail : Array U64 17#usize) (q : Usize) (x : X3) :
    RustM (St4 × Array U64 25#usize × Usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize) :=
  sampling.rej_ntt_poly_x3_tr_loop pk tail q x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
    x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2

/-- The lane-3 part of the result: the block counter is at most `q + 1`, and either lane 3 of the state is the sponge after
`t` blocks or the saved state is the sponge after the last block. -/
def T3End (M : List UInt8) (q : Nat) (st : St4) (trs : Array U64 25#usize) (t : Usize) : Prop :=
  t.val ≤ q + 1 ∧ (t.val ≤ q → pj st 3 = HS M t.val) ∧ (t.val = q + 1 → toLanes trs = HS M (q + 1))

theorem T3_end (M : List UInt8) (q t0 b : Nat) (st : St4) (trs : Array U64 25#usize) (t : Usize)
    (h : T3 M q t0 b st trs t) : T3End M q st trs t :=
  ⟨by have := h.1; omega, h.2.1, h.2.2⟩

def Fin3 (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N : Nat) (M : List UInt8) (q : Nat)
    (res : St4 × Array U64 25#usize × Usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize) : Prop :=
  FinL (Tn rho s r N 0) N res.2.2.2.1 ∧ FinL (Tn rho s r N 1) N res.2.2.2.2.1 ∧ FinL (Tn rho s r N 2) N res.2.2.2.2.2 ∧
    T3End M q res.1 res.2.1 res.2.2.1

theorem more_lt3 (rho : Array U8 32#usize) (s r : Array U8 4#usize) (G b : Nat) (M : List UInt8) (q t0 : Nat)
    (hfin : ∀ i, i < 3 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) (hbG : b ≤ G) (x : X3)
    (h : GInv3 rho s r (56 * G) b M q t0 x) (hm : x.2.2.2.2.2.2.2.2.2 = true) : b < G := by
  by_contra hcon
  have hbe : b = G := by omega
  subst hbe
  obtain ⟨⟨_, hl0, hl1, hl2, _⟩, hmore⟩ := h
  have hany := hmore.mp hm
  have f0 := hfin 0 (by omega)
  have f1 := hfin 1 (by omega)
  have f2 := hfin 2 (by omega)
  have e0 : min 256 x.2.2.2.2.2.2.1.val = (stA (Tn rho s r (56 * b) 0) (56 * b)).2 := hl0.2.1
  have e1 : min 256 x.2.2.2.2.2.2.2.1.val = (stA (Tn rho s r (56 * b) 1) (56 * b)).2 := hl1.2.1
  have e2 : min 256 x.2.2.2.2.2.2.2.2.1.val = (stA (Tn rho s r (56 * b) 2) (56 * b)).2 := hl2.2.1
  rcases hany with h0 | h0 | h0 <;> omega

theorem rej3_loop_step (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8) (tail : Array U64 17#usize)
    (q : Usize) (t0 G b : Nat) (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (hfin : ∀ i, i < 3 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) (hbG : b ≤ G) (x : X3)
    (h : GInv3 rho s r (56 * G) b (bytes pk) q.val t0 x)
    (IH : ∀ x', b + 1 ≤ G → GInv3 rho s r (56 * G) (b + 1) (bytes pk) q.val t0 x' →
      runLoop3 pk tail q x' ⦃ res => Fin3 rho s r (56 * G) (bytes pk) q.val res ⦄) :
    runLoop3 pk tail q x ⦃ res => Fin3 rho s r (56 * G) (bytes pk) q.val res ⦄ := by
  obtain ⟨st, trs, t, p0, p1, p2, j0, j1, j2, more⟩ := x
  have hbody := rej3_body_spec rho s r pk tail q t0 (56 * G) b hq htail st trs t p0 p1 p2 j0 j1 j2 more
    (fun hm => by have := more_lt3 rho s r G b (bytes pk) q.val t0 hfin hbG _ h hm; omega) h
  obtain ⟨res, hr, hp⟩ := WP.spec_imp_exists hbody
  unfold runLoop3 sampling.rej_ntt_poly_x3_tr_loop
  dsimp only
  rw [loop]
  dsimp only
  rw [hr]
  cases res with
  | cont x' =>
    obtain ⟨hm, hx'⟩ := hp
    have := more_lt3 rho s r G b (bytes pk) q.val t0 hfin hbG _ h hm
    exact IH x' (by omega) hx'
  | done y =>
    obtain ⟨hmf, rfl⟩ := hp
    obtain ⟨⟨_, hl0, hl1, hl2, hT⟩, hmore⟩ := h
    have hn : ¬ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256) := fun hh => by
      have := hmore.mpr hh; simp [hmf] at this
    simp only [not_or, not_lt] at hn
    simp only [WP.spec_ok]
    exact ⟨lane_fin _ _ _ (by omega) _ _ hl0 hn.1, lane_fin _ _ _ (by omega) _ _ hl1 hn.2.1,
      lane_fin _ _ _ (by omega) _ _ hl2 hn.2.2, T3_end _ _ _ _ _ _ _ hT⟩

theorem rej3_loop_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8) (tail : Array U64 17#usize)
    (q : Usize) (t0 G : Nat) (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (hfin : ∀ i, i < 3 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) :
    ∀ k b, G - b = k → b ≤ G → ∀ x, GInv3 rho s r (56 * G) b (bytes pk) q.val t0 x →
      runLoop3 pk tail q x ⦃ res => Fin3 rho s r (56 * G) (bytes pk) q.val res ⦄ := by
  intro k
  induction k with
  | zero =>
    intro b hk hbG x h
    exact rej3_loop_step rho s r pk tail q t0 G b hq htail hfin hbG x h (fun x' hb _ => by omega)
  | succ k ih =>
    intro b hk hbG x h
    exact rej3_loop_step rho s r pk tail q t0 G b hq htail hfin hbG x h
      (fun x' hb hx' => ih (b + 1) (by omega) hb x' hx')

/-! ### Partial correctness of the loop -/

theorem GInv3_fuel (rho : Array U8 32#usize) (s r : Array U8 4#usize) (b N N' : Nat) (M : List UInt8) (q t0 : Nat)
    (hb : 56 * b ≤ N) (hN : N ≤ N') (x : X3) (h : GInv3 rho s r N b M q t0 x) : GInv3 rho s r N' b M q t0 x := by
  obtain ⟨⟨hst, hl0, hl1, hl2, hT⟩, hm⟩ := h
  exact ⟨⟨hst, LaneInv_fuel rho s r 0 b N N' hb hN _ _ hl0, LaneInv_fuel rho s r 1 b N N' hb hN _ _ hl1,
    LaneInv_fuel rho s r 2 b N N' hb hN _ _ hl2, hT⟩, hm⟩

theorem rej3_loop_partial (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8)
    (tail : Array U64 17#usize) (q : Usize) (t0 : Nat) (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k) (x : X3)
    (hx : ∃ b, GInv3 rho s r (56 * b) b (bytes pk) q.val t0 x) :
    runLoop3 pk tail q x ⦃ res => ∃ (F : Nat) (P : Nat → Poly),
      (∀ i, i < 3 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) ∧
      FinP (P 0) res.2.2.2.1 ∧ FinP (P 1) res.2.2.2.2.1 ∧ FinP (P 2) res.2.2.2.2.2 ∧
      T3End (bytes pk) q.val res.1 res.2.1 res.2.2.1 ⦄div := by
  unfold runLoop3 sampling.rej_ntt_poly_x3_tr_loop
  refine loop.dspec_inv _ (fun x : X3 => ∃ b, GInv3 rho s r (56 * b) b (bytes pk) q.val t0 x) ?_ ?_ x hx
  · rintro ⟨st, trs, t, p0, p1, p2, j0, j1, j2, more⟩ ⟨b, hI⟩
    have hI' := GInv3_fuel rho s r b (56 * b) (56 * (b + 1)) (bytes pk) q.val t0 le_rfl (by omega) _ hI
    have hbody := rej3_body_spec rho s r pk tail q t0 (56 * (b + 1)) b hq htail st trs t p0 p1 p2 j0 j1 j2 more
      (fun _ => le_rfl) hI'
    refine WP.dspec_mono' (WP.spec_dspec _ _ _ hbody) ?_
    rintro (x' | y) h
    · exact ⟨b + 1, h.2⟩
    · obtain ⟨hmf, rfl⟩ := h
      obtain ⟨⟨_, hl0, hl1, hl2, hT⟩, hmore⟩ := hI
      have hn : ¬ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256) := fun hh => by
        have := hmore.mpr hh; simp [hmf] at this
      simp only [not_or, not_lt] at hn
      have e0 : min 256 j0.val = (stA (Tn rho s r (56 * b) 0) (56 * b)).2 := hl0.2.1
      have e1 : min 256 j1.val = (stA (Tn rho s r (56 * b) 1) (56 * b)).2 := hl1.2.1
      have e2 : min 256 j2.val = (stA (Tn rho s r (56 * b) 2) (56 * b)).2 := hl2.2.1
      have hfin : ∀ i, i < 3 → Spec.RejNTTPoly (56 * b) (Mi rho s r i) =
          some (stA (Tn rho s r (56 * b) i) (56 * b)).1 := by
        intro i hi
        apply rej_some_of_fin
        show 256 ≤ (stA (Tn rho s r (56 * b) i) (56 * b)).2
        interval_cases i <;> omega
      refine ⟨56 * b, fun i => (stA (Tn rho s r (56 * b) i) (56 * b)).1, hfin, ?_, ?_, ?_, T3_end _ _ _ _ _ _ _ hT⟩
      · exact lane_fin _ _ _ le_rfl _ _ hl0 hn.1
      · exact lane_fin _ _ _ le_rfl _ _ hl1 hn.2.1
      · exact lane_fin _ _ _ le_rfl _ _ hl2 hn.2.2


/-! ## The group sampler -/

theorem set_lane3_pj (st st1 : St4) (s : Array U64 25#usize)
    (h : ∀ k, k < 25 → ∀ i, i < 4 → ln (at4 st1 k) i = if i = 3 then toU64 (s.val[k]!) else ln (at4 st k) i) :
    (∀ i, i < 3 → pj st1 i = pj st i) ∧ pj st1 3 = toLanes s := by
  refine ⟨fun i hi => ?_, ?_⟩
  · apply st_ext
    intro k hk
    rw [pj_getElem _ _ _ hk, pj_getElem _ _ _ hk, h k hk i (by omega), if_neg (by omega)]
  · apply st_ext
    intro k hk
    rw [pj_getElem _ _ _ hk, h k hk 3 (by omega), if_pos rfl,
      getElem!_pos (toLanes s) k (by simpa using hk), toLanes_get s k hk]
    rw [getElem!_pos s.val k (by rw [len25]; exact hk)]

theorem init3_GInv (rho : Array U8 32#usize) (s r : Array U8 4#usize) (M : List UInt8) (q t0 N : Nat)
    (st1 : St4) (trs0 : Array U64 25#usize) (t0u : Usize) (ht0 : t0u.val = t0) (ht0q : t0 ≤ q + 1)
    (hs0 : toLanes trs0 = HS M t0)
    (hst : ∀ i, i < 3 → pj st1 i = padSt (Mi rho s r i)) (h3 : pj st1 3 = toLanes trs0) :
    GInv3 rho s r N 0 M q t0 (st1, trs0, t0u, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32,
      Array.repeat 312#usize 0#u32, 0#usize, 0#usize, 0#usize, true) := by
  have hl : ∀ T : List UInt8, LaneInv T (56 * 0) (Array.repeat 312#usize 0#u32) 0#usize := by
    intro T
    have hj0 : (0#usize).val = 0 := rfl
    have h0 : stA T (56 * 0) = (Poly.zero, 0) := by simp [stA]
    refine ⟨by rw [hj0]; omega, ?_, ?_⟩
    · rw [hj0, h0]; rfl
    · rw [h0]; intro k hk; exact absurd hk (by simp)
  refine ⟨⟨fun i hi => ?_, hl _, hl _, hl _, ?_⟩, ?_⟩
  · rw [hst i hi]; rfl
  · refine ⟨by simp [ht0]; omega, fun hh => ?_, fun hh => ?_⟩
    · show pj st1 3 = HS M t0u.val
      rw [h3, hs0, ht0]
    · show toLanes trs0 = HS M (q + 1)
      rw [hs0]
      show HS M t0 = HS M (q + 1)
      have : t0u.val = q + 1 := hh
      rw [← this, ht0]
  · show true = true ↔ _
    exact ⟨fun _ => Or.inl (show (0#usize).val < 256 by simp), fun _ => rfl⟩

theorem rej_ntt_poly_x3_tr_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8)
    (tail : Array U64 17#usize) (q : Usize) (trs0 : Array U64 25#usize) (t0 : Usize)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (ht0 : t0.val ≤ q.val + 1) (hs0 : toLanes trs0 = HS (bytes pk) t0.val)
    (F : Nat) (P : Nat → Poly) (hP : ∀ i, i < 3 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) :
    sampling.rej_ntt_poly_x3_tr rho s r pk tail q trs0 t0 ⦃ res =>
      (∀ (i : Nat) (hi : i < res.1.val.length), i < 3 → Repr (res.1.val[i]) (P i)) ∧
      res.2.2.val ≤ q.val + 1 ∧ toLanes res.2.1 = HS (bytes pk) res.2.2.val ⦄ := by
  have hG : F ≤ 56 * ((F + 55) / 56) := by omega
  set G := (F + 55) / 56 with hGdef
  have hP' : ∀ i, i < 3 → Spec.RejNTTPoly (56 * G) (Mi rho s r i) = some (P i) :=
    fun i hi => RejNTTPoly_mono _ _ _ _ (hP i hi) hG
  have hfinP : ∀ i, i < 3 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2 ∧
      (stA (Tn rho s r (56 * G) i) (56 * G)).1 = P i := fun i hi => rej_eq_some _ _ _ (hP' i hi)
  have hfin : ∀ i, i < 3 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2 := fun i hi => (hfinP i hi).1
  unfold sampling.rej_ntt_poly_x3_tr
  step as ⟨st, hst⟩
  step with set_lane3_spec st trs0 as ⟨st1, hst1⟩
  obtain ⟨hA, hB⟩ := set_lane3_pj st st1 trs0 hst1
  have hinit := init3_GInv rho s r (bytes pk) q.val t0.val (56 * G) st1 trs0 t0 rfl ht0 hs0
    (fun i hi => by rw [hA i hi, hst i (by omega)]; rfl) hB
  have hloop := rej3_loop_spec rho s r pk tail q t0.val G hq htail hfin G 0 (by omega) (by omega) _ hinit
  unfold runLoop3 at hloop
  dsimp only at hloop
  step with hloop
  have hres := st2_post
  obtain ⟨hf0, hf1, hf2, hte1, hte2, hte3⟩ := hres
  dsimp only at hf0 hf1 hf2 hte1 hte2 hte3
  have hfin0 := finP_of _ _ _ _ hf0 (hfinP 0 (by omega)).2
  have hfin1 := finP_of _ _ _ _ hf1 (hfinP 1 (by omega)).2
  have hfin2 := finP_of _ _ _ _ hf2 (hfinP 2 (by omega)).2
  by_cases htq : t ≤ q
  · have htq' : t.val ≤ q.val := by scalar_tac
    rw [if_pos htq]
    step with lane3_state_spec st2 as ⟨ts, hts⟩
    step*
    refine ⟨?_, hte1, by rw [hts]; exact hte2 htq'⟩
    intro i hi hi3
    interval_cases i
    · exact repr_of_first_256 _ _ _ a_post hfin0
    · exact repr_of_first_256 _ _ _ a1_post hfin1
    · exact repr_of_first_256 _ _ _ a2_post hfin2
  · have htq' : ¬ t.val ≤ q.val := by scalar_tac
    rw [if_neg htq]
    simp only [Std.bind_tc_ok]
    step*
    refine ⟨?_, hte1, hte3 (by omega) ▸ (by rw [show t.val = q.val + 1 by omega])⟩
    intro i hi hi3
    interval_cases i
    · exact repr_of_first_256 _ _ _ a_post hfin0
    · exact repr_of_first_256 _ _ _ a1_post hfin1
    · exact repr_of_first_256 _ _ _ a2_post hfin2

attribute [local step] lane3_state_spec

theorem rej_ntt_poly_x3_tr_partial (rho : Array U8 32#usize) (s r : Array U8 4#usize) (pk : Slice U8)
    (tail : Array U64 17#usize) (q : Usize) (trs0 : Array U64 25#usize) (t0 : Usize)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (ht0 : t0.val ≤ q.val + 1) (hs0 : toLanes trs0 = HS (bytes pk) t0.val) :
    sampling.rej_ntt_poly_x3_tr rho s r pk tail q trs0 t0 ⦃ res => ∃ (F : Nat) (P : Nat → Poly),
      (∀ i, i < 3 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) ∧
      (∀ (i : Nat) (hi : i < res.1.val.length), i < 3 → Repr (res.1.val[i]) (P i)) ∧
      res.2.2.val ≤ q.val + 1 ∧ toLanes res.2.1 = HS (bytes pk) res.2.2.val ⦄div := by
  unfold sampling.rej_ntt_poly_x3_tr
  step as ⟨st, hst⟩
  step with set_lane3_spec st trs0 as ⟨st1, hst1⟩
  obtain ⟨hA, hB⟩ := set_lane3_pj st st1 trs0 hst1
  have hinit := init3_GInv rho s r (bytes pk) q.val t0.val (56 * 0) st1 trs0 t0 rfl ht0 hs0
    (fun i hi => by rw [hA i hi, hst i (by omega)]; rfl) hB
  have hloop := rej3_loop_partial rho s r pk tail q t0.val hq htail
    (st1, trs0, t0, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32,
      0#usize, 0#usize, 0#usize, true) ⟨0, hinit⟩
  unfold runLoop3 at hloop
  dsimp only at hloop
  step with hloop
  obtain ⟨stA, trsA, tA, pa, pb, pc⟩ := t
  obtain ⟨hte1, hte2, hte3⟩ := st2_post5
  dsimp only at p11 p21 st2_post4 hte1 hte2 hte3
  have hfin0 := p11
  have hfin1 := p21
  have hfin2 := st2_post4
  step*
  by_cases htq : tA ≤ q
  · have htq' : tA.val ≤ q.val := by scalar_tac
    rw [if_pos htq]
    step with lane3_state_spec stA as ⟨ts, hts⟩
    step*
    refine ⟨st2, trs, p01, ?_, hte1, by rw [hts]; exact hte2 htq'⟩
    intro i hi hi3
    interval_cases i
    · exact repr_of_first_256 _ _ _ a_post hfin0
    · exact repr_of_first_256 _ _ _ a1_post hfin1
    · exact repr_of_first_256 _ _ _ a2_post hfin2
  · have htq' : ¬ tA.val ≤ q.val := by scalar_tac
    rw [if_neg htq]
    simp only [Std.bind_tc_ok]
    step*
    refine ⟨st2, trs, p01, ?_, hte1, ?_⟩
    · intro i hi hi3
      interval_cases i
      · exact repr_of_first_256 _ _ _ a_post hfin0
      · exact repr_of_first_256 _ _ _ a1_post hfin1
      · exact repr_of_first_256 _ _ _ a2_post hfin2
    · rw [show tA.val = q.val + 1 by omega]
      exact hte3 (by omega)

end Proofs
