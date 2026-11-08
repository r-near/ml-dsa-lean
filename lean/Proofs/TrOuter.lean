import Proofs.TrGroup

/-!
# `expand_a_tr_into_x4`: the 3+1 ExpandA with `tr = H(pk, 64)` in the fourth lane

The outer function of `docs/assurance.md` section 1.9. Its group loop takes three ExpandA entries per iteration through
`rej_ntt_poly_x3_tr` (proved in `TrGroup`), carrying the SHAKE256 sponge of `pk` as `(trs, t)`; the rest of the matrix is
`expand_a_from_x4` (ExpandA4) and the unreached blocks of the hash are finished by `tr_finish_scalar` (TrLaneRust).
The schedule (`g3`) is arbitrary here: correctness does not depend on it.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

/-! ## The group loop body, partial correctness -/

theorem tr_body_partial {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8) (n q g3 : Usize)
    (tail : Array U64 17#usize) (a : Array (Array (Array U32 256#usize) L) K)
    (trs : Array U64 25#usize) (t first g : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (ht : t.val ≤ q.val + 1) (hs : toLanes trs = HS (bytes pk) t.val)
    (F : Nat) (Pf : Nat → Poly) (h : GoodA rho n.val F Pf a first.val) :
    sampling.expand_a_tr_into_x4_loop.body rho pk n q g3 tail a trs t first g ⦃ c =>
      match c with
      | .done y => ¬ (first.val < n.val ∧ g.val < g3.val) ∧ y = (a, trs, t, first)
      | .cont (a', trs', t', first', g') => first'.val = first.val + 3 ∧ g'.val = g.val + 1 ∧
          t'.val ≤ q.val + 1 ∧ toLanes trs' = HS (bytes pk) t'.val ∧
          ∃ (F' : Nat) (Pf' : Nat → Poly), GoodA rho n.val F' Pf' a' first'.val ⦄div := by
  unfold sampling.expand_a_tr_into_x4_loop.body
  split
  · rename_i hlt
    have hf : first.val < n.val := by scalar_tac
    split
    · rename_i hgt
      step*
      step with rej_ntt_poly_x3_tr_partial rho (Array.make 4#usize [i1, i3, i5, i6] (by simp))
        (Array.make 4#usize [i8, i10, i12, i13] (by simp)) pk tail q trs t hq htail ht hs
      obtain ⟨pa, tr2, tt2⟩ := t2
      dsimp only at polys_post2 polys_post3 polys_post4
      have hlenA : a.val.length = K.val := a.property
      have hn1 : 1 ≤ n.val := by omega
      have he0 : e0.val < n.val := by rw [e0_post]; split_ifs <;> omega
      have he1 : e1.val < n.val := by rw [e1_post]; split_ifs <;> omega
      have he2 : e2.val < n.val := by rw [e2_post]; split_ifs <;> omega
      have hdiv : ∀ e : Nat, e < n.val → e / L.val < K.val := fun e he =>
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hmod : ∀ e : Nat, e % L.val < L.val := fun e => Nat.mod_lt _ hL
      have hi7 : i7.val < K.val := by rw [i7_post]; exact hdiv _ he0
      have hi9 : i9.val < K.val := by rw [i9_post]; exact hdiv _ he1
      have hi11 : i11.val < K.val := by rw [i11_post]; exact hdiv _ he2
      have hj0 : i.val < L.val := by rw [i_post]; exact hmod _
      have hj1 : i2.val < L.val := by rw [i2_post]; exact hmod _
      have hj2 : i4.val < L.val := by rw [i4_post]; exact hmod _
      step*
      obtain ⟨wa2, wb2⟩ := a2
      step*
      obtain ⟨wa6, wb6⟩ := a6
      step*
      obtain ⟨wa10, wb10⟩ := a10
      step*
      refine (WP.dspec_ok _).2 ?_
      subst a1_post2 a4_post2 a8_post2
      have hxr : ∀ (k : Nat) (hk : k < pa.val.length), k < 3 → Repr (pa.val[k]) (trs2 k) :=
        fun k hk hk3 => polys_post2 k hk hk3
      have hx0 := hxr 0 a1 (by omega)
      have hx1 := hxr 1 a4 (by omega)
      have hx2 := hxr 2 a8 (by omega)
      have hmod256 : ∀ e : Nat, e % L.val < 256 := fun e => lt_trans (hmod e) hLs
      have hdiv256 : ∀ e : Nat, e < n.val → e / L.val < 256 := fun e he => lt_trans (hdiv e he) hK
      have hs0 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 0
          = pSeed (bytesA rho) (e0.val / L.val) (e0.val % L.val) :=
        seed_of_cast rho e0.val L.val i1 i8 i i7 i1_post i8_post i_post i7_post (by rw [i_post]; exact hmod256 _)
          (by rw [i7_post]; exact hdiv256 _ he0)
      have hs1 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 1
          = pSeed (bytesA rho) (e1.val / L.val) (e1.val % L.val) :=
        seed_of_cast rho e1.val L.val i3 i10 i2 i9 i3_post i10_post i2_post i9_post (by rw [i2_post]; exact hmod256 _)
          (by rw [i9_post]; exact hdiv256 _ he1)
      have hs2 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 2
          = pSeed (bytesA rho) (e2.val / L.val) (e2.val % L.val) :=
        seed_of_cast rho e2.val L.val i5 i12 i4 i11 i5_post i12_post i4_post i11_post (by rw [i4_post]; exact hmod256 _)
          (by rw [i11_post]; exact hdiv256 _ he2)
      have hr0 := polys_post1 0 (by omega)
      have hr1 := polys_post1 1 (by omega)
      have hr2 := polys_post1 2 (by omega)
      rw [hs0] at hr0
      rw [hs1] at hr1
      rw [hs2] at hr2
      have dup : ∀ (x y : Nat) (P Q : Poly),
          Spec.RejNTTPoly polys (pSeed (bytesA rho) (x / L.val) (x % L.val)) = some P →
          Spec.RejNTTPoly polys (pSeed (bytesA rho) (y / L.val) (y % L.val)) = some Q → x = y → P = Q := by
        intro x y P Q h1 h2 hxy
        subst hxy
        exact Option.some.inj (h1.symm.trans h2)
      have hw2 : wb2 = a.set i7 := a2_post3
      have hw6 : wb6 = (wb2 a3).set i9 := a6_post3
      have hw10 : wb10 = (wb6 a7).set i11 := a10_post3
      obtain ⟨o1, n1⟩ := wstep a e0.val i7 i _ (trs2 0) wa2 hL i7_post i_post (by omega) a2_post2 hx0
      have eq1 : wb2 a3 = a.set i7 (wa2.set i (pa.val[0]'a1)) := by rw [hw2, a3_post]
      rw [← eq1] at o1 n1
      have hl1 : i9.val < (wb2 a3).val.length := by have := (wb2 a3).property; omega
      obtain ⟨o2, n2⟩ := wstep (wb2 a3) e1.val i9 i2 _ (trs2 1) wa6 hL i9_post i2_post hl1 a6_post2 hx1
      have eq2 : wb6 a7 = (wb2 a3).set i9 (wa6.set i2 (pa.val[1]'a4)) := by rw [hw6, a7_post]
      rw [← eq2] at o2 n2
      have hl2 : i11.val < (wb6 a7).val.length := by have := (wb6 a7).property; omega
      obtain ⟨o3, n3⟩ := wstep (wb6 a7) e2.val i11 i4 _ (trs2 2) wa10 hL i11_post i4_post hl2 a10_post2 hx2
      have eq3 : wb10 a11 = (wb6 a7).set i11 (wa10.set i4 (pa.val[2]'a8)) := by rw [hw10, a11_post]
      rw [← eq3] at o3 n3
      have mkc : ∀ (x y : Nat) (P Q : Poly), (x = y → P = Q) → (x ≠ y ∨ P = Q) := fun x y P Q h => by
        by_cases hh : x = y
        · exact Or.inr (h hh)
        · exact Or.inl hh
      have d10 : e1.val = e0.val → trs2 1 = trs2 0 := dup _ _ _ _ hr1 hr0
      have d20 : e2.val = e0.val → trs2 2 = trs2 0 := dup _ _ _ _ hr2 hr0
      have d21 : e2.val = e1.val → trs2 2 = trs2 1 := dup _ _ _ _ hr2 hr1
      have F0 := o3 _ _ (o2 _ _ n1 (mkc _ _ _ _ d10)) (mkc _ _ _ _ d20)
      have F1 := o3 _ _ n2 (mkc _ _ _ _ d21)
      have F2 := n3
      have hge0 : first.val ≤ e0.val := by rw [e0_post]; split_ifs <;> omega
      have hge1 : first.val ≤ e1.val := by rw [e1_post]; split_ifs <;> omega
      have hge2 : first.val ≤ e2.val := by rw [e2_post]; split_ifs <;> omega
      have hE0 : first.val + 0 < n.val → e0.val = first.val + 0 := fun hh => by rw [e0_post, if_pos hh]
      have hE1 : first.val + 1 < n.val → e1.val = first.val + 1 := fun hh => by rw [e1_post, if_pos hh]
      have hE2 : first.val + 2 < n.val → e2.val = first.val + 2 := fun hh => by rw [e2_post, if_pos hh]
      refine ⟨by omega, by omega, polys_post3, polys_post4, max F polys,
        fun e => if e < first.val then Pf e else trs2 (e - first.val), ?_⟩
      intro e he1 he2
      rw [first1_post] at he1
      by_cases hold' : e < first.val
      · obtain ⟨hr, hent⟩ := h e hold' he2
        show Spec.RejNTTPoly (max F polys) _ = some (if e < first.val then Pf e else trs2 (e - first.val)) ∧
          EntAt (wb10 a11) e (if e < first.val then Pf e else trs2 (e - first.val))
        rw [if_pos hold']
        refine ⟨RejNTTPoly_mono _ _ _ _ hr (le_max_left _ _), ?_⟩
        exact o3 e _ (o2 e _ (o1 e _ hent (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega))
      · show Spec.RejNTTPoly (max F polys) _ = some (if e < first.val then Pf e else trs2 (e - first.val)) ∧
          EntAt (wb10 a11) e (if e < first.val then Pf e else trs2 (e - first.val))
        rw [if_neg hold']
        rcases (by omega : e = first.val + 0 ∨ e = first.val + 1 ∨ e = first.val + 2) with hk | hk | hk
        · have hEk := hE0 (by omega)
          have hk' : e - first.val = 0 := by omega
          rw [hk']
          rw [hEk, ← hk] at hr0 F0
          exact ⟨RejNTTPoly_mono _ _ _ _ hr0 (le_max_right _ _), F0⟩
        · have hEk := hE1 (by omega)
          have hk' : e - first.val = 1 := by omega
          rw [hk']
          rw [hEk, ← hk] at hr1 F1
          exact ⟨RejNTTPoly_mono _ _ _ _ hr1 (le_max_right _ _), F1⟩
        · have hEk := hE2 (by omega)
          have hk' : e - first.val = 2 := by omega
          rw [hk']
          rw [hEk, ← hk] at hr2 F2
          exact ⟨RejNTTPoly_mono _ _ _ _ hr2 (le_max_right _ _), F2⟩
    · rename_i hgt
      simp only [WP.dspec_ok]
      exact ⟨fun hh => hgt (by scalar_tac), trivial⟩
  · rename_i hlt
    simp only [WP.dspec_ok]
    exact ⟨fun hh => hlt (by scalar_tac), trivial⟩


/-! ## The group loop, partial correctness -/

theorem tr_loop_partial {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8) (n q g3 : Usize)
    (tail : Array U64 17#usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (a : Array (Array (Array U32 256#usize) L) K) (trs : Array U64 25#usize) (t first g : Usize)
    (ht : t.val ≤ q.val + 1) (hs : toLanes trs = HS (bytes pk) t.val)
    (F : Nat) (Pf : Nat → Poly) (h : GoodA rho n.val F Pf a first.val) :
    sampling.expand_a_tr_into_x4_loop rho pk a n q g3 tail trs t first g ⦃ y =>
      (∃ (F' : Nat) (Pf' : Nat → Poly), GoodA rho n.val F' Pf' y.1 y.2.2.2.val) ∧
      y.2.2.1.val ≤ q.val + 1 ∧ toLanes y.2.1 = HS (bytes pk) y.2.2.1.val ⦄div := by
  unfold sampling.expand_a_tr_into_x4_loop
  refine loop.dspec_inv _ (fun x : Array (Array (Array U32 256#usize) L) K × Array U64 25#usize × Usize × Usize × Usize =>
    (∃ (F : Nat) (Pf : Nat → Poly), GoodA rho n.val F Pf x.1 x.2.2.2.1.val) ∧
      x.2.2.1.val ≤ q.val + 1 ∧ toLanes x.2.1 = HS (bytes pk) x.2.2.1.val) ?_ ?_ (a, trs, t, first, g)
    ⟨⟨F, Pf, h⟩, ht, hs⟩
  rintro ⟨a', trs', t', first', g'⟩ ⟨⟨F', Pf', hI⟩, ht', hs'⟩
  refine WP.dspec_mono' (tr_body_partial rho pk n q g3 tail a' trs' t' first' g' hn hL hLs hK hnKL hq htail ht' hs'
    F' Pf' hI) ?_
  rintro (⟨a'', trs'', t'', first'', g''⟩ | y) h
  · obtain ⟨_, _, h3, h4, h5⟩ := h
    exact ⟨h5, h3, h4⟩
  · obtain ⟨_, rfl⟩ := h
    exact ⟨⟨F', Pf', hI⟩, ht', hs'⟩

/-! ## Termination -/

theorem tr_body_term {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8) (n q g3 : Usize)
    (tail : Array U64 17#usize) (a : Array (Array (Array U32 256#usize) L) K)
    (trs : Array U64 25#usize) (t first g : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (ht : t.val ≤ q.val + 1) (hs : toLanes trs = HS (bytes pk) t.val)
    (F : Nat) (hF : ∀ e, e < n.val → ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P) :
    sampling.expand_a_tr_into_x4_loop.body rho pk n q g3 tail a trs t first g ⦃ c =>
      match c with
      | .done y => ¬ (first.val < n.val ∧ g.val < g3.val) ∧ y = (a, trs, t, first)
      | .cont (_, trs', t', first', _) => first.val < n.val ∧ first'.val = first.val + 3 ∧
          t'.val ≤ q.val + 1 ∧ toLanes trs' = HS (bytes pk) t'.val ⦄ := by
  unfold sampling.expand_a_tr_into_x4_loop.body
  split
  · rename_i hlt
    have hf : first.val < n.val := by scalar_tac
    split
    · rename_i hgt
      step*
      have hlenA : a.val.length = K.val := a.property
      have hn1 : 1 ≤ n.val := by omega
      have he0 : e0.val < n.val := by rw [e0_post]; split_ifs <;> omega
      have he1 : e1.val < n.val := by rw [e1_post]; split_ifs <;> omega
      have he2 : e2.val < n.val := by rw [e2_post]; split_ifs <;> omega
      have hdiv : ∀ e : Nat, e < n.val → e / L.val < K.val := fun e he =>
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hmod : ∀ e : Nat, e % L.val < L.val := fun e => Nat.mod_lt _ hL
      have hi7 : i7.val < K.val := by rw [i7_post]; exact hdiv _ he0
      have hi9 : i9.val < K.val := by rw [i9_post]; exact hdiv _ he1
      have hi11 : i11.val < K.val := by rw [i11_post]; exact hdiv _ he2
      have hj0 : i.val < L.val := by rw [i_post]; exact hmod _
      have hj1 : i2.val < L.val := by rw [i2_post]; exact hmod _
      have hj2 : i4.val < L.val := by rw [i4_post]; exact hmod _
      have hmod256 : ∀ e : Nat, e % L.val < 256 := fun e => lt_trans (hmod e) hLs
      have hdiv256 : ∀ e : Nat, e < n.val → e / L.val < 256 := fun e he => lt_trans (hdiv e he) hK
      have hs0 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 0
          = pSeed (bytesA rho) (e0.val / L.val) (e0.val % L.val) :=
        seed_of_cast rho e0.val L.val i1 i8 i i7 i1_post i8_post i_post i7_post (by rw [i_post]; exact hmod256 _)
          (by rw [i7_post]; exact hdiv256 _ he0)
      have hs1 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 1
          = pSeed (bytesA rho) (e1.val / L.val) (e1.val % L.val) :=
        seed_of_cast rho e1.val L.val i3 i10 i2 i9 i3_post i10_post i2_post i9_post (by rw [i2_post]; exact hmod256 _)
          (by rw [i9_post]; exact hdiv256 _ he1)
      have hs2 : Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp)) (Array.make 4#usize [i8, i10, i12, i13] (by simp)) 2
          = pSeed (bytesA rho) (e2.val / L.val) (e2.val % L.val) :=
        seed_of_cast rho e2.val L.val i5 i12 i4 i11 i5_post i12_post i4_post i11_post (by rw [i4_post]; exact hmod256 _)
          (by rw [i11_post]; exact hdiv256 _ he2)
      obtain ⟨P0, hP0⟩ := hF _ he0
      obtain ⟨P1, hP1⟩ := hF _ he1
      obtain ⟨P2, hP2⟩ := hF _ he2
      have hP : ∀ i, i < 3 → Spec.RejNTTPoly F (Mi rho (Array.make 4#usize [i1, i3, i5, i6] (by simp))
          (Array.make 4#usize [i8, i10, i12, i13] (by simp)) i) =
          some ((fun k => if k = 0 then P0 else if k = 1 then P1 else P2) i) := by
        intro k hk
        interval_cases k
        · rw [hs0]; exact hP0
        · rw [hs1]; exact hP1
        · rw [hs2]; exact hP2
      step with rej_ntt_poly_x3_tr_spec rho (Array.make 4#usize [i1, i3, i5, i6] (by simp))
        (Array.make 4#usize [i8, i10, i12, i13] (by simp)) pk tail q trs t hq htail ht hs F _ hP
      step*
    · rename_i hgt
      simp only [WP.spec_ok]
      exact ⟨fun hh => hgt (by scalar_tac), trivial⟩
  · rename_i hlt
    simp only [WP.spec_ok]
    exact ⟨fun hh => hlt (by scalar_tac), trivial⟩


theorem tr_loop_term {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8) (n q g3 : Usize)
    (tail : Array U64 17#usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (hq : q.val = (bytes pk).length / 136)
    (htail : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k)
    (F : Nat) (hF : ∀ e, e < n.val → ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P)
    (a : Array (Array (Array U32 256#usize) L) K) (trs : Array U64 25#usize) (t first g : Usize)
    (ht : t.val ≤ q.val + 1) (hs : toLanes trs = HS (bytes pk) t.val) :
    sampling.expand_a_tr_into_x4_loop rho pk a n q g3 tail trs t first g ⦃ y =>
      y.2.2.1.val ≤ q.val + 1 ∧ toLanes y.2.1 = HS (bytes pk) y.2.2.1.val ⦄ := by
  unfold sampling.expand_a_tr_into_x4_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array (Array U32 256#usize) L) K × Array U64 25#usize × Usize × Usize × Usize) =>
      n.val - p.2.2.2.1.val)
    (fun p => p.2.2.1.val ≤ q.val + 1 ∧ toLanes p.2.1 = HS (bytes pk) p.2.2.1.val)
  · rintro ⟨a', trs', t', first', g'⟩ ⟨ht', hs'⟩
    refine WP.spec_mono (tr_body_term rho pk n q g3 tail a' trs' t' first' g' hn hL hLs hK hnKL hq htail ht' hs'
      F hF) ?_
    rintro (⟨a'', trs'', t'', first'', g''⟩ | y) h
    · obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨⟨h3, h4⟩, by show n.val - first''.val < n.val - first'.val; omega⟩
    · obtain ⟨_, rfl⟩ := h
      exact ⟨ht', hs'⟩
  · exact ⟨ht, hs⟩

/-! ## The rest of the matrix and the whole function -/

theorem expand_a_from_x4_partial {K L : Usize} (rho : Array U8 32#usize) (hL : 0 < L.val) (hLs : L.val < 256)
    (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (a : Array (Array (Array U32 256#usize) L) K) (first : Usize)
    (F : Nat) (Pf : Nat → Poly) (h : GoodA rho (K.val * L.val) F Pf a first.val) :
    sampling.expand_a_from_x4 rho a first ⦃ y => ∃ (F' : Nat) (Pf' : Nat → Poly),
      GoodA rho (K.val * L.val) F' Pf' y (K.val * L.val) ⦄div := by
  unfold sampling.expand_a_from_x4
  step*
  have hn' : n.val = K.val * L.val := n_post
  have := x4_loop_partial rho n (by omega) hL hLs hK hn' a first F Pf (by rw [hn']; exact h)
  step with this
  rw [hn'] at y_post
  exact ⟨_, _, y_post⟩

theorem expand_a_from_x4_term {K L : Usize} (rho : Array U8 32#usize) (hL : 0 < L.val) (hLs : L.val < 256)
    (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (F : Nat)
    (hF : ∀ e, e < K.val * L.val →
      ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Usize) :
    sampling.expand_a_from_x4 rho a first ⦃ _ => True ⦄ := by
  unfold sampling.expand_a_from_x4
  step*
  have hn' : n.val = K.val * L.val := n_post
  exact x4_loop_term rho n (by omega) hL hLs hK hn' F (by rw [hn']; exact hF) a first

theorem tr_groups_ok (n q : Usize) (hn : n.val ≤ 2048) (hq : q.val + 5 ≤ Usize.max) :
    sampling.tr_groups n q ⦃ _ => True ⦄ := by
  unfold sampling.tr_groups
  step*

/-- The bytes of `SHAKE256(M, 64)` read off the final state: what `tr_finish_scalar` returns is `H(pk, 64)`. -/
theorem bytesA_tr (pk : Slice U8) (out : Array U8 64#usize)
    (h : ∀ j, j < 64 → UInt8.ofNat (out.val[j]!).val = KM.sb (HS (bytes pk) ((bytes pk).length / 136 + 1)) j) :
    bytesA out = H (bytes pk) 64 := by
  apply List.ext_getElem?
  intro j
  unfold H
  by_cases hj : j < 64
  · have hb : (bytesA out)[j]? = some (UInt8.ofNat (out.val[j]'(by rw [out.property]; exact hj)).val) := by
      simp [bytesA, List.getElem?_eq_getElem (show j < out.val.length by rw [out.property]; exact hj)]
    rw [hb, shake256_byte (bytes pk) j hj, ← h j hj]
    have : out.val[j]! = out.val[j]'(by rw [out.property]; exact hj) :=
      getElem!_pos out.val j (by rw [out.property]; exact hj)
    rw [this]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by rw [SHAKE256_length]; omega)]


theorem expand_a_tr_into_x4_partial {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048)
    (a : Array (Array (Array U32 256#usize) L) K) :
    sampling.expand_a_tr_into_x4 rho pk a ⦃ r => (∃ (F : Nat) (Pf : Nat → Poly),
      GoodA rho (K.val * L.val) F Pf r.2 (K.val * L.val)) ∧ bytesA r.1 = H (bytes pk) 64 ⦄div := by
  unfold sampling.expand_a_tr_into_x4
  simp only [RATE256_eq]
  step as ⟨n, hn'⟩
  step as ⟨q, hq'⟩
  have hlen : (Slice.len pk).val = (bytes pk).length := by simp [Slice.len, bytes]
  have hq : q.val = (bytes pk).length / 136 := by rw [hq', hlen]
  have hqb : q.val + 5 ≤ Usize.max := by
    have := (Slice.len pk).hmax
    scalar_tac
  step with tr_groups_ok n q (by omega) hqb as ⟨g3⟩
  step with tr_tail_lanes_spec pk as ⟨tail, htail⟩
  have hs0 : toLanes (Array.repeat 25#usize 0#u64) = HS (bytes pk) (0#usize).val := by
    rw [toLanes_repeat_zero]; exact (HS_zero _).symm
  have htail' : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k := by rw [hq]; exact htail
  have hloop := tr_loop_partial rho pk n q g3 tail (by omega) hL hLs hK hn' hq htail'
    a (Array.repeat 25#usize 0#u64) 0#usize 0#usize 0#usize (Nat.zero_le _) hs0 0 (fun _ => Poly.zero)
    (fun e he1 _ => absurd he1 (Nat.not_lt_zero e))
  step with hloop
  obtain ⟨aa, trsA, tA, fA⟩ := a1
  dsimp only at first a1_post2 a1_post3
  rw [hn'] at first
  step with expand_a_from_x4_partial rho hL hLs hK hKL aa fA trs1 t first
  step with tr_finish_scalar_spec pk tail q trsA tA hq a1_post2 htail' a1_post3 as ⟨out, hout⟩
  refine ⟨?_, ?_⟩
  · exact ⟨_, _, r_post⟩
  · apply bytesA_tr
    intro j hj
    rw [← hq]
    exact hout j hj


theorem expand_a_tr_into_x4_term {K L : Usize} (rho : Array U8 32#usize) (pk : Slice U8)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (F : Nat)
    (hF : ∀ e, e < K.val * L.val →
      ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P)
    (a : Array (Array (Array U32 256#usize) L) K) :
    sampling.expand_a_tr_into_x4 rho pk a ⦃ _ => True ⦄ := by
  unfold sampling.expand_a_tr_into_x4
  simp only [RATE256_eq]
  step as ⟨n, hn'⟩
  step as ⟨q, hq'⟩
  have hlen : (Slice.len pk).val = (bytes pk).length := by simp [Slice.len, bytes]
  have hq : q.val = (bytes pk).length / 136 := by rw [hq', hlen]
  have hqb : q.val + 5 ≤ Usize.max := by
    have := (Slice.len pk).hmax
    scalar_tac
  step with tr_groups_ok n q (by omega) hqb as ⟨g3⟩
  step with tr_tail_lanes_spec pk as ⟨tail, htail⟩
  have hs0 : toLanes (Array.repeat 25#usize 0#u64) = HS (bytes pk) (0#usize).val := by
    rw [toLanes_repeat_zero]; exact (HS_zero _).symm
  have htail' : ∀ k, k < 17 → toU64 (tail.val[k]!) = Wb (blkT (bytes pk) q.val) k := by rw [hq]; exact htail
  have hloop := tr_loop_term rho pk n q g3 tail (by omega) hL hLs hK hn' hq htail' F (by rw [hn']; exact hF)
    a (Array.repeat 25#usize 0#u64) 0#usize 0#usize 0#usize (Nat.zero_le _) hs0
  step with hloop
  step with expand_a_from_x4_term rho hL hLs hK hKL F hF a1 first
  step with tr_finish_scalar_spec pk tail q trs1 t hq a1_post1 htail' a1_post2 as ⟨out, hout⟩

end Proofs
