import Proofs.Sample4

/-!
# The 4-way ExpandA

`sampling.expand_a_x4 K L` is `sampling.expand_a K L` (`expand_a_x4_eq`): both are partially correct for the spec's
`ExpandA` (`expand_a_x4_partial`, `expand_a_partial`), the 4-way one terminates whenever the spec's `ExpandA` has a
result (`expand_a_x4_term`), and the matrix is unique (`ReprMat.unique`), so the two `RustM` values agree, divergence
included (`rustM_eq_of_partial`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

theorem foldlM_range_succ {α : Type} (f : α → Nat → Option α) (A : α) (m : Nat) :
    (List.range' 0 (m + 1)).foldlM f A = ((List.range' 0 m).foldlM f A).bind (fun B => f B m) := by
  rw [show List.range' 0 (m + 1) = List.range' 0 m ++ [m] by simp [List.range'_concat], List.foldlM_append]
  cases (List.range' 0 m).foldlM f A <;> simp [List.foldlM_cons]

/-- One row of ExpandA: columns `0 … m-1` of row `n` are the sampled polynomials, other rows are unchanged. -/
theorem inner_ent (p : Spec.Params) (F : Nat) (ρ : List UInt8) (n : Nat) (hn : n < p.k)
    (B : Vector (Vector Poly p.ℓ) p.k) :
    ∀ m, m ≤ p.ℓ → ∀ C, (List.range' 0 m).foldlM (innerF p F ρ n) B = some C →
      (∀ s (hsl : s < p.ℓ), s < m → Spec.RejNTTPoly F (pSeed ρ n s) = some ((C[n]'hn)[s]'hsl)) ∧
      (∀ rr (hrr : rr < p.k), rr ≠ n → C[rr]'hrr = B[rr]'hrr) := by
  intro m
  induction m with
  | zero =>
    intro _ C hC
    simp at hC
    subst hC
    exact ⟨fun s hsl hs => by omega, fun _ _ _ => rfl⟩
  | succ m ih =>
    intro hm C hC
    rw [foldlM_range_succ] at hC
    cases hprev : (List.range' 0 m).foldlM (innerF p F ρ n) B with
    | none => simp [hprev] at hC
    | some C' =>
      rw [hprev] at hC
      simp only [Option.bind_some] at hC
      obtain ⟨ih1, ih2⟩ := ih (by omega) C' hprev
      unfold innerF at hC
      rcases hr : Spec.RejNTTPoly F (pSeed ρ n m) with _ | a
      · simp [hr] at hC
      · simp only [hr, Option.some.injEq] at hC
        subst hC
        refine ⟨fun s hsl hs => ?_, fun rr hrr hne => ?_⟩
        · by_cases hsm : s = m
          · subst hsm
            rw [hr]
            simp [set!_eq', Vector.getElem_setIfInBounds, getElem!_pos, hn]
          · have := ih1 s hsl (by omega)
            rw [this]
            simp [set!_eq', Vector.getElem_setIfInBounds, getElem!_pos, hn, hsm, Ne.symm hsm]
        · rw [set!_eq', Vector.getElem_setIfInBounds hrr, if_neg (Ne.symm hne)]
          exact ih2 rr hrr hne


theorem outer_ent (p : Spec.Params) (F : Nat) (ρ : List UInt8) :
    ∀ n, n ≤ p.k → ∀ B, (List.range' 0 n).foldlM (outerF p F ρ)
        (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) = some B →
      ∀ r (hr : r < p.k), r < n → ∀ s (hs : s < p.ℓ),
        Spec.RejNTTPoly F (pSeed ρ r s) = some ((B[r]'hr)[s]'hs) := by
  intro n
  induction n with
  | zero => intro _ B _ r hr hrn; omega
  | succ n ih =>
    intro hn B hB r hr hrn s hs
    rw [foldlM_range_succ] at hB
    cases hprev : (List.range' 0 n).foldlM (outerF p F ρ) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) with
    | none => simp [hprev] at hB
    | some B' =>
      rw [hprev] at hB
      simp only [Option.bind_some] at hB
      have hnk : n < p.k := by omega
      unfold outerF at hB
      obtain ⟨i1, i2⟩ := inner_ent p F ρ n hnk B' p.ℓ le_rfl B hB
      by_cases hrn' : r = n
      · subst hrn'
        exact i1 s hs hs
      · have := ih (by omega) B' hprev r hr (by omega) s hs
        rw [this, i2 r hr hrn']

theorem expandA_ent (p : Spec.Params) (F : Nat) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k)
    (h : Spec.ExpandA p F ρ = some A) (r : Nat) (hr : r < p.k) (s : Nat) (hs : s < p.ℓ) :
    Spec.RejNTTPoly F (pSeed ρ r s) = some ((A[r]'hr)[s]'hs) := by
  rw [expandA_eq] at h
  exact outer_ent p F ρ p.k le_rfl A h r hr hr s hs


/-! ## Pointwise representation of the flattened matrix -/

/-- Entry `e` (row `e / L`, column `e % L`) of the extracted matrix represents `P`. -/
def EntAt {K L : Usize} (a : Array (Array (Array U32 256#usize) L) K) (e : Nat) (P : Poly) : Prop :=
  ∃ (r1 : Array (Array U32 256#usize) L) (c : Array U32 256#usize),
    a.val[e / L.val]? = some r1 ∧ r1.val[e % L.val]? = some c ∧ Repr c P

theorem EntAt_set {K L : Usize} (a : Array (Array (Array U32 256#usize) L) K) (e0 e : Nat) (P v : Poly)
    (i j : Usize) (x : Array U32 256#usize) (row : Array (Array U32 256#usize) L) (hL : 0 < L.val)
    (hi : i.val = e0 / L.val) (hj : j.val = e0 % L.val) (hi' : i.val < a.val.length)
    (hrow : a.val[i.val]? = some row) (hx : Repr x v)
    (h : EntAt a e P) (hne : e0 ≠ e ∨ v = P) :
    EntAt (a.set i (row.set j x)) e P := by
  obtain ⟨r1, c, h1, h2, h3⟩ := h
  have hj' : j.val < L.val := by rw [hj]; exact Nat.mod_lt _ hL
  have hrl : row.val.length = L.val := row.property
  by_cases hrr : i.val = e / L.val
  · rw [← hrr] at h1
    rw [hrow] at h1
    obtain rfl : row = r1 := Option.some.inj h1
    by_cases hcc : j.val = e % L.val
    · have hee : e0 = e := by
        have h1 := Nat.div_add_mod e0 L.val
        have h2 := Nat.div_add_mod e L.val
        rw [← hi, ← hj] at h1
        rw [← hrr, ← hcc] at h2
        omega
      have hvp : v = P := by
        rcases hne with hne | hne
        · exact absurd hee hne
        · exact hne
      subst hvp
      refine ⟨row.set j x, x, ?_, ?_, hx⟩
      · rw [Array.set_val_eq, ← hrr]; exact List.getElem?_set_self hi'
      · rw [Array.set_val_eq, ← hcc]; exact List.getElem?_set_self (by rw [hrl]; exact hj')
    · refine ⟨row.set j x, c, ?_, ?_, h3⟩
      · rw [Array.set_val_eq, ← hrr]; exact List.getElem?_set_self hi'
      · rw [Array.set_val_eq]; rw [List.getElem?_set_ne hcc]; exact h2
  · refine ⟨r1, c, ?_, h2, h3⟩
    rw [Array.set_val_eq, List.getElem?_set_ne hrr]; exact h1

theorem EntAt_new {K L : Usize} (a : Array (Array (Array U32 256#usize) L) K) (e0 : Nat) (v : Poly)
    (i j : Usize) (x : Array U32 256#usize) (row : Array (Array U32 256#usize) L) (hL : 0 < L.val)
    (hi : i.val = e0 / L.val) (hj : j.val = e0 % L.val) (hi' : i.val < a.val.length)
    (hx : Repr x v) :
    EntAt (a.set i (row.set j x)) e0 v := by
  have hj' : j.val < L.val := by rw [hj]; exact Nat.mod_lt _ hL
  have hrl : row.val.length = L.val := row.property
  refine ⟨row.set j x, x, ?_, ?_, hx⟩
  · rw [Array.set_val_eq, ← hi]; exact List.getElem?_set_self hi'
  · rw [Array.set_val_eq, ← hj]; exact List.getElem?_set_self (by rw [hrl]; exact hj')


/-! ## The group loop -/

@[step]
theorem entry_x4_spec (first l n : Usize) (hl : l.val ≤ 3) (hf : first.val < n.val) (hn : n.val ≤ 2048) :
    sampling.entry_x4 first l n ⦃ e =>
      e.val = if first.val + l.val < n.val then first.val + l.val else n.val - 1 ⦄ := by
  unfold sampling.entry_x4
  step*

theorem Mi_pSeed (rho : Array U8 32#usize) (s r : Array U8 4#usize) (k x y : Nat) (hx : x < 256) (hy : y < 256)
    (hs : (s.val[k]!).val = x) (hr : (r.val[k]!).val = y) : Mi rho s r k = pSeed (bytesA rho) y x := by
  unfold Mi pSeed
  rw [integerToBytes_one, integerToBytes_one, hs, hr, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  simp [List.append_assoc]

theorem wstep {K L : Usize} (A : Array (Array (Array U32 256#usize) L) K) (e0 : Nat) (i j : Usize)
    (x : Array U32 256#usize) (v : Poly) (row : Array (Array U32 256#usize) L) (hL : 0 < L.val)
    (hi : i.val = e0 / L.val) (hj : j.val = e0 % L.val) (hiK : i.val < A.val.length)
    (hrow : row = A.val[i.val]) (hx : Repr x v) :
    (∀ e P, EntAt A e P → (e0 ≠ e ∨ v = P) → EntAt (A.set i (row.set j x)) e P) ∧
      EntAt (A.set i (row.set j x)) e0 v := by
  have hrow' : A.val[i.val]? = some row := by rw [hrow]; exact List.getElem?_eq_getElem hiK
  exact ⟨fun e P h hne => EntAt_set A e0 e P v i j x row hL hi hj hiK hrow' hx h hne,
    EntAt_new A e0 v i j x row hL hi hj hiK hx⟩

theorem seed_of_cast (rho : Array U8 32#usize) (e L : Nat) (c q : U8) (col row : Usize)
    (hc : c = UScalar.cast .U8 col) (hq : q = UScalar.cast .U8 row) (hcol : col.val = e % L)
    (hrow : row.val = e / L) (hcl : col.val < 256) (hrw : row.val < 256) :
    bytesA rho ++ [UInt8.ofNat c.val, UInt8.ofNat q.val] = pSeed (bytesA rho) (e / L) (e % L) := by
  have h1 : c.val = col.val := by rw [hc, UScalar.cast_val_eq]; simp; omega
  have h2 : q.val = row.val := by rw [hq, UScalar.cast_val_eq]; simp; omega
  unfold pSeed
  rw [integerToBytes_one, integerToBytes_one, h1, h2, hcol, hrow] at *
  simp [List.append_assoc]
  rw [← hcol, ← hrow, Nat.mod_eq_of_lt hcl, Nat.mod_eq_of_lt hrw]
  simp [Nat.toUInt8]

def GoodA {K L : Usize} (rho : Array U8 32#usize) (n : Nat) (F : Nat) (Pf : Nat → Poly)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Nat) : Prop :=
  ∀ e, e < first → e < n → Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some (Pf e) ∧
    EntAt a e (Pf e)

theorem x4_body_partial {K L : Usize} (rho : Array U8 32#usize) (n : Usize)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (F : Nat) (Pf : Nat → Poly) (h : GoodA rho n.val F Pf a first.val) :
    sampling.expand_a_from_x4_loop.body rho n a first ⦃ c =>
      match c with
      | .done y => ¬ first.val < n.val ∧ y = a
      | .cont (a', first') => first'.val = first.val + 4 ∧
          ∃ (F' : Nat) (Pf' : Nat → Poly), GoodA rho n.val F' Pf' a' first'.val ⦄div := by
  unfold sampling.expand_a_from_x4_loop.body
  split
  · rename_i hlt
    have hf : first.val < n.val := by scalar_tac
    step*
    step with rej_ntt_poly_x4_partial
    rename_i P' pa
    have hlenA : a.val.length = K.val := a.property
    have hn1 : 1 ≤ n.val := by omega
    have he0 : e0.val < n.val := by rw [e0_post]; split_ifs <;> omega
    have he1 : e1.val < n.val := by rw [e1_post]; split_ifs <;> omega
    have he2 : e2.val < n.val := by rw [e2_post]; split_ifs <;> omega
    have he3 : e3.val < n.val := by rw [e3_post]; split_ifs <;> omega
    have hdiv : ∀ e : Nat, e < n.val → e / L.val < K.val := fun e he =>
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hmod : ∀ e : Nat, e % L.val < L.val := fun e => Nat.mod_lt _ hL
    have hi8 : i8.val < K.val := by rw [i8_post]; exact hdiv _ he0
    have hi10 : i10.val < K.val := by rw [i10_post]; exact hdiv _ he1
    have hi12 : i12.val < K.val := by rw [i12_post]; exact hdiv _ he2
    have hi14 : i14.val < K.val := by rw [i14_post]; exact hdiv _ he3
    have hj0 : i.val < L.val := by rw [i_post]; exact hmod _
    have hj1 : i2.val < L.val := by rw [i2_post]; exact hmod _
    have hj2 : i4.val < L.val := by rw [i4_post]; exact hmod _
    have hj3 : i6.val < L.val := by rw [i6_post]; exact hmod _
    step*
    obtain ⟨wa2, wb2⟩ := a2
    step*
    obtain ⟨wa6, wb6⟩ := a6
    step*
    obtain ⟨wa10, wb10⟩ := a10
    step*
    obtain ⟨wa14, wb14⟩ := a14
    step*
    refine (WP.dspec_ok _).2 ?_
    -- the sampled polynomials
    have hxr : ∀ (k : Nat) (hk : k < pa.val.length) (y : Array U32 256#usize), y = pa.val[k] → k < 4 → Repr y (P' k) :=
      fun k hk y hy hk4 => hy ▸ polys_post2 k hk hk4
    have hx0 := hxr 0 a1 _ rfl (by omega)
    have hx1 := hxr 1 a4 _ rfl (by omega)
    have hx2 := hxr 2 a8 _ rfl (by omega)
    have hx3 := hxr 3 a12 _ rfl (by omega)
    rw [a1_post2] at a3_post
    rw [a4_post2] at a7_post
    rw [a8_post2] at a11_post
    rw [a12_post2] at a15_post
    -- the seeds of the four lanes
    have hmod256 : ∀ e : Nat, e % L.val < 256 := fun e => lt_trans (hmod e) hLs
    have hdiv256 : ∀ e : Nat, e < n.val → e / L.val < 256 := fun e he => lt_trans (hdiv e he) hK
    have hs0 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 0
        = pSeed (bytesA rho) (e0.val / L.val) (e0.val % L.val) :=
      seed_of_cast rho e0.val L.val i1 i9 i i8 i1_post i9_post i_post i8_post (by rw [i_post]; exact hmod256 _)
        (by rw [i8_post]; exact hdiv256 _ he0)
    have hs1 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 1
        = pSeed (bytesA rho) (e1.val / L.val) (e1.val % L.val) :=
      seed_of_cast rho e1.val L.val i3 i11 i2 i10 i3_post i11_post i2_post i10_post (by rw [i2_post]; exact hmod256 _)
        (by rw [i10_post]; exact hdiv256 _ he1)
    have hs2 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 2
        = pSeed (bytesA rho) (e2.val / L.val) (e2.val % L.val) :=
      seed_of_cast rho e2.val L.val i5 i13 i4 i12 i5_post i13_post i4_post i12_post (by rw [i4_post]; exact hmod256 _)
        (by rw [i12_post]; exact hdiv256 _ he2)
    have hs3 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 3
        = pSeed (bytesA rho) (e3.val / L.val) (e3.val % L.val) :=
      seed_of_cast rho e3.val L.val i7 i15 i6 i14 i7_post i15_post i6_post i14_post (by rw [i6_post]; exact hmod256 _)
        (by rw [i14_post]; exact hdiv256 _ he3)
    have hr0 := polys_post1 0 (by omega)
    have hr1 := polys_post1 1 (by omega)
    have hr2 := polys_post1 2 (by omega)
    have hr3 := polys_post1 3 (by omega)
    rw [hs0] at hr0
    rw [hs1] at hr1
    rw [hs2] at hr2
    rw [hs3] at hr3
    have dup : ∀ (x y : Nat) (P Q : Poly),
        Spec.RejNTTPoly polys (pSeed (bytesA rho) (x / L.val) (x % L.val)) = some P →
        Spec.RejNTTPoly polys (pSeed (bytesA rho) (y / L.val) (y % L.val)) = some Q → x = y → P = Q := by
      intro x y P Q h1 h2 hxy
      subst hxy
      exact Option.some.inj (h1.symm.trans h2)
    -- the four writes
    have hw2 : wb2 = a.set i8 := a2_post3
    have hw6 : wb6 = (wb2 a3).set i10 := a6_post3
    have hw10 : wb10 = (wb6 a7).set i12 := a10_post3
    have hw14 : wb14 = (wb10 a11).set i14 := a14_post3
    obtain ⟨o1, n1⟩ := wstep a e0.val i8 i _ (P' 0) wa2 hL i8_post i_post (by omega) a2_post2 hx0
    have eq1 : wb2 a3 = a.set i8 (wa2.set i (pa.val[0]'a1)) := by rw [hw2, a3_post]
    rw [← eq1] at o1 n1
    have hl1 : i10.val < (wb2 a3).val.length := by have := (wb2 a3).property; omega
    obtain ⟨o2, n2⟩ := wstep (wb2 a3) e1.val i10 i2 _ (P' 1) wa6 hL i10_post i2_post hl1 a6_post2 hx1
    have eq2 : wb6 a7 = (wb2 a3).set i10 (wa6.set i2 (pa.val[1]'a4)) := by rw [hw6, a7_post]
    rw [← eq2] at o2 n2
    have hl2 : i12.val < (wb6 a7).val.length := by have := (wb6 a7).property; omega
    obtain ⟨o3, n3⟩ := wstep (wb6 a7) e2.val i12 i4 _ (P' 2) wa10 hL i12_post i4_post hl2 a10_post2 hx2
    have eq3 : wb10 a11 = (wb6 a7).set i12 (wa10.set i4 (pa.val[2]'a8)) := by rw [hw10, a11_post]
    rw [← eq3] at o3 n3
    have hl3 : i14.val < (wb10 a11).val.length := by have := (wb10 a11).property; omega
    obtain ⟨o4, n4⟩ := wstep (wb10 a11) e3.val i14 i6 _ (P' 3) wa14 hL i14_post i6_post hl3 a14_post2 hx3
    have eq4 : wb14 a15 = (wb10 a11).set i14 (wa14.set i6 (pa.val[3]'a12)) := by rw [hw14, a15_post]
    rw [← eq4] at o4 n4
    have mkc : ∀ (x y : Nat) (P Q : Poly), (x = y → P = Q) → (x ≠ y ∨ P = Q) := fun x y P Q h => by
      by_cases hh : x = y
      · exact Or.inr (h hh)
      · exact Or.inl hh
    have d10 : e1.val = e0.val → P' 1 = P' 0 := dup _ _ _ _ hr1 hr0
    have d20 : e2.val = e0.val → P' 2 = P' 0 := dup _ _ _ _ hr2 hr0
    have d30 : e3.val = e0.val → P' 3 = P' 0 := dup _ _ _ _ hr3 hr0
    have d21 : e2.val = e1.val → P' 2 = P' 1 := dup _ _ _ _ hr2 hr1
    have d31 : e3.val = e1.val → P' 3 = P' 1 := dup _ _ _ _ hr3 hr1
    have d32 : e3.val = e2.val → P' 3 = P' 2 := dup _ _ _ _ hr3 hr2
    have F0 := o4 _ _ (o3 _ _ (o2 _ _ n1 (mkc _ _ _ _ d10)) (mkc _ _ _ _ d20)) (mkc _ _ _ _ d30)
    have F1 := o4 _ _ (o3 _ _ n2 (mkc _ _ _ _ d21)) (mkc _ _ _ _ d31)
    have F2 := o4 _ _ n3 (mkc _ _ _ _ d32)
    have F3 := n4
    have hge0 : first.val ≤ e0.val := by rw [e0_post]; split_ifs <;> omega
    have hge1 : first.val ≤ e1.val := by rw [e1_post]; split_ifs <;> omega
    have hge2 : first.val ≤ e2.val := by rw [e2_post]; split_ifs <;> omega
    have hge3 : first.val ≤ e3.val := by rw [e3_post]; split_ifs <;> omega
    have hE0 : first.val + 0 < n.val → e0.val = first.val + 0 := fun hh => by rw [e0_post, if_pos hh]
    have hE1 : first.val + 1 < n.val → e1.val = first.val + 1 := fun hh => by rw [e1_post, if_pos hh]
    have hE2 : first.val + 2 < n.val → e2.val = first.val + 2 := fun hh => by rw [e2_post, if_pos hh]
    have hE3 : first.val + 3 < n.val → e3.val = first.val + 3 := fun hh => by rw [e3_post, if_pos hh]
    refine ⟨by omega, max F polys, fun e => if e < first.val then Pf e else P' (e - first.val), ?_⟩
    intro e he1 he2
    rw [first1_post] at he1
    by_cases hold' : e < first.val
    · obtain ⟨hr, hent⟩ := h e hold' he2
      show Spec.RejNTTPoly (max F polys) _ = some (if e < first.val then Pf e else P' (e - first.val)) ∧
        EntAt (wb14 a15) e (if e < first.val then Pf e else P' (e - first.val))
      rw [if_pos hold']
      refine ⟨RejNTTPoly_mono _ _ _ _ hr (le_max_left _ _), ?_⟩
      exact o4 e _ (o3 e _ (o2 e _ (o1 e _ hent (Or.inl (by omega))) (Or.inl (by omega))) (Or.inl (by omega)))
        (Or.inl (by omega))
    · show Spec.RejNTTPoly (max F polys) _ = some (if e < first.val then Pf e else P' (e - first.val)) ∧
        EntAt (wb14 a15) e (if e < first.val then Pf e else P' (e - first.val))
      rw [if_neg hold']
      rcases (by omega : e = first.val + 0 ∨ e = first.val + 1 ∨ e = first.val + 2 ∨ e = first.val + 3) with
        hk | hk | hk | hk
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
      · have hEk := hE3 (by omega)
        have hk' : e - first.val = 3 := by omega
        rw [hk']
        rw [hEk, ← hk] at hr3 F3
        exact ⟨RejNTTPoly_mono _ _ _ _ hr3 (le_max_right _ _), F3⟩
  · rename_i hlt
    have hf : ¬ first.val < n.val := by scalar_tac
    simp only [WP.dspec_ok]
    exact ⟨hf, trivial⟩


/-! ## The group loop, partial correctness -/

theorem x4_loop_partial {K L : Usize} (rho : Array U8 32#usize) (n : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Usize) (F : Nat) (Pf : Nat → Poly)
    (h : GoodA rho n.val F Pf a first.val) :
    sampling.expand_a_from_x4_loop rho a n first ⦃ y => ∃ (F' : Nat) (Pf' : Nat → Poly),
      GoodA rho n.val F' Pf' y n.val ⦄div := by
  unfold sampling.expand_a_from_x4_loop
  refine loop.dspec_inv _ (fun x : Array (Array (Array U32 256#usize) L) K × Usize =>
    ∃ (F : Nat) (Pf : Nat → Poly), GoodA rho n.val F Pf x.1 x.2.val) ?_ ?_ (a, first) ⟨F, Pf, h⟩
  rintro ⟨a', first'⟩ ⟨F', Pf', hI⟩
  refine WP.dspec_mono' (x4_body_partial rho n a' first' hn hL hLs hK hnKL F' Pf' hI) ?_
  rintro (⟨a'', first''⟩ | y) h
  · exact h.2
  · obtain ⟨hge, rfl⟩ := h
    exact ⟨F', Pf', fun e he1 he2 => hI e (by show e < first'.val; omega) he2⟩

theorem expand_a_into_x4_partial {K L : Usize} (rho : Array U8 32#usize) (hL : 0 < L.val) (hLs : L.val < 256)
    (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (a : Array (Array (Array U32 256#usize) L) K) :
    sampling.expand_a_into_x4 rho a ⦃ y => ∃ (F : Nat) (Pf : Nat → Poly),
      GoodA rho (K.val * L.val) F Pf y (K.val * L.val) ⦄div := by
  unfold sampling.expand_a_into_x4 sampling.expand_a_from_x4
  step*
  have hn' : n.val = K.val * L.val := n_post
  have := x4_loop_partial rho n (by omega) hL hLs hK hn' a 0#usize 0 (fun _ => Poly.zero)
    (fun e he1 _ => by simp at he1)
  step with this
  rw [hn'] at y_post
  exact ⟨_, _, y_post⟩


/-! ## From the pointwise statement to `ReprMat` -/

theorem flat_div (r s L : Nat) (hs : s < L) : (s + r * L) / L = r := by
  rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hs]; omega

theorem flat_mod (r s L : Nat) (hs : s < L) : (s + r * L) % L = s := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

theorem goodA_to_expandA {K L : Usize} (sp : Spec.Params) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (F : Nat) (Pf : Nat → Poly) (y : Array (Array (Array U32 256#usize) L) K)
    (h : GoodA rho (K.val * L.val) F Pf y (K.val * L.val)) :
    ∃ A : Vector (Vector Poly sp.ℓ) sp.k, Spec.ExpandA sp F (bytesA rho) = some A ∧ ReprMat y A := by
  have hent : ∀ r s, r < sp.k → s < sp.ℓ → s + r * L.val < K.val * L.val := by
    intro r s hr hs
    have : r * L.val + L.val ≤ K.val * L.val := by
      have : (r + 1) * L.val ≤ K.val * L.val := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    omega
  have hall : ∀ r, r < sp.k → ∀ s, s < sp.ℓ → (Spec.RejNTTPoly F (pSeed (bytesA rho) r s)).isSome = true := by
    intro r hr s hs
    obtain ⟨h1, _⟩ := h (s + r * L.val) (hent r s hr hs) (hent r s hr hs)
    rw [flat_div r s L.val (by omega), flat_mod r s L.val (by omega)] at h1
    rw [h1]; rfl
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp (expandA_isSome sp F (bytesA rho) hall)
  refine ⟨A, hA, hK, fun i hi => ⟨hL, fun j hj => ?_⟩⟩
  obtain ⟨h1, r1, c, h2, h3, h4⟩ := h (j + i * L.val) (hent i j hi hj) (hent i j hi hj)
  rw [flat_div i j L.val (by omega), flat_mod i j L.val (by omega)] at h1
  rw [flat_div i j L.val (by omega)] at h2
  rw [flat_mod i j L.val (by omega)] at h3
  have hent' := expandA_ent sp F (bytesA rho) A hA i hi j hj
  rw [h1] at hent'
  have hP : Pf (j + i * L.val) = (A[i]'hi)[j]'hj := Option.some.inj hent'
  have hlen : i < y.val.length := by have := y.property; omega
  have hr1 : r1 = y.val[i] := by
    rw [List.getElem?_eq_getElem hlen] at h2
    exact (Option.some.inj h2).symm
  subst hr1
  have hlen2 : j < (y.val[i]).val.length := by have := (y.val[i]).property; omega
  rw [List.getElem?_eq_getElem hlen2] at h3
  have hc : c = (y.val[i]).val[j] := (Option.some.inj h3).symm
  rw [← hc, ← hP]
  exact h4


theorem expand_a_x4_partial (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (hLpos : 0 < L.val) (hLs : L.val < 256) (hK256 : K.val < 256) (hKL : K.val * L.val ≤ 2048)
    (rho : Array U8 32#usize) :
    sampling.expand_a_x4 K L rho ⦃ r => ∃ (A : Vector (Vector Poly sp.ℓ) sp.k) (F : Nat),
      Spec.ExpandA sp F (bytesA rho) = some A ∧ ReprMat r A ⦄div := by
  unfold sampling.expand_a_x4
  step*
  have := expand_a_into_x4_partial (K := K) (L := L) rho hLpos hLs hK256 hKL
    (Array.repeat K (Array.repeat L (Array.repeat 256#usize 0#u32)))
  step with this
  obtain ⟨A, hA, hR⟩ := goodA_to_expandA sp hK hL rho _ _ _ r_post
  exact ⟨A, _, hA, hR⟩


/-! ## Termination of the group loop -/

theorem x4_body_term {K L : Usize} (rho : Array U8 32#usize) (n : Usize)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (F : Nat) (hF : ∀ e, e < n.val → ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P) :
    sampling.expand_a_from_x4_loop.body rho n a first ⦃ c =>
      match c with
      | .done _ => ¬ first.val < n.val
      | .cont (_, first') => first.val < n.val ∧ first'.val = first.val + 4 ⦄ := by
  unfold sampling.expand_a_from_x4_loop.body
  split
  · rename_i hlt
    have hf : first.val < n.val := by scalar_tac
    step*
    have hlenA : a.val.length = K.val := a.property
    have hn1 : 1 ≤ n.val := by omega
    have he0 : e0.val < n.val := by rw [e0_post]; split_ifs <;> omega
    have he1 : e1.val < n.val := by rw [e1_post]; split_ifs <;> omega
    have he2 : e2.val < n.val := by rw [e2_post]; split_ifs <;> omega
    have he3 : e3.val < n.val := by rw [e3_post]; split_ifs <;> omega
    have hdiv : ∀ e : Nat, e < n.val → e / L.val < K.val := fun e he =>
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hmod : ∀ e : Nat, e % L.val < L.val := fun e => Nat.mod_lt _ hL
    have hi8 : i8.val < K.val := by rw [i8_post]; exact hdiv _ he0
    have hi10 : i10.val < K.val := by rw [i10_post]; exact hdiv _ he1
    have hi12 : i12.val < K.val := by rw [i12_post]; exact hdiv _ he2
    have hi14 : i14.val < K.val := by rw [i14_post]; exact hdiv _ he3
    have hj0 : i.val < L.val := by rw [i_post]; exact hmod _
    have hj1 : i2.val < L.val := by rw [i2_post]; exact hmod _
    have hj2 : i4.val < L.val := by rw [i4_post]; exact hmod _
    have hj3 : i6.val < L.val := by rw [i6_post]; exact hmod _
    have hmod256 : ∀ e : Nat, e % L.val < 256 := fun e => lt_trans (hmod e) hLs
    have hdiv256 : ∀ e : Nat, e < n.val → e / L.val < 256 := fun e he => lt_trans (hdiv e he) hK
    have hs0 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 0
        = pSeed (bytesA rho) (e0.val / L.val) (e0.val % L.val) :=
      seed_of_cast rho e0.val L.val i1 i9 i i8 i1_post i9_post i_post i8_post (by rw [i_post]; exact hmod256 _)
        (by rw [i8_post]; exact hdiv256 _ he0)
    have hs1 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 1
        = pSeed (bytesA rho) (e1.val / L.val) (e1.val % L.val) :=
      seed_of_cast rho e1.val L.val i3 i11 i2 i10 i3_post i11_post i2_post i10_post (by rw [i2_post]; exact hmod256 _)
        (by rw [i10_post]; exact hdiv256 _ he1)
    have hs2 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 2
        = pSeed (bytesA rho) (e2.val / L.val) (e2.val % L.val) :=
      seed_of_cast rho e2.val L.val i5 i13 i4 i12 i5_post i13_post i4_post i12_post (by rw [i4_post]; exact hmod256 _)
        (by rw [i12_post]; exact hdiv256 _ he2)
    have hs3 : Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp)) (Array.make 4#usize [i9, i11, i13, i15] (by simp)) 3
        = pSeed (bytesA rho) (e3.val / L.val) (e3.val % L.val) :=
      seed_of_cast rho e3.val L.val i7 i15 i6 i14 i7_post i15_post i6_post i14_post (by rw [i6_post]; exact hmod256 _)
        (by rw [i14_post]; exact hdiv256 _ he3)
    obtain ⟨P0, hP0⟩ := hF _ he0
    obtain ⟨P1, hP1⟩ := hF _ he1
    obtain ⟨P2, hP2⟩ := hF _ he2
    obtain ⟨P3, hP3⟩ := hF _ he3
    have hP : ∀ i, i < 4 → Spec.RejNTTPoly F (Mi rho (Array.make 4#usize [i1, i3, i5, i7] (by simp))
        (Array.make 4#usize [i9, i11, i13, i15] (by simp)) i) =
        some ((fun k => if k = 0 then P0 else if k = 1 then P1 else if k = 2 then P2 else P3) i) := by
      intro k hk
      interval_cases k
      · rw [hs0]; exact hP0
      · rw [hs1]; exact hP1
      · rw [hs2]; exact hP2
      · rw [hs3]; exact hP3
    step with rej_ntt_poly_x4_spec rho (Array.make 4#usize [i1, i3, i5, i7] (by simp))
      (Array.make 4#usize [i9, i11, i13, i15] (by simp)) F _ hP
    step*
  · rename_i hlt
    have hf : ¬ first.val < n.val := by scalar_tac
    simp only [WP.spec_ok]
    exact hf


theorem x4_loop_term {K L : Usize} (rho : Array U8 32#usize) (n : Usize) (hn : n.val ≤ 2048)
    (hL : 0 < L.val) (hLs : L.val < 256) (hK : K.val < 256) (hnKL : n.val = K.val * L.val)
    (F : Nat) (hF : ∀ e, e < n.val → ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P)
    (a : Array (Array (Array U32 256#usize) L) K) (first : Usize) :
    sampling.expand_a_from_x4_loop rho a n first ⦃ _ => True ⦄ := by
  unfold sampling.expand_a_from_x4_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array (Array U32 256#usize) L) K × Usize) => n.val - p.2.val)
    (fun _ => True)
  · rintro ⟨a', first'⟩ _
    refine WP.spec_mono (x4_body_term rho n a' first' hn hL hLs hK hnKL F hF) ?_
    rintro (⟨a'', first''⟩ | y) h
    · exact ⟨trivial, by show n.val - first''.val < n.val - first'.val; omega⟩
    · trivial
  · trivial


theorem expand_a_into_x4_term {K L : Usize} (rho : Array U8 32#usize) (hL : 0 < L.val) (hLs : L.val < 256)
    (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (F : Nat)
    (hF : ∀ e, e < K.val * L.val →
      ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P)
    (a : Array (Array (Array U32 256#usize) L) K) :
    sampling.expand_a_into_x4 rho a ⦃ _ => True ⦄ := by
  unfold sampling.expand_a_into_x4 sampling.expand_a_from_x4
  step*
  have hn' : n.val = K.val * L.val := n_post
  exact x4_loop_term rho n (by omega) hL hLs hK hn' F (by rw [hn']; exact hF) a 0#usize

theorem expand_a_x4_term {K L : Usize} (rho : Array U8 32#usize) (hL : 0 < L.val) (hLs : L.val < 256)
    (hK : K.val < 256) (hKL : K.val * L.val ≤ 2048) (F : Nat)
    (hF : ∀ e, e < K.val * L.val →
      ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P) :
    sampling.expand_a_x4 K L rho ⦃ _ => True ⦄ := by
  unfold sampling.expand_a_x4
  step*
  exact expand_a_into_x4_term rho hL hLs hK hKL F hF _

theorem ReprMat.unique {K L : Usize} {k ℓ : Nat} {a b : Array (Array (Array U32 256#usize) L) K}
    {m : Vector (Vector Poly ℓ) k} (ha : ReprMat a m) (hb : ReprMat b m) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hk : i < k := by have := ha.len; have := a.property; omega
  have ra := ha.elt i hk
  have rb := hb.elt i hk
  apply Subtype.ext
  apply List.ext_getElem (by rw [(a.val[i]).property, (b.val[i]).property])
  intro j g1 g2
  have hj : j < ℓ := by have := ra.len; have := (a.val[i]).property; omega
  exact congrArg (fun x : Array U32 256#usize => x) (Repr.unique (ra.elt j hj) (rb.elt j hj))


/-- Two `RustM` computations that are both partially correct for a property `P`-gated outcome, terminate when `P`
holds, and agree on every pair of `ok` values, are equal. -/
theorem rustM_eq_of_partial {α : Type} (x y : RustM α) (P : Prop) (Qx Qy : α → Prop)
    (hx : x ⦃ Qx ⦄div) (hy : y ⦃ Qy ⦄div) (hQx : ∀ a, Qx a → P) (hQy : ∀ a, Qy a → P)
    (hxt : P → ∃ a, x = ok a) (hyt : P → ∃ a, y = ok a) (heq : ∀ a b, x = ok a → y = ok b → a = b) : x = y := by
  by_cases hP : P
  · obtain ⟨a, ha⟩ := hxt hP
    obtain ⟨b, hb⟩ := hyt hP
    rw [ha, hb, heq a b ha hb]
  · cases hxc : x with
    | ok a => rw [hxc] at hx; exact absurd (hQx a hx) hP
    | fail e => rw [hxc] at hx; exact hx.elim
    | div =>
      cases hyc : y with
      | ok b => rw [hyc] at hy; exact absurd (hQy b hy) hP
      | fail e => rw [hyc] at hy; exact hy.elim
      | div => rfl

theorem expand_a_x4_eq (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (hl0 : 0 < sp.ℓ) (hk8 : sp.k ≤ 8) (hkl : sp.k + sp.ℓ < 256) (rho : Array U8 32#usize) :
    sampling.expand_a_x4 K L rho = sampling.expand_a K L rho := by
  have hLpos : 0 < L.val := by omega
  have hLs : L.val < 256 := by omega
  have hK256 : K.val < 256 := by omega
  have hKL : K.val * L.val ≤ 2048 := by
    have : K.val * L.val ≤ 8 * 255 := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine rustM_eq_of_partial _ _ (∃ (A : Vector (Vector Poly sp.ℓ) sp.k) (F : Nat),
      Spec.ExpandA sp F (bytesA rho) = some A) _ _
    (expand_a_x4_partial sp K L hK hL hLpos hLs hK256 hKL rho) (expand_a_partial sp K L hK hL rho)
    (fun a ⟨A, F, h, _⟩ => ⟨A, F, h⟩) (fun a ⟨A, F, h, _⟩ => ⟨A, F, h⟩) ?_ ?_ ?_
  · rintro ⟨A, F, hA⟩
    have hF : ∀ e, e < K.val * L.val →
        ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P := by
      intro e he
      have h1 : e / L.val < sp.k := by
        rw [← hK]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
      have h2 : e % L.val < sp.ℓ := by rw [← hL]; exact Nat.mod_lt _ hLpos
      exact ⟨_, expandA_ent sp F (bytesA rho) A hA _ h1 _ h2⟩
    exact WP.spec_imp_exists (expand_a_x4_term rho hLpos hLs hK256 hKL F hF) |>.imp fun r hr => hr.1
  · rintro ⟨A, F, hA⟩
    exact (WP.spec_imp_exists (expand_a_spec sp K L hK hL rho A F hA)).imp fun r hr => hr.1
  · intro a b ha hb
    have h1 := expand_a_x4_partial sp K L hK hL hLpos hLs hK256 hKL rho
    have h2 := expand_a_partial sp K L hK hL rho
    rw [ha] at h1
    rw [hb] at h2
    obtain ⟨A1, F1, e1, r1⟩ := (WP.dspec_ok _).1 h1
    obtain ⟨A2, F2, e2, r2⟩ := (WP.dspec_ok _).1 h2
    have e1' := ExpandA_mono sp _ F1 (max F1 F2) A1 e1 (le_max_left _ _)
    have e2' := ExpandA_mono sp _ F2 (max F1 F2) A2 e2 (le_max_right _ _)
    have hAA : A1 = A2 := Option.some.inj (e1'.symm.trans e2')
    subst hAA
    exact ReprMat.unique r1 r2

end Proofs
