import Proofs.ExpandA4
import Proofs.TrOuter
import Proofs.PartialSample
import Proofs.Verify

/-!
# The 4-way verify body equals the scalar one (core)

`verify.verify_internal_x4 K L` (the 4-way ExpandA, prepared key built in place) is *equal* as a `RustM` value to the
scalar `verify.verify_internal K L`, for every input, for every parameter set that satisfies `Params.Std`. Equality
includes divergence: both sides are `div` exactly when the spec's `ExpandA` has no result at any fuel.

This file holds the equalities themselves, so that `Proofs/API.lean` (which connects the public `api.verify_NN` to the
bodies the refinement theorems are about) can use them; the statements about the `api` wrappers run with the 4-way
verifier are in `Proofs/FastVerify.lean`.

* `expand_a_x4_eq_std`, `expand_a_tr_into_x4_eq`: the 4-way ExpandA (with `tr`) is the scalar one.
* `prepare_vk_into_x4_zero`, `prepare_vk_x4_zeroed_bind`, `prepare_vk_x4_eq`: the key half.
* `verify_internal_x4_eq`: the whole verifier, for any `p`, `pk`, `m_prefix`, `m`, `sig`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open Verify
open SampleA

/-- `prepare_vk_into_x4` on the all-zero key is `prepare_vk_x4`. -/
theorem prepare_vk_into_x4_zero (K L : Usize) (pk : Slice U8) :
    verify.prepare_vk_into_x4 pk
      ({ a_hat := Array.repeat K (Array.repeat L (Array.repeat 256#usize 0#u32))
         t1_2d_hat := Array.repeat K (Array.repeat 256#usize 0#u32)
         tr := Array.repeat 64#usize 0#u8 } : verify.PreparedVk K L) = verify.prepare_vk_x4 K L pk := rfl

/-- The in-place 4-way key half followed by anything is the by-value `prepare_vk_x4` followed by it. -/
theorem prepare_vk_x4_zeroed_bind {α : Type} (K L : Usize) (pk : Slice U8)
    (F : verify.PreparedVk K L → RustM α) :
    (verify.PreparedVk.zeroed K L >>= fun vk => verify.prepare_vk_into_x4 pk vk >>= F) =
      (verify.prepare_vk_x4 K L pk >>= F) := by
  simp only [verify.PreparedVk.zeroed, Std.bind_tc_ok]
  rw [prepare_vk_into_x4_zero]

/-- The numeric facts about `K`, `L` that the 4-way ExpandA needs, from the standard parameter bundle. -/
theorem expand_a_x4_eq_std {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (rho : Array U8 32#usize) :
    sampling.expand_a_x4 K L rho = sampling.expand_a K L rho :=
  expand_a_x4_eq sp K L hp.1.K_eq hp.1.L_eq hp.2.ell_pos hp.2.k_le_8 hp.2.kl_lt rho

theorem bytesA_inj {n : Usize} {a b : Array U8 n} (h : bytesA a = bytesA b) : a = b :=
  Subtype.ext (List.map_injective_iff.mpr ofNat_val_injective h)

/-- **The 3+1 ExpandA with `tr` is ExpandA followed by `tr = H(pk, 64)`.** `expand_a_tr_into_x4` returns
exactly what `expand_a` and `hash_pk` return, as `RustM` values (so including divergence, which happens where ExpandA's
does), whatever matrix it starts from and whatever its schedule decides. -/
theorem expand_a_tr_into_x4_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (rho : Array U8 32#usize) (pk : Slice U8)
    (a : Array (Array (Array U32 256#usize) L) K) :
    sampling.expand_a_tr_into_x4 rho pk a =
      (sampling.expand_a K L rho >>= fun a1 => verify.hash_pk pk >>= fun tr => ok (tr, a1)) := by
  have hK : K.val = sp.k := hp.1.K_eq
  have hL : L.val = sp.ℓ := hp.1.L_eq
  have hl0 := hp.2.ell_pos
  have hk8 := hp.2.k_le_8
  have hkl := hp.2.kl_lt
  have hLpos : 0 < L.val := by omega
  have hLs : L.val < 256 := by omega
  have hK256 : K.val < 256 := by omega
  have hKL : K.val * L.val ≤ 2048 := by
    have : K.val * L.val ≤ 8 * 255 := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨tr0, htr0, htr0b⟩ := WP.spec_imp_exists (hash_pk_spec pk)
  rw [htr0]
  simp only [Std.bind_tc_ok]
  have hx := expand_a_tr_into_x4_partial (K := K) (L := L) rho pk hLpos hLs hK256 hKL a
  have hy : (sampling.expand_a K L rho >>= fun a1 => ok (tr0, a1)) ⦃ r => (∃ (A : Vector (Vector Poly sp.ℓ) sp.k)
      (F : Nat), Spec.ExpandA sp F (bytesA rho) = some A ∧ ReprMat r.2 A) ∧ r.1 = tr0 ⦄div := by
    refine WP.dspec_bind' (expand_a_partial sp K L hK hL rho) ?_
    rintro a1 ⟨A, F, hA, hR⟩
    simp only [WP.dspec_ok]
    exact ⟨⟨A, F, hA, hR⟩, trivial⟩
  refine rustM_eq_of_partial _ _ (∃ (A : Vector (Vector Poly sp.ℓ) sp.k) (F : Nat),
      Spec.ExpandA sp F (bytesA rho) = some A) _ _ hx hy ?_ ?_ ?_ ?_ ?_
  · rintro r ⟨⟨F, Pf, hg⟩, _⟩
    obtain ⟨A, hA, _⟩ := goodA_to_expandA sp hK hL rho F Pf r.2 hg
    exact ⟨A, F, hA⟩
  · rintro r ⟨⟨A, F, hA, _⟩, _⟩
    exact ⟨A, F, hA⟩
  · rintro ⟨A, F, hA⟩
    have hF : ∀ e, e < K.val * L.val →
        ∃ P, Spec.RejNTTPoly F (pSeed (bytesA rho) (e / L.val) (e % L.val)) = some P := by
      intro e he
      have h1 : e / L.val < sp.k := by
        rw [← hK]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
      have h2 : e % L.val < sp.ℓ := by rw [← hL]; exact Nat.mod_lt _ hLpos
      exact ⟨_, expandA_ent sp F (bytesA rho) A hA _ h1 _ h2⟩
    exact (WP.spec_imp_exists (expand_a_tr_into_x4_term rho pk hLpos hLs hK256 hKL F hF a)).imp fun r hr => hr.1
  · rintro ⟨A, F, hA⟩
    obtain ⟨a1, ha1, _⟩ := WP.spec_imp_exists (expand_a_spec sp K L hK hL rho A F hA)
    exact ⟨(tr0, a1), by rw [ha1]; rfl⟩
  · intro r1 r2 h1 h2
    have e1 := hx
    have e2 := hy
    rw [h1] at e1
    rw [h2] at e2
    obtain ⟨⟨F1, Pf1, hg⟩, hb⟩ := (WP.dspec_ok _).1 e1
    obtain ⟨⟨A2, F2, hA2, hR2⟩, h2tr⟩ := (WP.dspec_ok _).1 e2
    obtain ⟨A1, hA1, hR1⟩ := goodA_to_expandA sp hK hL rho F1 Pf1 r1.2 hg
    have e1' := ExpandA_mono sp _ F1 (max F1 F2) A1 hA1 (le_max_left _ _)
    have e2' := ExpandA_mono sp _ F2 (max F1 F2) A2 hA2 (le_max_right _ _)
    have hAA : A1 = A2 := Option.some.inj (e1'.symm.trans e2')
    subst hAA
    have hmat : r1.2 = r2.2 := ReprMat.unique hR1 hR2
    have htr : r1.1 = r2.1 := by
      apply bytesA_inj
      rw [hb, h2tr, htr0b]
    exact Prod.ext htr hmat

/-- **`prepare_vk_x4` is `prepare_vk`.** -/
theorem prepare_vk_x4_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk : Slice U8) :
    verify.prepare_vk_x4 K L pk = verify.prepare_vk K L pk := by
  unfold verify.prepare_vk_x4 verify.prepare_vk
  simp only [expand_a_tr_into_x4_eq hp, bind_assoc, Std.bind_tc_ok]
  rfl

/-- **`verify_internal_x4` is `verify_internal`**, as `RustM` values (so including divergence), for every input. -/
theorem verify_internal_x4_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (p : Impl.params.Params) (pk m_prefix m sig : Slice U8) :
    verify.verify_internal_x4 K L p pk m_prefix m sig = verify.verify_internal K L p pk m_prefix m sig := by
  rw [verify_internal_def]
  unfold verify.verify_internal_x4
  simp only [prepare_vk_x4_zeroed_bind, prepare_vk_x4_eq hp]
  rfl

end Proofs
