import Proofs.Steps
import Proofs.StdParams
import Proofs.EncodeKeys

/-!
# Bridge lemmas for the Sign / Verify composition

Three gaps between the leaf theorems and what the composition needs.

1. **The `Z_q` norm of a stored vector.** `sign_internal` calls `vec_infinity_norm` on `z` and `ct0`, which are
   held as `ReprVec` (canonical residues of `Z_q` elements), and the specification compares the `Z_q` norm
   `‖·‖∞` (= `|c mod± q|` coefficientwise, `Spec.Rounding`). `vec_infinity_norm_spec_zq` says the extracted norm is
   exactly that, with no bound premise: `|c mod± q| ≤ (q-1)/2` always holds
   (`Zq_modPM_natAbs_le`), so the premise of `vec_infinity_norm_spec` is automatic once the stored vector is
   viewed as the integer vector `z.map Poly.modPM` (`ReprVec.modPM`).
2. **`LowBits` is bounded by `γ₂`.** `‖LowBitsVec sp v‖∞ ≤ γ₂` (the spec's `r₀ ∈ (−γ₂, γ₂]`, minus one in
   the corner case of Algorithm 36 step 5). `r₀` is held as a `ReprIntVec` of `LowBitsVec` (`response_spec`), so the
   Int-norm `vec_infinity_norm_spec` applies; `vec_infinity_norm_lowbits_spec` packages that.
3. **`t₁` after `pkDecode`.** Every coefficient of the spec's `t₁` lies in `[0, 2^10)` (`pkDecode_t1_range`),
   which is the range premise of `scale_vec_by_2d_spec`; `pk_decode_spec_range` and
   `scale_vec_by_2d_pk_decode` give the forms Verify uses.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## 1. The `Z_q` infinity norm -/

/-- `‖f w‖∞ = ‖w‖∞` for a norm-preserving map applied entrywise. -/
theorem infNorm_map {α β : Type} [InfNorm α] [InfNorm β] {n : Nat} (f : α → β)
    (hf : ∀ x, ‖f x‖∞ = ‖x‖∞) (w : Vector α n) : ‖w.map f‖∞ = ‖w‖∞ := by
  rw [infNorm_vec_eq, infNorm_vec_eq, Vector.toList_map, List.foldl_map]
  simp only [hf]

/-- `|c mod± q| ≤ (q-1)/2` for every `c ∈ Z_q`. -/
theorem Zq_modPM_natAbs_le (c : Zq) : (Zq.modPM c).natAbs ≤ (Spec.q - 1) / 2 := by
  have h1 := Spec.modPM_lower (c.val : Int) Spec.q (by decide)
  have h2 := Spec.modPM_upper (c.val : Int) Spec.q (by decide)
  unfold Zq.modPM
  simp only [Spec.q] at h1 h2 ⊢
  omega

/-- The norm of a `Z_q` coefficient is at most `(q-1)/2`. -/
theorem infNorm_Zq_le (c : Zq) : ‖c‖∞ ≤ 4190208 := by
  have := Zq_modPM_natAbs_le c
  simp only [Spec.q] at this
  exact this

/-- `Poly.modPM` followed by the coercion back to `Z_q` is the identity. -/
theorem Poly_modPM_toZq (p : Poly) : RPoly.toZq (Poly.modPM p) = p := by
  apply Vector.ext
  intro i hi
  simp [RPoly.toZq, Poly.modPM, Zq.modPM_cast]

/-- `Poly.modPM` preserves the norm (`‖c‖∞ = |c mod± q|` coefficientwise). -/
theorem infNorm_Poly_modPM (p : Poly) : ‖Poly.modPM p‖∞ = ‖p‖∞ :=
  infNorm_map Zq.modPM (fun _ => rfl) p

/-- `(z.map Poly.modPM)` has the same norm as `z`. -/
theorem infNorm_vec_modPM {n : Nat} (z : Vector Poly n) : ‖z.map Poly.modPM‖∞ = ‖z‖∞ :=
  infNorm_map Poly.modPM infNorm_Poly_modPM z

/-- The `Z_q` norm of a vector of polynomials is at most `(q-1)/2`. -/
theorem infNorm_vec_Zq_le {n : Nat} (z : Vector Poly n) : ‖z‖∞ ≤ 4190208 :=
  (infNorm_le_iff z _).2 fun i _ => (infNorm_le_iff z[i] _).2 fun k _ => infNorm_Zq_le _

/-- A canonical array representing `p ∈ R_q` stores the centered integer polynomial `p mod± q`. -/
theorem Repr.modPM {a : Array U32 256#usize} {p : Poly} (h : Repr a p) : ReprInt a (Poly.modPM p) :=
  ReprInt.of_repr (by rw [Poly_modPM_toZq]; exact h)

/-- A stored vector of `Z_q` polynomials stores the integer vector of their centered representatives. -/
theorem ReprVec.modPM {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {v : Vector Poly k}
    (h : ReprVec a v) : ReprIntVec a (v.map Poly.modPM) :=
  ⟨h.len, fun i hi => by simpa using (h.elt i hi).modPM⟩

/-- **`vec_infinity_norm` of a stored `Z_q` vector is the specification's `‖z‖∞`** (`|c mod± q|`, maximum over
all coefficients), with no bound premise. -/
theorem vec_infinity_norm_spec_zq {N : Usize} {n : Nat} (w : Array (Array U32 256#usize) N)
    (z : Vector Poly n) (hw : ReprVec w z) :
    rounding.vec_infinity_norm w ⦃ r => r.val = ‖z‖∞ ⦄ := by
  have h := vec_infinity_norm_spec w (z.map Poly.modPM) hw.modPM
    (by rw [infNorm_vec_modPM]; exact infNorm_vec_Zq_le z)
  rw [infNorm_vec_modPM] at h
  exact h

/-! ## 2. `LowBits` is bounded by `γ₂` -/

/-- `LowBits(r) ∈ [−γ₂, γ₂]` for every `r ∈ Z_q` (FIPS 204 Alg. 36: `r₀ ∈ (−γ₂, γ₂]`, and `r₀ − 1` in the corner
case). -/
theorem LowBits_bounds (sp : Spec.Params) (hg : StdGamma2 sp) (r : Zq) :
    -(sp.γ₂ : Int) ≤ Spec.LowBits sp r ∧ Spec.LowBits sp r ≤ sp.γ₂ := by
  have hpos : 0 < sp.γ₂ := by rcases hg with h | h <;> omega
  have h1 := Spec.modPM_lower (r.val : Int) (2 * sp.γ₂) (by omega)
  have h2 := Spec.modPM_upper (r.val : Int) (2 * sp.γ₂) (by omega)
  have e1 : (2 * sp.γ₂ + 1) / 2 = sp.γ₂ := by omega
  have e2 : 2 * sp.γ₂ / 2 = sp.γ₂ := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [LowBits_eq, Decompose_eq]
  split <;> simp only [] <;> omega

/-- `|LowBits(r)| ≤ γ₂`. -/
theorem LowBits_natAbs_le (sp : Spec.Params) (hg : StdGamma2 sp) (r : Zq) :
    ‖Spec.LowBits sp r‖∞ ≤ sp.γ₂ := by
  have := LowBits_bounds sp hg r
  rw [infNorm_int]
  omega

/-- **`‖LowBitsVec sp v‖∞ ≤ γ₂`** for every `v ∈ R_q^n`. -/
theorem LowBitsVec_infNorm_le (sp : Spec.Params) (hg : StdGamma2 sp) {n : Nat} (v : Vector Poly n) :
    ‖Spec.LowBitsVec sp v‖∞ ≤ sp.γ₂ :=
  (infNorm_le_iff _ _).2 fun i hi => (infNorm_le_iff _ _).2 fun k hk => by
    simpa [Spec.LowBitsVec] using LowBits_natAbs_le sp hg v[i][k]

/-- `γ₂ ≤ (q-1)/2`, the premise range of `vec_infinity_norm_spec`. -/
theorem StdGamma2.le_half {sp : Spec.Params} (hg : StdGamma2 sp) : sp.γ₂ ≤ 4190208 := by
  rcases hg with h | h <;> omega

/-- **The `r0` norm check of `sign_internal`.** `r0` is held as a `ReprIntVec` of `LowBitsVec sp v` (as
`response_spec` returns it); `vec_infinity_norm` returns the spec's `‖LowBitsVec sp v‖∞`, which is at most `γ₂`.
No norm premise is needed. -/
theorem vec_infinity_norm_lowbits_spec {N : Usize} {n : Nat} (sp : Spec.Params) (hg : StdGamma2 sp)
    (w : Array (Array U32 256#usize) N) (v : Vector Poly n) (hw : ReprIntVec w (Spec.LowBitsVec sp v)) :
    rounding.vec_infinity_norm w ⦃ r => r.val = ‖Spec.LowBitsVec sp v‖∞ ∧ r.val ≤ sp.γ₂ ⦄ := by
  have hb := LowBitsVec_infNorm_le sp hg v
  apply WP.spec_mono (vec_infinity_norm_spec w (Spec.LowBitsVec sp v) hw (le_trans hb hg.le_half))
  intro r hr
  exact ⟨hr, by omega⟩

/-! ## 3. `t₁` after `pkDecode` -/

/-- Every coefficient of the `t₁` produced by `Spec.pkDecode` lies in `[0, 2^10)` (`d = 13`). -/
theorem pkDecode_t1_range (sp : Spec.Params) (hd : sp.d = 13) (pk : List UInt8) :
    ∀ (r : Nat) (hr : r < sp.k) (c : Nat) (hc : c < 256),
      0 ≤ ((Spec.pkDecode sp pk).2[r]'hr)[c]'hc ∧ ((Spec.pkDecode sp pk).2[r]'hr)[c]'hc < 1024 := by
  intro r hr c hc
  have ht := t1Bits_eq sp hd
  have hb : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
  have e : ((Spec.pkDecode sp pk).2[r]'hr)[c]'hc =
      (SimpleBitUnpack (slice pk (32 + r * (32 * sp.t1Bits)) (32 * sp.t1Bits)) (2 ^ sp.t1Bits - 1))[c]'hc := by
    have := pkDecode_get sp pk r hr
    exact congrArg (fun v => v[c]'hc) this
  rw [e, ht, SimpleBitUnpack_get _ _ _ hc, hb]
  have hlt := BV_lt (byteBit (slice pk (32 + r * (32 * 10)) (32 * 10))) (byteBit_le _) (10 * c) 10
  have h2 : (2 : Nat) ^ 10 = 1024 := by norm_num
  rw [h2] at hlt
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast hlt⟩

/-- **`pk_decode_spec` with the range of `t₁`**: besides `ρ` and the `ReprIntVec` of `t₁`, every coefficient of
the decoded `t₁` is in `[0, 2^10)`, which is the premise of `scale_vec_by_2d_spec`. -/
theorem pk_decode_spec_range {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (pk : Slice U8) (hL : pk.val.length = 32 + 320 * sp.k) :
    encode.pk_decode K pk ⦃ r => bytesA r.1 = (Spec.pkDecode sp (bytes pk)).1 ∧
      ReprIntVec r.2 (Spec.pkDecode sp (bytes pk)).2 ∧
      ∀ (i : Nat) (hi : i < sp.k) (c : Nat) (hc : c < 256),
        0 ≤ ((Spec.pkDecode sp (bytes pk)).2[i]'hi)[c]'hc ∧
          ((Spec.pkDecode sp (bytes pk)).2[i]'hi)[c]'hc < 1024 ⦄ := by
  apply WP.spec_mono (pk_decode_spec ip sp hp pk hL)
  intro r hr
  exact ⟨hr.1, hr.2, pkDecode_t1_range sp hp.d_eq _⟩

/-- **`scale_vec_by_2d` on the `t₁` array of `pk_decode`**: the range premise is discharged by
`pkDecode_t1_range`, leaving only `ReprIntVec` (as `pk_decode_spec` returns it). -/
theorem scale_vec_by_2d_pk_decode {N : Usize} (sp : Spec.Params) (hd : sp.d = 13) (pk : List UInt8)
    (t1 : Array (Array U32 256#usize) N) (ht : ReprIntVec t1 (Spec.pkDecode sp pk).2) :
    verify.scale_vec_by_2d t1 ⦃ r =>
      ReprVec r (((Spec.pkDecode sp pk).2.map RPoly.toZq).map (·.map (· * (2 ^ sp.d : Zq)))) ⦄ :=
  scale_vec_by_2d_spec sp hd t1 _ ht (pkDecode_t1_range sp hd pk)

end Proofs
