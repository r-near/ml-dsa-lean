import Proofs.PartialVerify
import Proofs.APIInternal

/-!
# Partial correctness and panic-freedom of the public verification API

For `NN ∈ {44, 65, 87}` and every `pk`, `m`, `ctx`, `σ` of the API types:

* `verify_NN_partial`: `api.verify_NN` never returns `fail` (it never panics), and if it returns `ok b` then
  `Spec.Verify … F = some b` for some fuel `F`.
* `verify_internal_NN_partial`: the same for `api.verify_internal_NN` and `Spec.Verify_internal`.
* `verify_NN_exact`, `verify_internal_NN_exact`: together with the older `verify_NN_correct` (spec `some b`
  at `F` gives `ok b`), the Rust agrees exactly with the unbounded FIPS 204 algorithm: for all `F` and `b`,
  `Spec … F = some b → Rust = ok b`; `Rust = ok b → ∃ F, Spec … F = some b`; and the Rust is never `fail`.
  So the Rust diverges exactly when FIPS 204 diverges (no fuel makes the spec return `some`).

No premise other than the argument types. See `Proofs/Partial.lean` for the technique.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open API APIInternal

theorem dspec_not_fail {α : Type} {x : RustM α} {P : α → Prop} (h : x ⦃ P ⦄div) : ∀ e, x ≠ .fail e := by
  intro e he
  rw [he] at h
  exact h

/-! ## Generic bodies -/

theorem verifyInternalAPI_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (pk : Array U8 n) (m : Slice U8) (sig : Array U8 N) :
    verifyInternalAPI n N K L (ok ip) pk m sig ⦃ r =>
      ∃ F, Spec.Verify_internal sp (bytesA pk) (bytes m) (bytesA sig) F = some r ⦄div := by
  unfold verifyInternalAPI
  simp only [Std.bind_tc_ok]
  step*
  refine WP.dspec_mono' (verify_internal_partial hp s s2 s1 m) ?_
  rintro r ⟨F, hF⟩
  refine ⟨F, ?_⟩
  rw [s_post, s2_post, s1_post] at hF
  simp only [bytes_to_slice, bytesA_empty, List.nil_append] at hF
  exact hF

theorem verifyAPI_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize)
    (pk : Array U8 n) (m ctx : Slice U8) (sig : Array U8 N) :
    verifyAPI n N K L (ok ip) pk m ctx sig ⦃ r =>
      ∃ F, Spec.Verify sp (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some r ⦄div := by
  unfold verifyAPI
  refine dspec_bind_of_spec (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · have h' : 255 < (bytes ctx).length := by simp only [bytes_length]; exact ho
    simp only [WP.dspec_ok]
    exact ⟨{}, Verify_long sp _ _ _ _ {} h'⟩
  · obtain ⟨hl, htake, hdrop⟩ := ho
    simp only [Std.bind_tc_ok]
    step*
    have hlen : ctx.len.val = ctx.val.length := by simp
    have hs1 : bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx :=
      prefix_bytes ctx b' i1 s1 (by rw [i1_post, hlen]) s1_post1 htake
    have hbs : bytes s = bytesA pk := by rw [s_post, bytes_to_slice]
    have hbs2 : bytes s2 = bytesA sig := by rw [s2_post, bytes_to_slice]
    refine WP.dspec_mono' (verify_internal_partial hp s s2 s1 m) ?_
    rintro r ⟨F, hF⟩
    refine ⟨F, ?_⟩
    rw [Verify_short sp _ _ _ _ F (by simpa using hl)]
    rw [hbs, hbs2, hs1] at hF
    simpa [List.append_assoc] using hF

/-! ## The six public functions -/

theorem verify_44_dspec (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_44 pk m ctx sig ⦃ r =>
      ∃ F, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_44_eq, hip]
  exact verifyAPI_partial hp _ _ pk m ctx sig

theorem verify_65_dspec (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_65 pk m ctx sig ⦃ r =>
      ∃ F, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_65_eq, hip]
  exact verifyAPI_partial hp _ _ pk m ctx sig

theorem verify_87_dspec (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_87 pk m ctx sig ⦃ r =>
      ∃ F, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_87_eq, hip]
  exact verifyAPI_partial hp _ _ pk m ctx sig

theorem verify_internal_44_dspec (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_internal_44 pk m sig ⦃ r =>
      ∃ F, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_internal_44_eq, hip]
  exact verifyInternalAPI_partial hp _ _ pk m sig

theorem verify_internal_65_dspec (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_internal_65 pk m sig ⦃ r =>
      ∃ F, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_internal_65_eq, hip]
  exact verifyInternalAPI_partial hp _ _ pk m sig

theorem verify_internal_87_dspec (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_internal_87 pk m sig ⦃ r =>
      ∃ F, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some r ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_internal_87_eq, hip]
  exact verifyInternalAPI_partial hp _ _ pk m sig

/-! ## Headline statements -/

/-- **ML-DSA-44 `verify`, partial correctness and panic-freedom.** For every input the Rust never returns
`fail` (never panics), and if it returns `ok b` then the spec returns `some b` at some fuel. -/
theorem verify_44_partial (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_44 pk m ctx sig ≠ .fail e) ∧
    ∀ b, api.verify_44 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b :=
  ⟨dspec_not_fail (verify_44_dspec pk m ctx sig), fun b hb => WP.dspec_imp_forall (verify_44_dspec pk m ctx sig) b hb⟩

/-- **ML-DSA-65 `verify`, partial correctness and panic-freedom.** -/
theorem verify_65_partial (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_65 pk m ctx sig ≠ .fail e) ∧
    ∀ b, api.verify_65 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b :=
  ⟨dspec_not_fail (verify_65_dspec pk m ctx sig), fun b hb => WP.dspec_imp_forall (verify_65_dspec pk m ctx sig) b hb⟩

/-- **ML-DSA-87 `verify`, partial correctness and panic-freedom.** -/
theorem verify_87_partial (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_87 pk m ctx sig ≠ .fail e) ∧
    ∀ b, api.verify_87 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b :=
  ⟨dspec_not_fail (verify_87_dspec pk m ctx sig), fun b hb => WP.dspec_imp_forall (verify_87_dspec pk m ctx sig) b hb⟩

/-- **ML-DSA-44 `verify_internal`, partial correctness and panic-freedom.** -/
theorem verify_internal_44_partial (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_internal_44 pk m sig ≠ .fail e) ∧
    ∀ b, api.verify_internal_44 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b :=
  ⟨dspec_not_fail (verify_internal_44_dspec pk m sig),
    fun b hb => WP.dspec_imp_forall (verify_internal_44_dspec pk m sig) b hb⟩

/-- **ML-DSA-65 `verify_internal`, partial correctness and panic-freedom.** -/
theorem verify_internal_65_partial (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_internal_65 pk m sig ≠ .fail e) ∧
    ∀ b, api.verify_internal_65 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b :=
  ⟨dspec_not_fail (verify_internal_65_dspec pk m sig),
    fun b hb => WP.dspec_imp_forall (verify_internal_65_dspec pk m sig) b hb⟩

/-- **ML-DSA-87 `verify_internal`, partial correctness and panic-freedom.** -/
theorem verify_internal_87_partial (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_internal_87 pk m sig ≠ .fail e) ∧
    ∀ b, api.verify_internal_87 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b :=
  ⟨dspec_not_fail (verify_internal_87_dspec pk m sig),
    fun b hb => WP.dspec_imp_forall (verify_internal_87_dspec pk m sig) b hb⟩

/-! ## Exactness: the Rust agrees with the unbounded FIPS 204 algorithm -/

/-- **ML-DSA-44 `verify` is exactly the unbounded FIPS 204 Algorithm 3.** For all `F` and `b`:
`Spec … F = some b → Rust = ok b`; `Rust = ok b → ∃ F, Spec … F = some b`; and the Rust is never `fail`.
(So the Rust diverges exactly when the spec returns `none` at every fuel.) -/
theorem verify_44_exact (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_44 pk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_44 pk m ctx sig = ok b) ∧
    (∀ b, api.verify_44 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :=
  ⟨(verify_44_partial pk m ctx sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_44_correct pk m ctx sig F b hs)
      exact hr,
    (verify_44_partial pk m ctx sig).2⟩

/-- **ML-DSA-65 `verify` is exactly the unbounded FIPS 204 Algorithm 3.** -/
theorem verify_65_exact (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_65 pk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_65 pk m ctx sig = ok b) ∧
    (∀ b, api.verify_65 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :=
  ⟨(verify_65_partial pk m ctx sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_65_correct pk m ctx sig F b hs)
      exact hr,
    (verify_65_partial pk m ctx sig).2⟩

/-- **ML-DSA-87 `verify` is exactly the unbounded FIPS 204 Algorithm 3.** -/
theorem verify_87_exact (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_87 pk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_87 pk m ctx sig = ok b) ∧
    (∀ b, api.verify_87 pk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :=
  ⟨(verify_87_partial pk m ctx sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_87_correct pk m ctx sig F b hs)
      exact hr,
    (verify_87_partial pk m ctx sig).2⟩

/-- **ML-DSA-44 `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_44_exact (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_internal_44 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_44 pk m sig = ok b) ∧
    (∀ b, api.verify_internal_44 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b) :=
  ⟨(verify_internal_44_partial pk m sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_internal_44_correct pk m sig F b hs)
      exact hr,
    (verify_internal_44_partial pk m sig).2⟩

/-- **ML-DSA-65 `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_65_exact (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_internal_65 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_65 pk m sig = ok b) ∧
    (∀ b, api.verify_internal_65 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b) :=
  ⟨(verify_internal_65_partial pk m sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_internal_65_correct pk m sig F b hs)
      exact hr,
    (verify_internal_65_partial pk m sig).2⟩

/-- **ML-DSA-87 `verify_internal` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_87_exact (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_internal_87 pk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_87 pk m sig = ok b) ∧
    (∀ b, api.verify_internal_87 pk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b) :=
  ⟨(verify_internal_87_partial pk m sig).1,
    fun F b hs => by
      obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (verify_internal_87_correct pk m sig F b hs)
      exact hr,
    (verify_internal_87_partial pk m sig).2⟩

end Proofs
