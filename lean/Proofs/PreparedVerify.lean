import Proofs.PartialAPI

/-!
# Prepared verifying keys (`verifying_key_NN`, `verify_prepared_NN`, `verify_internal_prepared_NN`)

`api.verifying_key_NN pk` computes the part of Verify that depends on the public key alone (Â, NTT(t₁ · 2^d),
tr = H(pk, 64)); `api.verify_prepared_NN` and `api.verify_internal_prepared_NN` check a signature against it.
Proved for `NN ∈ {44, 65, 87}`:

* `verifying_key_NN_partial`: `verifying_key_NN pk` never fails; it returns a key holding exactly Â = ExpandA(ρ)
  (at some fuel of the spec), NTT(t₁ · 2^d) and tr = H(pk, 64) for `(ρ, t₁) = pkDecode pk`; it diverges only where
  ExpandA does (the `⦃ ⦄div` form of `PartialAPI`).
* `verify_prepared_NN_eq`, `verify_internal_prepared_NN_eq`: if `verifying_key_NN pk = ok vk`, then for every
  `m`, `ctx`, `σ` the prepared function returns exactly what `verify_NN pk m ctx σ` (resp.
  `verify_internal_NN pk m σ`) returns, including `fail` and `div`. No premise besides the `ok vk`: since
  `verify_NN` rejects a malformed σ before it prepares the key, the unprepared function never diverges where the
  prepared one is not even defined.
* `verify_prepared_NN_exact`, `verify_internal_prepared_NN_exact`: the prepared functions agree exactly with the
  unbounded FIPS 204 Algorithm 3 (resp. 8) on the key bytes `vk` was built from, in the style of
  `verify_NN_exact`: never `fail`; the spec's verdict at any fuel is the Rust result; a Rust result is the spec's
  verdict at some fuel.

The equality is a rewrite of `verify_internal` (`prepare_vk`, then `verify_decoded`) against
`verify_prepared_internal` (`verify_decoded` on a `vk` equal to the prepared one): see `Proofs/Verify.lean` for the
pieces (`prepare_vk_spec`, `verify_decoded_spec`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open API APIInternal Verify

/-! ## Generic bodies -/

/-- The body of `api.verify_prepared_NN`, generic in the array size and the parameter record. -/
def verifyPreparedAPI (N : Usize) (K L : Usize) (P : RustM params.Params) (vk : verify.PreparedVk K L)
    (m ctx : Slice U8) (sig : Array U8 N) : RustM Bool := do
  let o ← api.ctx_prefix ctx
  match o with
  | none => ok false
  | some b =>
    let p ← P
    let i := Slice.len ctx
    let i1 ← 2#usize + i
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) b
        { «end» := i1 }
    let s1 ← lift (Array.to_slice sig)
    verify.verify_prepared_internal p vk s m s1

/-- The body of `api.verify_internal_prepared_NN`. -/
def verifyInternalPreparedAPI (N : Usize) (K L : Usize) (P : RustM params.Params) (vk : verify.PreparedVk K L)
    (m : Slice U8) (sig : Array U8 N) : RustM Bool := do
  let p ← P
  let s ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s1 ← lift (Array.to_slice sig)
  verify.verify_prepared_internal p vk s m s1

theorem verify_prepared_44_def (vk : api.VerifyingKey44) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_prepared_44 vk m ctx sig =
      verifyPreparedAPI 2420#usize 4#usize 4#usize params.ML_DSA_44 vk.inner m ctx sig := rfl
theorem verify_prepared_65_def (vk : api.VerifyingKey65) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_prepared_65 vk m ctx sig =
      verifyPreparedAPI 3309#usize 6#usize 5#usize params.ML_DSA_65 vk.inner m ctx sig := rfl
theorem verify_prepared_87_def (vk : api.VerifyingKey87) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_prepared_87 vk m ctx sig =
      verifyPreparedAPI 4627#usize 8#usize 7#usize params.ML_DSA_87 vk.inner m ctx sig := rfl

theorem verify_internal_prepared_44_def (vk : api.VerifyingKey44) (m : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_internal_prepared_44 vk m sig =
      verifyInternalPreparedAPI 2420#usize 4#usize 4#usize params.ML_DSA_44 vk.inner m sig := rfl
theorem verify_internal_prepared_65_def (vk : api.VerifyingKey65) (m : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_internal_prepared_65 vk m sig =
      verifyInternalPreparedAPI 3309#usize 6#usize 5#usize params.ML_DSA_65 vk.inner m sig := rfl
theorem verify_internal_prepared_87_def (vk : api.VerifyingKey87) (m : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_internal_prepared_87 vk m sig =
      verifyInternalPreparedAPI 4627#usize 8#usize 7#usize params.ML_DSA_87 vk.inner m sig := rfl

/-! ## `verify_internal = prepare_vk ; verify_prepared_internal` -/

/-- For a key `vk` that `prepare_vk` returns for `pk`, the unprepared `verify_internal` and the prepared
`verify_prepared_internal` are the same computation (for a `pk` of the right length). -/
theorem verify_internal_prepared_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk m_prefix m sig : Slice U8) (hpk : pk.val.length = sp.pkLen)
    (vk : verify.PreparedVk K L) (hvk : verify.prepare_vk K L pk = ok vk) :
    verify.verify_internal K L ip pk m_prefix m sig = verify.verify_prepared_internal ip vk m_prefix m sig := by
  obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (pk_len_spec hp)
  have hg : (Slice.len pk != r) = false := by
    cases hb : (Slice.len pk != r)
    · rfl
    · exact absurd (by rw [hrv]; exact hpk) ((len_bne_iff pk r).1 hb)
  have hg' : pk.val.length = r.val := by rw [hrv]; exact hpk
  unfold verify.verify_internal verify.verify_prepared_internal
  simp [hr, hg, hg', hvk]

/-- The API bodies: `verifyPreparedAPI` on a prepared key equals `verifyAPI` on the key bytes. -/
theorem verifyPreparedAPI_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.pkLen) (pk : Array U8 n)
    (vk : verify.PreparedVk K L) (hvk : verify.prepare_vk K L (Array.to_slice pk) = ok vk)
    (m ctx : Slice U8) (sig : Array U8 N) :
    verifyPreparedAPI N K L (ok ip) vk m ctx sig = verifyAPI n N K L (ok ip) pk m ctx sig := by
  have hpkl : (Array.to_slice pk).val.length = sp.pkLen := by
    have := pk.property
    simp only [Array.to_slice]
    omega
  have key : ∀ mp m' s, verify.verify_internal K L ip (Array.to_slice pk) mp m' s =
      verify.verify_prepared_internal ip vk mp m' s :=
    fun mp m' s => verify_internal_prepared_eq hp (Array.to_slice pk) mp m' s hpkl vk hvk
  unfold verifyPreparedAPI verifyAPI
  simp [lift, key]
  intro v _
  rfl

theorem verifyInternalPreparedAPI_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.pkLen) (pk : Array U8 n)
    (vk : verify.PreparedVk K L) (hvk : verify.prepare_vk K L (Array.to_slice pk) = ok vk)
    (m : Slice U8) (sig : Array U8 N) :
    verifyInternalPreparedAPI N K L (ok ip) vk m sig = verifyInternalAPI n N K L (ok ip) pk m sig := by
  have hpkl : (Array.to_slice pk).val.length = sp.pkLen := by
    have := pk.property
    simp only [Array.to_slice]
    omega
  have key : ∀ mp m' s, verify.verify_internal K L ip (Array.to_slice pk) mp m' s =
      verify.verify_prepared_internal ip vk mp m' s :=
    fun mp m' s => verify_internal_prepared_eq hp (Array.to_slice pk) mp m' s hpkl vk hvk
  unfold verifyInternalPreparedAPI verifyInternalAPI
  simp [lift, key]

/-! ## `verifying_key_NN` -/

theorem verifying_key_44_prepare (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (h : api.verifying_key_44 pk = ok vk) : verify.prepare_vk 4#usize 4#usize (Array.to_slice pk) = ok vk.inner := by
  unfold api.verifying_key_44 at h
  rcases hv : verify.prepare_vk 4#usize 4#usize (Array.to_slice pk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

theorem verifying_key_65_prepare (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (h : api.verifying_key_65 pk = ok vk) : verify.prepare_vk 6#usize 5#usize (Array.to_slice pk) = ok vk.inner := by
  unfold api.verifying_key_65 at h
  rcases hv : verify.prepare_vk 6#usize 5#usize (Array.to_slice pk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

theorem verifying_key_87_prepare (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (h : api.verifying_key_87 pk = ok vk) : verify.prepare_vk 8#usize 7#usize (Array.to_slice pk) = ok vk.inner := by
  unfold api.verifying_key_87 at h
  rcases hv : verify.prepare_vk 8#usize 7#usize (Array.to_slice pk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

/-- The relation a prepared key has to the key bytes: Â = ExpandA(ρ) (at some fuel), NTT(t₁ · 2^d), tr. -/
def PreparedOf (sp : Spec.Params) {K L : Usize} (pkb : List UInt8) (vk : verify.PreparedVk K L) : Prop :=
  ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F : Nat),
    Spec.ExpandA sp F (Spec.pkDecode sp pkb).1 = some A ∧
    ReprMat vk.a_hat A ∧
    ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp pkb).2.map RPoly.toZq).map
      (·.map (· * (2 ^ sp.d : Zq))))) ∧
    bytesA vk.tr = H pkb 64

theorem prepare_vk_partial' {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n : Usize) (hn : n.val = sp.pkLen) (pk : Array U8 n) :
    verify.prepare_vk K L (Array.to_slice pk) ⦃ vk => PreparedOf sp (bytesA pk) vk ⦄div := by
  have hpkLen : (Array.to_slice pk).val.length = 32 + 320 * sp.k := by
    have := pk.property
    have h2 := KeyGen.pkLen_eq sp hp.params.d_eq
    simp only [Array.to_slice]
    omega
  apply WP.dspec_mono' (prepare_vk_partial hp (Array.to_slice pk) hpkLen)
  intro vk hvk
  rw [bytes_to_slice] at hvk
  exact hvk

/-- **ML-DSA-44 `verifying_key`, partial correctness and panic-freedom.** It never returns `fail`; if it
returns `vk` then `vk` holds Â = ExpandA(ρ) (at some fuel), NTT(t₁ · 2^d) and tr = H(pk, 64), where
(ρ, t₁) = pkDecode(pk). It diverges only where ExpandA does. -/
theorem verifying_key_44_partial (pk : Array U8 1312#usize) :
    api.verifying_key_44 pk ⦃ vk => PreparedOf Spec.ML_DSA_44 (bytesA pk) vk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  unfold api.verifying_key_44
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_vk_partial' hp 1312#usize (by decide) pk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

theorem verifying_key_65_partial (pk : Array U8 1952#usize) :
    api.verifying_key_65 pk ⦃ vk => PreparedOf Spec.ML_DSA_65 (bytesA pk) vk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  unfold api.verifying_key_65
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_vk_partial' hp 1952#usize (by decide) pk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

theorem verifying_key_87_partial (pk : Array U8 2592#usize) :
    api.verifying_key_87 pk ⦃ vk => PreparedOf Spec.ML_DSA_87 (bytesA pk) vk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  unfold api.verifying_key_87
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_vk_partial' hp 2592#usize (by decide) pk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

/-- **ML-DSA-44 `verifying_key` never fails.** (It may diverge, exactly where ExpandA does; see
`verifying_key_44_partial` for what it returns otherwise.) -/
theorem verifying_key_44_not_fail (pk : Array U8 1312#usize) : ∀ e, api.verifying_key_44 pk ≠ .fail e :=
  dspec_not_fail (verifying_key_44_partial pk)

theorem verifying_key_65_not_fail (pk : Array U8 1952#usize) : ∀ e, api.verifying_key_65 pk ≠ .fail e :=
  dspec_not_fail (verifying_key_65_partial pk)

theorem verifying_key_87_not_fail (pk : Array U8 2592#usize) : ∀ e, api.verifying_key_87 pk ≠ .fail e :=
  dspec_not_fail (verifying_key_87_partial pk)

/-! ## Equality with the unprepared functions -/

/-- **ML-DSA-44: `verify_prepared` equals `verify`.** For every `pk` and every prepared key `vk` that
`verifying_key_44 pk` returns, and every `m`, `ctx`, `σ`, the prepared verification returns exactly what
`verify_44 pk m ctx σ` returns. -/
theorem verify_prepared_44_eq (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_prepared_44 vk m ctx sig = api.verify_44 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_prepared_44_def, verify_44_eq, hip]
  exact verifyPreparedAPI_eq hp 1312#usize 2420#usize (by decide) pk vk.inner (verifying_key_44_prepare pk vk hvk)
    m ctx sig

theorem verify_prepared_65_eq (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_prepared_65 vk m ctx sig = api.verify_65 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_prepared_65_def, verify_65_eq, hip]
  exact verifyPreparedAPI_eq hp 1952#usize 3309#usize (by decide) pk vk.inner (verifying_key_65_prepare pk vk hvk)
    m ctx sig

theorem verify_prepared_87_eq (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_prepared_87 vk m ctx sig = api.verify_87 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_prepared_87_def, verify_87_eq, hip]
  exact verifyPreparedAPI_eq hp 2592#usize 4627#usize (by decide) pk vk.inner (verifying_key_87_prepare pk vk hvk)
    m ctx sig

/-- **ML-DSA-44: `verify_internal_prepared` equals `verify_internal`.** -/
theorem verify_internal_prepared_44_eq (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_internal_prepared_44 vk m sig = api.verify_internal_44 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_internal_prepared_44_def, verify_internal_44_eq, hip]
  exact verifyInternalPreparedAPI_eq hp 1312#usize 2420#usize (by decide) pk vk.inner
    (verifying_key_44_prepare pk vk hvk) m sig

theorem verify_internal_prepared_65_eq (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_internal_prepared_65 vk m sig = api.verify_internal_65 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_internal_prepared_65_def, verify_internal_65_eq, hip]
  exact verifyInternalPreparedAPI_eq hp 1952#usize 3309#usize (by decide) pk vk.inner
    (verifying_key_65_prepare pk vk hvk) m sig

theorem verify_internal_prepared_87_eq (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_internal_prepared_87 vk m sig = api.verify_internal_87 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_internal_prepared_87_def, verify_internal_87_eq, hip]
  exact verifyInternalPreparedAPI_eq hp 2592#usize 4627#usize (by decide) pk vk.inner
    (verifying_key_87_prepare pk vk hvk) m sig

/-! ## Exactness against the unbounded FIPS 204 algorithms -/

/-- **ML-DSA-44 `verify_prepared` is exactly the unbounded FIPS 204 Algorithm 3** on the key bytes `vk` was
prepared from: never `fail`; `Spec.Verify … F = some b` at any fuel gives `ok b`; `ok b` gives some fuel at which
the spec returns `some b`. -/
theorem verify_prepared_44_exact (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_prepared_44 vk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_prepared_44 vk m ctx sig = ok b) ∧
    (∀ b, api.verify_prepared_44 vk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) := by
  rw [verify_prepared_44_eq pk vk hvk m ctx sig]
  exact verify_44_exact pk m ctx sig

theorem verify_prepared_65_exact (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_prepared_65 vk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_prepared_65 vk m ctx sig = ok b) ∧
    (∀ b, api.verify_prepared_65 vk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) := by
  rw [verify_prepared_65_eq pk vk hvk m ctx sig]
  exact verify_65_exact pk m ctx sig

theorem verify_prepared_87_exact (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_prepared_87 vk m ctx sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b →
      api.verify_prepared_87 vk m ctx sig = ok b) ∧
    (∀ b, api.verify_prepared_87 vk m ctx sig = ok b →
      ∃ F, Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) := by
  rw [verify_prepared_87_eq pk vk hvk m ctx sig]
  exact verify_87_exact pk m ctx sig

/-- **ML-DSA-44 `verify_internal_prepared` is exactly the unbounded FIPS 204 Algorithm 8.** -/
theorem verify_internal_prepared_44_exact (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m : Slice U8) (sig : Array U8 2420#usize) :
    (∀ e, api.verify_internal_prepared_44 vk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_prepared_44 vk m sig = ok b) ∧
    (∀ b, api.verify_internal_prepared_44 vk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_prepared_44_eq pk vk hvk m sig]
  exact verify_internal_44_exact pk m sig

theorem verify_internal_prepared_65_exact (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m : Slice U8) (sig : Array U8 3309#usize) :
    (∀ e, api.verify_internal_prepared_65 vk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_prepared_65 vk m sig = ok b) ∧
    (∀ b, api.verify_internal_prepared_65 vk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_prepared_65_eq pk vk hvk m sig]
  exact verify_internal_65_exact pk m sig

theorem verify_internal_prepared_87_exact (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m : Slice U8) (sig : Array U8 4627#usize) :
    (∀ e, api.verify_internal_prepared_87 vk m sig ≠ .fail e) ∧
    (∀ F b, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b →
      api.verify_internal_prepared_87 vk m sig = ok b) ∧
    (∀ b, api.verify_internal_prepared_87 vk m sig = ok b →
      ∃ F, Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b) := by
  rw [verify_internal_prepared_87_eq pk vk hvk m sig]
  exact verify_internal_87_exact pk m sig

end Proofs
