import Proofs.PartialSign

/-!
# Prepared signing keys (`signing_key_NN`, `sign_prepared_NN`, `sign_internal_prepared_NN`)

`api.signing_key_NN sk` computes the part of Sign that depends on the secret key alone (skDecode, ŝ₁, ŝ₂, t̂₀, Â, K,
tr); `api.sign_prepared_NN` and `api.sign_internal_prepared_NN` sign with it. Proved for `NN ∈ {44, 65, 87}`:

* `signing_key_NN_partial`: `signing_key_NN sk` never fails; it returns a key holding exactly the values
  `skDecode sk` gives (K, tr, and the NTTs of s₁, s₂, t₀) and Â = ExpandA(ρ) (at some fuel of the spec); it diverges
  only where ExpandA does (the `⦃ ⦄div` form of `PartialAPI`).
* `sign_prepared_NN_eq`, `sign_internal_prepared_NN_eq`: if `signing_key_NN sk = ok ssk`, then for every `m`, `ctx`,
  `rnd` the prepared function returns exactly what `sign_NN sk m ctx rnd` (resp. `sign_internal_NN sk m rnd`) returns,
  including `fail` and `div`. No premise besides the `ok ssk`.
* `sign_prepared_NN_exact`, `sign_internal_prepared_NN_exact`: the prepared functions agree exactly with the
  unbounded FIPS 204 Algorithm 2 (resp. 7) on the key bytes `ssk` was built from, in the style of `sign_NN_exact`.

The equality is a rewrite: the extracted `sign_internal` is `prepare_sk` followed by `sign_prepared_internal`, and
`sign_prepared_NN` is `sign_NN` with the first half replaced by the key it was handed. The pieces are proved in
`Proofs/Sign.lean` (`prepare_sk_spec`, `sign_prepared_core`) and `Proofs/PartialSign.lean` (`prepare_sk_partial`,
`sign_prepared_partial`).

Not covered by the Lean model: the `Drop` impl of `PreparedSk` under the `zeroize` feature (Aeneas models neither
`Drop` nor volatile writes). The extracted code is the code without that feature.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open API APIInternal Sign PartialSign

/-! ## Generic bodies -/

/-- The body of `api.sign_prepared_NN`, generic in the array size and the parameter record. -/
def signPreparedAPI (N : Usize) (K L : Usize) (P : RustM params.Params) (ps : sign.PreparedSk K L)
    (m ctx : Slice U8) (rnd : Array U8 32#usize) : RustM (Option (Array U8 N)) := do
  let o ← api.ctx_prefix ctx
  match o with
  | none => ok none
  | some b =>
    let p ← P
    let sig := Array.repeat N 0#u8
    let i := Slice.len ctx
    let i1 ← 2#usize + i
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) b
        { «end» := i1 }
    let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut sig)
    let (b1, s2) ← sign.sign_prepared_internal p ps s m rnd s1
    if b1
    then let sig1 := to_slice_mut_back s2
         ok (some sig1)
    else ok none

/-- The body of `api.sign_internal_prepared_NN`. -/
def signInternalPreparedAPI (N : Usize) (K L : Usize) (P : RustM params.Params) (ps : sign.PreparedSk K L)
    (m : Slice U8) (rnd : Array U8 32#usize) : RustM (Option (Array U8 N)) := do
  let p ← P
  let sig := Array.repeat N 0#u8
  let s ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut sig)
  let (b, s2) ← sign.sign_prepared_internal p ps s m rnd s1
  if b
  then let sig1 := to_slice_mut_back s2
       ok (some sig1)
  else ok none

theorem sign_prepared_44_def (ssk : api.SigningKey44) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_44 ssk m ctx rnd =
      signPreparedAPI 2420#usize 4#usize 4#usize params.ML_DSA_44 ssk.inner m ctx rnd := rfl

theorem sign_internal_prepared_44_def (ssk : api.SigningKey44) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_44 ssk m rnd =
      signInternalPreparedAPI 2420#usize 4#usize 4#usize params.ML_DSA_44 ssk.inner m rnd := rfl

theorem sign_prepared_65_def (ssk : api.SigningKey65) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_65 ssk m ctx rnd =
      signPreparedAPI 3309#usize 6#usize 5#usize params.ML_DSA_65 ssk.inner m ctx rnd := rfl

theorem sign_internal_prepared_65_def (ssk : api.SigningKey65) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_65 ssk m rnd =
      signInternalPreparedAPI 3309#usize 6#usize 5#usize params.ML_DSA_65 ssk.inner m rnd := rfl

theorem sign_prepared_87_def (ssk : api.SigningKey87) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_87 ssk m ctx rnd =
      signPreparedAPI 4627#usize 8#usize 7#usize params.ML_DSA_87 ssk.inner m ctx rnd := rfl

theorem sign_internal_prepared_87_def (ssk : api.SigningKey87) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_87 ssk m rnd =
      signInternalPreparedAPI 4627#usize 8#usize 7#usize params.ML_DSA_87 ssk.inner m rnd := rfl

/-! ## `sign_internal = prepare_sk ; sign_prepared_internal` -/

/-- For a key `ps` that `prepare_sk` returns for `sk`, the unprepared `sign_internal` and the prepared
`sign_prepared_internal` are the same computation. -/
theorem sign_internal_prepared_eq {ip : Impl.params.Params} {K L : Usize}
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (ps : sign.PreparedSk K L) (hps : sign.prepare_sk K L ip sk = ok ps) :
    sign.sign_internal K L ip sk m_prefix m rnd sig = sign.sign_prepared_internal ip ps m_prefix m rnd sig := by
  unfold sign.sign_internal
  simp [hps]

/-- The API bodies: `signPreparedAPI` on a prepared key equals `signAPI` on the key bytes. -/
theorem signPreparedAPI_eq {ip : Impl.params.Params} {K L : Usize} (n N : Usize) (sk : Array U8 n)
    (ps : sign.PreparedSk K L) (hps : sign.prepare_sk K L ip (Array.to_slice sk) = ok ps)
    (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    signPreparedAPI N K L (ok ip) ps m ctx rnd = signAPI n N K L (ok ip) sk m ctx rnd := by
  have key : ∀ s1 m' s2, sign.sign_internal K L ip (Array.to_slice sk) s1 m' rnd s2 =
      sign.sign_prepared_internal ip ps s1 m' rnd s2 :=
    fun s1 m' s2 => sign_internal_prepared_eq (Array.to_slice sk) s1 m' rnd s2 ps hps
  unfold signPreparedAPI signAPI
  simp [lift, key]
  intro v _
  rfl

theorem signInternalPreparedAPI_eq {ip : Impl.params.Params} {K L : Usize} (n N : Usize) (sk : Array U8 n)
    (ps : sign.PreparedSk K L) (hps : sign.prepare_sk K L ip (Array.to_slice sk) = ok ps)
    (m : Slice U8) (rnd : Array U8 32#usize) :
    signInternalPreparedAPI N K L (ok ip) ps m rnd = signInternalAPI n N K L (ok ip) sk m rnd := by
  have key : ∀ s1 m' s2, sign.sign_internal K L ip (Array.to_slice sk) s1 m' rnd s2 =
      sign.sign_prepared_internal ip ps s1 m' rnd s2 :=
    fun s1 m' s2 => sign_internal_prepared_eq (Array.to_slice sk) s1 m' rnd s2 ps hps
  unfold signInternalPreparedAPI signInternalAPI
  simp [lift, key]

/-! ## `signing_key_NN` -/

theorem signing_key_44_prepare (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (h : api.signing_key_44 sk = ok ssk) (ip : Impl.params.Params) (hip : params.ML_DSA_44 = ok ip) :
    sign.prepare_sk 4#usize 4#usize ip (Array.to_slice sk) = ok ssk.inner := by
  unfold api.signing_key_44 at h
  rw [hip] at h
  rcases hv : sign.prepare_sk 4#usize 4#usize ip (Array.to_slice sk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

theorem signing_key_65_prepare (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (h : api.signing_key_65 sk = ok ssk) (ip : Impl.params.Params) (hip : params.ML_DSA_65 = ok ip) :
    sign.prepare_sk 6#usize 5#usize ip (Array.to_slice sk) = ok ssk.inner := by
  unfold api.signing_key_65 at h
  rw [hip] at h
  rcases hv : sign.prepare_sk 6#usize 5#usize ip (Array.to_slice sk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

theorem signing_key_87_prepare (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (h : api.signing_key_87 sk = ok ssk) (ip : Impl.params.Params) (hip : params.ML_DSA_87 = ok ip) :
    sign.prepare_sk 8#usize 7#usize ip (Array.to_slice sk) = ok ssk.inner := by
  unfold api.signing_key_87 at h
  rw [hip] at h
  rcases hv : sign.prepare_sk 8#usize 7#usize ip (Array.to_slice sk) with e | pv | _ <;> simp [lift, hv] at h
  subst h
  rfl

/-- The relation a prepared signing key has to the key bytes: the values `skDecode` gives (K, tr, the NTTs of
s₁, s₂, t₀) and Â = ExpandA(ρ) (at some fuel). -/
def PreparedSkOf (sp : Spec.Params) {K L : Usize} (skb : List UInt8) (ps : sign.PreparedSk K L) : Prop :=
  ∃ (ρ Kk tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F : Nat),
    Spec.skDecode sp skb = (ρ, Kk, tr, s₁, s₂, t₀) ∧
    Spec.ExpandA sp F ρ = some A ∧
    ReprMat ps.a_hat A ∧
    ReprVec ps.s1_hat (NTTVec (s₁.map RPoly.toZq)) ∧
    ReprVec ps.s2_hat (NTTVec (s₂.map RPoly.toZq)) ∧
    ReprVec ps.t0_hat (NTTVec (t₀.map RPoly.toZq)) ∧
    bytesA ps.key = Kk ∧ bytesA ps.tr = tr

theorem prepare_sk_partial' {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n : Usize) (hn : n.val = sp.skLen) (sk : Array U8 n) :
    sign.prepare_sk K L ip (Array.to_slice sk) ⦃ ps => PreparedSkOf sp (bytesA sk) ps ⦄div := by
  have hsk : (Array.to_slice sk).length = sp.skLen := by
    have := sk.property
    show (Array.to_slice sk).val.length = sp.skLen
    simp only [Array.to_slice]
    omega
  rcases hd : Spec.skDecode sp (bytes (Array.to_slice sk)) with ⟨ρ, Kk, tr, s₁, s₂, t₀⟩
  apply WP.dspec_mono' (prepare_sk_partial hp (Array.to_slice sk) hsk ρ Kk tr s₁ s₂ t₀ hd)
  rintro ps ⟨A, F1, hA, hAh, h1, h2, h3, hk, ht⟩
  rw [bytes_to_slice] at hd
  exact ⟨ρ, Kk, tr, s₁, s₂, t₀, A, F1, hd, hA, hAh, h1, h2, h3, hk, ht⟩

/-- **ML-DSA-44 `signing_key`, partial correctness and panic-freedom.** It never returns `fail`; if it returns
`ssk` then `ssk` holds K, tr and the NTTs of s₁, s₂, t₀ as `skDecode` gives them, and Â = ExpandA(ρ) (at some fuel).
It diverges only where ExpandA does. -/
theorem signing_key_44_partial (sk : Array U8 2560#usize) :
    api.signing_key_44 sk ⦃ ssk => PreparedSkOf Spec.ML_DSA_44 (bytesA sk) ssk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  unfold api.signing_key_44
  rw [hip]
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_sk_partial' hp 2560#usize
    (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl) sk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

theorem signing_key_44_not_fail (sk : Array U8 2560#usize) : ∀ e, api.signing_key_44 sk ≠ .fail e :=
  dspec_not_fail (signing_key_44_partial sk)

theorem signing_key_65_partial (sk : Array U8 4032#usize) :
    api.signing_key_65 sk ⦃ ssk => PreparedSkOf Spec.ML_DSA_65 (bytesA sk) ssk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  unfold api.signing_key_65
  rw [hip]
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_sk_partial' hp 4032#usize
    (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl) sk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

theorem signing_key_65_not_fail (sk : Array U8 4032#usize) : ∀ e, api.signing_key_65 sk ≠ .fail e :=
  dspec_not_fail (signing_key_65_partial sk)

theorem signing_key_87_partial (sk : Array U8 4896#usize) :
    api.signing_key_87 sk ⦃ ssk => PreparedSkOf Spec.ML_DSA_87 (bytesA sk) ssk.inner ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  unfold api.signing_key_87
  rw [hip]
  simp only [lift, Std.bind_tc_ok]
  refine WP.dspec_bind' (prepare_sk_partial' hp 4896#usize
    (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl) sk) ?_
  intro pv hpv
  simp only [WP.dspec_ok]
  exact hpv

theorem signing_key_87_not_fail (sk : Array U8 4896#usize) : ∀ e, api.signing_key_87 sk ≠ .fail e :=
  dspec_not_fail (signing_key_87_partial sk)

/-! ## Equality with the unprepared functions -/

/-- **ML-DSA-44: `sign_prepared` equals `sign`.** For every `sk` and every prepared key `ssk` that
`signing_key_44 sk` returns, and every `m`, `ctx`, `rnd`, the prepared signing returns exactly what
`sign_44 sk m ctx rnd` returns. -/
theorem sign_prepared_44_eq (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_44 ssk m ctx rnd = api.sign_44 sk m ctx rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_prepared_44_def, sign_44_eq, hip]
  exact signPreparedAPI_eq 2560#usize 2420#usize sk ssk.inner (signing_key_44_prepare sk ssk hssk ip hip) m ctx rnd

/-- **ML-DSA-44: `sign_internal_prepared` equals `sign_internal`.** -/
theorem sign_internal_prepared_44_eq (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_44 ssk m rnd = api.sign_internal_44 sk m rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_internal_prepared_44_def, sign_internal_44_eq, hip]
  exact signInternalPreparedAPI_eq 2560#usize 2420#usize sk ssk.inner (signing_key_44_prepare sk ssk hssk ip hip) m rnd

theorem sign_prepared_65_eq (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_65 ssk m ctx rnd = api.sign_65 sk m ctx rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_prepared_65_def, sign_65_eq, hip]
  exact signPreparedAPI_eq 4032#usize 3309#usize sk ssk.inner (signing_key_65_prepare sk ssk hssk ip hip) m ctx rnd

theorem sign_internal_prepared_65_eq (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_65 ssk m rnd = api.sign_internal_65 sk m rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_internal_prepared_65_def, sign_internal_65_eq, hip]
  exact signInternalPreparedAPI_eq 4032#usize 3309#usize sk ssk.inner (signing_key_65_prepare sk ssk hssk ip hip) m rnd

theorem sign_prepared_87_eq (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_87 ssk m ctx rnd = api.sign_87 sk m ctx rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_prepared_87_def, sign_87_eq, hip]
  exact signPreparedAPI_eq 4896#usize 4627#usize sk ssk.inner (signing_key_87_prepare sk ssk hssk ip hip) m ctx rnd

theorem sign_internal_prepared_87_eq (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_87 ssk m rnd = api.sign_internal_87 sk m rnd := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_internal_prepared_87_def, sign_internal_87_eq, hip]
  exact signInternalPreparedAPI_eq 4896#usize 4627#usize sk ssk.inner (signing_key_87_prepare sk ssk hssk ip hip) m rnd

/-! ## Exactness against the unbounded FIPS 204 algorithms -/

/-- **ML-DSA-44 `sign_prepared` is exactly the unbounded FIPS 204 Algorithm 2** on the key bytes `ssk` was
prepared from, as `sign_44_exact` says of `sign_44`: never `fail`; if the spec returns `σ` at any fuel, the Rust returns
`some σ'` with `σ'` holding `σ`; if the Rust returns `some σ`, the spec returns `σ` at some fuel; the Rust returns `none`
exactly when `|ctx| > 255` or the spec is `Exhausted` at some fuel. -/
theorem sign_prepared_44_exact (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_prepared_44 ssk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_prepared_44 ssk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_prepared_44 ssk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_prepared_44 ssk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) := by
  rw [sign_prepared_44_eq sk ssk hssk m ctx rnd]
  exact sign_44_exact sk m ctx rnd

/-- **ML-DSA-44 `sign_internal_prepared` is exactly the unbounded FIPS 204 Algorithm 7** on the key bytes `ssk`
was prepared from (see `sign_internal_44_exact`). -/
theorem sign_internal_prepared_44_exact (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_prepared_44 ssk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_44 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_prepared_44 ssk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_prepared_44 ssk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_44 (kappaBudget Spec.ML_DSA_44) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_prepared_44 ssk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) := by
  rw [sign_internal_prepared_44_eq sk ssk hssk m rnd]
  exact sign_internal_44_exact sk m rnd

theorem sign_prepared_65_exact (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_prepared_65 ssk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_prepared_65 ssk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_prepared_65 ssk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_prepared_65 ssk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) := by
  rw [sign_prepared_65_eq sk ssk hssk m ctx rnd]
  exact sign_65_exact sk m ctx rnd

theorem sign_internal_prepared_65_exact (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_prepared_65 ssk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_65 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_prepared_65 ssk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_prepared_65 ssk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_65 (kappaBudget Spec.ML_DSA_65) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_prepared_65 ssk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) := by
  rw [sign_internal_prepared_65_eq sk ssk hssk m rnd]
  exact sign_internal_65_exact sk m rnd

theorem sign_prepared_87_exact (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_prepared_87 ssk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_prepared_87 ssk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_prepared_87 ssk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_prepared_87 ssk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) := by
  rw [sign_prepared_87_eq sk ssk hssk m ctx rnd]
  exact sign_87_exact sk m ctx rnd

theorem sign_internal_prepared_87_exact (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_prepared_87 ssk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_87 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_prepared_87 ssk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_prepared_87 ssk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_87 (kappaBudget Spec.ML_DSA_87) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_prepared_87 ssk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) := by
  rw [sign_internal_prepared_87_eq sk ssk hssk m rnd]
  exact sign_internal_87_exact sk m rnd

end Proofs
