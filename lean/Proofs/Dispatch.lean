import Proofs.FastVerify
import Proofs.PreparedVerify

/-!
# The CPU dispatch is proved: every flag value computes the scalar function

The AVX2 build of the crate chooses, at run time, between the scalar verify functions and the same 4-way code compiled
inside `#[target_feature(enable = "avx2")]` wrappers. In the source this choice is made by three crate-private
functions of `src/fast_verify.rs` (`verify_internal_with`, `prepare_vk_with`, `verify_prepared_internal_with`), which take
the result of the CPU check as a value (`Option<cpu::Avx2>`: `Some(_)` means "AVX2 is available"), and by the fifteen
`api::NAME_with` functions, which carry that value from the public function (`NAME pk .. = NAME_with(cpu::avx2(), pk, ..)`)
to them. All of these are extracted and proved here:

* `verify_internal_with_eq`, `prepare_vk_with_eq`, `verify_prepared_internal_with_eq`: for **every** `Option cpu.Avx2`,
  as `RustM` equalities (so including divergence), the `_with` function is the scalar function (`verify.verify_internal`,
  `verify.prepare_vk`, `verify.verify_prepared_internal`). The first two use `Params.Std` (the 4-way ExpandA is proved
  equal to the scalar one for the standard parameter bundle, `FastVerify.lean`); the third needs nothing.
* `api_verify_NN_with_eq`, `api_verify_internal_NN_with_eq`, `api_verifying_key_NN_with_eq`, `api_verify_prepared_NN_with_eq`,
  `api_verify_internal_prepared_NN_with_eq` (NN = 44, 65, 87): for every flag value, `api.NAME_with t ..` equals the public
  `api.NAME ..`. The extraction models the CPU check `cpu.avx2` as `ok none` (the miri stub), so the statements about
  `api.NAME` in `API.lean`, `APIInternal.lean`, `Divergence.lean` and `PreparedVerify.lean` are statements about the
  `none` arm; these theorems extend them to every flag value, including `Some _`, which the real CPU check returns on a
  machine with AVX2.

What is *not* a theorem and is not claimed: that `cpu::avx2()` returns `Some(_)` only when the CPU and OS can execute AVX2
(it is the single `unsafe` justification: only `cpu::avx2()` constructs an `Avx2` token, and it does so after `detect_avx2`
of `src/cpu.rs`, which tests that CPUID's maximum basic leaf is at least 7, leaf 1 ECX bits 26 to 28 (XSAVE, OSXSAVE, AVX),
XCR0 bits 1 and 2 (the OS saves XMM and YMM state) and leaf 7 subleaf 0 EBX bit 5 (AVX2), and caches the answer, unless the
build already enables AVX2 statically). "CPU and OS support AVX2 whenever the detector reports it" is an assumption. A false
negative only selects the scalar function, which is proved to be the same function. A false positive executes a
`#[target_feature(enable = "avx2")]` function on a CPU or OS that cannot run it, which is undefined behavior: SIGILL is
one possible outcome, not a guaranteed one, and the equality theorems do not constrain it. Also not a theorem: that the
compiler's code for the `#[target_feature]` wrappers computes the Rust function (the compiler is trusted as for the rest of
the crate; the `checkct` and BINSEC runs and the differential tests look at the compiled code), and that LLVM vectorizes
the loops (a performance property checked by `scripts/check-avx2-inlining.sh`, not a correctness assumption).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open API APIInternal Verify

/-! ## The three functions of `fast_verify` -/

/-- `verify_internal_with` is `verify_internal` for every flag value. -/
theorem verify_internal_with_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (t : Option cpu.Avx2) (p : Impl.params.Params) (pk m_prefix m sig : Slice U8) :
    fast_verify.verify_internal_with K L t p pk m_prefix m sig = verify.verify_internal K L p pk m_prefix m sig := by
  cases t with
  | none => rfl
  | some _ =>
    unfold fast_verify.verify_internal_with fast_verify.dispatch.verify_internal_avx2
    exact verify_internal_x4_eq hp p pk m_prefix m sig

/-- The AVX2 `prepare_vk` wrapper is `prepare_vk`. -/
theorem prepare_vk_avx2_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk : Slice U8) :
    fast_verify.dispatch.prepare_vk_avx2 K L pk = verify.prepare_vk K L pk := by
  rw [← prepare_vk_x4_eq hp]
  have h := prepare_vk_x4_zeroed_bind K L pk (fun vk => ok vk)
  have e : ∀ x : RustM (verify.PreparedVk K L), (x >>= fun vk => ok vk) = x := fun x => by cases x <;> rfl
  simp only [e] at h
  exact h

/-- `prepare_vk_with` is `prepare_vk` for every flag value. -/
theorem prepare_vk_with_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (t : Option cpu.Avx2) (pk : Slice U8) :
    fast_verify.prepare_vk_with K L t pk = verify.prepare_vk K L pk := by
  cases t with
  | none => rfl
  | some _ =>
    unfold fast_verify.prepare_vk_with
    exact prepare_vk_avx2_eq hp pk

/-- `verify_prepared_internal_with` is `verify_prepared_internal` for every flag value (both arms call the same
function; the AVX2 wrapper adds nothing but the `target_feature`). -/
theorem verify_prepared_internal_with_eq {K L : Usize} (t : Option cpu.Avx2) (p : Impl.params.Params)
    (vk : verify.PreparedVk K L) (m_prefix m sig : Slice U8) :
    fast_verify.verify_prepared_internal_with t p vk m_prefix m sig =
      verify.verify_prepared_internal p vk m_prefix m sig := by
  cases t <;> rfl

/-! ## Generic bodies of the `api.NAME_with` functions -/

/-- The body of `api.verify_NN_with`. -/
def verifyAPIWith (t : Option cpu.Avx2) (n N : Usize) (K L : Usize) (P : RustM params.Params) (pk : Array U8 n)
    (m ctx : Slice U8) (sig : Array U8 N) : RustM Bool := do
  let o ← api.ctx_prefix ctx
  match o with
  | none => ok false
  | some b =>
    let p ← P
    let s ← lift (Array.to_slice pk)
    let i := Slice.len ctx
    let i1 ← 2#usize + i
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) b
        { «end» := i1 }
    let s2 ← lift (Array.to_slice sig)
    fast_verify.verify_internal_with K L t p s s1 m s2

/-- The body of `api.verify_internal_NN_with`. -/
def verifyInternalAPIWith (t : Option cpu.Avx2) (n N : Usize) (K L : Usize) (P : RustM params.Params)
    (pk : Array U8 n) (m : Slice U8) (sig : Array U8 N) : RustM Bool := do
  let p ← P
  let s ← lift (Array.to_slice pk)
  let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s2 ← lift (Array.to_slice sig)
  fast_verify.verify_internal_with K L t p s s1 m s2

/-- The body of `api.verify_prepared_NN_with`. -/
def verifyPreparedAPIWith (t : Option cpu.Avx2) (N : Usize) (K L : Usize) (P : RustM params.Params)
    (vk : verify.PreparedVk K L) (m ctx : Slice U8) (sig : Array U8 N) : RustM Bool := do
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
    fast_verify.verify_prepared_internal_with t p vk s m s1

/-- The body of `api.verify_internal_prepared_NN_with`. -/
def verifyInternalPreparedAPIWith (t : Option cpu.Avx2) (N : Usize) (K L : Usize) (P : RustM params.Params)
    (vk : verify.PreparedVk K L) (m : Slice U8) (sig : Array U8 N) : RustM Bool := do
  let p ← P
  let s ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s1 ← lift (Array.to_slice sig)
  fast_verify.verify_prepared_internal_with t p vk s m s1

theorem verifyAPIWith_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (t : Option cpu.Avx2) (n N : Usize) (pk : Array U8 n) (m ctx : Slice U8)
    (sig : Array U8 N) :
    verifyAPIWith t n N K L (ok ip) pk m ctx sig = verifyAPI n N K L (ok ip) pk m ctx sig := by
  simp only [verifyAPIWith, verifyAPI, verify_internal_with_eq hp]
  rfl

theorem verifyInternalAPIWith_eq {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (t : Option cpu.Avx2) (n N : Usize) (pk : Array U8 n) (m : Slice U8)
    (sig : Array U8 N) :
    verifyInternalAPIWith t n N K L (ok ip) pk m sig = verifyInternalAPI n N K L (ok ip) pk m sig := by
  simp only [verifyInternalAPIWith, verifyInternalAPI, verify_internal_with_eq hp]

theorem verifyPreparedAPIWith_eq {K L : Usize} (ip : Impl.params.Params) (t : Option cpu.Avx2) (N : Usize)
    (vk : verify.PreparedVk K L) (m ctx : Slice U8) (sig : Array U8 N) :
    verifyPreparedAPIWith t N K L (ok ip) vk m ctx sig = verifyPreparedAPI N K L (ok ip) vk m ctx sig := by
  simp only [verifyPreparedAPIWith, verifyPreparedAPI, verify_prepared_internal_with_eq]
  rfl

theorem verifyInternalPreparedAPIWith_eq {K L : Usize} (ip : Impl.params.Params) (t : Option cpu.Avx2) (N : Usize)
    (vk : verify.PreparedVk K L) (m : Slice U8) (sig : Array U8 N) :
    verifyInternalPreparedAPIWith t N K L (ok ip) vk m sig = verifyInternalPreparedAPI N K L (ok ip) vk m sig := by
  simp only [verifyInternalPreparedAPIWith, verifyInternalPreparedAPI, verify_prepared_internal_with_eq]

/-! ## The fifteen `api.NAME_with` functions, for every flag value -/

/-! ### ML-DSA-44 -/

theorem api_verify_44_with_eq (t : Option cpu.Avx2) (pk : Array U8 1312#usize) (m ctx : Slice U8)
    (sig : Array U8 2420#usize) : api.verify_44_with t pk m ctx sig = api.verify_44 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  have h1 : api.verify_44_with t pk m ctx sig =
      verifyAPIWith t 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m ctx sig := rfl
  rw [h1, hip, verifyAPIWith_eq hp, verify_44_eq, hip]

theorem api_verify_internal_44_with_eq (t : Option cpu.Avx2) (pk : Array U8 1312#usize) (m : Slice U8)
    (sig : Array U8 2420#usize) : api.verify_internal_44_with t pk m sig = api.verify_internal_44 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  have h1 : api.verify_internal_44_with t pk m sig =
      verifyInternalAPIWith t 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 pk m sig := rfl
  rw [h1, hip, verifyInternalAPIWith_eq hp, verify_internal_44_eq, hip]

theorem api_verifying_key_44_with_eq (t : Option cpu.Avx2) (pk : Array U8 1312#usize) :
    api.verifying_key_44_with t pk = api.verifying_key_44 pk := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  have h1 : api.verifying_key_44_with t pk = (do
      let s ← lift (Array.to_slice pk)
      let pv ← fast_verify.prepare_vk_with 4#usize 4#usize t s
      ok ({ inner := pv } : api.VerifyingKey44)) := rfl
  rw [h1, verifying_key_44_def]
  simp only [prepare_vk_with_eq hp]

theorem api_verify_prepared_44_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey44) (m ctx : Slice U8)
    (sig : Array U8 2420#usize) : api.verify_prepared_44_with t vk m ctx sig = api.verify_prepared_44 vk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  have h1 : api.verify_prepared_44_with t vk m ctx sig =
      verifyPreparedAPIWith t 2420#usize 4#usize 4#usize params.ML_DSA_44 vk.inner m ctx sig := rfl
  rw [h1, hip, verifyPreparedAPIWith_eq, verify_prepared_44_def, hip]

theorem api_verify_internal_prepared_44_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey44) (m : Slice U8)
    (sig : Array U8 2420#usize) :
    api.verify_internal_prepared_44_with t vk m sig = api.verify_internal_prepared_44 vk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  have h1 : api.verify_internal_prepared_44_with t vk m sig =
      verifyInternalPreparedAPIWith t 2420#usize 4#usize 4#usize params.ML_DSA_44 vk.inner m sig := rfl
  rw [h1, hip, verifyInternalPreparedAPIWith_eq, verify_internal_prepared_44_def, hip]

/-! ### ML-DSA-65 -/

theorem api_verify_65_with_eq (t : Option cpu.Avx2) (pk : Array U8 1952#usize) (m ctx : Slice U8)
    (sig : Array U8 3309#usize) : api.verify_65_with t pk m ctx sig = api.verify_65 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  have h1 : api.verify_65_with t pk m ctx sig =
      verifyAPIWith t 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m ctx sig := rfl
  rw [h1, hip, verifyAPIWith_eq hp, verify_65_eq, hip]

theorem api_verify_internal_65_with_eq (t : Option cpu.Avx2) (pk : Array U8 1952#usize) (m : Slice U8)
    (sig : Array U8 3309#usize) : api.verify_internal_65_with t pk m sig = api.verify_internal_65 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  have h1 : api.verify_internal_65_with t pk m sig =
      verifyInternalAPIWith t 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 pk m sig := rfl
  rw [h1, hip, verifyInternalAPIWith_eq hp, verify_internal_65_eq, hip]

theorem api_verifying_key_65_with_eq (t : Option cpu.Avx2) (pk : Array U8 1952#usize) :
    api.verifying_key_65_with t pk = api.verifying_key_65 pk := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  have h1 : api.verifying_key_65_with t pk = (do
      let s ← lift (Array.to_slice pk)
      let pv ← fast_verify.prepare_vk_with 6#usize 5#usize t s
      ok ({ inner := pv } : api.VerifyingKey65)) := rfl
  rw [h1, verifying_key_65_def]
  simp only [prepare_vk_with_eq hp]

theorem api_verify_prepared_65_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey65) (m ctx : Slice U8)
    (sig : Array U8 3309#usize) : api.verify_prepared_65_with t vk m ctx sig = api.verify_prepared_65 vk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  have h1 : api.verify_prepared_65_with t vk m ctx sig =
      verifyPreparedAPIWith t 3309#usize 6#usize 5#usize params.ML_DSA_65 vk.inner m ctx sig := rfl
  rw [h1, hip, verifyPreparedAPIWith_eq, verify_prepared_65_def, hip]

theorem api_verify_internal_prepared_65_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey65) (m : Slice U8)
    (sig : Array U8 3309#usize) :
    api.verify_internal_prepared_65_with t vk m sig = api.verify_internal_prepared_65 vk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  have h1 : api.verify_internal_prepared_65_with t vk m sig =
      verifyInternalPreparedAPIWith t 3309#usize 6#usize 5#usize params.ML_DSA_65 vk.inner m sig := rfl
  rw [h1, hip, verifyInternalPreparedAPIWith_eq, verify_internal_prepared_65_def, hip]

/-! ### ML-DSA-87 -/

theorem api_verify_87_with_eq (t : Option cpu.Avx2) (pk : Array U8 2592#usize) (m ctx : Slice U8)
    (sig : Array U8 4627#usize) : api.verify_87_with t pk m ctx sig = api.verify_87 pk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  have h1 : api.verify_87_with t pk m ctx sig =
      verifyAPIWith t 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m ctx sig := rfl
  rw [h1, hip, verifyAPIWith_eq hp, verify_87_eq, hip]

theorem api_verify_internal_87_with_eq (t : Option cpu.Avx2) (pk : Array U8 2592#usize) (m : Slice U8)
    (sig : Array U8 4627#usize) : api.verify_internal_87_with t pk m sig = api.verify_internal_87 pk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  have h1 : api.verify_internal_87_with t pk m sig =
      verifyInternalAPIWith t 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 pk m sig := rfl
  rw [h1, hip, verifyInternalAPIWith_eq hp, verify_internal_87_eq, hip]

theorem api_verifying_key_87_with_eq (t : Option cpu.Avx2) (pk : Array U8 2592#usize) :
    api.verifying_key_87_with t pk = api.verifying_key_87 pk := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  have h1 : api.verifying_key_87_with t pk = (do
      let s ← lift (Array.to_slice pk)
      let pv ← fast_verify.prepare_vk_with 8#usize 7#usize t s
      ok ({ inner := pv } : api.VerifyingKey87)) := rfl
  rw [h1, verifying_key_87_def]
  simp only [prepare_vk_with_eq hp]

theorem api_verify_prepared_87_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey87) (m ctx : Slice U8)
    (sig : Array U8 4627#usize) : api.verify_prepared_87_with t vk m ctx sig = api.verify_prepared_87 vk m ctx sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  have h1 : api.verify_prepared_87_with t vk m ctx sig =
      verifyPreparedAPIWith t 4627#usize 8#usize 7#usize params.ML_DSA_87 vk.inner m ctx sig := rfl
  rw [h1, hip, verifyPreparedAPIWith_eq, verify_prepared_87_def, hip]

theorem api_verify_internal_prepared_87_with_eq (t : Option cpu.Avx2) (vk : api.VerifyingKey87) (m : Slice U8)
    (sig : Array U8 4627#usize) :
    api.verify_internal_prepared_87_with t vk m sig = api.verify_internal_prepared_87 vk m sig := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  have h1 : api.verify_internal_prepared_87_with t vk m sig =
      verifyInternalPreparedAPIWith t 4627#usize 8#usize 7#usize params.ML_DSA_87 vk.inner m sig := rfl
  rw [h1, hip, verifyInternalPreparedAPIWith_eq, verify_internal_prepared_87_def, hip]

end Proofs
