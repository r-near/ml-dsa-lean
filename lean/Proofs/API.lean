import Spec.MLDSA
import Proofs.StdParams
import Proofs.KeyGen
import Proofs.Verify
import Proofs.Sign
import Proofs.Steps

/-!
# The public API (Algorithms 1, 2 and 3)

`Impl.api.keygen_NN`, `sign_NN` and `verify_NN` (NN = 44, 65, 87) are the FIPS 204 external interface.
Each is a corollary of the internal refinement theorems (`keygen_internal_spec`, `sign_internal_spec_some`,
`sign_internal_spec_none`, `verify_internal_spec`) and `ctx_prefix_spec`:

* `keygen_NN_correct`: if `Spec.KeyGen` returns `some (pk, sk)` for ξ, the Rust returns arrays holding them.
* `verify_NN_correct`: if `Spec.Verify` returns `some b`, the Rust returns `b`. For `|ctx| > 255` the spec returns
  `some false` (FIPS 204 errata) and so does the Rust.
* `sign_NN_correct_some`: if `Spec.Sign` returns `some σ`, the Rust returns `some σ'` with `σ'` holding σ.
* `sign_NN_correct_ctx_long`: for `|ctx| > 255` both the spec and the Rust return `none` (⊥).
* `sign_NN_correct_exhausted`: if the κ budget is exhausted (`Sign.Exhausted`), the Rust returns `none`.

The only premises are the spec's `some` / `Exhausted` hypotheses. The fixed-size arrays discharge the length
facts of keygen and sign (Verify needs none) and `ML_DSA_NN_std` the parameter facts. Each function is stated once generically (`keygenAPI`,
`signAPI`, `verifyAPI` are the shared bodies, `rfl`-equal to the three extracted functions) and instantiated.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open HintAux

namespace API

/-- The body of `api.keygen_NN`, generic in the sizes of the arrays and the parameter record. -/
def keygenAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (xi : Array U8 32#usize) :
    RustM ((Array U8 n) × (Array U8 N)) := do
  let p ← P
  let pk := Array.repeat n 0#u8
  let sk := Array.repeat N 0#u8
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut pk)
  let (s1, to_slice_mut_back1) ← lift (Array.to_slice_mut sk)
  let (s2, s3) ← keygen.keygen_internal K L p xi s s1
  let pk1 := to_slice_mut_back s2
  let sk1 := to_slice_mut_back1 s3
  ok (pk1, sk1)

theorem keygen_44_eq : api.keygen_44 = keygenAPI 1312#usize 2560#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem keygen_65_eq : api.keygen_65 = keygenAPI 1952#usize 4032#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem keygen_87_eq : api.keygen_87 = keygenAPI 2592#usize 4896#usize 8#usize 7#usize params.ML_DSA_87 := rfl

/-- The body of `api.sign_NN`. -/
def signAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (sk : Array U8 n) (m ctx : Slice U8)
    (rnd : Array U8 32#usize) : RustM (Option (Array U8 N)) := do
  let o ← api.ctx_prefix ctx
  match o with
  | none => ok none
  | some b =>
    let p ← P
    let sig := Array.repeat N 0#u8
    let s ← lift (Array.to_slice sk)
    let i := Slice.len ctx
    let i1 ← 2#usize + i
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) b
        { «end» := i1 }
    let (s2, to_slice_mut_back) ← lift (Array.to_slice_mut sig)
    let (b1, s3) ← sign.sign_internal K L p s s1 m rnd s2
    if b1
    then let sig1 := to_slice_mut_back s3
         ok (some sig1)
    else ok none

theorem sign_44_eq : api.sign_44 = signAPI 2560#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem sign_65_eq : api.sign_65 = signAPI 4032#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem sign_87_eq : api.sign_87 = signAPI 4896#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 := rfl

/-- The body of `api.verify_NN`. -/
def verifyAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (pk : Array U8 n) (m ctx : Slice U8)
    (sig : Array U8 N) : RustM Bool := do
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
    verify.verify_internal K L p s s1 m s2

theorem verify_44_eq : api.verify_44 = verifyAPI 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem verify_65_eq : api.verify_65 = verifyAPI 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem verify_87_eq : api.verify_87 = verifyAPI 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 := rfl

/-! ## Length facts about the spec's key encodings -/

theorem skEncode_length (sp : Spec.Params) (hd : sp.d = 13) (ρ K tr : List UInt8) (hρ : ρ.length = 32)
    (hK : K.length = 32) (htr : tr.length = 64) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k) :
    (Spec.skEncode sp ρ K tr s₁ s₂ t₀).length = sp.skLen := by
  have hc : bitlen (2 ^ (13 - 1) - 1 + 2 ^ (13 - 1)) = 13 := by decide +kernel
  rw [skEncode_eq, skLen_eq sp hd]
  have h1 : (((List.range' 0 sp.ℓ).map fun i => BitPack s₁[i]! sp.η sp.η).flatten).length =
      sp.ℓ * (32 * bitlen (2 * sp.η)) :=
    flat_length (fun i => BitPack s₁[i]! sp.η sp.η) (32 * bitlen (2 * sp.η))
      (fun t => by rw [BitPack_length]; congr 2; omega) sp.ℓ
  have h2 : (((List.range' 0 sp.k).map fun i => BitPack s₂[i]! sp.η sp.η).flatten).length =
      sp.k * (32 * bitlen (2 * sp.η)) :=
    flat_length (fun i => BitPack s₂[i]! sp.η sp.η) (32 * bitlen (2 * sp.η))
      (fun t => by rw [BitPack_length]; congr 2; omega) sp.k
  have h3 : (((List.range' 0 sp.k).map fun i =>
      BitPack t₀[i]! (2 ^ (sp.d - 1) - 1) (2 ^ (sp.d - 1))).flatten).length = sp.k * 416 :=
    flat_length (fun i => BitPack t₀[i]! (2 ^ (sp.d - 1) - 1) (2 ^ (sp.d - 1))) 416
      (fun t => by rw [BitPack_length, hd, hc]) sp.k
  simp only [List.length_append, hρ, hK, htr, h1, h2, h3]
  ring

/-- Both outputs of `KeyGen_internal` have the encoded lengths. -/
theorem keygen_lens (sp : Spec.Params) (hd : sp.d = 13) (F : Spec.Fuel) (ξ pk' sk' : List UInt8)
    (hs : Spec.KeyGen_internal sp ξ F = some (pk', sk')) :
    pk'.length = sp.pkLen ∧ sk'.length = sp.skLen := by
  obtain ⟨A, s₁, s₂, -, -, hpk, hsk⟩ := KeyGen.keygen_some sp F ξ pk' sk' hs
  have hH : (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128).length = 128 :=
    SHAKE256_length _ _
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hH hpk hsk
  have h32 : (slice out 0 32).length = 32 := by simp [slice, hH]
  have h32' : (slice out 96 32).length = 32 := by simp [slice, hH]
  have h64 : (H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).1) 64).length = 64 :=
    SHAKE256_length _ _
  constructor
  · rw [hpk, KeyGen.pkEncode_length sp hd _ h32, KeyGen.pkLen_eq sp hd]
  · rw [hsk]
    exact skEncode_length sp hd _ _ _ h32 h32' h64 _ _ _

/-! ## Algorithm 1 -/

theorem keygenAPI_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.pkLen) (hN : N.val = sp.skLen)
    (ξ : Array U8 32#usize) (F : Spec.Fuel) (pk sk : List UInt8)
    (hs : Spec.KeyGen sp (bytesA ξ) F = some (pk, sk)) :
    keygenAPI n N K L (ok ip) ξ ⦃ r => bytesA r.1 = pk ∧ bytesA r.2 = sk ⦄ := by
  have hs' : Spec.KeyGen_internal sp (bytesA ξ) F = some (pk, sk) := hs
  obtain ⟨hlpk, hlsk⟩ := keygen_lens sp hp.2.d_eq F _ pk sk hs'
  unfold keygenAPI
  simp only [Std.bind_tc_ok]
  step*
  have hsl : s.val.length = sp.pkLen := by rw [s_post1]; simp [Array.repeat_val, hn]
  have hsl1 : s1.val.length = sp.skLen := by rw [s1_post1]; simp [Array.repeat_val, hN]
  refine WP.spec_bind (keygen_internal_spec hp ξ s s1 hsl hsl1 F pk sk hs') ?_
  rintro ⟨s2, s3⟩ ⟨h2, h3⟩
  simp only [] at h2 h3
  have hl2 : s2.val.length = n.val := by
    have := congrArg List.length h2
    simp only [bytes_length] at this
    omega
  have hl3 : s3.val.length = N.val := by
    have := congrArg List.length h3
    simp only [bytes_length] at this
    omega
  refine (WP.spec_ok _).mpr ⟨?_, ?_⟩
  · rw [s_post2, bytesA_from_slice _ _ hl2, h2]
  · rw [s1_post2, bytesA_from_slice _ _ hl3, h3]

theorem _root_.Proofs.keygen_44_correct (ξ : Array U8 32#usize) (F : Spec.Fuel) (pk sk : List UInt8)
    (hs : Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (pk, sk)) :
    api.keygen_44 ξ ⦃ r => bytesA r.1 = pk ∧ bytesA r.2 = sk ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [keygen_44_eq, hip]
  exact keygenAPI_spec hp _ _ (by rw [show Spec.ML_DSA_44.pkLen = 1312 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl) ξ F pk sk hs

theorem _root_.Proofs.keygen_65_correct (ξ : Array U8 32#usize) (F : Spec.Fuel) (pk sk : List UInt8)
    (hs : Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (pk, sk)) :
    api.keygen_65 ξ ⦃ r => bytesA r.1 = pk ∧ bytesA r.2 = sk ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [keygen_65_eq, hip]
  exact keygenAPI_spec hp _ _ (by rw [show Spec.ML_DSA_65.pkLen = 1952 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl) ξ F pk sk hs

theorem _root_.Proofs.keygen_87_correct (ξ : Array U8 32#usize) (F : Spec.Fuel) (pk sk : List UInt8)
    (hs : Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (pk, sk)) :
    api.keygen_87 ξ ⦃ r => bytesA r.1 = pk ∧ bytesA r.2 = sk ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [keygen_87_eq, hip]
  exact keygenAPI_spec hp _ _ (by rw [show Spec.ML_DSA_87.pkLen = 2592 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl) ξ F pk sk hs

/-! ## M′ and the prefix buffer -/

/-- The spec's `M′` of Algorithms 2 and 3, as the two-byte header, `ctx` and `M`. -/
theorem mprime_eq (ctx M : List UInt8) :
    IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M = [0, UInt8.ofNat ctx.length] ++ ctx ++ M := by
  rw [KeyGen.integerToBytes_one, KeyGen.integerToBytes_one]
  have e : (ctx.length % 256).toUInt8 = UInt8.ofNat ctx.length := by
    exact UInt8.ofNat_mod_size
  have e0 : (0 % 256).toUInt8 = (0 : UInt8) := by decide
  rw [e, e0]
  simp

/-- The slice `&prefix[..2 + |ctx|]` of the buffer built by `ctx_prefix` is `0 ‖ |ctx| ‖ ctx`. -/
theorem prefix_bytes (ctx : Slice U8) (b : Array U8 257#usize) (i1 : Usize) (s1 : Slice U8)
    (hi1 : i1.val = 2 + ctx.val.length)
    (h1 : s1.val = List.slice 0 i1.val (Array.to_slice b).val)
    (htake : (bytesA b).take (2 + ctx.val.length) = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx) :
    bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx := by
  have h2 : s1.val = (Array.to_slice b).val.take i1.val := by rw [h1]; simp [List.slice]
  have h3 : bytes s1 = (bytes (Array.to_slice b)).take i1.val := by simp only [bytes, h2, List.map_take]
  rw [h3, bytes_to_slice, hi1, htake]

/-! ## The spec side of the context handling -/

theorem Verify_long (sp : Spec.Params) (pk M σ ctx : List UInt8) (F : Spec.Fuel) (h : 255 < ctx.length) :
    Spec.Verify sp pk M σ ctx F = some false := by
  simp [Spec.Verify, h]

theorem Verify_short (sp : Spec.Params) (pk M σ ctx : List UInt8) (F : Spec.Fuel) (h : ctx.length ≤ 255) :
    Spec.Verify sp pk M σ ctx F = Spec.Verify_internal sp pk ([0, UInt8.ofNat ctx.length] ++ ctx ++ M) σ F := by
  have h' : ¬ 255 < ctx.length := by omega
  rw [← mprime_eq]
  simp [Spec.Verify, h', List.append_assoc]

theorem Sign_long (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel) (h : 255 < ctx.length) :
    Spec.Sign sp sk M ctx rnd F = none := by
  simp [Spec.Sign, h]

theorem Sign_short (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel) (h : ctx.length ≤ 255) :
    Spec.Sign sp sk M ctx rnd F =
      Spec.Sign_internal_bounded sp (kappaBudget sp) sk ([0, UInt8.ofNat ctx.length] ++ ctx ++ M) rnd F := by
  have h' : ¬ 255 < ctx.length := by omega
  rw [← mprime_eq]
  simp [Spec.Sign, Spec.Sign_internal, h', List.append_assoc]

/-! ## Length of the signature the spec returns -/

theorem sigEncode_length (sp : Spec.Params) (hs : StdSig sp) (ct : List UInt8) (hct : ct.length = sp.lam / 4)
    (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k) : (Spec.sigEncode sp ct z h).length = sp.sigLen := by
  obtain ⟨hbl, -⟩ := hs.bitlen_eq
  rw [sigEncode_eq]
  have h1 : (((List.range' 0 sp.ℓ).map fun i => BitPack z[i]! (sp.γ₁ - 1) sp.γ₁).flatten).length =
      sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1))) :=
    flat_length (fun i => BitPack z[i]! (sp.γ₁ - 1) sp.γ₁) (32 * (1 + bitlen (sp.γ₁ - 1)))
      (fun t => by rw [BitPack_length, hbl]) sp.ℓ
  simp only [List.length_append, hct, h1, HintBitPack_length]
  unfold Spec.Params.sigLen
  ring

theorem attemptAt_ct (sp : Spec.Params) (F : Spec.Fuel) (P : Proofs.Sign.Pre sp) (κ : Nat) (ct : List UInt8)
    (o) (h : Proofs.Sign.attemptAt sp F P κ = some (ct, o)) : ct = Proofs.Sign.ctildeAt sp P κ := by
  unfold Proofs.Sign.attemptAt at h
  split at h
  · simp at h; exact h.1.symm
  · simp at h

theorem loopRes_ct_len (sp : Spec.Params) (F : Spec.Fuel) (P : Proofs.Sign.Pre sp) :
    ∀ n κ ct z h, Proofs.Sign.loopRes sp F P n κ = some (some (ct, z, h)) → ct.length = sp.lam / 4 := by
  intro n
  induction n with
  | zero => intro κ ct z h hh; simp [Proofs.Sign.loopRes] at hh
  | succ n ih =>
    intro κ ct z h hh
    unfold Proofs.Sign.loopRes at hh
    split_ifs at hh with hc
    · simp at hh
    · rcases hat : Proofs.Sign.attemptAt sp F P κ with _ | ⟨ct', _ | ⟨z', h'⟩⟩
      · rw [hat] at hh; simp at hh
      · rw [hat] at hh
        exact ih _ _ _ _ hh
      · rw [hat] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        rw [attemptAt_ct sp F P κ ct' _ hat]
        exact SHAKE256_length _ _

/-- If the bounded spec returns `σ`, then `σ` has `sigLen` bytes. -/
theorem sign_len (sp : Spec.Params) (hs : StdSig sp) (B : Nat) (F : Spec.Fuel) (sk M' rnd σ : List UInt8)
    (h : Spec.Sign_internal_bounded sp B sk M' rnd F = some σ) : σ.length = sp.sigLen := by
  rw [Proofs.Sign.Sign_internal_bounded_eq] at h
  rcases hP : Proofs.Sign.pre sp F sk M' rnd with _ | P
  · rw [hP] at h; simp at h
  rw [hP] at h
  simp only [] at h
  rcases hl : Proofs.Sign.loopRes sp F P B 0 with _ | _ | ⟨ct, z, hh⟩
  · rw [hl] at h; simp [Proofs.Sign.encodeRes] at h
  · rw [hl] at h; simp [Proofs.Sign.encodeRes] at h
  · rw [hl] at h
    simp only [Proofs.Sign.encodeRes, Option.some.injEq] at h
    subst h
    exact sigEncode_length sp hs ct (loopRes_ct_len sp F P B 0 ct z hh hl) _ _

/-! ## Algorithm 3 -/

theorem verifyAPI_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize)
    (pk : Array U8 n) (m ctx : Slice U8) (sig : Array U8 N) (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify sp (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :
    verifyAPI n N K L (ok ip) pk m ctx sig ⦃ r => r = b ⦄ := by
  unfold verifyAPI
  refine WP.spec_bind (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · have h' : 255 < (bytes ctx).length := by simp only [bytes_length]; exact ho
    rw [Verify_long sp _ _ _ _ F h'] at hs
    have hb : false = b := Option.some.inj hs
    refine (WP.spec_ok _).mpr hb
  · obtain ⟨hl, htake, hdrop⟩ := ho
    simp only [Std.bind_tc_ok]
    step*
    have hlen : ctx.len.val = ctx.val.length := by simp
    have hs1 : bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx :=
      prefix_bytes ctx b' i1 s1 (by rw [i1_post, hlen]) s1_post1 htake
    have hbs : bytes s = bytesA pk := by rw [s_post, bytes_to_slice]
    have hbs2 : bytes s2 = bytesA sig := by rw [s2_post, bytes_to_slice]
    refine verify_internal_spec hp s s2 s1 m F b ?_
    rw [Verify_short sp _ _ _ _ F (by simpa using hl)] at hs
    rw [hbs, hbs2, hs1]
    simpa [List.append_assoc] using hs

theorem _root_.Proofs.verify_44_correct (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize)
    (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :
    api.verify_44 pk m ctx sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_44_eq, hip]
  exact verifyAPI_spec hp _ _ pk m ctx sig F b hs


theorem _root_.Proofs.verify_65_correct (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize)
    (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :
    api.verify_65 pk m ctx sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_65_eq, hip]
  exact verifyAPI_spec hp _ _ pk m ctx sig F b hs

theorem _root_.Proofs.verify_87_correct (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize)
    (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) :
    api.verify_87 pk m ctx sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_87_eq, hip]
  exact verifyAPI_spec hp _ _ pk m ctx sig F b hs

/-- For `|ctx| > 255` the spec's `Verify` is `false` and so is the Rust. -/
theorem verifyAPI_ctx_long (n N K L : Usize) (P : RustM params.Params) (pk : Array U8 n) (m ctx : Slice U8)
    (sig : Array U8 N) (h : 255 < ctx.val.length) :
    verifyAPI n N K L P pk m ctx sig ⦃ r => r = false ⦄ := by
  unfold verifyAPI
  refine WP.spec_bind (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · exact (WP.spec_ok _).mpr rfl
  · exact absurd ho.1 (by omega)

/-! ## Algorithm 2 -/

theorem signAPI_ctx_long (n N K L : Usize) (P : RustM params.Params) (sk : Array U8 n) (m ctx : Slice U8)
    (rnd : Array U8 32#usize) (h : 255 < ctx.val.length) :
    signAPI n N K L P sk m ctx rnd ⦃ r => r = none ⦄ := by
  unfold signAPI
  refine WP.spec_bind (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · exact (WP.spec_ok _).mpr rfl
  · exact absurd ho.1 (by omega)

theorem signAPI_some {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m ctx : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign sp (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) :
    signAPI n N K L (ok ip) sk m ctx rnd ⦃ r => ∃ s, r = some s ∧ bytesA s = σ ⦄ := by
  have hcl : ctx.val.length ≤ 255 := by
    by_contra hh
    rw [Sign_long sp _ _ _ _ F (by simp only [bytes_length]; omega)] at hs
    exact absurd hs (by simp)
  unfold signAPI
  refine WP.spec_bind (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · exact absurd ho (by omega)
  · obtain ⟨hl, htake, hdrop⟩ := ho
    simp only [Std.bind_tc_ok]
    step*
    have hlen : ctx.len.val = ctx.val.length := by simp
    have hs1 : bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx :=
      prefix_bytes ctx b' i1 s1 (by rw [i1_post, hlen]) s1_post1 htake
    have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
    have hls : s.length = sp.skLen := by
      have := congrArg List.length hbs
      simp only [bytes_length, bytesA_length] at this
      show s.val.length = _
      omega
    have hls2 : s2.length = sp.sigLen := by
      show s2.val.length = _
      rw [s2_post1]; simp [Array.repeat_val, hN]
    rw [Sign_short sp _ _ _ _ F (by simpa using hl)] at hs
    simp only [bytes_length] at hs
    have hspec : Spec.Sign_internal_bounded sp (kappaBudget sp) (bytes s) (bytes s1 ++ bytes m) (bytesA rnd) F
        = some σ := by
      rw [hbs, hs1]; exact hs
    have hlenσ : σ.length = sp.sigLen :=
      sign_len sp (Params.Std.params hp).stdSig _ F _ _ _ σ hspec
    refine WP.spec_bind (Proofs.Sign.sign_internal_spec_some hp s s1 m rnd s2 hls hls2 _ F σ hspec) ?_
    rintro ⟨b1, s3⟩ ⟨hb1, hs3⟩
    have hb1' : b1 = true := hb1
    have hs3' : bytes s3 = σ := hs3
    subst hb1'
    have hl3 : s3.val.length = N.val := by
      have := congrArg List.length hs3'
      simp only [bytes_length] at this
      omega
    refine (WP.spec_ok _).mpr ⟨_, rfl, ?_⟩
    rw [s2_post2, bytesA_from_slice _ _ hl3, hs3']

/-- If the κ budget is exhausted (`Exhausted`), the spec's `Sign` is `none` (for `|ctx| ≤ 255`). -/
theorem sign_exhausted_spec_none (sp : Spec.Params) (F : Spec.Fuel) (sk M ctx rnd : List UInt8)
    (hl : ctx.length ≤ 255)
    (hex : Proofs.Sign.Exhausted sp F sk (IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M) rnd) :
    Spec.Sign sp sk M ctx rnd F = none := by
  rw [Sign_short sp _ _ _ _ F hl, ← mprime_eq]
  exact Proofs.Sign.exhausted_spec_none sp F sk _ rnd hex

theorem signAPI_exhausted {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m ctx : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted sp F (bytesA sk)
      (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :
    signAPI n N K L (ok ip) sk m ctx rnd ⦃ r => r = none ⦄ := by
  by_cases hcl : ctx.val.length ≤ 255
  swap
  · exact signAPI_ctx_long n N K L _ sk m ctx rnd (by omega)
  unfold signAPI
  refine WP.spec_bind (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · exact absurd ho (by omega)
  · obtain ⟨hl, htake, hdrop⟩ := ho
    simp only [Std.bind_tc_ok]
    step*
    have hlen : ctx.len.val = ctx.val.length := by simp
    have hs1 : bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx :=
      prefix_bytes ctx b' i1 s1 (by rw [i1_post, hlen]) s1_post1 htake
    have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
    have hls : s.length = sp.skLen := by
      have := congrArg List.length hbs
      simp only [bytes_length, bytesA_length] at this
      show s.val.length = _
      omega
    have hls2 : s2.length = sp.sigLen := by
      show s2.val.length = _
      rw [s2_post1]; simp [Array.repeat_val, hN]
    rw [mprime_eq] at hex
    simp only [bytes_length] at hex
    have hex' : Proofs.Sign.Exhausted sp F (bytes s) (bytes s1 ++ bytes m) (bytesA rnd) := by
      rw [hbs, hs1]; exact hex
    refine WP.spec_bind (Proofs.Sign.sign_internal_spec_none hp s s1 m rnd s2 hls hls2 F hex') ?_
    rintro ⟨b1, s3⟩ hb1
    have hb1' : b1 = false := hb1.1
    subst hb1'
    exact (WP.spec_ok _).mpr rfl


/-! ### ML-DSA-44 -/

/-- **Algorithm 2 (`Sign`), ML-DSA-44, success.** If the spec returns `σ`, the Rust returns `some σ'` with
`σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_44_correct_some (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) :
    api.sign_44 sk m ctx rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_44_eq, hip]
  exact signAPI_some hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m ctx rnd F σ hs

/-- **Algorithm 2, ML-DSA-44, `|ctx| > 255`.** The spec returns `⊥` (`none`) and so does the Rust. -/
theorem _root_.Proofs.sign_44_correct_ctx_long (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      api.sign_44 sk m ctx rnd ⦃ r => r = none ⦄ := by
  refine ⟨Sign_long _ _ _ _ _ F h, ?_⟩
  rw [sign_44_eq]
  exact signAPI_ctx_long _ _ _ _ _ sk m ctx rnd (by simpa using h)

/-- **Algorithm 2, ML-DSA-44, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`, for the spec's `M′`), the Rust returns `none`. -/
theorem _root_.Proofs.sign_44_correct_exhausted (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
      (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :
    api.sign_44 sk m ctx rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_44_eq, hip]
  exact signAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m ctx rnd F hex

/-- **Algorithm 3, ML-DSA-44, `|ctx| > 255`.** The spec returns `false` and so does the Rust. -/
theorem _root_.Proofs.verify_44_ctx_long (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some false ∧
      api.verify_44 pk m ctx sig ⦃ r => r = false ⦄ := by
  refine ⟨Verify_long _ _ _ _ _ F h, ?_⟩
  rw [verify_44_eq]
  exact verifyAPI_ctx_long _ _ _ _ _ pk m ctx sig (by simpa using h)

/-! ### ML-DSA-65 -/

/-- **Algorithm 2 (`Sign`), ML-DSA-65, success.** If the spec returns `σ`, the Rust returns `some σ'` with
`σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_65_correct_some (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) :
    api.sign_65 sk m ctx rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_65_eq, hip]
  exact signAPI_some hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m ctx rnd F σ hs

/-- **Algorithm 2, ML-DSA-65, `|ctx| > 255`.** The spec returns `⊥` (`none`) and so does the Rust. -/
theorem _root_.Proofs.sign_65_correct_ctx_long (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      api.sign_65 sk m ctx rnd ⦃ r => r = none ⦄ := by
  refine ⟨Sign_long _ _ _ _ _ F h, ?_⟩
  rw [sign_65_eq]
  exact signAPI_ctx_long _ _ _ _ _ sk m ctx rnd (by simpa using h)

/-- **Algorithm 2, ML-DSA-65, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`, for the spec's `M′`), the Rust returns `none`. -/
theorem _root_.Proofs.sign_65_correct_exhausted (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
      (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :
    api.sign_65 sk m ctx rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_65_eq, hip]
  exact signAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m ctx rnd F hex

/-- **Algorithm 3, ML-DSA-65, `|ctx| > 255`.** The spec returns `false` and so does the Rust. -/
theorem _root_.Proofs.verify_65_ctx_long (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some false ∧
      api.verify_65 pk m ctx sig ⦃ r => r = false ⦄ := by
  refine ⟨Verify_long _ _ _ _ _ F h, ?_⟩
  rw [verify_65_eq]
  exact verifyAPI_ctx_long _ _ _ _ _ pk m ctx sig (by simpa using h)

/-! ### ML-DSA-87 -/

/-- **Algorithm 2 (`Sign`), ML-DSA-87, success.** If the spec returns `σ`, the Rust returns `some σ'` with
`σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_87_correct_some (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) :
    api.sign_87 sk m ctx rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_87_eq, hip]
  exact signAPI_some hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m ctx rnd F σ hs

/-- **Algorithm 2, ML-DSA-87, `|ctx| > 255`.** The spec returns `⊥` (`none`) and so does the Rust. -/
theorem _root_.Proofs.sign_87_correct_ctx_long (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      api.sign_87 sk m ctx rnd ⦃ r => r = none ⦄ := by
  refine ⟨Sign_long _ _ _ _ _ F h, ?_⟩
  rw [sign_87_eq]
  exact signAPI_ctx_long _ _ _ _ _ sk m ctx rnd (by simpa using h)

/-- **Algorithm 2, ML-DSA-87, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`, for the spec's `M′`), the Rust returns `none`. -/
theorem _root_.Proofs.sign_87_correct_exhausted (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
      (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :
    api.sign_87 sk m ctx rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_87_eq, hip]
  exact signAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m ctx rnd F hex

/-- **Algorithm 3, ML-DSA-87, `|ctx| > 255`.** The spec returns `false` and so does the Rust. -/
theorem _root_.Proofs.verify_87_ctx_long (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize)
    (F : Spec.Fuel) (h : 255 < (bytes ctx).length) :
    Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some false ∧
      api.verify_87 pk m ctx sig ⦃ r => r = false ⦄ := by
  refine ⟨Verify_long _ _ _ _ _ F h, ?_⟩
  rw [verify_87_eq]
  exact verifyAPI_ctx_long _ _ _ _ _ pk m ctx sig (by simpa using h)

end API

end Proofs
