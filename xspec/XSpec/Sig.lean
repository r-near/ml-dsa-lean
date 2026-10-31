import XSpec.Keys

/-!
# Algorithms 26 and 27 (`sigEncode`, `sigDecode`)

Against `EndToEnd.MLDSA.fipsSigEncode` / `fipsSigDecode` (ocaml-pq's transcription of the two algorithms, on
`MLDSAAlg` types).  Hints: our `Vector HintPoly k` is `fun r c => if h[r]![c]! then 1 else 0`
(`hintToVec`); decoded hints come back as `hintToPoly`.  `sigEncode` needs the precondition of
`HintBitPack` (weight at most `ω`); `sigDecode` needs `|σ| = sigLen` (checked first by `Verify_internal`).
-/

open Spec

namespace XSpec


theorem sigEncode_flat (p : Spec.Params) (c : List UInt8) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k) :
    Spec.sigEncode p c z h = c ++ ((List.range' 0 p.ℓ).map fun i => BitPack z[i]! (p.γ₁ - 1) p.γ₁).flatten ++
      HintBitPack p h := by
  unfold Spec.sigEncode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- The `z` component of `sigDecode`. -/
def sigZ (p : Spec.Params) (σ : List UInt8) : Vector RPoly p.ℓ :=
  (List.range' 0 p.ℓ).foldl (fun (w : Vector RPoly p.ℓ) a => w.set! a
    (BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁)) (Vector.replicate p.ℓ (Vector.replicate 256 0))

theorem sigZ_get (p : Spec.Params) (σ : List UInt8) (i : Nat) (hi : i < p.ℓ) :
    (sigZ p σ)[i] = BitUnpack (slice σ (p.lam / 4 + i * (32 * (1 + bitlen (p.γ₁ - 1))))
      (32 * (1 + bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁ := by
  unfold sigZ
  refine (EB.vec_fold_gen (m := p.ℓ) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁) p.ℓ i hi).trans ?_
  rw [if_pos hi]

theorem sigDecode_flat (p : Spec.Params) (σ : List UInt8) :
    Spec.sigDecode p σ = (HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.ω + p.k))).map (fun h => (slice σ 0 (p.lam / 4), sigZ p σ, h)) := by
  unfold Spec.sigDecode sigZ
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases hH : HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1)))) (p.ω + p.k)) <;>
    simp [hH, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


/-! ## `hintBitUnpack` only reads the first `ω + k` bytes -/

section Trunc

open OcamlPq.Encoding.Hint

theorem unpackWhile_congr (y y' : List ℕ) (ω : ℕ) (hy : ∀ j < ω, y.getD j 0 = y'.getD j 0) (i first stop : ℕ)
    (hs : stop ≤ ω) :
    ∀ n index h, stop - index = n → unpackWhile y i first stop index h = unpackWhile y' i first stop index h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro index h hn
    conv_lhs => rw [unpackWhile]
    conv_rhs => rw [unpackWhile]
    by_cases hlt : index < stop
    · rw [if_pos hlt, if_pos hlt]
      have e1 : y.getD index 0 = y'.getD index 0 := hy index (by omega)
      have e2 : y.getD (index - 1) 0 = y'.getD (index - 1) 0 := hy (index - 1) (by omega)
      rw [e1, e2]
      split_ifs with hc
      · rfl
      · exact ih (stop - (index + 1)) (by omega) _ _ rfl
    · rw [if_neg hlt, if_neg hlt]

theorem unpackRows_congr (k ω : ℕ) (y y' : List ℕ) (hy : ∀ j < ω + k, y.getD j 0 = y'.getD j 0) :
    ∀ n i h index, k - i = n → unpackRows k ω y i h index = unpackRows k ω y' i h index := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i h index hn
    conv_lhs => rw [unpackRows]
    conv_rhs => rw [unpackRows]
    by_cases hi : i < k
    · rw [if_pos hi, if_pos hi]
      have e : y.getD (ω + i) 0 = y'.getD (ω + i) 0 := hy _ (by omega)
      rw [e]
      by_cases hb : y'.getD (ω + i) 0 < index ∨ y'.getD (ω + i) 0 > ω
      · rw [if_pos hb, if_pos hb]
      · rw [if_neg hb, if_neg hb]
        have hs : y'.getD (ω + i) 0 ≤ ω := by omega
        rw [unpackWhile_congr y y' ω (fun j hj => hy j (by omega)) i index _ hs _ index h rfl]
        cases hw : unpackWhile y' i index (y'.getD (ω + i) 0) index h with
        | none => rfl
        | some r => exact ih (k - (i + 1)) (by omega) _ _ _ rfl
    · rw [if_neg hi, if_neg hi]

theorem unpackTrailing_congr (ω : ℕ) (y y' : List ℕ) (hy : ∀ j < ω, y.getD j 0 = y'.getD j 0) :
    ∀ n i, ω - i = n → unpackTrailing ω y i = unpackTrailing ω y' i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hn
    conv_lhs => rw [unpackTrailing]
    conv_rhs => rw [unpackTrailing]
    by_cases hi : i < ω
    · rw [if_pos hi, if_pos hi, hy i hi]
      split_ifs with hc
      · rfl
      · exact ih (ω - (i + 1)) (by omega) _ rfl
    · rw [if_neg hi, if_neg hi]

theorem hintBitUnpack_congr (k ω : ℕ) (y y' : List ℕ) (hy : ∀ j < ω + k, y.getD j 0 = y'.getD j 0) :
    hintBitUnpack k ω y = hintBitUnpack k ω y' := by
  unfold hintBitUnpack
  rw [unpackRows_congr k ω y y' hy _ 0 _ 0 rfl]
  cases hr : unpackRows k ω y' 0 (fun _ _ => 0) 0 with
  | none => rfl
  | some r =>
    simp only
    rw [unpackTrailing_congr ω y y' (fun j hj => hy j (by omega)) _ _ rfl]

theorem getD_take_lt (l : List ℕ) (n j : ℕ) (hj : j < n) : (l.take n).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hj]

theorem hintBitUnpack_take (k ω : ℕ) (y : List ℕ) :
    hintBitUnpack k ω (y.take (ω + k)) = hintBitUnpack k ω y :=
  hintBitUnpack_congr k ω _ _ (fun j hj => getD_take_lt y _ j hj)

end Trunc


/-! ## `sigEncode` -/

section Enc

open OcamlPq.MLDSAAlg
open OcamlPq.EndToEnd.MLDSA

theorem foldl_append_nat (len : ℕ) (f : ℕ → List ℕ) (acc : List ℕ) :
    (List.range len).foldl (fun a i => a ++ f i) acc = acc ++ ((List.range len).map f).flatten := by
  induction len generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp [List.append_assoc]

/-- A hint (ours) as a hint polynomial vector of ocaml-pq's end-to-end specification. -/
def hpoly {k : Nat} (H : Vector HintPoly k) : PolyVec := fun r c => ((hv H r c : ℕ) : ℤ)

theorem hintToVec_hpoly {k : Nat} (H : Vector HintPoly k) : hintToVec k (hpoly H) = hv H := by
  funext r c
  unfold hintToVec hpoly hv
  by_cases h : r < k ∧ c < 256 ∧ (H[r]!)[c]! = true
  · simp [h]
  · simp [h]

theorem sigEncode_eq {p : Spec.Params} (hp : Std3 p) (c : List UInt8) (z : Vector RPoly p.ℓ)
    (h : Vector HintPoly p.k) (hw : HintWeight h ≤ p.ω) :
    u8ToBytes (Spec.sigEncode p c z h) =
      fipsSigEncode (algParams p) (u8ToBytes c) (fun i => rfn z[i]!) (hpoly h) := by
  unfold fipsSigEncode OcamlPq.Encoding.Mldsa.sigEncode
  rw [u8ToBytes_eq_natToBytes, sigEncode_flat, bytesToNat_u8ToBytes]
  congr 1
  simp only [encParams, algParams]
  rw [hintToVec_hpoly, foldl_append_nat, ← hintBitPack_eq p hp.omega_lt h hw]
  simp only [bytesN, List.map_append, List.map_flatten, List.map_map]
  rw [← List.range_eq_range']
  have hm : (List.range p.ℓ).map (List.map UInt8.toNat ∘ fun i => BitPack z[i]! (p.γ₁ - 1) p.γ₁) =
      (List.range p.ℓ).map (fun i => OcamlPq.Encoding.Spec.bitPack
        ((vecToLists p.ℓ fun i => rfn z[i]!).getD i []) (p.γ₁ - 1) p.γ₁) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < p.ℓ := List.mem_range.mp hi
    have := bitPack_eq z[i]! (p.γ₁ - 1) p.γ₁
    simp only [bytesN] at this
    simp only [Function.comp, this]
    simp [vecToLists, List.getD_eq_getElem?_getD, hi', polyToList_rfn]
  rw [hm]


/-! ## `sigDecode` -/

theorem bytesN_slice (σ : List UInt8) (off n : ℕ) : bytesN (slice σ off n) = ((bytesN σ).drop off).take n := by
  simp [slice, bytesN, List.map_take, List.map_drop]

theorem listToPoly_nil : listToPoly [] = fun _ => (0 : ℤ) := by
  funext i; simp [listToPoly]

/-- `sigDecode` (Algorithm 27) against ocaml-pq's `fipsSigDecode`, for every byte string (neither side checks
the length; `Verify_internal` does).  The decoded `c̃` and `z` agree, `h` agrees through `hpoly`, and `none`
(`⊥`) agrees. -/
theorem sigDecode_eq {p : Spec.Params} (hp : Std3 p) (σ : List UInt8) :
    (Spec.sigDecode p σ).map (fun x => (u8ToBytes x.1, (fun r => rfn (x.2.1[r]!)), hpoly x.2.2)) =
      fipsSigDecode (algParams p) (u8ToBytes σ) := by
  unfold fipsSigDecode OcamlPq.Encoding.Mldsa.sigDecode
  rw [bytesToNat_u8ToBytes, sigDecode_flat]
  simp only [encParams, algParams, Option.map_map]
  have key : (HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + Spec.bitlen (p.γ₁ - 1)))) (p.ω + p.k))).map hv =
      OcamlPq.Encoding.Hint.hintBitUnpack p.k p.ω
        ((bytesN σ).drop (p.lam / 4 + p.ℓ * (32 * (1 + OcamlPq.Encoding.Spec.bitlen (p.γ₁ - 1))))) := by
    rw [hintBitUnpack_eq, bytesN_slice, bitlen_eq_size, OcamlPq.Encoding.Spec.bitlen]
    exact hintBitUnpack_take _ _ _
  simp only [bitlen_eq_size, OcamlPq.Encoding.Spec.bitlen] at key ⊢
  have hz : ∀ r, (fun r => rfn ((sigZ p σ)[r]!)) r = listsToVec ((List.range p.ℓ).map (fun i =>
      OcamlPq.Encoding.Spec.bitUnpack (List.take (32 * (1 + (p.γ₁ - 1).size))
        (List.drop (p.lam / 4 + i * (32 * (1 + (p.γ₁ - 1).size))) (bytesN σ))) (p.γ₁ - 1) p.γ₁)) r := by
    intro r
    beta_reduce
    by_cases hr : r < p.ℓ
    · rw [getElem!_pos (sigZ p σ) r hr, sigZ_get p σ r hr]
      simp only [listsToVec]
      rw [List.getD_eq_getElem?_getD]
      simp only [List.getElem?_map, List.getElem?_range hr, Option.map_some, Option.getD_some]
      simp only [bitlen_eq_size]
      rw [← bytesN_slice, ← bitUnpack_eq]
      exact (listToPoly_rfn_toList _).symm
    · rw [getElem!_neg (sigZ p σ) r (by simpa using hr)]
      simp only [listsToVec]
      rw [List.getD_eq_getElem?_getD]
      have hn : (List.range p.ℓ)[r]? = none := List.getElem?_eq_none (by simp; omega)
      rw [List.getElem?_map, hn]
      simp only [Option.map_none, Option.getD_none, listToPoly_nil]
      funext i
      simp only [rfn]
      by_cases hi : i < 256
      · rw [getElem!_pos (default : RPoly) i hi]; simp [default]
      · rw [getElem!_neg (default : RPoly) i (by simpa using hi)]; rfl
  rcases hH : HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + (p.γ₁ - 1).size))) (p.ω + p.k)) with _ | H
  · rw [hH] at key
    simp only [Option.map_none] at key
    rw [← key]
    simp
  · rw [hH] at key
    simp only [Option.map_some] at key
    rw [← key]
    simp only [Option.map_some, Function.comp, Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, funext hz, rfl⟩
    rw [u8ToBytes_eq_natToBytes, bytesN_slice]
    simp

end Enc

/-! ## `skDecode` -/

section Sk

open OcamlPq.Encoding.Mldsa

theorem Std3.eta {p : Spec.Params} (h : Std3 p) : p.η = 2 ∨ p.η = 4 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem Std3.etaBits_eq {p : Spec.Params} (h : Std3 p) : Spec.bitlen (2 * p.η) = etaBits p.η := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem Std3.skSize_eq {p : Spec.Params} (h : Std3 p) : (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).skSize = p.skLen := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem bitUnpack_le (v : List ℕ) (a b : ℕ) : ∀ w ∈ OcamlPq.Encoding.Spec.bitUnpack v a b, w ≤ b := by
  intro w hw
  simp only [OcamlPq.Encoding.Spec.bitUnpack, List.mem_map] at hw
  obtain ⟨i, -, rfl⟩ := hw
  have := Int.natCast_nonneg (OcamlPq.Encoding.Spec.bitsToInteger
    ((List.range (OcamlPq.Encoding.Spec.bitlen (a + b))).map fun t =>
      (OcamlPq.Encoding.Spec.bytesToBits v).getD (i * OcamlPq.Encoding.Spec.bitlen (a + b) + t) 0)
    (OcamlPq.Encoding.Spec.bitlen (a + b)))
  omega

/-- The decoded secret polynomials all lie in `[-η, η]` (the range check that ocaml-pq's decoder performs
and FIPS 204's `skDecode` does not). -/
def SkInRange (p : Spec.Params) (s₁ : Vector RPoly p.ℓ) (s₂ : Vector RPoly p.k) : Prop :=
  (∀ i < p.ℓ, ∀ c ∈ s₁[i]!.toList, -(p.η : ℤ) ≤ c ∧ c ≤ p.η) ∧
  (∀ i < p.k, ∀ c ∈ s₂[i]!.toList, -(p.η : ℤ) ≤ c ∧ c ≤ p.η)


theorem slice_length (σ : List UInt8) (off n : ℕ) (h : off + n ≤ σ.length) : (slice σ off n).length = n := by
  simp [slice]; omega

theorem unpackEta_slice {p : Spec.Params} (hp : Std3 p) (sk : List UInt8) (off : ℕ)
    (hoff : off + 32 * Spec.bitlen (2 * p.η) ≤ sk.length) :
    unpackEta p.η (OcamlPq.Encoding.sub (bytesN sk) off (32 * etaBits p.η)) =
      if (∀ c ∈ (BitUnpack (slice sk off (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c)
      then some (BitUnpack (slice sk off (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList else none := by
  have hb := hp.etaBits_eq
  have hsub : OcamlPq.Encoding.sub (bytesN sk) off (32 * etaBits p.η) =
      bytesN (slice sk off (32 * Spec.bitlen (2 * p.η))) := by
    rw [hb]; exact (bytesN_slice sk off _).symm
  have hv : (bytesN (slice sk off (32 * Spec.bitlen (2 * p.η)))).length = 32 * etaBits p.η := by
    simp only [bytesN, List.length_map]; rw [slice_length _ _ _ hoff, hb]
  have hbytes : ∀ x ∈ bytesN (slice sk off (32 * Spec.bitlen (2 * p.η))), x < 256 := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    exact UInt8.toNat_lt b
  have h1 := unpackEta_eq p.η hp.eta _ hv hbytes
  have h2 := unpackEta_eq_none_iff p.η hp.eta _ hv hbytes
  have h3 := bitUnpack_eq (slice sk off (32 * Spec.bitlen (2 * p.η))) p.η p.η
  rw [hsub]
  by_cases hr : ∀ c ∈ (BitUnpack (slice sk off (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c
  · rw [if_pos hr, h1]
    have : ¬ ((OcamlPq.Encoding.Packer.unpackCodes (etaBits p.η) (bytesN (slice sk off (32 * Spec.bitlen (2 * p.η))))).any
        (fun value => decide (value > 2 * p.η)) = true) := by
      intro hany
      have hn : unpackEta p.η (bytesN (slice sk off (32 * Spec.bitlen (2 * p.η)))) = none := by
        rw [h1, if_pos hany]
      obtain ⟨w, hw, hlt⟩ := h2.mp hn
      rw [← h3] at hw
      have := hr w hw
      omega
    rw [if_neg this, h3]
  · rw [if_neg hr]
    push Not at hr
    obtain ⟨c, hc, hlt⟩ := hr
    exact h2.mpr ⟨c, by rw [← h3] at *; exact hc, hlt⟩ 

theorem decodeEtaVector_slice {p : Spec.Params} (hp : Std3 p) (sk : List UInt8) (pos n : ℕ)
    (hpos : pos + n * (32 * Spec.bitlen (2 * p.η)) ≤ sk.length) :
    decodeEtaVector (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)) (bytesN sk) n pos =
      (if ∀ i < n, ∀ c ∈ (BitUnpack (slice sk (pos + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c
       then some ((List.range n).map fun i => (BitUnpack (slice sk (pos + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList) else none,
       pos + n * (32 * Spec.bitlen (2 * p.η))) := by
  have hE : (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).etaPackedBytes = 32 * Spec.bitlen (2 * p.η) := by
    rw [OcamlPq.Encoding.Mldsa.Params.etaPackedBytes_eq, hp.etaBits_eq]; rfl
  have hE' : (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).etaPackedBytes = 32 * etaBits p.η := by
    rw [OcamlPq.Encoding.Mldsa.Params.etaPackedBytes_eq]; rfl
  rw [decodeEtaVector_eq, hE]
  have hblk : ∀ i < n, unpackEta (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).eta (etaBlock (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)) (bytesN sk) pos i) =
      if (∀ c ∈ (BitUnpack (slice sk (pos + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c)
      then some (BitUnpack (slice sk (pos + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList else none := by
    intro i hi
    have hle : (i + 1) * (32 * Spec.bitlen (2 * p.η)) ≤ n * (32 * Spec.bitlen (2 * p.η)) :=
      Nat.mul_le_mul_right _ hi
    have := unpackEta_slice hp sk (pos + i * (32 * Spec.bitlen (2 * p.η))) (by
      rw [Nat.add_mul] at hle; omega)
    rw [← hp.etaBits_eq] at this
    unfold etaBlock
    rw [hE]
    exact this
  by_cases hr : ∀ i < n, ∀ c ∈ (BitUnpack (slice sk (pos + i * (32 * Spec.bitlen (2 * p.η)))
      (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c
  · have hs : ∀ i < n, (unpackEta (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).eta (etaBlock (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)) (bytesN sk)
        pos i)).isSome := by
      intro i hi
      rw [hblk i hi, if_pos (hr i hi)]; rfl
    rw [if_pos hr]
    refine Prod.ext ((if_pos hs).trans ?_) rfl
    show some _ = some _
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    show (unpackEta _ _).getD [] = _
    rw [hblk i hi', if_pos (hr i hi')]; rfl
  · rw [if_neg hr]
    have : ¬ ∀ i < n, (unpackEta (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).eta (etaBlock (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)) (bytesN sk)
        pos i)).isSome := by
      intro h
      apply hr
      intro i hi c hc
      have := h i hi
      rw [hblk i hi] at this
      by_contra hlt
      rw [if_neg (fun hall => hlt (hall c hc))] at this
      simp at this
    exact Prod.ext (if_neg this) rfl

theorem toList_map_toList {n : ℕ} (v : Vector RPoly n) (g : ℕ → RPoly) (h : ∀ i (hi : i < n), v[i] = g i) :
    v.toList.map Vector.toList = (List.range n).map (fun i => (g i).toList) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp [h i hi]

open Classical in
/-- `skDecode` (Algorithm 25) against ocaml-pq's `decodeSk` (their `decode_expanded_signing_key`).  Theirs
rejects a key of the wrong length and any `s₁`/`s₂` coefficient below `-η` (`unpack_eta`); ours is FIPS-literal
and accepts everything.  So: on keys of the right length whose decoded `s₁`, `s₂` lie in `[-η, η]` the two
decoders agree on all six components; on every other `sk` theirs is `none`. -/
theorem skDecode_eq {p : Spec.Params} (hp : Std3 p) (sk : List UInt8) :
    decodeSk (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)) (bytesN sk) =
      if sk.length = p.skLen ∧ SkInRange p (Spec.skDecode p sk).2.2.2.1 (Spec.skDecode p sk).2.2.2.2.1 then
        some (bytesN (Spec.skDecode p sk).1, bytesN (Spec.skDecode p sk).2.1, bytesN (Spec.skDecode p sk).2.2.1,
          (Spec.skDecode p sk).2.2.2.1.toList.map Vector.toList,
          (Spec.skDecode p sk).2.2.2.2.1.toList.map Vector.toList,
          (Spec.skDecode p sk).2.2.2.2.2.toList.map Vector.toList)
      else none := by
  by_cases hlen : sk.length = p.skLen
  · have hd := hp.d
    have hsk : p.skLen = 128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) + 416 * p.k := by
      unfold Params.skLen; rw [hd]; ring
    have hS1 : ∀ i < p.ℓ, (Spec.skDecode p sk).2.2.2.1[i]! =
        BitUnpack (slice sk (128 + i * (32 * Spec.bitlen (2 * p.η))) (32 * Spec.bitlen (2 * p.η))) p.η p.η := by
      intro i hi
      rw [getElem!_pos _ i (by simpa using hi)]; exact EB.skDecode_s1 p sk i hi
    have hS2 : ∀ i < p.k, (Spec.skDecode p sk).2.2.2.2.1[i]! =
        BitUnpack (slice sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η := by
      intro i hi
      rw [getElem!_pos _ i (by simpa using hi)]; exact EB.skDecode_s2 p sk i hi
    have hup : ∀ (v : List UInt8) (c : ℤ), c ∈ (BitUnpack v p.η p.η).toList → c ≤ p.η := by
      intro v c hc
      rw [bitUnpack_eq] at hc
      exact bitUnpack_le _ _ _ c hc
    have hrange : SkInRange p (Spec.skDecode p sk).2.2.2.1 (Spec.skDecode p sk).2.2.2.2.1 ↔
        (∀ i < p.ℓ, ∀ c ∈ (BitUnpack (slice sk (128 + i * (32 * Spec.bitlen (2 * p.η)))
          (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c) ∧
        (∀ i < p.k, ∀ c ∈ (BitUnpack (slice sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) +
          i * (32 * Spec.bitlen (2 * p.η))) (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c) := by
      unfold SkInRange
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i hi c hc => (h1 i hi c (by rw [hS1 i hi]; exact hc)).1,
          fun i hi c hc => (h2 i hi c (by rw [hS2 i hi]; exact hc)).1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun i hi c hc => by rw [hS1 i hi] at hc; exact ⟨h1 i hi c hc, hup _ _ hc⟩,
          fun i hi c hc => by rw [hS2 i hi] at hc; exact ⟨h2 i hi c hc, hup _ _ hc⟩⟩
    have hmul : ∀ n, n * (32 * Spec.bitlen (2 * p.η)) ≤ (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) →
        128 + n * (32 * Spec.bitlen (2 * p.η)) ≤ sk.length := by
      intro n hn; rw [hlen, hsk]; omega
    have hv1 := decodeEtaVector_slice hp sk 128 p.ℓ
      (hmul _ (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    have hv2 := decodeEtaVector_slice hp sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η))) p.k (by
      have := hmul (p.ℓ + p.k) le_rfl
      rw [Nat.add_mul] at this; omega)
    unfold decodeSk
    rw [if_neg (by simp [bytesN, hlen, hp.skSize_eq])]
    simp only
    rw [show (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).l = p.ℓ from rfl,
      show (OcamlPq.EndToEnd.MLDSA.encParams (algParams p)).k = p.k from rfl, hv1]
    have hrho := EB.skDecode_fst p sk
    have hsub : ∀ off n, OcamlPq.Encoding.sub (bytesN sk) off n = bytesN (slice sk off n) :=
      fun off n => (bytesN_slice sk off n).symm
    have e1 : (List.range p.ℓ).map (fun i => (BitUnpack (slice sk (128 + i * (32 * Spec.bitlen (2 * p.η)))
        (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList) = (Spec.skDecode p sk).2.2.2.1.toList.map Vector.toList :=
      (toList_map_toList _ (fun i => BitUnpack (slice sk (128 + i * (32 * Spec.bitlen (2 * p.η)))
        (32 * Spec.bitlen (2 * p.η))) p.η p.η) (fun i hi => EB.skDecode_s1 p sk i hi)).symm
    have e2 : (List.range p.k).map (fun i => (BitUnpack (slice sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) +
        i * (32 * Spec.bitlen (2 * p.η))) (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList) =
        (Spec.skDecode p sk).2.2.2.2.1.toList.map Vector.toList :=
      (toList_map_toList _ (fun i => BitUnpack (slice sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) +
        i * (32 * Spec.bitlen (2 * p.η))) (32 * Spec.bitlen (2 * p.η))) p.η p.η)
        (fun i hi => EB.skDecode_s2 p sk i hi)).symm
    have e3 : (List.range p.k).map (fun index => unpackT0 (OcamlPq.Encoding.sub (bytesN sk)
        (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) + p.k * (32 * Spec.bitlen (2 * p.η)) + index * 416) 416)) =
        (Spec.skDecode p sk).2.2.2.2.2.toList.map Vector.toList := by
      rw [toList_map_toList _ (fun i => BitUnpack (slice sk (128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) +
        i * (32 * p.d)) (32 * p.d)) (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))) (fun i hi => EB.skDecode_t0 p sk i hi)]
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      have hoff : 128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) + p.k * (32 * Spec.bitlen (2 * p.η)) + i * 416 =
          128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) + i * (32 * 13) := by
        rw [Nat.add_mul]; omega
      have hle : 128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) + i * (32 * 13) + 32 * 13 ≤ sk.length := by
        rw [hlen, hsk]; omega
      rw [hd, hoff, hsub]
      have hlen' : (bytesN (slice sk (128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) + i * (32 * 13))
          (32 * 13))).length = 416 := by
        simp only [bytesN, List.length_map]; rw [slice_length _ _ _ hle]
      have hbytes : ∀ x ∈ bytesN (slice sk (128 + (p.ℓ + p.k) * (32 * Spec.bitlen (2 * p.η)) + i * (32 * 13))
          (32 * 13)), x < 256 := by
        intro x hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
        exact UInt8.toNat_lt b
      rw [unpackT0_eq _ hlen' hbytes, ← bitUnpack_eq]
    by_cases h1 : ∀ i < p.ℓ, ∀ c ∈ (BitUnpack (slice sk (128 + i * (32 * Spec.bitlen (2 * p.η)))
        (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c
    · rw [if_pos h1]
      simp only []
      rw [hv2]
      by_cases h2 : ∀ i < p.k, ∀ c ∈ (BitUnpack (slice sk (128 + p.ℓ * (32 * Spec.bitlen (2 * p.η)) +
          i * (32 * Spec.bitlen (2 * p.η))) (32 * Spec.bitlen (2 * p.η))) p.η p.η).toList, -(p.η : ℤ) ≤ c
      · rw [if_pos h2, if_pos ⟨hlen, hrange.mpr ⟨h1, h2⟩⟩]
        simp only []
        rw [e1, e2, e3, hsub, hsub, hsub, hrho.1, hrho.2.1, hrho.2.2]
      · rw [if_neg h2, if_neg (fun h => h2 (hrange.mp h.2).2)]
    · rw [if_neg h1, if_neg (fun h => h1 (hrange.mp h.2).1)]
  · rw [if_neg (fun h => hlen h.1)]
    unfold decodeSk
    rw [if_pos]
    simp only [bytesN, List.length_map, hp.skSize_eq]
    exact hlen

end Sk

end XSpec
