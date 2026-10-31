import XSpec.Hint

/-!
# Algorithms 22-28: `pkEncode`, `pkDecode`, `skEncode`, `skDecode`, `sigEncode`, `sigDecode`, `w1Encode`

Our side acts on `List UInt8`, `RPoly = Vector Int 256` and `Vector HintPoly k`; ocaml-pq's end-to-end
specification (`MLDSAAlg` / `EndToEnd.MLDSA`) on `MLDSAAlg.Bytes = List (Fin 256)`, `Poly = ℕ → ℤ` and
`HintVec`.  Adapters:

* bytes: `u8ToBytes` (ocaml-pq's own adapter); `bytesN` for the `List ℕ` of the Encoding area;
* polynomials: `rfn w = fun i => w[i]!`;
* parameters: `algParams p` (ocaml-pq's `Params`, with `cTildeBytes = λ/4`); statements about the codecs
  assume `Std3 p` (one of the three standardized sets), which gives `d = 13` and discharges every numeric fact.
-/

open Spec

namespace XSpec

open OcamlPq.MLDSAAlg
open OcamlPq.EndToEnd.MLDSA

/-- One of the three standardized parameter sets. -/
def Std3 (p : Spec.Params) : Prop := p = ML_DSA_44 ∨ p = ML_DSA_65 ∨ p = ML_DSA_87

/-- ocaml-pq's parameter record for one of our parameter records (`c̃` has `λ/4` bytes). -/
def algParams (p : Spec.Params) : OcamlPq.MLDSAAlg.Params :=
  ⟨p.k, p.ℓ, p.η, p.τ, p.γ₁, p.γ₂, p.ω, p.lam / 4⟩

theorem algParams_44 : algParams ML_DSA_44 = mldsa44 := by decide +kernel
theorem algParams_65 : algParams ML_DSA_65 = mldsa65 := by decide +kernel
theorem algParams_87 : algParams ML_DSA_87 = mldsa87 := by decide +kernel

theorem Std3.valid {p : Spec.Params} (h : Std3 p) : (algParams p).Valid := by
  rcases h with rfl | rfl | rfl
  · rw [algParams_44]; exact Or.inl rfl
  · rw [algParams_65]; exact Or.inr (Or.inl rfl)
  · rw [algParams_87]; exact Or.inr (Or.inr rfl)

theorem Std3.d {p : Spec.Params} (h : Std3 p) : p.d = 13 := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem Std3.omega_lt {p : Spec.Params} (h : Std3 p) : p.ω < 256 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- A polynomial of `R` as an index function. -/
def rfn (w : RPoly) : ℕ → ℤ := fun i => w[i]!

theorem u8ToBytes_eq_natToBytes (l : List UInt8) : u8ToBytes l = natToBytes (bytesN l) := by
  simp [u8ToBytes, natToBytes, bytesN, u8ToByte, Function.comp_def]

theorem bytesToNat_u8ToBytes (l : List UInt8) : bytesToNat (u8ToBytes l) = bytesN l := by
  rw [u8ToBytes_eq_natToBytes]
  apply bytesToNat_natToBytes
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact UInt8.toNat_lt b

theorem polyToList_rfn (w : RPoly) : polyToList (rfn w) = w.toList := by
  apply List.ext_getElem
  · simp [polyToList]
  · intro i h1 h2
    have : i < 256 := by simpa [polyToList] using h1
    simp [polyToList, rfn, vget! w i this]

theorem polyToNatList_rfn (w : RPoly) : polyToNatList (rfn w) = w.toList.map Int.toNat := by
  apply List.ext_getElem
  · simp [polyToNatList]
  · intro i h1 h2
    have : i < 256 := by simpa [polyToNatList] using h1
    simp [polyToNatList, rfn, vget! w i this]

/-- `SimpleBitPack` on both sides' representations. -/
theorem sbp_corr (w : RPoly) (b : Nat) :
    u8ToBytes (Spec.SimpleBitPack w b) = fipsSimpleBitPack (rfn w) b := by
  unfold fipsSimpleBitPack
  rw [u8ToBytes_eq_natToBytes, simpleBitPack_eq, polyToNatList_rfn]

theorem bp_corr (w : RPoly) (a b : Nat) :
    u8ToBytes (Spec.BitPack w a b) = fipsBitPack (rfn w) a b := by
  unfold fipsBitPack
  rw [u8ToBytes_eq_natToBytes, bitPack_eq, polyToList_rfn]

theorem listToPoly_rfn_toList (w : RPoly) : listToPoly w.toList = rfn w := by
  funext i
  show w.toList.getD i 0 = w[i]!
  exact getD_toList w i

/-- `BitUnpack` on both sides' representations. -/
theorem bu_corr (v : List UInt8) (a b : Nat) :
    rfn (Spec.BitUnpack v a b) = fipsBitUnpack (u8ToBytes v) a b := by
  unfold fipsBitUnpack
  rw [bytesToNat_u8ToBytes, ← bitUnpack_eq, listToPoly_rfn_toList]

theorem foldl_append_eq' (len : ℕ) (f : ℕ → Bytes) (acc : Bytes) :
    (List.range len).foldl (fun a i => a ++ f i) acc = acc ++ ((List.range len).map f).flatten :=
  foldl_append_eq len f acc

theorem u8ToBytes_flatten (L : List (List UInt8)) :
    u8ToBytes L.flatten = (L.map u8ToBytes).flatten := by
  simp only [u8ToBytes, List.map_flatten]
  rfl

theorem flatten_range'_eq {α : Type} (n : Nat) (f : Nat → List α) :
    ((List.range' 0 n).map f) = ((List.range n).map f) := by
  rw [List.range_eq_range']

/-- `pkEncode` (Algorithm 22) against ocaml-pq's `pkEncode` with its FIPS building blocks. -/
theorem pkEncode_eq {p : Spec.Params} (hp : Std3 p) (ρ : List UInt8) (t₁ : Vector RPoly p.k) :
    u8ToBytes (Spec.pkEncode p ρ t₁) =
      OcamlPq.MLDSAAlg.pkEncode (keyFips (algParams p)) (algParams p) (u8ToBytes ρ)
        (fun i => rfn t₁[i]!) := by
  have hf := e2eFacts hp.valid
  have ht : p.t1Bits = 10 := by
    unfold Params.t1Bits; rw [hp.d]; rfl
  unfold OcamlPq.MLDSAAlg.pkEncode
  rw [foldl_append_eq', EB.pkEncode_eq]
  have e : u8ToBytes (ρ ++ ((List.range' 0 p.k).map fun i => Spec.SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)).flatten) =
      u8ToBytes ρ ++ (((List.range' 0 p.k).map fun i => Spec.SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)).map u8ToBytes).flatten := by
    simp only [u8ToBytes, List.map_append, List.map_flatten]
    rfl
  have h : ((List.range' 0 p.k).map fun i => Spec.SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)).map u8ToBytes =
      (List.range (algParams p).k).map (fun i => (keyFips (algParams p)).simpleBitPack (rfn t₁[i]!)
        (2 ^ (OcamlPq.MLDSAAlg.bitlen (OcamlPq.MLDSAAlg.q - 1) - OcamlPq.MLDSAAlg.d) - 1)) := by
    rw [← List.range_eq_range', List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, keyFips, hf.t1Bound, ht]
    exact sbp_corr _ _
  rw [e, h]

theorem flat_corr (n : Nat) (f : Nat → List UInt8) (g : Nat → Bytes) (h : ∀ i, u8ToBytes (f i) = g i) :
    u8ToBytes ((List.range' 0 n).map f).flatten = ((List.range n).map g).flatten := by
  rw [u8ToBytes_flatten, ← List.range_eq_range', List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

theorem u8ToBytes_append (a b : List UInt8) : u8ToBytes (a ++ b) = u8ToBytes a ++ u8ToBytes b := by
  simp [u8ToBytes]

theorem getD_map_cast (l : List ℕ) (i : Nat) : (l.map (fun x : ℕ => (x : ℤ))).getD i 0 = ((l.getD i 0 : ℕ) : ℤ) := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp

theorem rfn_unpack (v : List UInt8) (b : Nat) :
    rfn (Spec.SimpleBitUnpack v b) = natListToPoly (OcamlPq.Encoding.Spec.simpleBitUnpack (bytesN v) b) := by
  funext i
  have h := simpleBitUnpack_eq v b
  have := getD_toList (Spec.SimpleBitUnpack v b) i
  simp only [rfn, ← this, h, natListToPoly, getD_map_cast]

/-- `pkDecode` (Algorithm 23) against ocaml-pq's `fipsPkDecode`, for every `pk`. -/
theorem pkDecode_eq {p : Spec.Params} (hp : Std3 p) (pk : List UInt8) :
    u8ToBytes (Spec.pkDecode p pk).1 = (fipsPkDecode (algParams p) (u8ToBytes pk)).1 ∧
    (fun r => rfn ((Spec.pkDecode p pk).2[r]!)) = (fipsPkDecode (algParams p) (u8ToBytes pk)).2 := by
  have hf := e2eFacts hp.valid
  have ht : p.t1Bits = 10 := by
    unfold Params.t1Bits; rw [hp.d]; rfl
  refine ⟨?_, ?_⟩
  · rw [EB.pkDecode_fst]
    simp [fipsPkDecode, u8ToBytes, List.map_take]
  · funext r
    unfold fipsPkDecode
    simp only [hf.t1Bits]
    by_cases hr : r < p.k
    · have hr' : r < (algParams p).k := hr
      rw [if_pos hr', getElem!_pos _ r (by simpa using hr), EB.pkDecode_get p pk r hr, ht]
      have hb : bytesToNat (List.take (32 * 10) (List.drop (32 + r * (32 * 10)) (u8ToBytes pk))) =
          bytesN (slice pk (32 + r * (32 * 10)) (32 * 10)) := by
        rw [bytesToNat_take, bytesToNat_drop, bytesToNat_u8ToBytes]
        simp [slice, bytesN, List.map_take, List.map_drop]
      rw [hb, rfn_unpack]
    · have hr' : ¬ r < (algParams p).k := hr
      rw [if_neg hr', getElem!_neg _ r (by simpa using hr)]
      funext i
      simp [rfn, getElem!_neg, default]
      by_cases hi : i < 256
      · rw [getElem!_pos _ i (by simpa using hi)]; simp
      · rw [getElem!_neg _ i (by simpa using hi)]; rfl

/-- `skEncode` (Algorithm 24) against ocaml-pq's `skEncode` with its FIPS building blocks. -/
theorem skEncode_eq {p : Spec.Params} (hp : Std3 p) (ρ K tr : List UInt8) (s₁ : Vector RPoly p.ℓ)
    (s₂ t₀ : Vector RPoly p.k) :
    u8ToBytes (Spec.skEncode p ρ K tr s₁ s₂ t₀) =
      OcamlPq.MLDSAAlg.skEncode (keyFips (algParams p)) (algParams p) (u8ToBytes ρ) (u8ToBytes K)
        (u8ToBytes tr) (fun i => rfn s₁[i]!) (fun i => rfn s₂[i]!) (fun i => rfn t₀[i]!) := by
  have hf := e2eFacts hp.valid
  have hd := hp.d
  unfold OcamlPq.MLDSAAlg.skEncode
  simp only [foldl_append_eq']
  rw [EB.skEncode_eq]
  simp only [u8ToBytes_append]
  have e1 := flat_corr p.ℓ (fun i => Spec.BitPack s₁[i]! p.η p.η) (fun i => fipsBitPack (rfn s₁[i]!) p.η p.η)
    (fun i => bp_corr _ _ _)
  have e2 := flat_corr p.k (fun i => Spec.BitPack s₂[i]! p.η p.η) (fun i => fipsBitPack (rfn s₂[i]!) p.η p.η)
    (fun i => bp_corr _ _ _)
  have e3 := flat_corr p.k (fun i => Spec.BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1)))
    (fun i => fipsBitPack (rfn t₀[i]!) (2 ^ (OcamlPq.MLDSAAlg.d - 1) - 1) (2 ^ (OcamlPq.MLDSAAlg.d - 1)))
    (fun i => by rw [bp_corr]; rw [hd]; rfl)
  simp only [List.append_assoc, e1, e2, e3, keyFips, algParams]

/-- `w1Encode` (Algorithm 28) against ocaml-pq's `w1Encode`, for any signing bundle whose `SimpleBitPack` is
FIPS 204's (`signFips` is one). -/
theorem w1Encode_eq {p : Spec.Params} (hp : Std3 p) (F : SignFips) (hF : F.simpleBitPack = fipsSimpleBitPack)
    (w₁ : Vector RPoly p.k) :
    u8ToBytes (Spec.w1Encode p w₁) =
      OcamlPq.MLDSAAlg.w1Encode F (algParams p) (fun i => rfn w₁[i]!) := by
  unfold OcamlPq.MLDSAAlg.w1Encode
  rw [foldl_append_eq' ]
  rw [EB.w1Encode_eq]
  simp only [List.nil_append, hF]
  exact flat_corr p.k _ _ (fun i => sbp_corr _ _)

end XSpec
