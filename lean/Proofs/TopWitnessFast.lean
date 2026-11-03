import Proofs.Correctness
import Proofs.EncodeBits
import Proofs.NTTOps
import Proofs.SampleA
import Proofs.TopWitnessSeed

/-!
# Kernel-friendly equivalents of the quadratic parts of the specification

`lean/Spec` is written as the pseudocode is: `Array.push` / `set!` loops, `BytesToBits`, `BitsToBytes`. Evaluated by
the kernel these copy a list at every step and the kernel caches every copy, so one `BitUnpack` or `SimpleBitPack`
costs more than 100 GB. This module (not imported by the default build roots) defines linear-time replacements,
and proves them equal to the specification **for all inputs**:

* `SimpleBitPackF` / `BitUnpackF`: the byte string is one big natural number (`bytesN`, `packN`), whose windows are
  read with `/` and `%` (GMP-backed in the kernel);
* `MatrixVectorNTT` and `ScalarVectorNTT` with the pointwise `AddNTT` / `MultiplyNTT` loops replaced by `+` / `zipWith`.

It also fixes the literal notation of the witnesses: `Pl` / `Rl` build a polynomial from a list, `v4` a vector of
length 4.
-/

open Spec
set_option maxRecDepth 8192

namespace Proofs
namespace TopWitness

/-! ## Literals -/

/-- The element of `R_q` / `T_q` whose coefficients are the (reduced) naturals of `l` (zero if `|l| ≠ 256`). -/
def Pl (l : List Nat) : Poly :=
  if h : l.length = 256 then
    ⟨(List.map (fun n : Nat => (Nat.cast n : Zq)) l).toArray, by simp only [List.size_toArray, List.length_map]; exact h⟩
  else Poly.zero

/-- The element of `R` whose coefficients are `l` (zero if `|l| ≠ 256`). -/
def Rl (l : List Int) : RPoly :=
  if h : l.length = 256 then ⟨l.toArray, by simp only [List.size_toArray]; exact h⟩ else Vector.replicate 256 0

/-- A vector of length 4. -/
def v4 {α : Type} (a b c d : α) : Vector α 4 := ⟨#[a, b, c, d], rfl⟩

theorem v4_ext {α : Type} {a b c d a' b' c' d' : α} (h0 : a = a') (h1 : b = b') (h2 : c = c') (h3 : d = d') :
    v4 a b c d = v4 a' b' c' d' := by subst h0 h1 h2 h3; rfl

theorem v4_map {α β : Type} (f : α → β) (a b c d : α) :
    (v4 a b c d).map f = v4 (f a) (f b) (f c) (f d) := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [v4]

theorem v4_zipWith {α β γ : Type} (f : α → β → γ) (a b c d : α) (a' b' c' d' : β) :
    Vector.zipWith f (v4 a b c d) (v4 a' b' c' d') = v4 (f a a') (f b b') (f c c') (f d d') := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [v4]

theorem v4_add {α : Type} [Add α] (a b c d a' b' c' d' : α) :
    v4 a b c d + v4 a' b' c' d' = v4 (a + a') (b + b') (c + c') (d + d') := v4_zipWith _ _ _ _ _ _ _ _ _

theorem v4_sub {α : Type} [Sub α] (a b c d a' b' c' d' : α) :
    v4 a b c d - v4 a' b' c' d' = v4 (a - a') (b - b') (c - c') (d - d') := v4_zipWith _ _ _ _ _ _ _ _ _

theorem v4_neg {α : Type} [Neg α] (a b c d : α) : -(v4 a b c d) = v4 (-a) (-b) (-c) (-d) := v4_map _ _ _ _ _

theorem v4_get0 {α : Type} (a b c d : α) : (v4 a b c d)[0] = a := rfl
theorem v4_get1 {α : Type} (a b c d : α) : (v4 a b c d)[1] = b := rfl
theorem v4_get2 {α : Type} (a b c d : α) : (v4 a b c d)[2] = c := rfl
theorem v4_get3 {α : Type} (a b c d : α) : (v4 a b c d)[3] = d := rfl

theorem NTTVec_v4 (a b c d : Poly) : Spec.NTTVec (v4 a b c d) = v4 (NTT a) (NTT b) (NTT c) (NTT d) := v4_map _ _ _ _ _
theorem NTTInvVec_v4 (a b c d : Poly) :
    Spec.NTTInvVec (v4 a b c d) = v4 (NTTInv a) (NTTInv b) (NTTInv c) (NTTInv d) := v4_map _ _ _ _ _

/-! ## Bytes as one natural number -/

/-- The natural number whose little-endian base-256 digits are the bytes of `v`. -/
def bytesN : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesN bs

/-- `x₀ % 2^c + 2^c (x₁ % 2^c + 2^c (...))`: the windows `xᵢ mod 2^c` side by side. -/
def packN (c : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x % 2 ^ c + 2 ^ c * packN c xs

/-- The low `n` base-256 digits of `N`, as bytes. -/
def natBytes : Nat → Nat → List UInt8
  | _, 0 => []
  | N, n + 1 => (N % 256).toUInt8 :: natBytes (N / 256) n

theorem natBytes_eq (n : Nat) : ∀ N, natBytes N n = (List.range n).map (fun k => ((N / 256 ^ k) % 256).toUInt8) := by
  induction n with
  | zero => intro N; rfl
  | succ n ih =>
    intro N
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, natBytes, ih]
    congr 1
    · simp
    · apply List.map_congr_left
      intro k _
      simp only [Function.comp, Nat.add_comm 1 k, pow_succ, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]

/-! ### Windows of `BV` -/

theorem BV_slice (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (s n m : Nat) (h : s + n ≤ m) :
    BV g s n = (BV g 0 m / 2 ^ s) % 2 ^ n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have e1 := BV_add g 0 s n
  have e2 := BV_add g 0 (s + n) r
  have l1 := BV_lt g hg 0 s
  have l2 := BV_lt g hg s n
  have l3 := BV_lt g hg 0 (s + n)
  rw [Nat.zero_add] at e1
  rw [e2, e1]
  have p : 2 ^ (s + n) = 2 ^ s * 2 ^ n := pow_add _ _ _
  have hs : 0 < 2 ^ s := by positivity
  have hn : 0 < 2 ^ n := by positivity
  -- (a + 2^s * x + 2^s 2^n R) / 2^s = x + 2^n R
  have d : (BV g 0 s + 2 ^ s * BV g s n + 2 ^ (s + n) * BV g (0 + (s + n)) r) / 2 ^ s =
      BV g s n + 2 ^ n * BV g (0 + (s + n)) r := by
    rw [p, show BV g 0 s + 2 ^ s * BV g s n + 2 ^ s * 2 ^ n * BV g (0 + (s + n)) r =
        BV g 0 s + 2 ^ s * (BV g s n + 2 ^ n * BV g (0 + (s + n)) r) by ring]
    rw [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt l1, Nat.zero_add]
  rw [d, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l2]

theorem packN_BV (g : Nat → Nat) (f : Nat → Nat) (c : Nat) (hw : ∀ i, i < 256 → BV g (c * i) c = f i % 2 ^ c) :
    ∀ n j, j + n ≤ 256 → BV g (c * j) (c * n) = packN c ((List.range' j n).map f) := by
  intro n
  induction n with
  | zero => intro j _; simp [BV, packN]
  | succ n ih =>
    intro j hj
    rw [List.range'_succ, List.map_cons, packN, show c * (n + 1) = c + c * n by ring, BV_add, hw j (by omega),
      show c * j + c = c * (j + 1) by ring, ih (j + 1) (by omega)]

theorem packN_bytes (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (f : Nat → Nat) (c : Nat)
    (hw : ∀ i, i < 256 → BV g (c * i) c = f i % 2 ^ c) (k : Nat) (hk : k < 32 * c) :
    BV g (8 * k) 8 = (packN c ((List.range' 0 256).map f) / 256 ^ k) % 256 := by
  rw [BV_slice g hg (8 * k) 8 (c * 256) (by omega), ← packN_BV g f c hw 256 0 (by omega), Nat.mul_zero,
    show (256 : Nat) ^ k = 2 ^ (8 * k) by rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]]
  norm_num

/-! ## `SimpleBitPack` and `BitPack` -/

/-- The packed bytes of 256 windows of width `c` (the shared tail of `SimpleBitPack` and `BitPack`). -/
def packBytes (c : Nat) (f : Nat → Nat) : List UInt8 := natBytes (packN c ((List.range' 0 256).map f)) (32 * c)

theorem pack_model_fast (f : Nat → Nat) (c : Nat) :
    BitsToBytes ((List.range' 0 256).map (fun i => IntegerToBits (f i) c)).flatten = packBytes c f := by
  obtain ⟨g, hg, hw, h3⟩ := pack_model f c
  rw [h3, packBytes, natBytes_eq]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [packN_bytes g hg f c hw k hk]


theorem SimpleBitPack_fast (w : RPoly) (b : Nat) :
    SimpleBitPack w b = packBytes (bitlen b) (fun i => (w[i]!).toNat) := by
  rw [← pack_model_fast]
  unfold SimpleBitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem BitPack_fast (w : RPoly) (a b : Nat) :
    BitPack w a b = packBytes (bitlen (a + b)) (fun i => ((b : Int) - w[i]!).toNat) := by
  rw [← pack_model_fast]
  unfold BitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- `pkEncode` (Algorithm 22) with the fast packing. -/
def pkEncodeF (p : Params) (ρ : List UInt8) (t₁ : Vector RPoly p.k) : List UInt8 :=
  ρ ++ ((List.range' 0 p.k).map fun i =>
    packBytes (bitlen (2 ^ p.t1Bits - 1)) (fun j => ((t₁[i]!)[j]!).toNat)).flatten

theorem pkEncode_fast (p : Params) (ρ : List UInt8) (t₁ : Vector RPoly p.k) : pkEncode p ρ t₁ = pkEncodeF p ρ t₁ := by
  rw [pkEncode_eq]
  unfold pkEncodeF
  simp only [SimpleBitPack_fast]

/-- `w1Encode` (Algorithm 28) with the fast packing. -/
def w1EncodeF (p : Params) (w₁ : Vector RPoly p.k) : List UInt8 :=
  ((List.range' 0 p.k).map fun i =>
    packBytes (bitlen ((q - 1) / (2 * p.γ₂) - 1)) (fun j => ((w₁[i]!)[j]!).toNat)).flatten

theorem w1Encode_fast (p : Params) (w₁ : Vector RPoly p.k) : w1Encode p w₁ = w1EncodeF p w₁ := by
  rw [w1Encode_eq]
  unfold w1EncodeF
  simp only [SimpleBitPack_fast]

/-! ## `BitUnpack` -/

theorem byteBit_cons_lt (b : UInt8) (bs : List UInt8) (t : Nat) (ht : t < 8) :
    byteBit (b :: bs) t = b.toNat / 2 ^ t % 2 := by
  have h1 : t / 8 = 0 := by omega
  have h2 : t % 8 = t := by omega
  simp [byteBit, h1, h2]

theorem byteBit_cons_add (b : UInt8) (bs : List UInt8) (t : Nat) : byteBit (b :: bs) (t + 8) = byteBit bs t := by
  have h1 : (t + 8) / 8 = t / 8 + 1 := by omega
  have h2 : (t + 8) % 8 = t % 8 := by omega
  simp [byteBit, h1, h2]

theorem byteBit_eq_dig (v : List UInt8) : ∀ t, byteBit v t = dig (bytesN v) t := by
  induction v with
  | nil => intro t; simp [byteBit, bytesN, dig, show (default : UInt8).toNat = 0 from rfl]
  | cons b bs ih =>
    intro t
    have hb := b.toNat_lt
    by_cases ht : t < 8
    · rw [byteBit_cons_lt _ _ _ ht]
      simp only [dig, bytesN]
      have h8 : (256 : Nat) = 2 ^ t * 2 ^ (8 - t) := by
        rw [← pow_add, show t + (8 - t) = 8 by omega]; norm_num
      have h2 : (2 : Nat) ^ (8 - t) = 2 * 2 ^ (7 - t) := by
        rw [← pow_succ']; congr 1; omega
      rw [h8, h2, show 2 ^ t * (2 * 2 ^ (7 - t)) * bytesN bs = 2 ^ t * (2 * (2 ^ (7 - t) * bytesN bs)) by ring,
        Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 8 := ⟨t - 8, by omega⟩
      rw [byteBit_cons_add, ih]
      simp only [dig, bytesN]
      rw [show t' + 8 = 8 + t' by omega, pow_add, ← Nat.div_div_eq_div_mul]
      rw [show (2 : Nat) ^ 8 = 256 by norm_num, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hb,
        Nat.zero_add]

theorem BV_byteBit_N (v : List UInt8) (s c : Nat) : BV (byteBit v) s c = (bytesN v / 2 ^ s) % 2 ^ c := by
  rw [show byteBit v = dig (bytesN v) from funext (byteBit_eq_dig v), BV_dig]

/-- `BitUnpack` (Algorithm 19) reading the windows of one big natural number. -/
def BitUnpackF (v : List UInt8) (a b : Nat) : RPoly :=
  Rl ((List.range' 0 256).map fun i =>
    (b : Int) - ((bytesN v / 2 ^ (bitlen (a + b) * i)) % 2 ^ (bitlen (a + b)) : Nat))

theorem BitUnpack_fast (v : List UInt8) (a b : Nat) : BitUnpack v a b = BitUnpackF v a b := by
  apply Vector.ext
  intro i hi
  rw [BitUnpack_get v a b i hi, BV_byteBit_N]
  unfold BitUnpackF Rl
  rw [dif_pos (by simp)]
  simp [hi]


/-! ## Pointwise operations -/

theorem MultiplyNTT_eq_zipWith (a b : Poly) : MultiplyNTT a b = Vector.zipWith (· * ·) a b := by
  rw [MultiplyNTT_eq_fold, pwFold_full]

/-- `MatrixVectorNTT` (Algorithm 48) with `AddNTT` and `MultiplyNTT` replaced by `+` and `zipWith`. -/
def MatrixVectorNTTF {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) : Vector Poly k := Id.run do
  let mut w : Vector Poly k := Vector.replicate k Poly.zero
  for i in [0:k] do
    for j in [0:ℓ] do
      w := w.set! i (w[i]! + Vector.zipWith (· * ·) (M[i]!)[j]! v[j]!)
  return w

theorem MatrixVectorNTT_fast {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) :
    Spec.MatrixVectorNTT M v = MatrixVectorNTTF M v := by
  unfold Spec.MatrixVectorNTT MatrixVectorNTTF
  simp only [AddNTT_eq_add, MultiplyNTT_eq_zipWith]

theorem ScalarVectorNTT_fast {ℓ : Nat} (C : Poly) (V : Vector Poly ℓ) :
    Spec.ScalarVectorNTT C V = V.map (fun p => Vector.zipWith (· * ·) C p) := by
  have h1 : Spec.ScalarVectorNTT C V =
      (List.range' 0 ℓ).foldl (fun (c : Vector Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero) := by
    simp [Spec.ScalarVectorNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [h1, foldl_set_replicate_full ℓ Poly.zero (fun j => MultiplyNTT C V[j]!)]
  apply Vector.ext
  intro j hj
  simp [MultiplyNTT_eq_zipWith, vget! V j hj]

/-! ## `ExpandMask` -/

theorem maskPoly_fast (sp : Spec.Params) (ρ : List UInt8) (μ j : Nat) :
    maskPoly sp ρ μ j = BitUnpackF (H (ρ ++ IntegerToBytes (μ + j) 2) (32 * (1 + bitlen (sp.γ₁ - 1))))
      (sp.γ₁ - 1) sp.γ₁ := BitUnpack_fast _ _ _

theorem ExpandMask_44 (ρ : List UInt8) (μ : Nat) :
    Spec.ExpandMask Spec.ML_DSA_44 ρ μ = v4 (maskPoly Spec.ML_DSA_44 ρ μ 0) (maskPoly Spec.ML_DSA_44 ρ μ 1)
      (maskPoly Spec.ML_DSA_44 ρ μ 2) (maskPoly Spec.ML_DSA_44 ρ μ 3) := by
  apply Vector.ext
  intro i hi
  rw [ExpandMask_get _ _ _ i hi]
  have h4 : i < 4 := hi
  interval_cases i <;> rfl


/-! ## `ExpandA` from its entries -/

theorem foldlM_range_inv {α : Type} (f : α → Nat → Option α) (I : Nat → α → Prop) (x0 : α) (h0 : I 0 x0) :
    ∀ n, (∀ i x, i < n → I i x → ∃ x', f x i = some x' ∧ I (i + 1) x') →
      ∃ x, (List.range' 0 n).foldlM f x0 = some x ∧ I n x := by
  intro n
  induction n with
  | zero => intro _; exact ⟨x0, rfl, h0⟩
  | succ n ih =>
    intro hs
    obtain ⟨x, hx, hI⟩ := ih (fun i x hi => hs i x (by omega))
    obtain ⟨x', hx', hI'⟩ := hs n x (by omega) hI
    refine ⟨x', ?_, hI'⟩
    rw [List.range'_concat, List.foldlM_append, hx]
    simp [hx']

theorem vget_set! {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i j : Nat) (x : α) (hi : i < n) :
    (v.set! i x)[j]! = if j = i then x else v[j]! := by
  by_cases hj : j < n
  · rw [getElem!_pos _ j (by simpa using hj), set!_eq', Vector.getElem_setIfInBounds hj]
    by_cases e : j = i
    · subst e; simp
    · simp [e, Ne.symm e, getElem!_pos v j hj]
  · have e : j ≠ i := by omega
    rw [if_neg e, getElem!_neg _ j (by simpa using hj), getElem!_neg _ j (by simpa using hj)]

/-- `Â[r][s]` as a cell. -/
abbrev cell {k ℓ : Nat} (A : Vector (Vector Poly ℓ) k) (r s : Nat) : Poly := (A[r]!)[s]!


theorem expandA_of_entries (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k)
    (h : ∀ r, r < p.k → ∀ s, s < p.ℓ → Spec.RejNTTPoly fuel (SampleA.pSeed ρ r s) = some (cell A r s)) :
    Spec.ExpandA p fuel ρ = some A := by
  rw [SampleA.expandA_eq]
  let J : Nat → Nat → Vector (Vector Poly p.ℓ) p.k → Prop := fun n m X =>
    ∀ i, i < p.k → ∀ j, j < p.ℓ → cell X i j = if (i < n ∨ (i = n ∧ j < m)) then cell A i j else Poly.zero
  have step : ∀ n X, n < p.k → J n 0 X → ∃ X', SampleA.outerF p fuel ρ X n = some X' ∧ J (n + 1) 0 X' := by
    intro n X hn hX
    unfold SampleA.outerF
    obtain ⟨X', hX', hJ⟩ := foldlM_range_inv (SampleA.innerF p fuel ρ n) (fun m X => J n m X) X hX p.ℓ (by
      intro m X hm hJ
      refine ⟨X.set! n ((X[n]!).set! m (cell A n m)), ?_, ?_⟩
      · unfold SampleA.innerF; rw [h n hn m hm]
      · intro i hi j hj
        have e := hJ i hi j hj
        unfold cell at e ⊢
        rw [vget_set! _ _ _ _ hn]
        by_cases hin : i = n
        · subst hin
          rw [if_pos rfl, vget_set! _ _ _ _ hm]
          by_cases hjm : j = m
          · subst hjm; simp
          · rw [if_neg hjm]
            rw [e]
            have : (j < m) ↔ (j < m + 1) := by omega
            simp [hjm, this]
        · rw [if_neg hin, e]
          simp [hin])
    refine ⟨X', hX', ?_⟩
    intro i hi j hj
    have e := hJ i hi j hj
    rw [e]
    by_cases hin : i = n
    · subst hin; simp [hj]
    · have h1 : (i ≤ n) ↔ (i < n) := by omega
      simp [hin, h1]
  obtain ⟨X, hX, hJ⟩ := foldlM_range_inv (SampleA.outerF p fuel ρ) (fun n X => J n 0 X)
    (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) (by
      intro i hi j hj
      have h1 : (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero))[i]! =
          Vector.replicate p.ℓ Poly.zero := by
        rw [getElem!_pos _ i (by simpa using hi)]; simp
      unfold cell
      rw [h1, getElem!_pos _ j (by simpa using hj)]
      simp) p.k (fun n X hn hX => step n X hn hX)
  rw [hX]
  congr 1
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have e := hJ i hi j hj
  simp only [hi, true_or, if_true] at e
  unfold cell at e
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ j (by simpa using hj)] at e
  rw [getElem!_pos A i (by simpa using hi), getElem!_pos _ j (by simpa using hj)] at e
  exact e

end TopWitness
end Proofs
