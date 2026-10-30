import Proofs.Field
import Spec.Rounding

/-!
# The representation layer: how Rust values denote Spec values

Every refinement proof (rounding, Keccak, encodings, samplers, KeyGen/Sign/Verify) imports this file. It fixes,
once, what it means for an extracted Rust value to *represent* a specification value, and proves the generic
facts about those representations (injectivity, indexing, updating, slicing, ...).

## The representations

| Rust (extracted)                                  | Spec                           | Relation |
|---------------------------------------------------|--------------------------------|----------|
| `Array U32 256#usize` (canonical, `< q`)          | `Spec.Poly`                    | `Repr a p` |
| same, a centered integer polynomial               | `Spec.RPoly = Vector Int 256`  | `ReprInt a v` |
| `Array (Array U32 256#usize) K`                   | `Vector Spec.Poly k`           | `ReprVec a v` |
| `Array (Array (Array U32 256#usize) L) K`         | `Vector (Vector Spec.Poly ℓ) k`| `ReprMat a m` |
| `Array Bool 256#usize`, `Array (Array Bool 256#usize) K` | `HintPoly`, `Vector HintPoly k` | `ReprHint`, `ReprHintVec` |
| `Slice U8`, `Array U8 n`                          | `List UInt8`                   | `bytes`, `bytesA` |
| `Impl.params.Params` with `K`, `L`                | `Spec.Params`                  | `Params.Valid` |

`Canonical a` says every coefficient is `< q`; `toZq a` is the polynomial of `Z_q` it denotes (computable,
`Vector.ofFn` over the array's list). `Repr a p` is the bundle `Canonical a ∧ toZq a = p`; because `toZq` is
injective on canonical arrays (`toZq_inj`) the relation is functional in both directions (`Repr.unique`), so a
theorem may conclude `Repr r (Spec.Foo ..)` and the array `r` is determined.

Spec decoders and samplers return integer polynomials (`RPoly`). The Rust side stores the canonical residue
mod `q`; `ReprInt a v` means `Canonical a ∧ toZq a = RPoly.toZq v`. Because `RPoly.toZq` is not injective on `Int`,
the statements that need the integers back (norms, `pack_signed`) carry a bound: `|v[i]| ≤ (q-1)/2` for
`infinity_norm`, `-a ≤ v ≤ b` with `b < q` for `field.sub b _`.

Bytes: `bytes s = s.val.map (fun x => UInt8.ofNat x.val)`, `bytesA` likewise for fixed-size arrays. A `List`
map is what `simp` handles best (`List.getElem_map`, `List.map_append`, `List.map_take`, ...); `bytes_inj` recovers
the Rust value from its bytes.

## House style (read before writing a refinement proof)

1. One refinement lemma per extracted function, as a weakest-precondition statement tagged `@[step]`:

   ```
   @[step]
   theorem foo_spec (hp : Params.Valid ip K L sp) (a : Array U32 256#usize) (ha : Repr a p) :
       Impl.m.foo ip a ⦃ r => Repr r (Spec.Foo sp p) ⦄
   ```

   `⦃ r => … ⦄` (Aeneas `WP.spec`) excludes failure and divergence. Where it is useful, derive a headline form
   `∃ r, Impl.m.foo ip a = ok r ∧ Repr r (Spec.Foo sp p)` with `WP.spec_imp_exists` (see `Proofs.ntt_correct`).
2. Hypotheses use `Repr`, `ReprInt`, `ReprVec`, `ReprMat`, `Params.Valid` (and the named premises of STATUS.md).
   No statement is made for an arbitrary `Impl.params.Params`: it always comes with `Params.Valid ip K L sp`
   for a spec parameter set `sp`. The three standard sets are witnesses that the premise is satisfiable
   (`ML_DSA_44_valid`, `ML_DSA_65_valid`, `ML_DSA_87_valid`).
3. Loops: use `loop.spec_decr_nat` with a measure and an invariant that says the state equals a `foldl` of the
   spec's loop body over `List.range'` (the model), then close the inductive step with `step*` and the
   `toZq_set`/`toZq_getElem` helpers below. Worked examples: `Proofs.inner_loop` and `Proofs.outer_loop` in
   `Proofs/NTT.lean` (a body model `bfly`, invariant `toZq p.1 = (List.range' start (p.2 - start)).foldl bfly …`,
   step `List.range'_concat`), and `vec_norm_row_spec` in this file for a scalar
   accumulator.
4. Constant-time mask idioms are discharged with `ct_lt_mask_spec` / `ct_select_spec` below instead of bit
   twiddling in every proof.
5. Statements are in the standard-axioms fragment only; `lean/headline-theorems.txt` lists the headline names
   that `scripts/check-axioms.sh` checks.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Canonical arrays as polynomials over Z_q -/

/-- All coefficients are canonical representatives. -/
def Canonical (w : Array U32 256#usize) : Prop := ∀ x ∈ w.val, x.val < Spec.q

theorem len256 (w : Array U32 256#usize) : w.val.length = 256 := by
  exact w.property

/-- The polynomial of Z_q represented by a coefficient array (computable). -/
def toZq (w : Array U32 256#usize) : Poly :=
  Vector.ofFn fun i : Fin 256 => (((w.val[i.val]'(by rw [len256 w]; exact i.isLt)).val : Nat) : Zq)

theorem canon_get {w : Array U32 256#usize} (hc : Canonical w) {k : Nat} (h : k < w.val.length) :
    (w.val[k]).val < 8380417 :=
  hc _ (List.getElem_mem h)

theorem canonical_set (w : Array U32 256#usize) (i : Usize) (x : U32) (hw : Canonical w)
    (hx : x.val < Spec.q) : Canonical (w.set i x) := by
  intro y hy
  rw [Array.set_val_eq] at hy
  rcases List.mem_or_eq_of_mem_set hy with h | h
  · exact hw y h
  · subst h; exact hx

theorem set!_eq' {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := rfl

theorem set!_eq (xs : Vector Zq 256) (i : Nat) (x : Zq) : xs.set! i x = xs.setIfInBounds i x := rfl

theorem toZq_get (w : Array U32 256#usize) (k : Nat) (hk : k < 256) :
    (toZq w)[k] = (((w.val[k]'(by rw [len256 w]; exact hk)).val : Nat) : Zq) := by
  simp [toZq]

theorem toZq_getElem! (w : Array U32 256#usize) (k : Nat) (hk : k < 256) :
    (toZq w)[k]! = (((w[k]!).val : Nat) : Zq) := by
  have hk' : k < w.val.length := by rw [len256 w]; exact hk
  rw [getElem!_pos _ _ (by simpa using hk), toZq_get w k hk]
  simp [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem toZq_getElem (w : Array U32 256#usize) (k : Nat) (hk : k < w.val.length) :
    (toZq w)[k]! = (((w.val[k]).val : Nat) : Zq) := by
  have hk' : k < 256 := by have := len256 w; omega
  rw [getElem!_pos _ _ (by simpa using hk'), toZq_get w k hk']

theorem toZq_set (w : Array U32 256#usize) (i : Usize) (x : U32) (_hi : i.val < 256) :
    toZq (w.set i x) = (toZq w).set! i.val (x.val : Zq) := by
  apply Vector.ext
  intro k hk
  rw [set!_eq, Vector.getElem_setIfInBounds hk]
  simp only [toZq, Vector.getElem_ofFn, Array.set_val_eq]
  by_cases h : i.val = k
  · subst h
    simp
  · simp [h]

theorem vec_getElem!_set!_ne (xs : Vector Zq 256) {i j : Nat} (x : Zq) (hj : j < 256) (h : i ≠ j) :
    (xs.set! i x)[j]! = xs[j]! := by
  rw [set!_eq, getElem!_pos _ _ (by simpa using hj), getElem!_pos _ _ (by simpa using hj)]
  exact Vector.getElem_setIfInBounds_ne hj h

/-- The all-zero array is canonical and represents the zero polynomial. -/
theorem canonical_repeat_zero : Canonical (Array.repeat 256#usize 0#u32) := by
  intro x hx
  simp [Array.repeat_val] at hx
  subst hx
  decide

theorem toZq_repeat_zero : toZq (Array.repeat 256#usize 0#u32) = Poly.zero := by
  apply Vector.ext
  intro k hk
  simp only [toZq, Poly.zero, Vector.getElem_ofFn, Vector.getElem_replicate, Array.repeat_val,
    List.getElem_replicate]
  rfl

/-! ## Injectivity and the `Repr` bundle -/

/-- On canonical arrays `toZq` is injective: the representation determines the array. -/
theorem toZq_inj {a b : Array U32 256#usize} (ha : Canonical a) (hb : Canonical b)
    (h : toZq a = toZq b) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [len256 a, len256 b])
  intro k h1 h2
  have hk : k < 256 := by rw [len256 a] at h1; exact h1
  have e : (((a.val[k]).val : Nat) : Zq) = (((b.val[k]).val : Nat) : Zq) := by
    have := congrArg (fun p : Poly => p[k]) h
    simpa [toZq] using this
  have e2 := congrArg ZMod.val e
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (canon_get ha h1),
    Nat.mod_eq_of_lt (canon_get hb h2)] at e2
  exact UScalar.eq_of_val_eq e2

/-- `a` is the canonical array denoting the polynomial `p`. -/
structure Repr (a : Array U32 256#usize) (p : Poly) : Prop where
  canon : Canonical a
  eq : toZq a = p

theorem Repr.unique {a b : Array U32 256#usize} {p : Poly} (ha : Repr a p) (hb : Repr b p) : a = b :=
  toZq_inj ha.canon hb.canon (ha.eq.trans hb.eq.symm)

theorem Repr.of_toZq {a : Array U32 256#usize} (h : Canonical a) : Repr a (toZq a) := ⟨h, rfl⟩

/-- The coefficient at `k` is the residue of `p[k]`. -/
theorem Repr.coeff {a : Array U32 256#usize} {p : Poly} (h : Repr a p) (k : Nat) (hk : k < 256) :
    ((((a.val[k]'(by rw [len256 a]; exact hk)).val : Nat)) : Zq) = p[k] := by
  rw [← h.eq, toZq_get a k hk]

theorem repr_repeat_zero : Repr (Array.repeat 256#usize 0#u32) Poly.zero :=
  ⟨canonical_repeat_zero, toZq_repeat_zero⟩

theorem Repr.set {a : Array U32 256#usize} {p : Poly} (h : Repr a p) (i : Usize) (x : U32)
    (hi : i.val < 256) (hx : x.val < Spec.q) :
    Repr (a.set i x) (p.set! i.val (x.val : Zq)) :=
  ⟨canonical_set a i x h.canon hx, by rw [toZq_set a i x hi, h.eq]⟩

/-! ### Vectors of polynomials -/

/-- `a` represents the vector `v` of polynomials: same length, and entry `i` represents `v[i]`. -/
structure ReprVec {K : Usize} {k : Nat} (a : Array (Array U32 256#usize) K) (v : Vector Poly k) : Prop where
  len : K.val = k
  elt : ∀ (i : Nat) (hi : i < k), Repr (a.val[i]'(by have := a.property; omega)) v[i]

theorem ReprVec.unique {K : Usize} {k : Nat} {a b : Array (Array U32 256#usize) K} {v : Vector Poly k}
    (ha : ReprVec a v) (hb : ReprVec b v) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < k := by have := a.property; have := ha.len; omega
  exact Repr.unique (ha.elt i hi) (hb.elt i hi)

/-- Entry `i` of a represented vector, as an extracted `Array.index_usize`. -/
theorem ReprVec.index_spec {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {v : Vector Poly k}
    (h : ReprVec a v) (i : Usize) (hi : i.val < k) :
    Array.index_usize a i ⦃ x => Repr x v[i.val] ⦄ := by
  have hlt : i.val < a.val.length := by have := a.property; have := h.len; omega
  have e : a[i]? = some (a.val[i.val]'hlt) := by simp
  unfold Array.index_usize
  rw [e]
  simp only [WP.spec_ok]
  exact h.elt i.val hi

/-- Replacing entry `i` by a representation of `p` represents the vector with entry `i` replaced. -/
theorem ReprVec.set {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {v : Vector Poly k}
    (h : ReprVec a v) (i : Usize) (x : Array U32 256#usize) (p : Poly) (hx : Repr x p) (_hi : i.val < k) :
    ReprVec (a.set i x) (v.set! i.val p) := by
  refine ⟨h.len, fun j hj => ?_⟩
  have hlt : j < a.val.length := by have := a.property; have := h.len; omega
  rw [set!_eq', Vector.getElem_setIfInBounds hj]
  simp only [Array.set_val_eq]
  by_cases hij : i.val = j
  · subst hij; simpa using hx
  · simpa [hij, List.getElem_set] using h.elt j hj

/-! ### Matrices -/

/-- `a` represents the `k × ℓ` matrix `m` (row `r`, column `s` is `m[r][s]`). -/
structure ReprMat {K L : Usize} {k ℓ : Nat} (a : Array (Array (Array U32 256#usize) L) K)
    (m : Vector (Vector Poly ℓ) k) : Prop where
  len : K.val = k
  elt : ∀ (i : Nat) (hi : i < k), ReprVec (a.val[i]'(by have := a.property; omega)) m[i]

theorem ReprMat.unique {K L : Usize} {k ℓ : Nat} {a b : Array (Array (Array U32 256#usize) L) K}
    {m : Vector (Vector Poly ℓ) k} (ha : ReprMat a m) (hb : ReprMat b m) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < k := by have := a.property; have := ha.len; omega
  exact ReprVec.unique (ha.elt i hi) (hb.elt i hi)

/-! ### Hint polynomials -/

/-- The hint polynomial denoted by a Boolean array. -/
def toHint (a : Array Bool 256#usize) : HintPoly :=
  Vector.ofFn fun i : Fin 256 => a.val[i.val]'(by rw [a.property]; exact i.isLt)

/-- `a` represents the hint polynomial `h`. -/
def ReprHint (a : Array Bool 256#usize) (h : HintPoly) : Prop := toHint a = h

theorem toHint_inj {a b : Array Bool 256#usize} (h : toHint a = toHint b) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro k h1 h2
  have hk : k < 256 := by have : a.val.length = 256 := a.property; omega
  have := congrArg (fun p : HintPoly => p[k]) h
  simpa [toHint] using this

theorem ReprHint.unique {a b : Array Bool 256#usize} {h : HintPoly} (ha : ReprHint a h)
    (hb : ReprHint b h) : a = b :=
  toHint_inj (ha.trans hb.symm)

/-- `a` represents the vector `h` of hint polynomials. -/
structure ReprHintVec {K : Usize} {k : Nat} (a : Array (Array Bool 256#usize) K) (h : Vector HintPoly k) :
    Prop where
  len : K.val = k
  elt : ∀ (i : Nat) (hi : i < k), ReprHint (a.val[i]'(by have := a.property; omega)) h[i]

theorem ReprHintVec.unique {K : Usize} {k : Nat} {a b : Array (Array Bool 256#usize) K}
    {h : Vector HintPoly k} (ha : ReprHintVec a h) (hb : ReprHintVec b h) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < k := by have := a.property; have := ha.len; omega
  exact ReprHint.unique (ha.elt i hi) (hb.elt i hi)

/-! ## Constant-time mask idioms -/

theorem wrapping_sub_val_u64 (a b : U64) :
    (core.num.U64.wrapping_sub a b).val = (2 ^ 64 - b.val + a.val) % 2 ^ 64 := by
  show (a.bv - b.bv).toNat = _
  rw [BitVec.toNat_sub, UScalar.bv_toNat, UScalar.bv_toNat]

/-- The optimization barriers are the identity in the extracted (proved) code. -/
theorem barrier_u64_spec (x : U64) : field.barrier_u64 x ⦃ y => y = x ⦄ := by
  simp [field.barrier_u64]

theorem barrier_u32_spec (x : U32) : field.barrier_u32 x ⦃ y => y = x ⦄ := by
  simp [field.barrier_u32]

attribute [step] barrier_u64_spec barrier_u32_spec

/-- `ct_lt_mask a b` is all-ones if `a < b` and zero otherwise (for `a, b < 2^63`). -/
theorem ct_lt_mask_spec (a b : U64) (ha : a.val < 2 ^ 63) (hb : b.val < 2 ^ 63) :
    field.ct_lt_mask a b ⦃ m => (a.val < b.val → m.val = 2 ^ 64 - 1) ∧ (b.val ≤ a.val → m.val = 0) ⦄ := by
  unfold field.ct_lt_mask
  simp only [field.barrier_u64, lift, bind_tc_ok]
  step*
  rw [Nat.shiftRight_eq_div_pow, wrapping_sub_val_u64] at i1_post1
  rw [wrapping_sub_val_u64]
  constructor
  · intro h
    have : i1.val = 1 := by omega
    rw [this]; norm_num
  · intro h
    have : i1.val = 0 := by omega
    rw [this]; norm_num

/-- `ct_select if_false if_true mask` picks `if_true` under the all-ones mask and `if_false` under zero. -/
theorem ct_select_spec (a b m : U32) (hm : m = 0#u32 ∨ m = 4294967295#u32) :
    field.ct_select a b m ⦃ r => (m = 0#u32 → r = a) ∧ (m = 4294967295#u32 → r = b) ⦄ := by
  unfold field.ct_select
  simp only [field.barrier_u32, lift, bind_tc_ok]
  rcases hm with h | h
  · have e : (a ^^^ ((a ^^^ b) &&& m)) = a := by
      rw [h]; apply UScalar.eq_of_val_eq; simp
    simp only [WP.spec_ok]; rw [e]
    exact ⟨fun _ => rfl, fun h' => by rw [h] at h'; exact absurd h' (by decide)⟩
  · have e : (a ^^^ ((a ^^^ b) &&& m)) = b := by
      rw [h]; apply UScalar.eq_of_val_eq; simp
    simp only [WP.spec_ok]; rw [e]
    exact ⟨fun h' => by rw [h] at h'; exact absurd h' (by decide), fun _ => rfl⟩

attribute [step] ct_lt_mask_spec ct_select_spec

/-! ## Integer polynomials: `ReprInt` -/

/-- `a` stores the integer polynomial `v` as canonical residues mod `q`. -/
def ReprInt (a : Array U32 256#usize) (v : RPoly) : Prop :=
  Canonical a ∧ toZq a = RPoly.toZq v

theorem ReprInt.canon {a : Array U32 256#usize} {v : RPoly} (h : ReprInt a v) : Canonical a := h.1

theorem ReprInt.repr {a : Array U32 256#usize} {v : RPoly} (h : ReprInt a v) : Repr a (RPoly.toZq v) :=
  ⟨h.1, h.2⟩

theorem ReprInt.of_repr {a : Array U32 256#usize} {v : RPoly} (h : Repr a (RPoly.toZq v)) : ReprInt a v :=
  ⟨h.canon, h.eq⟩

/-- Two arrays storing the same integer polynomial are equal. -/
theorem ReprInt.unique {a b : Array U32 256#usize} {v : RPoly} (ha : ReprInt a v) (hb : ReprInt b v) :
    a = b :=
  Repr.unique ha.repr hb.repr

/-- Two integer polynomials stored in the same array agree modulo `q` (they need not be equal). -/
theorem ReprInt.toZq_eq {a : Array U32 256#usize} {v w : RPoly} (hv : ReprInt a v) (hw : ReprInt a w) :
    RPoly.toZq v = RPoly.toZq w := hv.2.symm.trans hw.2

/-- Coefficientwise: the stored residue is `v[k] mod q`. -/
theorem ReprInt.coeff {a : Array U32 256#usize} {v : RPoly} (h : ReprInt a v) (k : Nat) (hk : k < 256) :
    (((a.val[k]'(by rw [len256 a]; exact hk)).val : Nat) : Int) = v[k] % (Spec.q : Int) := by
  have e := congrArg (fun p : Poly => p[k]) h.2
  simp only [toZq_get a k hk, RPoly.toZq, Vector.getElem_map] at e
  have e2 : ((((a.val[k]'(by rw [len256 a]; exact hk)).val : Nat) : Int) : Zq) = ((v[k] : Int) : Zq) := by
    rw [Int.cast_natCast]; exact e
  rw [ZMod.intCast_eq_intCast_iff'] at e2
  have hlt := canon_get h.1 (show k < a.val.length by rw [len256 a]; exact hk)
  rw [← e2]
  exact (Int.emod_eq_of_lt (by omega) (by simp only [Spec.q]; omega)).symm

theorem ReprInt.set {a : Array U32 256#usize} {v : RPoly} (h : ReprInt a v) (i : Usize) (x : U32) (c : Int)
    (hi : i.val < 256) (hx : x.val < Spec.q) (hxc : ((x.val : Nat) : Zq) = (c : Zq)) :
    ReprInt (a.set i x) (v.set! i.val c) := by
  refine ⟨canonical_set a i x h.1 hx, ?_⟩
  rw [toZq_set a i x hi, h.2]
  apply Vector.ext
  intro k hk
  rw [set!_eq, set!_eq', Vector.getElem_setIfInBounds hk]
  simp only [RPoly.toZq, Vector.getElem_map, Vector.getElem_setIfInBounds hk]
  split <;> simp_all

/-! ### `Zq.modPM` on canonical residues -/

/-- `r mod± q` of a canonical residue `r`: `r` if `r ≤ (q-1)/2`, else `r - q`. -/
theorem Zq_modPM_natCast (r : Nat) (hr : r < Spec.q) :
    Zq.modPM ((r : Nat) : Zq) = if r ≤ 4190208 then (r : Int) else (r : Int) - Spec.q := by
  haveI : NeZero Spec.q := ⟨by decide⟩
  have hr' : r < 8380417 := hr
  have hmod : (r : Int) % (Spec.q : Int) = r := Int.emod_eq_of_lt (by omega) (by simp only [Spec.q]; omega)
  simp only [Zq.modPM, ZMod.val_natCast, Nat.mod_eq_of_lt hr, Spec.modPM, hmod]
  simp only [Spec.q]
  split <;> split <;> omega

/-- The centered representative of `c : Zq` is the unique integer of absolute value `≤ (q-1)/2` congruent to it. -/
theorem Zq_modPM_eq_of_small (c : Zq) (v : Int) (hv : v.natAbs ≤ (Spec.q - 1) / 2) (h : (v : Zq) = c) :
    Zq.modPM c = v := by
  haveI : NeZero Spec.q := ⟨by decide⟩
  subst h
  have h1 : (((v : Zq)).val : Int) = v % (Spec.q : Int) := ZMod.val_intCast v
  simp only [Zq.modPM, h1, Spec.modPM]
  simp only [Spec.q] at hv ⊢
  split <;> omega

/-- Satisfiability witness for `ReprInt`: the zero array stores the zero integer polynomial. -/
theorem reprInt_zero : ReprInt (Array.repeat 256#usize 0#u32) (Vector.replicate 256 (0 : Int)) := by
  refine ⟨canonical_repeat_zero, ?_⟩
  rw [toZq_repeat_zero]
  apply Vector.ext
  intro k hk
  simp [Poly.zero, RPoly.toZq]

/-! ### The infinity norm of one coefficient -/

theorem lower_of_mask (i3 i4 : U64) (lower : U32) (h4 : i4 = ~~~i3)
    (hl : lower = UScalar.cast UScalarTy.U32 i4) :
    (i3.val = 0 → lower = 4294967295#u32) ∧ (i3.val = 2 ^ 64 - 1 → lower = 0#u32) := by
  constructor
  · intro h
    have : i3 = 0#u64 := UScalar.eq_of_val_eq h
    subst this; subst h4; subst hl; decide
  · intro h
    have : i3 = 18446744073709551615#u64 := UScalar.eq_of_val_eq (by simpa using h)
    subst this; subst h4; subst hl; decide

/-- `infinity_norm r = |r mod± q|` for a canonical `r`. -/
theorem infinity_norm_spec (r : U32) (hr : r.val < 8380417) :
    rounding.infinity_norm r ⦃ y => y.val = if r.val ≤ 4190208 then r.val else 8380417 - r.val ⦄ := by
  unfold rounding.infinity_norm
  simp only [global_simps]
  step*
  all_goals
    have hi1 : i1.val = 4190208 := by simp [i1_post, i_post1]
    have hi2 : i2.val = r.val := by simp [i2_post]
    have hmask := lower_of_mask i3 i4 lower i4_post lower_post
  · by_cases h : r.val ≤ 4190208
    · exact Or.inr (hmask.1 (i3_post2 (by omega)))
    · exact Or.inl (hmask.2 (i3_post1 (by omega)))
  · by_cases h : r.val ≤ 4190208
    · have := y_post2 (hmask.1 (i3_post2 (by omega)))
      subst this; simp [h]
    · have := y_post1 (hmask.2 (i3_post1 (by omega)))
      subst this; simp [h, i5_post1]

theorem infNorm_int (x : Int) : ‖x‖∞ = x.natAbs := rfl

/-- `infinity_norm` of a canonical residue that stores the integer `v` with `|v| ≤ (q-1)/2` is `|v|`
(`= ‖v‖∞` on `Int`). -/
theorem infinity_norm_repr (r : U32) (v : Int) (hr : r.val < 8380417)
    (hv : (r.val : Int) = v % (Spec.q : Int)) (hb : v.natAbs ≤ (Spec.q - 1) / 2) :
    rounding.infinity_norm r ⦃ y => y.val = ‖v‖∞ ⦄ := by
  apply WP.spec_mono (infinity_norm_spec r hr)
  intro y hy
  rw [infNorm_int, hy]
  simp only [Spec.q] at hv hb
  split <;> omega

/-! ### Norms of vectors: list models of `‖·‖∞` -/

theorem foldl_max_start {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun m x => max m (f x)) a = max a (l.foldl (fun m x => max m (f x)) 0) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; rw [ih, ih (max 0 (f x))]; omega

theorem foldl_max_le_iff {α : Type} (f : α → Nat) (l : List α) (a B : Nat) :
    l.foldl (fun m x => max m (f x)) a ≤ B ↔ a ≤ B ∧ ∀ x ∈ l, f x ≤ B := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, max_le_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- `‖w‖∞` of a vector is the `foldl` of `max` over the list of entries' norms. -/
theorem infNorm_vec_eq {α : Type} [InfNorm α] {n : Nat} (w : Vector α n) :
    ‖w‖∞ = w.toList.foldl (fun m x => max m ‖x‖∞) 0 := by
  show w.foldl (fun m x => max m (InfNorm.infNorm x)) 0 = _
  rw [Vector.foldl, ← Array.foldl_toList]
  rfl

/-- `‖w‖∞ ≤ B` iff every entry's norm is. -/
theorem infNorm_le_iff {α : Type} [InfNorm α] {n : Nat} (w : Vector α n) (B : Nat) :
    ‖w‖∞ ≤ B ↔ ∀ (i : Nat) (hi : i < n), ‖w[i]‖∞ ≤ B := by
  rw [infNorm_vec_eq, foldl_max_le_iff]
  constructor
  · rintro ⟨-, h⟩ i hi
    have e : w[i] = w.toList[i]'(by simpa using hi) := by simp
    rw [e]
    exact h _ (List.getElem_mem _)
  · intro h
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have e : w.toList[i] = w[i]'(by simpa using hi) := by simp
    rw [e]
    exact h i (by simpa using hi)

/-- `a` stores the vector `v` of integer polynomials. -/
structure ReprIntVec {K : Usize} {k : Nat} (a : Array (Array U32 256#usize) K) (v : Vector RPoly k) : Prop where
  len : K.val = k
  elt : ∀ (i : Nat) (hi : i < k), ReprInt (a.val[i]'(by have := a.property; omega)) v[i]

theorem ReprIntVec.unique {K : Usize} {k : Nat} {a b : Array (Array U32 256#usize) K} {v : Vector RPoly k}
    (ha : ReprIntVec a v) (hb : ReprIntVec b v) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < k := by have := a.property; have := ha.len; omega
  exact ReprInt.unique (ha.elt i hi) (hb.elt i hi)

theorem ReprIntVec.repr {K : Usize} {k : Nat} {a : Array (Array U32 256#usize) K} {v : Vector RPoly k}
    (h : ReprIntVec a v) : ReprVec a (v.map RPoly.toZq) :=
  ⟨h.len, fun i hi => by simpa using (h.elt i hi).repr⟩

attribute [step] infinity_norm_spec

theorem cast_mask (i4 : U64) (i5 : U32) (h : i5 = UScalar.cast UScalarTy.U32 i4) :
    (i4.val = 0 → i5 = 0#u32) ∧ (i4.val = 2 ^ 64 - 1 → i5 = 4294967295#u32) := by
  constructor
  · intro hv
    have : i4 = 0#u64 := UScalar.eq_of_val_eq hv
    subst this; subst h; decide
  · intro hv
    have : i4 = 18446744073709551615#u64 := UScalar.eq_of_val_eq (by simpa using hv)
    subst this; subst h; decide

theorem foldl_take_succ {α β : Type} (f : β → α → β) (l : List α) (b : β) (j : Nat) (h : j < l.length) :
    (l.take (j + 1)).foldl f b = f ((l.take j).foldl f b) l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The inner loop of `vec_infinity_norm` over one stored row `p` (all `|p[k]| ≤ (q-1)/2`):
the running maximum becomes `max acc ‖p‖∞`. -/
theorem vec_norm_row_spec {N : Usize} (w : Array (Array U32 256#usize) N) (i : Usize) (hi : i.val < N.val)
    (p : RPoly) (hrow : ReprInt (w.val[i.val]'(by have := w.property; omega)) p)
    (hb : ∀ (k : Nat) (hk : k < 256), p[k].natAbs ≤ 4190208) (acc : U32) (hacc : acc.val ≤ 4190208) :
    rounding.vec_infinity_norm_loop0_loop0 w acc i 0#usize ⦃ r => r.val = max acc.val ‖p‖∞ ⦄ := by
  have hrowlen : i.val < w.val.length := by have := w.property; omega
  unfold rounding.vec_infinity_norm_loop0_loop0
  apply loop.spec_decr_nat
    (fun (pr : U32 × Usize) => 256 - pr.2.val)
    (fun pr => pr.2.val ≤ 256 ∧ pr.1.val ≤ 4190208 ∧
       pr.1.val = (p.toList.take pr.2.val).foldl (fun m x => max m x.natAbs) acc.val)
  · rintro ⟨ac, j⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [rounding.vec_infinity_norm_loop0_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := hj
      step*
      · subst a_post2 i1_post2; exact canon_get hrow.1 _
      · subst a_post2 i1_post2
        have hc := hrow.coeff j.val hj'
        unfold Spec.q at hc
        have hbj := hb j.val hj'
        have hmask := cast_mask i4 i5 i5_post
        have hi2 : i2.val = ac.val := by rw [i2_post]; simp
        have hi3 : i3.val = x.val := by rw [i3_post]; simp
        have hx : x.val = p[j.val].natAbs := by
          rw [x_post]; split <;> omega
        have key : acc1.val = max ac.val x.val := by
          by_cases hlt : i2.val < i3.val
          · rw [acc1_post2 (hmask.2 (i4_post1 hlt))]; omega
          · rw [acc1_post1 (hmask.1 (i4_post2 (by omega)))]; omega
        have hlen : j.val < p.toList.length := by simpa using hj'
        refine ⟨by omega, by omega, ?_, by omega⟩
        rw [j1_post, foldl_take_succ _ _ _ _ hlen, ← h3, key, hx]
        simp
    · rename_i hj
      have hj' : j.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      have hl : p.toList.length = 256 := by simp
      rw [h3, hj', List.take_of_length_le (by omega), foldl_max_start, infNorm_vec_eq]
      simp [infNorm_int]
  · exact ⟨by simp, hacc, by simp⟩

/-- `vec_infinity_norm` of a stored vector of integer polynomials is the spec's `‖v‖∞`, provided that norm is
at most `(q-1)/2` (below which `|v mod± q|` and `|v|` agree). -/
theorem vec_infinity_norm_spec {N : Usize} (w : Array (Array U32 256#usize) N) {n : Nat}
    (v : Vector RPoly n) (hw : ReprIntVec w v) (hb : ‖v‖∞ ≤ 4190208) :
    rounding.vec_infinity_norm w ⦃ r => r.val = ‖v‖∞ ⦄ := by
  have hbi := (infNorm_le_iff v 4190208).1 hb
  unfold rounding.vec_infinity_norm rounding.vec_infinity_norm_loop0
  apply loop.spec_decr_nat
    (fun (pr : U32 × Usize) => N.val - pr.2.val)
    (fun pr => pr.2.val ≤ N.val ∧ pr.1.val ≤ 4190208 ∧
       pr.1.val = (v.toList.take pr.2.val).foldl (fun m x => max m ‖x‖∞) 0)
  · rintro ⟨ac, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [rounding.vec_infinity_norm_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hik : i.val < n := by have := hw.len; omega
      have hbk : ∀ (k : Nat) (hk : k < 256), v[i.val][k].natAbs ≤ 4190208 :=
        fun k hk => (infNorm_le_iff v[i.val] 4190208).1 (hbi i.val hik) k hk
      have hrow := vec_norm_row_spec w i hi' v[i.val] (hw.elt i.val hik) hbk ac h2
      step with hrow
      step*
      have hlen : i.val < v.toList.length := by simpa using hik
      have hnb := hbi i.val hik
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [i1_post, foldl_take_succ _ _ _ _ hlen, ← h3, acc1_post]
      simp
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      have hl : v.toList.length = n := by simp
      have := hw.len
      rw [h3, hi', List.take_of_length_le (by omega), ← infNorm_vec_eq]
  · exact ⟨by simp, by simp, by simp⟩

/-! ## `field.sub` as used by `pack_signed` / `unpack_signed` -/

/-- `field.sub b z` computes `(b - z) mod q`, as a canonical residue. -/
theorem sub_int_spec (b z : U32) (hb : b.val < 8380417) (hz : z.val < 8380417) :
    field.sub b z ⦃ y => y.val < 8380417 ∧ (y.val : Int) % 8380417 = ((b.val : Int) - z.val) % 8380417 ⦄ := by
  apply WP.spec_mono (sub_spec b z hb hz)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  omega

/-- If `w` stores the integer `v` (as the residue `v mod q`) and `-a ≤ v ≤ b` with `a + b < q`, then
`field.sub b w` is the canonical residue `b - v ∈ [0, q)`: the shape `pack_signed` computes. -/
theorem sub_signed_spec (b w : U32) (v : Int) (a : Nat) (hb : b.val < 8380417) (hw : w.val < 8380417)
    (hwv : (w.val : Int) = v % 8380417) (hv1 : -(a : Int) ≤ v) (hv2 : v ≤ b.val)
    (hab : a + b.val < 8380417) :
    field.sub b w ⦃ y => y.val = ((b.val : Int) - v).toNat ⦄ := by
  apply WP.spec_mono (sub_spec b w hb hw)
  rintro y ⟨h1, h2⟩
  omega

/-- The same, from `ReprInt` and a coefficient index. -/
theorem ReprInt.sub_signed {a : Array U32 256#usize} {v : RPoly} (h : ReprInt a v) (k : Nat) (hk : k < 256)
    (b : U32) (n : Nat) (hb : b.val < 8380417) (hv1 : -(n : Int) ≤ v[k]) (hv2 : v[k] ≤ b.val)
    (hab : n + b.val < 8380417) :
    field.sub b (a.val[k]'(by rw [len256 a]; exact hk)) ⦃ y => y.val = ((b.val : Int) - v[k]).toNat ⦄ :=
  sub_signed_spec b _ v[k] n hb (canon_get h.1 _) (by simpa using h.coeff k hk) hv1 hv2 hab

/-! ## Parameters -/

/-- The extracted parameter record `ip` (with const generics `K`, `L`) is the spec parameter set `sp`.

Bundles: the const generics (`K = k`, `L = ℓ`), every scalar field of `ip`, the derived bit widths, and the facts
about the two Barrett constants that the rounding proofs use (`reduce_mod`: `⌊x · mult / 2^shift⌋` with
`mult = ⌊2^shift / 2γ₂⌋`, `shift = 2 (⌊log₂ 2γ₂⌋ + 1)`; `decompose`: division by `2γ₂` as multiplication by
`⌈2^48 / 2γ₂⌉` then `>> 48`). `d = 13` is hard-coded in the Rust code (Power2Round, `t0` packing). -/
structure Params.Valid (ip : Impl.params.Params) (K L : Usize) (sp : Spec.Params) : Prop where
  K_eq : K.val = sp.k
  L_eq : L.val = sp.ℓ
  k_eq : ip.k.val = sp.k
  l_eq : ip.l.val = sp.ℓ
  d_eq : sp.d = 13
  eta : ip.eta.val = sp.η
  eta_bits : ip.eta_bits.val = Spec.bitlen (2 * sp.η)
  tau : ip.tau.val = sp.τ
  beta : ip.beta.val = sp.β
  gamma1 : ip.gamma1.val = sp.γ₁
  gamma1_bits : ip.gamma1_bits.val = 1 + Spec.bitlen (sp.γ₁ - 1)
  gamma2 : ip.gamma2.val = sp.γ₂
  w1_bits : ip.w1_bits.val = Spec.bitlen (sp.m - 1)
  omega : ip.omega.val = sp.ω
  c_tilde_len : ip.c_tilde_len.val = sp.lam / 4
  shift : ip.two_gamma2_shift.val = 2 * (Nat.log2 (2 * sp.γ₂) + 1)
  mult : ip.two_gamma2_mult.val = 2 ^ ip.two_gamma2_shift.val / (2 * sp.γ₂)
  div_mult : ip.two_gamma2_div_mult.val = (2 ^ 48 + 2 * sp.γ₂ - 1) / (2 * sp.γ₂)

@[step]
theorem ML_DSA_44_spec :
    params.ML_DSA_44 ⦃ ip => Params.Valid ip 4#usize 4#usize Spec.ML_DSA_44 ⦄ := by
  have e : (1#u32 <<< 17#i32) = ok 131072#u32 := by rfl
  unfold params.ML_DSA_44
  simp only [e, bind_tc_ok, WP.spec_ok]
  constructor <;> decide +kernel

@[step]
theorem ML_DSA_65_spec :
    params.ML_DSA_65 ⦃ ip => Params.Valid ip 6#usize 5#usize Spec.ML_DSA_65 ⦄ := by
  have e : (1#u32 <<< 19#i32) = ok 524288#u32 := by rfl
  unfold params.ML_DSA_65
  simp only [e, bind_tc_ok, WP.spec_ok]
  constructor <;> decide +kernel

@[step]
theorem ML_DSA_87_spec :
    params.ML_DSA_87 ⦃ ip => Params.Valid ip 8#usize 7#usize Spec.ML_DSA_87 ⦄ := by
  have e : (1#u32 <<< 19#i32) = ok 524288#u32 := by rfl
  unfold params.ML_DSA_87
  simp only [e, bind_tc_ok, WP.spec_ok]
  constructor <;> decide +kernel

/-- Satisfiability witness for the `Params.Valid` premise: ML-DSA-44. -/
theorem ML_DSA_44_valid :
    ∃ ip, params.ML_DSA_44 = ok ip ∧ Params.Valid ip 4#usize 4#usize Spec.ML_DSA_44 := by
  obtain ⟨ip, h, hv⟩ := WP.spec_imp_exists ML_DSA_44_spec
  exact ⟨ip, h, hv⟩

/-- Satisfiability witness for the `Params.Valid` premise: ML-DSA-65. -/
theorem ML_DSA_65_valid :
    ∃ ip, params.ML_DSA_65 = ok ip ∧ Params.Valid ip 6#usize 5#usize Spec.ML_DSA_65 := by
  obtain ⟨ip, h, hv⟩ := WP.spec_imp_exists ML_DSA_65_spec
  exact ⟨ip, h, hv⟩

/-- Satisfiability witness for the `Params.Valid` premise: ML-DSA-87. -/
theorem ML_DSA_87_valid :
    ∃ ip, params.ML_DSA_87 = ok ip ∧ Params.Valid ip 8#usize 7#usize Spec.ML_DSA_87 := by
  obtain ⟨ip, h, hv⟩ := WP.spec_imp_exists ML_DSA_87_spec
  exact ⟨ip, h, hv⟩

/-! ## Bytes -/

/-- The bytes of a slice, as the spec's `List UInt8`. -/
def bytes (s : Slice U8) : List UInt8 := s.val.map fun x => UInt8.ofNat x.val

/-- The bytes of a fixed-size array. -/
def bytesA {n : Usize} (a : Array U8 n) : List UInt8 := a.val.map fun x => UInt8.ofNat x.val

@[simp] theorem bytes_length (s : Slice U8) : (bytes s).length = s.val.length := by simp [bytes]

@[simp] theorem bytesA_length {n : Usize} (a : Array U8 n) : (bytesA a).length = n.val := by
  simp [bytesA, a.property]

theorem bytes_getElem (s : Slice U8) (i : Nat) (hi : i < (bytes s).length) :
    (bytes s)[i] = UInt8.ofNat (s.val[i]'(by simpa using hi)).val := by
  simp [bytes]

theorem bytesA_getElem {n : Usize} (a : Array U8 n) (i : Nat) (hi : i < (bytesA a).length) :
    (bytesA a)[i] = UInt8.ofNat (a.val[i]'(by simpa [a.property] using hi)).val := by
  simp [bytesA]

theorem toNat_ofNat_val (x : U8) : (UInt8.ofNat x.val).toNat = x.val := by
  have : x.val < 256 := by scalar_tac
  simp [Nat.mod_eq_of_lt this]

theorem ofNat_val_inj {x y : U8} (h : UInt8.ofNat x.val = UInt8.ofNat y.val) : x = y := by
  have := congrArg UInt8.toNat h
  rw [toNat_ofNat_val, toNat_ofNat_val] at this
  exact UScalar.eq_of_val_eq this

theorem ofNat_val_injective : Function.Injective (fun x : U8 => UInt8.ofNat x.val) :=
  fun _ _ h => ofNat_val_inj h

/-- The byte view loses nothing: equal bytes mean equal slices. -/
theorem bytes_inj {s t : Slice U8} (h : bytes s = bytes t) : s = t :=
  Subtype.ext (List.map_injective_iff.mpr ofNat_val_injective h)

theorem bytesA_inj {n : Usize} {a b : Array U8 n} (h : bytesA a = bytesA b) : a = b :=
  Subtype.ext (List.map_injective_iff.mpr ofNat_val_injective h)

theorem bytes_to_slice {n : Usize} (a : Array U8 n) : bytes (Array.to_slice a) = bytesA a := by
  simp [bytes, bytesA, Array.val_to_slice]

theorem bytes_set (s : Slice U8) (i : Usize) (x : U8) :
    bytes (s.set i x) = (bytes s).set i.val (UInt8.ofNat x.val) := by
  simp [bytes, List.map_set]

theorem bytesA_set {n : Usize} (a : Array U8 n) (i : Usize) (x : U8) :
    bytesA (a.set i x) = (bytesA a).set i.val (UInt8.ofNat x.val) := by
  simp [bytesA, List.map_set]

theorem bytesA_from_slice {n : Usize} (a : Array U8 n) (s : Slice U8) (h : s.val.length = n.val) :
    bytesA (Array.from_slice a s) = bytes s := by
  simp [bytesA, bytes, Array.from_slice_val a s h]

theorem bytesA_repeat_zero (n : Usize) : bytesA (Array.repeat n 0#u8) = List.replicate n.val 0 := by
  simp [bytesA, Array.repeat_val, List.map_replicate]

/-- `Slice.index_usize` reads the `i`-th byte. -/
theorem bytes_getElem?_eq (s : Slice U8) (i : Nat) :
    (bytes s)[i]? = s.val[i]?.map fun x => UInt8.ofNat x.val := by
  simp [bytes]

/-! ### Sub-slices: `&s[a..b]`, `&s[..b]`, `&s[a..]` and their `_mut` forms

`slice_range_spec` etc. are stated for any element type (`.val` lists); the `_bytes` forms restate them through
`bytes`. The `_mut` forms give the back function (writing a sub-slice of the right length back):
`take a ++ t ++ drop b`. -/

theorem slice_range_spec {T : Type} (s : Slice T) (r : core.ops.range.Range Usize)
    (h1 : r.start.val ≤ r.end.val) (h2 : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice T) s r ⦃ t =>
      t.val = (s.val.drop r.start.val).take (r.end.val - r.start.val) ⦄ := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index]
  split
  · simp [WP.spec_ok, List.slice]
  · rename_i h
    exfalso; apply h
    exact ⟨by scalar_tac, by simpa [Slice.length] using h2⟩

theorem slice_range_mut_spec {T : Type} (s : Slice T) (r : core.ops.range.Range Usize)
    (h1 : r.start.val ≤ r.end.val) (h2 : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice T) s r ⦃ p =>
      p.1.val = (s.val.drop r.start.val).take (r.end.val - r.start.val) ∧
      ∀ t : Slice T, t.val.length = r.end.val - r.start.val →
        (p.2 t).val = s.val.take r.start.val ++ t.val ++ s.val.drop r.end.val ⦄ := by
  simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
  split
  · simp only [WP.spec_ok, List.slice]
    refine ⟨by simp, fun t ht => ?_⟩
    simp only [List.setSlice!]
    have e : min t.val.length (s.val.length - r.start.val) = t.val.length := by omega
    rw [e, List.take_of_length_le (le_refl _), show r.start.val + t.val.length = r.end.val by omega]
  · rename_i h
    exfalso; apply h
    exact ⟨by scalar_tac, by simpa [Slice.length] using h2⟩

theorem slice_to_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeTo Usize)
    (h : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice T) s r ⦃ t =>
      t.val = s.val.take r.end.val ⦄ := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index]
  split
  · simp [WP.spec_ok]
  · rename_i h'
    exfalso; apply h'
    simpa [Slice.length] using h

theorem slice_to_mut_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeTo Usize)
    (h : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice T) s r ⦃ p =>
      p.1.val = s.val.take r.end.val ∧
      ∀ t : Slice T, t.val.length = r.end.val → (p.2 t).val = t.val ++ s.val.drop r.end.val ⦄ := by
  simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  split
  · simp only [WP.spec_ok]
    refine ⟨by simp, fun t ht => ?_⟩
    simp only [List.setSlice!]
    have e : min t.val.length (s.val.length - 0) = t.val.length := by omega
    rw [e, List.take_of_length_le (le_refl _), ht]
    simp
  · rename_i h'
    exfalso; apply h'
    simpa [Slice.length] using h

theorem slice_from_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeFrom Usize)
    (h : r.start.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice T) s r ⦃ t =>
      t.val = s.val.drop r.start.val ⦄ := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  split
  · simp [WP.spec_ok]
  · rename_i h'
    exfalso; apply h'
    simpa [Slice.length] using h

theorem slice_from_mut_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeFrom Usize)
    (h : r.start.val ≤ s.val.length) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice T) s r ⦃ p =>
      p.1.val = s.val.drop r.start.val ∧
      ∀ t : Slice T, t.val.length = s.val.length - r.start.val →
        (p.2 t).val = s.val.take r.start.val ++ t.val ⦄ := by
  simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
  split
  · simp only [WP.spec_ok, Slice.getElem!_val_drop]
    refine ⟨trivial, fun t ht => ?_⟩
    simp only [List.setSlice!]
    have e : min t.val.length (s.val.length - r.start.val) = t.val.length := by omega
    rw [e, List.take_of_length_le (le_refl _), ht, show r.start.val + (s.val.length - r.start.val) = s.val.length by omega]
    simp
  · rename_i h'
    exfalso; apply h'
    simpa [Slice.length] using h

/-! The same through `bytes`. -/

theorem slice_range_bytes (s : Slice U8) (r : core.ops.range.Range Usize)
    (h1 : r.start.val ≤ r.end.val) (h2 : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s r ⦃ t =>
      bytes t = ((bytes s).drop r.start.val).take (r.end.val - r.start.val) ⦄ := by
  apply WP.spec_mono (slice_range_spec s r h1 h2)
  intro t ht
  simp [bytes, ht, List.map_take, List.map_drop]

theorem slice_range_mut_bytes (s : Slice U8) (r : core.ops.range.Range Usize)
    (h1 : r.start.val ≤ r.end.val) (h2 : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8) s r ⦃ p =>
      bytes p.1 = ((bytes s).drop r.start.val).take (r.end.val - r.start.val) ∧
      ∀ t : Slice U8, t.val.length = r.end.val - r.start.val →
        bytes (p.2 t) = (bytes s).take r.start.val ++ bytes t ++ (bytes s).drop r.end.val ⦄ := by
  apply WP.spec_mono (slice_range_mut_spec s r h1 h2)
  rintro p ⟨hp, hb⟩
  refine ⟨by simp [bytes, hp, List.map_take, List.map_drop], fun t ht => ?_⟩
  simp [bytes, hb t ht, List.map_take, List.map_drop]

theorem slice_to_bytes (s : Slice U8) (r : core.ops.range.RangeTo Usize) (h : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) s r ⦃ t =>
      bytes t = (bytes s).take r.end.val ⦄ := by
  apply WP.spec_mono (slice_to_spec s r h)
  intro t ht
  simp [bytes, ht, List.map_take]

theorem slice_from_bytes (s : Slice U8) (r : core.ops.range.RangeFrom Usize) (h : r.start.val ≤ s.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) s r ⦃ t =>
      bytes t = (bytes s).drop r.start.val ⦄ := by
  apply WP.spec_mono (slice_from_spec s r h)
  intro t ht
  simp [bytes, ht, List.map_drop]

end Proofs
