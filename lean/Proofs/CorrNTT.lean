import Spec.NTTOps
import Spec.Rounding
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# The algebra of the specification's NTT (Phase 5, part P1)

Facts about `Spec.NTT` (Algorithm 41), `Spec.NTTInv` (Algorithm 42) and the pointwise product `MultiplyNTT`
(Algorithm 45) that the correctness bound `‖c s₂‖∞ ≤ β` needs. This file imports only `Spec.*` and Mathlib, so
it does not rebuild when the Rust is re-extracted.

## Results

* `NTTInv_NTT`, `NTT_NTTInv`: the two inverse identities.
* `NTT_add`, `NTT_smul`, `NTTInv_add`, `NTTInv_smul`: linearity (additive and `Zq`-homogeneous).
* `NTT_eval`: coefficient `k` of `NTT w` is the value of `∑ w[i] X^i` at the root `rt 8 k` of `X^256 + 1`.
* `negaMul`: the product in `Zq[X]/(X^256 + 1)`, defined directly by the convolution sum with the sign flip.
* `NTT_negaMul`, `NTTInv_MultiplyNTT`: the convolution theorem
  `NTTInv (MultiplyNTT (NTT a) (NTT b)) = negaMul a b`.
* `cs_norm_bound`: `‖NTTInvVec (ScalarVectorNTT (NTT c) (NTTVec s))‖∞ ≤ τ η` for a challenge `c` with `τ`
  coefficients in `{-1, 1}` and a secret vector `s` with `‖s‖∞ ≤ η` (the shape of `c s₁`, `c s₂` in Algorithm 7).

## Route (and why not "linear map + 256 kernel checks")

The planned route was: both transforms are linear, so an identity holds once it holds on the 256 basis vectors,
each checked by `decide +kernel`. Linearity by induction on the loop structure is fine, but the kernel checks are
not: a single `NTT (e_j)` costs about a minute of kernel time (and tens of GB of memory) because the
`Id.run do` loops build thunk chains of `Vector.set!`. So the identities are proved algebraically instead;
the only kernel checks are three small tables of twiddle factors (`zeta_pair`, `zeta_sq`, `rt8_pow`, a few
seconds in total).

1. *Layers, pointwise.* Each `nttLayer` / `nttInvLayer` is rewritten from its `forIn` loops to folds
   (`nttLayer_eq`, `nttInvLayer_eq`), and the folds are described coefficient by coefficient (`nttLayer_lo`,
   `nttLayer_hi`, `nttInvLayer_lo`, `nttInvLayer_hi`): block `b`, offset `j < len`, low index `2 len b + j`,
   high index `+ len`.
2. *Layers invert each other.* With `z = ζ^BitRev8(B + b)` forward and `z' = -ζ^BitRev8(2B - 1 - b)` backward,
   `z' z = 1` (`zeta_pair`), so `If ∘ Lf = 2 · id` and `Lf ∘ If = 2 · id` layer by layer (`inv_fwd`, `fwd_inv`);
   eight layers give `2^8`, cancelled by the final scaling `256⁻¹ = 8347681`.
3. *Evaluation.* After `e` layers, block `b` (of width `N = 256 / 2^e`) agrees with the input polynomial at every
   root of `X^N - rt e b` (`inv_step`); after eight layers `NTT w` is the vector of values `w(rt 8 k)`.
   Linearity, the convolution theorem and `NTT_eval` follow from `rt 8 k ^ 256 = -1`.
-/

open Spec

namespace Proofs.Corr

/-! ## Indexing helpers -/

theorem vget! (w : Poly) {i : Nat} (hi : i < 256) : w[i]! = w[i] :=
  getElem!_pos w i (by simpa using hi)

theorem vgetG {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) {i : Nat} (hi : i < n) :
    v[i]! = v[i] := getElem!_pos v i (by simpa using hi)

theorem ntt_set!_eq {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := rfl

theorem default_zq : (default : Zq) = 0 := rfl

theorem get!_set! (w : Poly) (i : Nat) (x : Zq) (k : Nat) :
    (w.set! i x)[k]! = if i = k ∧ k < 256 then x else w[k]! := by
  by_cases hk : k < 256
  · rw [vget! _ hk, ntt_set!_eq, Vector.getElem_setIfInBounds hk]
    by_cases hik : i = k <;> simp [hik, hk]
  · have h1 : ¬ (i = k ∧ k < 256) := fun h => hk h.2
    rw [if_neg h1]
    rw [getElem!_neg (w.set! i x) k (by simpa using hk), getElem!_neg w k (by simpa using hk)]

/-! ## The forward layer, pointwise -/

/-- One iteration of the inner `for j` loop of `nttLayer`. -/
def fwdStep (len : Nat) (z : Zq) (w : Poly) (j : Nat) : Poly :=
  (w.set! (j + len) (w[j]! - z * w[j + len]!)).set! j
    ((w.set! (j + len) (w[j]! - z * w[j + len]!))[j]! + z * w[j + len]!)

theorem fwdStep_get (len : Nat) (z : Zq) (hlen : 0 < len) (v : Poly) (j i : Nat) :
    (fwdStep len z v j)[i]! =
      if j = i ∧ i < 256 then v[j]! + z * v[j + len]!
      else if j + len = i ∧ i < 256 then v[j]! - z * v[j + len]! else v[i]! := by
  simp only [fwdStep, get!_set!]
  have : ¬ (j + len = j ∧ j < 256) := by omega
  simp only [this, if_false]

theorem fwdInner (len : Nat) (z : Zq) (hlen : 0 < len) (s : Nat) (hs : s + 2 * len ≤ 256) (w : Poly) :
    ∀ n, n ≤ len → ∀ i, ((List.range' s n).foldl (fwdStep len z) w)[i]! =
      if s ≤ i ∧ i < s + n then w[i]! + z * w[i + len]!
      else if s + len ≤ i ∧ i < s + len + n then w[i - len]! - z * w[i]!
      else w[i]! := by
  intro n
  induction n with
  | zero =>
    intro _ i
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro hn i
    have ih' := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      fwdStep_get len z hlen]
    simp only [ih', Nat.one_mul]
    grind

/-- One iteration of the block loop of `nttLayer`, on the state `(m, start, ŵ)`. -/
def fwdBlockF (len : Nat) (b : MProd Nat (MProd Nat Poly)) (_a : Nat) : MProd Nat (MProd Nat Poly) :=
  ⟨b.fst + 1, b.snd.fst + 2 * len,
    (List.range' b.snd.fst len).foldl (fwdStep len (zeta (b.fst + 1))) b.snd.snd⟩

/-- The block loop state after `i` blocks. -/
def fwdBlockFold (len m0 : Nat) (w0 : Poly) (i : Nat) : MProd Nat (MProd Nat Poly) :=
  (List.range' 0 i).foldl (fwdBlockF len) ⟨m0, 0, w0⟩

theorem nttLayer_eq (len : Nat) (w : Poly) (m : Nat) :
    nttLayer len w m =
      ((fwdBlockFold len m w (256 / (2 * len))).snd.snd, (fwdBlockFold len m w (256 / (2 * len))).fst) := by
  unfold nttLayer fwdBlockFold
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  constructor <;> rfl

theorem fwdBlockFold_succ (len m0 : Nat) (w0 : Poly) (i : Nat) :
    fwdBlockFold len m0 w0 (i + 1) = fwdBlockF len (fwdBlockFold len m0 w0 i) i := by
  simp [fwdBlockFold, List.range'_concat, List.foldl_append]

theorem fwdBlockFold_zero (len m0 : Nat) (w0 : Poly) : fwdBlockFold len m0 w0 0 = ⟨m0, 0, w0⟩ := rfl

theorem fwdBlockFold_fst (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (fwdBlockFold len m0 w0 i).fst = m0 + i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [fwdBlockFold_succ]; simp [fwdBlockF, ih]; omega

theorem fwdBlockFold_start (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (fwdBlockFold len m0 w0 i).snd.fst = 2 * len * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [fwdBlockFold_succ]; simp [fwdBlockF, ih]; ring

theorem div_mod_blk (len i k : Nat) (_hlen : 0 < len) (h1 : 2 * len * i ≤ k)
    (h2 : k < 2 * len * i + 2 * len) : k / (2 * len) = i ∧ k % (2 * len) = k - 2 * len * i := by
  have h3 : k / (2 * len) = i := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  refine ⟨h3, ?_⟩
  have := Nat.div_add_mod k (2 * len)
  rw [h3] at this
  omega

theorem fwdBlockFold_get (len m0 : Nat) (hlen : 0 < len) (w : Poly) :
    ∀ i, 2 * len * i ≤ 256 → ∀ k, (fwdBlockFold len m0 w i).snd.snd[k]! =
      if k < 2 * len * i then
        (if k % (2 * len) < len then w[k]! + zeta (m0 + k / (2 * len) + 1) * w[k + len]!
         else w[k - len]! - zeta (m0 + k / (2 * len) + 1) * w[k]!)
      else w[k]! := by
  intro i
  induction i with
  | zero => intro _ k; simp [fwdBlockFold_zero]
  | succ i ih =>
    intro hi k
    have e : 2 * len * (i + 1) = 2 * len * i + 2 * len := by ring
    have ih' := ih (by omega)
    have hdm := div_mod_blk len i k hlen
    rw [fwdBlockFold_succ]
    simp only [fwdBlockF, fwdBlockFold_fst, fwdBlockFold_start]
    rw [fwdInner len _ hlen (2 * len * i) (by omega) _ len le_rfl k]
    simp only [ih']
    rw [e]
    grind

theorem nttLayer_snd (len : Nat) (w : Poly) (m : Nat) :
    (nttLayer len w m).2 = m + 256 / (2 * len) := by
  rw [nttLayer_eq, fwdBlockFold_fst]

/-- Low half of block `b` after one forward layer: `ŵ[j] + z ŵ[j + len]`. -/
theorem nttLayer_lo (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (w : Poly)
    (b j : Nat) (hb : b < B) (hj : j < len) :
    (nttLayer len w m).1[2 * len * b + j]! =
      w[2 * len * b + j]! + zeta (m + b + 1) * w[2 * len * b + j + len]! := by
  have hd : 256 / (2 * len) = B := by rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  rw [nttLayer_eq, hd]
  dsimp only
  rw [fwdBlockFold_get len m hlen w B (by omega)]
  have h1 : 2 * len * (b + 1) ≤ 2 * len * B := Nat.mul_le_mul_left _ hb
  have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
  have hdm := div_mod_blk len b (2 * len * b + j) hlen (by omega) (by omega)
  grind

/-- High half of block `b` after one forward layer: `ŵ[j] - z ŵ[j + len]`. -/
theorem nttLayer_hi (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (w : Poly)
    (b j : Nat) (hb : b < B) (hj : j < len) :
    (nttLayer len w m).1[2 * len * b + j + len]! =
      w[2 * len * b + j]! - zeta (m + b + 1) * w[2 * len * b + j + len]! := by
  have hd : 256 / (2 * len) = B := by rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  rw [nttLayer_eq, hd]
  dsimp only
  rw [fwdBlockFold_get len m hlen w B (by omega)]
  have h1 : 2 * len * (b + 1) ≤ 2 * len * B := Nat.mul_le_mul_left _ hb
  have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
  have hdm := div_mod_blk len b (2 * len * b + j + len) hlen (by omega) (by omega)
  grind

/-! ## The inverse layer, pointwise -/

/-- One iteration of the inner `for j` loop of `nttInvLayer`. -/
def invStep (len : Nat) (z : Zq) (w : Poly) (j : Nat) : Poly :=
  let w1 := w.set! j (w[j]! + w[j + len]!)
  let w2 := w1.set! (j + len) (w[j]! - w1[j + len]!)
  w2.set! (j + len) (z * w2[j + len]!)

theorem invStep_get (len : Nat) (z : Zq) (hlen : 0 < len) (v : Poly) (j i : Nat) :
    (invStep len z v j)[i]! =
      if j = i ∧ i < 256 then v[j]! + v[j + len]!
      else if j + len = i ∧ i < 256 then z * (v[j]! - v[j + len]!) else v[i]! := by
  simp only [invStep, get!_set!]
  grind

theorem invInner (len : Nat) (z : Zq) (hlen : 0 < len) (s : Nat) (hs : s + 2 * len ≤ 256) (w : Poly) :
    ∀ n, n ≤ len → ∀ i, ((List.range' s n).foldl (invStep len z) w)[i]! =
      if s ≤ i ∧ i < s + n then w[i]! + w[i + len]!
      else if s + len ≤ i ∧ i < s + len + n then z * (w[i - len]! - w[i]!)
      else w[i]! := by
  intro n
  induction n with
  | zero =>
    intro _ i
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro hn i
    have ih' := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
      invStep_get len z hlen]
    simp only [ih', Nat.one_mul]
    grind

/-- One iteration of the block loop of `nttInvLayer`, on the state `(m, start, w)`. -/
def invBlockF (len : Nat) (b : MProd Nat (MProd Nat Poly)) (_a : Nat) :
    MProd Nat (MProd Nat Poly) :=
  ⟨b.fst - 1, b.snd.fst + 2 * len,
    (List.range' b.snd.fst len).foldl (invStep len (-zeta (b.fst - 1))) b.snd.snd⟩

/-- The block loop state after `i` blocks. -/
def invBlockFold (len m0 : Nat) (w0 : Poly) (i : Nat) : MProd Nat (MProd Nat Poly) :=
  (List.range' 0 i).foldl (invBlockF len) ⟨m0, 0, w0⟩

theorem nttInvLayer_eq (len : Nat) (w : Poly) (m : Nat) :
    nttInvLayer len w m =
      ((invBlockFold len m w (256 / (2 * len))).snd.snd,
        (invBlockFold len m w (256 / (2 * len))).fst) := by
  unfold nttInvLayer invBlockFold
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, -neg_mul]
  constructor <;> rfl

theorem invBlockFold_succ (len m0 : Nat) (w0 : Poly) (i : Nat) :
    invBlockFold len m0 w0 (i + 1) = invBlockF len (invBlockFold len m0 w0 i) i := by
  simp [invBlockFold, List.range'_concat, List.foldl_append]

theorem invBlockFold_zero (len m0 : Nat) (w0 : Poly) : invBlockFold len m0 w0 0 = ⟨m0, 0, w0⟩ := rfl

theorem invBlockFold_fst (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (invBlockFold len m0 w0 i).fst = m0 - i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [invBlockFold_succ]; simp [invBlockF, ih]; omega

theorem invBlockFold_start (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (invBlockFold len m0 w0 i).snd.fst = 2 * len * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [invBlockFold_succ]; simp [invBlockF, ih]; ring

theorem invBlockFold_get (len m0 : Nat) (hlen : 0 < len) (w : Poly) :
    ∀ i, 2 * len * i ≤ 256 → ∀ k, (invBlockFold len m0 w i).snd.snd[k]! =
      if k < 2 * len * i then
        (if k % (2 * len) < len then w[k]! + w[k + len]!
         else (-zeta (m0 - k / (2 * len) - 1)) * (w[k - len]! - w[k]!))
      else w[k]! := by
  intro i
  induction i with
  | zero => intro _ k; simp [invBlockFold_zero]
  | succ i ih =>
    intro hi k
    have e : 2 * len * (i + 1) = 2 * len * i + 2 * len := by ring
    have ih' := ih (by omega)
    have hdm := div_mod_blk len i k hlen
    rw [invBlockFold_succ]
    simp only [invBlockF, invBlockFold_fst, invBlockFold_start]
    rw [invInner len _ hlen (2 * len * i) (by omega) _ len le_rfl k]
    simp only [ih']
    rw [e]
    grind

theorem nttInvLayer_snd (len : Nat) (w : Poly) (m : Nat) :
    (nttInvLayer len w m).2 = m - 256 / (2 * len) := by
  rw [nttInvLayer_eq, invBlockFold_fst]

/-- Low half of block `b` after one inverse layer: `w[j] + w[j + len]`. -/
theorem nttInvLayer_lo (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (w : Poly)
    (b j : Nat) (hb : b < B) (hj : j < len) :
    (nttInvLayer len w m).1[2 * len * b + j]! = w[2 * len * b + j]! + w[2 * len * b + j + len]! := by
  have hd : 256 / (2 * len) = B := by rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  rw [nttInvLayer_eq, hd]
  dsimp only
  rw [invBlockFold_get len m hlen w B (by omega)]
  have h1 : 2 * len * (b + 1) ≤ 2 * len * B := Nat.mul_le_mul_left _ hb
  have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
  have hdm := div_mod_blk len b (2 * len * b + j) hlen (by omega) (by omega)
  grind

/-- High half of block `b` after one inverse layer: `-ζ^BitRev8(m-b-1) (w[j] - w[j + len])`. -/
theorem nttInvLayer_hi (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (w : Poly)
    (b j : Nat) (hb : b < B) (hj : j < len) :
    (nttInvLayer len w m).1[2 * len * b + j + len]! =
      (-zeta (m - b - 1)) * (w[2 * len * b + j]! - w[2 * len * b + j + len]!) := by
  have hd : 256 / (2 * len) = B := by rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  rw [nttInvLayer_eq, hd]
  dsimp only
  rw [invBlockFold_get len m hlen w B (by omega)]
  have h1 : 2 * len * (b + 1) ≤ 2 * len * B := Nat.mul_le_mul_left _ hb
  have e : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
  have hdm := div_mod_blk len b (2 * len * b + j + len) hlen (by omega) (by omega)
  grind

/-! ## Scalar multiples, extensionality, and the layers invert each other -/

/-- The scalar multiple `c · a` of a polynomial. -/
def pscale (c : Zq) (a : Poly) : Poly := a.map (c * ·)

theorem get!_pscale (c : Zq) (a : Poly) (k : Nat) : (pscale c a)[k]! = c * a[k]! := by
  by_cases hk : k < 256
  · rw [vget! _ hk, vget! _ hk]; simp [pscale]
  · rw [getElem!_neg (pscale c a) k (by simpa using hk), getElem!_neg a k (by simpa using hk),
      default_zq]
    simp

theorem poly_ext (a b : Poly) (h : ∀ k, k < 256 → a[k]! = b[k]!) : a = b := by
  apply Vector.ext
  intro k hk
  have := h k hk
  rwa [vget! a hk, vget! b hk] at this

theorem pscale_pscale (c d : Zq) (a : Poly) : pscale c (pscale d a) = pscale (c * d) a := by
  apply poly_ext; intro k _; simp only [get!_pscale]; ring

theorem pscale_one (a : Poly) : pscale 1 a = a := by
  apply poly_ext; intro k _; simp only [get!_pscale]; ring

theorem cover (len B k : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (hk : k < 256) :
    ∃ b j, b < B ∧ j < len ∧ (k = 2 * len * b + j ∨ k = 2 * len * b + j + len) := by
  have h1 := Nat.div_add_mod k (2 * len)
  have h2 : k % (2 * len) < 2 * len := Nat.mod_lt _ (by omega)
  have h3 : k / (2 * len) < B := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    nlinarith
  by_cases h : k % (2 * len) < len
  · exact ⟨k / (2 * len), k % (2 * len), h3, h, Or.inl (by omega)⟩
  · exact ⟨k / (2 * len), k % (2 * len) - len, h3, by omega, Or.inr (by omega)⟩

theorem ext_layer (len B : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (X Y : Poly)
    (h : ∀ b j, b < B → j < len → X[2 * len * b + j]! = Y[2 * len * b + j]! ∧
      X[2 * len * b + j + len]! = Y[2 * len * b + j + len]!) : X = Y := by
  apply poly_ext
  intro k hk
  obtain ⟨b, j, hb, hj, h1 | h1⟩ := cover len B k hlen hB hk
  · subst h1; exact (h b j hb hj).1
  · subst h1; exact (h b j hb hj).2

/-- The forward layer as a function of the polynomial. -/
def Lf (len m : Nat) (w : Poly) : Poly := (nttLayer len w m).1

/-- The inverse layer as a function of the polynomial. -/
def If (len m : Nat) (w : Poly) : Poly := (nttInvLayer len w m).1

theorem Lf_pscale (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (c : Zq) (w : Poly) :
    Lf len m (pscale c w) = pscale c (Lf len m w) := by
  apply ext_layer len B hlen hB
  intro b j hb hj
  simp only [Lf, nttLayer_lo len B m hlen hB _ b j hb hj, nttLayer_hi len B m hlen hB _ b j hb hj,
    get!_pscale]
  constructor <;> ring

theorem If_pscale (len B m : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (c : Zq) (w : Poly) :
    If len m (pscale c w) = pscale c (If len m w) := by
  apply ext_layer len B hlen hB
  intro b j hb hj
  simp only [If, nttInvLayer_lo len B m hlen hB _ b j hb hj, nttInvLayer_hi len B m hlen hB _ b j hb hj,
    get!_pscale]
  constructor <;> ring

/-- The twiddle pairing that makes each inverse layer undo the forward layer with the same blocks:
`-ζ^BitRev8(2B-1-b) · ζ^BitRev8(B+b) = 1`, for `B = 1, 2, ..., 128` and `b < B`. -/
theorem zeta_pair : ∀ e : Fin 8, ∀ b : Fin 128, b.val < 2 ^ e.val →
    -(zeta (2 * 2 ^ e.val - b.val - 1)) * zeta (2 ^ e.val + b.val) = 1 := by decide +kernel

theorem inv_fwd (len B m0 m1 : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (hm0 : m0 + 1 = B)
    (hm1 : m1 = 2 * B) (hz : ∀ b, b < B → -(zeta (2 * B - b - 1)) * zeta (B + b) = 1) (w : Poly) :
    If len m1 (Lf len m0 w) = pscale 2 w := by
  apply ext_layer len B hlen hB
  intro b j hb hj
  have hzb := hz b hb
  have e1 : m0 + b + 1 = B + b := by omega
  have e2 : m1 - b - 1 = 2 * B - b - 1 := by omega
  simp only [If, Lf, nttInvLayer_lo len B m1 hlen hB _ b j hb hj,
    nttInvLayer_hi len B m1 hlen hB _ b j hb hj, nttLayer_lo len B m0 hlen hB _ b j hb hj,
    nttLayer_hi len B m0 hlen hB _ b j hb hj, get!_pscale, e1, e2]
  constructor
  · ring
  · linear_combination (2 * w[2 * len * b + j + len]!) * hzb

theorem fwd_inv (len B m0 m1 : Nat) (hlen : 0 < len) (hB : 2 * len * B = 256) (hm0 : m0 + 1 = B)
    (hm1 : m1 = 2 * B) (hz : ∀ b, b < B → -(zeta (2 * B - b - 1)) * zeta (B + b) = 1) (w : Poly) :
    Lf len m0 (If len m1 w) = pscale 2 w := by
  apply ext_layer len B hlen hB
  intro b j hb hj
  have hzb := hz b hb
  have e1 : m0 + b + 1 = B + b := by omega
  have e2 : m1 - b - 1 = 2 * B - b - 1 := by omega
  simp only [If, Lf, nttInvLayer_lo len B m1 hlen hB _ b j hb hj,
    nttInvLayer_hi len B m1 hlen hB _ b j hb hj, nttLayer_lo len B m0 hlen hB _ b j hb hj,
    nttLayer_hi len B m0 hlen hB _ b j hb hj, get!_pscale, e1, e2]
  constructor
  · linear_combination (w[2 * len * b + j]! - w[2 * len * b + j + len]!) * hzb
  · linear_combination (-(w[2 * len * b + j]! - w[2 * len * b + j + len]!)) * hzb

theorem zeta_pair' (e : Nat) (he : e < 8) :
    ∀ b, b < 2 ^ e → -(zeta (2 * 2 ^ e - b - 1)) * zeta (2 ^ e + b) = 1 := by
  intro b hb
  have : 2 ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact zeta_pair ⟨e, he⟩ ⟨b, by omega⟩ hb

theorem inv_fwd_e (e : Nat) (he : e < 8) (len m0 m1 : Nat) (hlen : 2 * len * 2 ^ e = 256)
    (hm0 : m0 + 1 = 2 ^ e) (hm1 : m1 = 2 * 2 ^ e) (c : Zq) (w : Poly) :
    If len m1 (pscale c (Lf len m0 w)) = pscale (c * 2) w := by
  have hl : 0 < len := Nat.pos_of_ne_zero (fun h => by simp [h] at hlen)
  rw [If_pscale len (2 ^ e) m1 hl hlen, inv_fwd len (2 ^ e) m0 m1 hl hlen hm0 hm1 (zeta_pair' e he),
    pscale_pscale]

theorem inv_fwd_e' (e : Nat) (he : e < 8) (len m0 m1 : Nat) (hlen : 2 * len * 2 ^ e = 256)
    (hm0 : m0 + 1 = 2 ^ e) (hm1 : m1 = 2 * 2 ^ e) (w : Poly) :
    If len m1 (Lf len m0 w) = pscale 2 w := by
  have hl : 0 < len := Nat.pos_of_ne_zero (fun h => by simp [h] at hlen)
  exact inv_fwd len (2 ^ e) m0 m1 hl hlen hm0 hm1 (zeta_pair' e he) w

theorem fwd_inv_e (e : Nat) (he : e < 8) (len m0 m1 : Nat) (hlen : 2 * len * 2 ^ e = 256)
    (hm0 : m0 + 1 = 2 ^ e) (hm1 : m1 = 2 * 2 ^ e) (c : Zq) (w : Poly) :
    Lf len m0 (pscale c (If len m1 w)) = pscale (c * 2) w := by
  have hl : 0 < len := Nat.pos_of_ne_zero (fun h => by simp [h] at hlen)
  rw [Lf_pscale len (2 ^ e) m0 hl hlen, fwd_inv len (2 ^ e) m0 m1 hl hlen hm0 hm1 (zeta_pair' e he),
    pscale_pscale]

/-! ## Algorithms 41 and 42 as compositions of layers -/

/-- Algorithm 41 is the composition of its eight layers. -/
theorem NTT_eq_layers (w : Poly) :
    NTT w = (let p := nttLayer 128 w 0
             let p := nttLayer 64 p.1 p.2
             let p := nttLayer 32 p.1 p.2
             let p := nttLayer 16 p.1 p.2
             let p := nttLayer 8 p.1 p.2
             let p := nttLayer 4 p.1 p.2
             let p := nttLayer 2 p.1 p.2
             (nttLayer 1 p.1 p.2).1) := by
  simp [NTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ]

theorem NTT_eq (w : Poly) :
    NTT w = Lf 1 127 (Lf 2 63 (Lf 4 31 (Lf 8 15 (Lf 16 7 (Lf 32 3 (Lf 64 1 (Lf 128 0 w))))))) := by
  rw [NTT_eq_layers]
  simp [nttLayer_snd, Lf]

/-- One iteration of the scaling loop of Algorithm 42. -/
def scaleF (b : Poly) (a : Nat) : Poly := Vector.set! b a (8347681 * b[a]!)

theorem scale_fold (x : Poly) : ∀ n, n ≤ 256 → ∀ k, ((List.range' 0 n).foldl scaleF x)[k]! =
    if k < n then 8347681 * x[k]! else x[k]! := by
  intro n
  induction n with
  | zero => intro _ k; simp
  | succ n ih =>
    intro hn k
    have ih := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [scaleF, get!_set!, ih, Nat.zero_add, Nat.one_mul]
    grind

theorem scale_eq (x : Poly) : (List.range' 0 256).foldl scaleF x = pscale 8347681 x := by
  apply poly_ext
  intro k hk
  rw [scale_fold x 256 le_rfl, get!_pscale, if_pos hk]

/-- Algorithm 42 is the composition of its eight layers followed by the scaling loop. -/
theorem NTTInv_eq_layers (w : Poly) :
    NTTInv w = (List.range' 0 256).foldl scaleF
             (let p := nttInvLayer 1 w 256
              let p := nttInvLayer 2 p.1 p.2
              let p := nttInvLayer 4 p.1 p.2
              let p := nttInvLayer 8 p.1 p.2
              let p := nttInvLayer 16 p.1 p.2
              let p := nttInvLayer 32 p.1 p.2
              let p := nttInvLayer 64 p.1 p.2
              (nttInvLayer 128 p.1 p.2).1) := by
  simp [NTTInv, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    show List.range' 0 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rfl

theorem NTTInv_eq (w : Poly) :
    NTTInv w = pscale 8347681
      (If 128 2 (If 64 4 (If 32 8 (If 16 16 (If 8 32 (If 4 64 (If 2 128 (If 1 256 w)))))))) := by
  rw [NTTInv_eq_layers, scale_eq]
  simp [nttInvLayer_snd, If]

/-- **`NTT⁻¹ ∘ NTT = id`.** -/
theorem NTTInv_NTT (w : Poly) : NTTInv (NTT w) = w := by
  rw [NTTInv_eq, NTT_eq,
    inv_fwd_e' 7 (by norm_num) 1 127 256 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 6 (by norm_num) 2 63 128 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 5 (by norm_num) 4 31 64 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 4 (by norm_num) 8 15 32 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 3 (by norm_num) 16 7 16 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 2 (by norm_num) 32 3 8 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 1 (by norm_num) 64 1 4 (by norm_num) (by norm_num) (by norm_num),
    inv_fwd_e 0 (by norm_num) 128 0 2 (by norm_num) (by norm_num) (by norm_num),
    pscale_pscale, show (8347681 : Zq) * (2 * 2 * 2 * 2 * 2 * 2 * 2 * 2) = 1 by decide, pscale_one]

/-- **`NTT ∘ NTT⁻¹ = id`.** -/
theorem NTT_NTTInv (w : Poly) : NTT (NTTInv w) = w := by
  rw [NTT_eq, NTTInv_eq,
    fwd_inv_e 0 (by norm_num) 128 0 2 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 1 (by norm_num) 64 1 4 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 2 (by norm_num) 32 3 8 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 3 (by norm_num) 16 7 16 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 4 (by norm_num) 8 15 32 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 5 (by norm_num) 4 31 64 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 6 (by norm_num) 2 63 128 (by norm_num) (by norm_num) (by norm_num),
    fwd_inv_e 7 (by norm_num) 1 127 256 (by norm_num) (by norm_num) (by norm_num),
    show (8347681 : Zq) * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 = 1 by decide, pscale_one]

/-! ## `NTT` is evaluation at the roots of `X^256 + 1` -/

/-- The root of `X^N - ρ` attached to block `b` after `e` layers: `rt 0 0 = -1` (the modulus is `X^256 + 1`)
and the children of a block with root `ρ = z²` have roots `z` and `-z`, where `z` is the twiddle factor used
by the layer. -/
def rt : Nat → Nat → Zq
  | 0, _ => -1
  | e + 1, b => (if b % 2 = 0 then 1 else -1) * zeta (2 ^ e + b / 2)

/-- The twiddle factor of a block squares to the block's root. -/
theorem zeta_sq : ∀ e : Fin 8, ∀ c : Fin 128, c.val < 2 ^ e.val →
    zeta (2 ^ e.val + c.val) ^ 2 = rt e.val c.val := by decide +kernel

/-- Every final root is a root of `X^256 + 1`. -/
theorem rt8_pow : ∀ k : Fin 256, rt 8 k.val ^ 256 = -1 := by decide +kernel

/-- `S` holds, in block `b` of width `N`, a polynomial that agrees with `w` at every root of `X^N - r b`. -/
def AgreesAt (B N : Nat) (r : Nat → Zq) (S w : Poly) : Prop :=
  ∀ b, b < B → ∀ x : Zq, x ^ N = r b →
    ∑ i ∈ Finset.range N, S[b * N + i]! * x ^ i = ∑ i ∈ Finset.range 256, w[i]! * x ^ i

theorem agrees_step (e len : Nat) (he : e < 8) (hlen : 0 < len) (hB : 2 * len * 2 ^ e = 256)
    (S w : Poly) (h : AgreesAt (2 ^ e) (2 * len) (rt e) S w) :
    AgreesAt (2 * 2 ^ e) len (rt (e + 1)) (Lf len (2 ^ e - 1) S) w := by
  intro b' hb' x hx
  have hBpos : 0 < 2 ^ e := by positivity
  have hB7 : 2 ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨b, rfl | rfl⟩ : ∃ b, b' = 2 * b ∨ b' = 2 * b + 1 := ⟨b' / 2, by omega⟩
  · have hb : b < 2 ^ e := by omega
    have hzs := zeta_sq ⟨e, he⟩ ⟨b, by omega⟩ hb
    simp only [rt, show 2 * b % 2 = 0 by omega, if_true, one_mul, show 2 * b / 2 = b by omega] at hx
    simp only at hzs
    have hx2 : x ^ (2 * len) = rt e b := by
      rw [← hzs, ← hx, ← pow_mul, mul_comm]
    have key := h b hb x hx2
    rw [two_mul, Finset.sum_range_add] at key
    have e1 : ∀ i ∈ Finset.range len,
        (Lf len (2 ^ e - 1) S)[2 * b * len + i]! * x ^ i =
          S[b * (len + len) + i]! * x ^ i + S[b * (len + len) + (len + i)]! * x ^ (len + i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have := nttLayer_lo len (2 ^ e) (2 ^ e - 1) hlen hB S b i hb hi'
      have eq1 : 2 * b * len + i = 2 * len * b + i := by ring
      have eq2 : b * (len + len) + i = 2 * len * b + i := by ring
      have eq3 : b * (len + len) + (len + i) = 2 * len * b + i + len := by ring
      have eq4 : 2 ^ e - 1 + b + 1 = 2 ^ e + b := by omega
      rw [eq1, eq2, eq3]
      simp only [Lf]
      rw [this, eq4, pow_add, hx]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    exact key
  · have hb : b < 2 ^ e := by omega
    have hzs := zeta_sq ⟨e, he⟩ ⟨b, by omega⟩ hb
    simp only [rt, show (2 * b + 1) % 2 = 1 by omega, show (1 : Nat) ≠ 0 by omega, if_false,
      show (2 * b + 1) / 2 = b by omega] at hx
    simp only at hzs
    have hx2 : x ^ (2 * len) = rt e b := by
      rw [← hzs, mul_comm, pow_mul, hx]; ring
    have key := h b hb x hx2
    rw [two_mul, Finset.sum_range_add] at key
    have e1 : ∀ i ∈ Finset.range len,
        (Lf len (2 ^ e - 1) S)[(2 * b + 1) * len + i]! * x ^ i =
          S[b * (len + len) + i]! * x ^ i + S[b * (len + len) + (len + i)]! * x ^ (len + i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have := nttLayer_hi len (2 ^ e) (2 ^ e - 1) hlen hB S b i hb hi'
      have eq1 : (2 * b + 1) * len + i = 2 * len * b + i + len := by ring
      have eq2 : b * (len + len) + i = 2 * len * b + i := by ring
      have eq3 : b * (len + len) + (len + i) = 2 * len * b + i + len := by ring
      have eq4 : 2 ^ e - 1 + b + 1 = 2 ^ e + b := by omega
      rw [eq1, eq2, eq3]
      simp only [Lf]
      rw [this, eq4, pow_add, hx]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    exact key

/-- The state of `NTT` after `e` layers. -/
def nttState (w : Poly) : Nat → Poly
  | 0 => w
  | e + 1 => Lf (128 / 2 ^ e) (2 ^ e - 1) (nttState w e)

theorem nttState_agrees (w : Poly) :
    ∀ e, e ≤ 8 → AgreesAt (2 ^ e) (256 / 2 ^ e) (rt e) (nttState w e) w := by
  intro e
  induction e with
  | zero =>
    intro _ b hb x _
    have : b = 0 := by omega
    subst this
    simp [nttState]
  | succ e ih =>
    intro he
    have ih := ih (by omega)
    have h128 : 2 ^ e ∣ 128 := by
      have : 2 ^ e ∣ 2 ^ 7 := pow_dvd_pow 2 (by omega)
      simpa using this
    have hl : 128 / 2 ^ e * 2 ^ e = 128 := Nat.div_mul_cancel h128
    have hpos : 0 < 2 ^ e := by positivity
    have hlen : 0 < 128 / 2 ^ e := Nat.div_pos (by
      have : 2 ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) hpos
    have hB : 2 * (128 / 2 ^ e) * 2 ^ e = 256 := by nlinarith
    have hN : 256 / 2 ^ e = 2 * (128 / 2 ^ e) := by
      rw [← Nat.mul_div_assoc _ h128]
    have hN' : 256 / 2 ^ (e + 1) = 128 / 2 ^ e := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hN]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hN] at ih
    rw [hN', pow_succ, mul_comm (2 ^ e) 2]
    exact agrees_step e (128 / 2 ^ e) (by omega) hlen hB _ w ih

theorem NTT_state (w : Poly) : NTT w = nttState w 8 := by
  rw [NTT_eq]; rfl

/-- **`NTT` is evaluation.** Coefficient `k` of `NTT w` is `w(r_k)`, the value at `r_k = rt 8 k` of the
polynomial `∑ w[i] X^i`. -/
theorem NTT_eval (w : Poly) (k : Nat) (hk : k < 256) :
    (NTT w)[k]! = ∑ i ∈ Finset.range 256, w[i]! * rt 8 k ^ i := by
  have := nttState_agrees w 8 le_rfl k (by norm_num; exact hk) (rt 8 k) (by norm_num)
  rw [NTT_state]
  simpa using this

/-! ## Linearity -/

theorem get!_add (a b : Poly) (k : Nat) : (a + b)[k]! = a[k]! + b[k]! := by
  by_cases hk : k < 256
  · rw [vget! _ hk, vget! _ hk, vget! _ hk]
    show (Vector.zipWith (· + ·) a b)[k] = _
    simp
  · rw [getElem!_neg (a + b) k (by simpa using hk), getElem!_neg a k (by simpa using hk),
      getElem!_neg b k (by simpa using hk), default_zq]
    simp

/-- `NTT` is additive. -/
theorem NTT_add (a b : Poly) : NTT (a + b) = NTT a + NTT b := by
  apply poly_ext
  intro k hk
  rw [get!_add, NTT_eval _ k hk, NTT_eval _ k hk, NTT_eval _ k hk, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by rw [get!_add]; ring)

/-- `NTT` is homogeneous over `Zq`. -/
theorem NTT_smul (c : Zq) (a : Poly) : NTT (pscale c a) = pscale c (NTT a) := by
  apply poly_ext
  intro k hk
  rw [get!_pscale, NTT_eval _ k hk, NTT_eval _ k hk, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [get!_pscale]; ring)

theorem NTT_injective (a b : Poly) (h : NTT a = NTT b) : a = b := by
  rw [← NTTInv_NTT a, ← NTTInv_NTT b, h]

/-- `NTTInv` is additive. -/
theorem NTTInv_add (a b : Poly) : NTTInv (a + b) = NTTInv a + NTTInv b := by
  apply NTT_injective
  rw [NTT_add, NTT_NTTInv, NTT_NTTInv, NTT_NTTInv]

/-- `NTTInv` is homogeneous over `Zq`. -/
theorem NTTInv_smul (c : Zq) (a : Poly) : NTTInv (pscale c a) = pscale c (NTTInv a) := by
  apply NTT_injective
  rw [NTT_smul, NTT_NTTInv, NTT_NTTInv]

/-! ## The negacyclic product -/

/-- The product in `Z_q[X] / (X^256 + 1)`: coefficient `k` is the sum of `a_i b_j` over `i + j = k`, minus the
sum over `i + j = k + 256` (because `X^256 = -1`). -/
def negaMul (a b : Poly) : Poly :=
  Vector.ofFn fun k : Fin 256 =>
    ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
      if i + j = k.val then a[i]! * b[j]!
      else if i + j = k.val + 256 then -(a[i]! * b[j]!) else 0

theorem negaMul_get (a b : Poly) (k : Nat) (hk : k < 256) :
    (negaMul a b)[k]! = ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
      if i + j = k then a[i]! * b[j]! else if i + j = k + 256 then -(a[i]! * b[j]!) else 0 := by
  rw [vget! _ hk]
  simp [negaMul]

theorem term_sum (A r : Zq) (hr : r ^ 256 = -1) (i j : Nat) (hi : i < 256) (hj : j < 256) :
    ∑ m ∈ Finset.range 256, (if i + j = m then A else if i + j = m + 256 then -A else 0) * r ^ m
      = A * r ^ i * r ^ j := by
  by_cases h : i + j < 256
  · rw [Finset.sum_eq_single (i + j)]
    · rw [if_pos rfl, pow_add]; ring
    · intro m _ hne
      rw [if_neg (by omega), if_neg (by omega)]; simp
    · intro h'; exact absurd (Finset.mem_range.2 h) h'
  · rw [Finset.sum_eq_single (i + j - 256)]
    · rw [if_neg (by omega), if_pos (by omega)]
      have e : i + j = (i + j - 256) + 256 := by omega
      have hp : r ^ i * r ^ j = - r ^ (i + j - 256) := by
        rw [← pow_add]
        conv_lhs => rw [e]
        rw [pow_add, hr]; ring
      rw [mul_assoc, hp]; ring
    · intro m hm hne
      have hm' := Finset.mem_range.1 hm
      rw [if_neg (by omega), if_neg (by omega)]; simp
    · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'

theorem conv_eval (a b : Poly) (r : Zq) (hr : r ^ 256 = -1) :
    ∑ m ∈ Finset.range 256, (negaMul a b)[m]! * r ^ m =
      (∑ i ∈ Finset.range 256, a[i]! * r ^ i) * ∑ j ∈ Finset.range 256, b[j]! * r ^ j := by
  rw [Finset.sum_mul_sum]
  have h1 : ∀ m ∈ Finset.range 256, (negaMul a b)[m]! * r ^ m =
      ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
        (if i + j = m then a[i]! * b[j]! else if i + j = m + 256 then -(a[i]! * b[j]!) else 0) * r ^ m := by
    intro m hm
    rw [negaMul_get a b m (Finset.mem_range.1 hm), Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [term_sum _ r hr i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]
  ring

/-! ## `MultiplyNTT` is pointwise -/

/-- One iteration of the loop of `MultiplyNTT`. -/
def pwF (a b c : Poly) (j : Nat) : Poly := c.set! j (a[j]! * b[j]!)

theorem MultiplyNTT_eq_fold (a b : Poly) :
    MultiplyNTT a b = (List.range' 0 256).foldl (pwF a b) Poly.zero := by
  simp [MultiplyNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

theorem zero_get! (k : Nat) : Poly.zero[k]! = 0 := by
  by_cases hk : k < 256
  · rw [vget! _ hk]; simp [Poly.zero]
  · rw [getElem!_neg Poly.zero k (by simpa using hk), default_zq]

theorem pw_fold_get (a b : Poly) : ∀ n, n ≤ 256 → ∀ k,
    ((List.range' 0 n).foldl (pwF a b) Poly.zero)[k]! = if k < n then a[k]! * b[k]! else 0 := by
  intro n
  induction n with
  | zero => intro _ k; simp [zero_get!]
  | succ n ih =>
    intro hn k
    have ih := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [pwF, get!_set!, ih, Nat.zero_add, Nat.one_mul]
    grind

theorem MultiplyNTT_get (a b : Poly) (k : Nat) (hk : k < 256) :
    (MultiplyNTT a b)[k]! = a[k]! * b[k]! := by
  rw [MultiplyNTT_eq_fold, pw_fold_get a b 256 le_rfl, if_pos hk]

/-- `NTT` turns the product of `R_q` into the pointwise product of `T_q`. -/
theorem NTT_negaMul (a b : Poly) : NTT (negaMul a b) = MultiplyNTT (NTT a) (NTT b) := by
  apply poly_ext
  intro k hk
  rw [MultiplyNTT_get _ _ k hk, NTT_eval _ k hk, NTT_eval _ k hk, NTT_eval _ k hk,
    conv_eval a b _ (rt8_pow ⟨k, hk⟩)]

/-- **Convolution theorem.** `NTT⁻¹(NTT a ∘ NTT b) = a · b` in `Z_q[X] / (X^256 + 1)`. -/
theorem NTTInv_MultiplyNTT (a b : Poly) :
    NTTInv (MultiplyNTT (NTT a) (NTT b)) = negaMul a b := by
  rw [← NTT_negaMul, NTTInv_NTT]

/-! ## The norm bound -/

theorem foldl_max_le {β : Type} (f : β → Nat) (l : List β) : ∀ m0 B : Nat,
    l.foldl (fun m x => max m (f x)) m0 ≤ B ↔ m0 ≤ B ∧ ∀ x ∈ l, f x ≤ B := by
  induction l with
  | nil => intro m0 B; simp
  | cons x l ih =>
    intro m0 B
    simp only [List.foldl_cons, ih, max_le_iff, List.mem_cons, forall_eq_or_imp]
    tauto

/-- `‖v‖∞ ≤ B` iff every entry has norm at most `B`. -/
theorem ntt_infNorm_vec_le_iff {α : Type} [InfNorm α] {n : Nat} (v : Vector α n) (B : Nat) :
    ‖v‖∞ ≤ B ↔ ∀ i (h : i < n), ‖v[i]‖∞ ≤ B := by
  show v.foldl (fun m x => max m (InfNorm.infNorm x)) 0 ≤ B ↔ _
  rw [Vector.foldl, ← Array.foldl_toList, foldl_max_le]
  simp only [Nat.zero_le, true_and, List.mem_iff_getElem]
  constructor
  · intro h i hi
    exact h _ ⟨i, by simpa using hi, by simp⟩
  · rintro h x ⟨i, hi, rfl⟩
    have hi' : i < n := by simpa using hi
    simpa using h i hi'

/-- The integer negacyclic convolution, coefficient `k`. -/
def convZ (c s : RPoly) (k : Nat) : Int :=
  ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
    if i + j = k then c[i]! * s[j]! else if i + j = k + 256 then -(c[i]! * s[j]!) else 0

theorem toZq_get! (c : RPoly) (i : Nat) : (RPoly.toZq c)[i]! = ((c[i]! : Int) : Zq) := by
  by_cases hi : i < 256
  · rw [vget! _ hi, vgetG c hi]; simp [RPoly.toZq]
  · rw [getElem!_neg (RPoly.toZq c) i (by simpa using hi), getElem!_neg c i (by simpa using hi),
      default_zq]
    simp [show (default : Int) = 0 from rfl]

theorem negaMul_toZq_get (c s : RPoly) (k : Nat) (hk : k < 256) :
    (negaMul (RPoly.toZq c) (RPoly.toZq s))[k]! = ((convZ c s k : Int) : Zq) := by
  rw [negaMul_get _ _ k hk]
  unfold convZ
  push_cast
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [toZq_get!]

theorem rowSum_abs (s : RPoly) (η : Nat) (hs : ∀ j, j < 256 → (s[j]!).natAbs ≤ η) (i k : Nat)
    (hi : i < 256) (hk : k < 256) :
    |∑ j ∈ Finset.range 256, (if i + j = k then s[j]! else if i + j = k + 256 then -s[j]! else 0)|
      ≤ (η : Int) := by
  by_cases h : i ≤ k
  · rw [Finset.sum_eq_single (k - i)]
    · rw [if_pos (by omega), Int.abs_eq_natAbs]
      exact_mod_cast hs (k - i) (by omega)
    · intro j hj hne
      have := Finset.mem_range.1 hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'
  · rw [Finset.sum_eq_single (k + 256 - i)]
    · rw [if_neg (by omega), if_pos (by omega), abs_neg, Int.abs_eq_natAbs]
      exact_mod_cast hs (k + 256 - i) (by omega)
    · intro j hj hne
      have := Finset.mem_range.1 hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h'; exact absurd (Finset.mem_range.2 (by omega)) h'

theorem convZ_abs (c s : RPoly) (τ η : Nat)
    (hc : ∀ i, i < 256 → c[i]! = 0 ∨ c[i]! = 1 ∨ c[i]! = -1)
    (hτ : ((Finset.range 256).filter (fun i => c[i]! ≠ 0)).card ≤ τ)
    (hs : ∀ j, j < 256 → (s[j]!).natAbs ≤ η) (k : Nat) (hk : k < 256) :
    |convZ c s k| ≤ ((τ * η : Nat) : Int) := by
  have h1 : convZ c s k = ∑ i ∈ Finset.range 256, c[i]! *
      ∑ j ∈ Finset.range 256, (if i + j = k then s[j]! else if i + j = k + 256 then -s[j]! else 0) := by
    unfold convZ
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs <;> ring
  have h2 : ∀ i ∈ Finset.range 256, |c[i]! *
      ∑ j ∈ Finset.range 256, (if i + j = k then s[j]! else if i + j = k + 256 then -s[j]! else 0)|
        ≤ (if c[i]! ≠ 0 then (1 : Int) else 0) * η := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hr := rowSum_abs s η hs i k hi' hk
    rw [abs_mul]
    rcases hc i hi' with h | h | h
    · simp [h]
    · simp [h]; exact hr
    · simp [h]; exact hr
  calc |convZ c s k| ≤ ∑ i ∈ Finset.range 256, |c[i]! *
        ∑ j ∈ Finset.range 256, (if i + j = k then s[j]! else if i + j = k + 256 then -s[j]! else 0)| := by
          rw [h1]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range 256, (if c[i]! ≠ 0 then (1 : Int) else 0) * η := Finset.sum_le_sum h2
    _ = ((Finset.range 256).filter (fun i => c[i]! ≠ 0)).card * (η : Int) := by
          rw [← Finset.sum_mul, Finset.sum_boole]
    _ ≤ ((τ * η : Nat) : Int) := by
          push_cast
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hτ) (by positivity)

/-- A small integer is its own centered residue. -/
theorem modPM_intCast (T : Int) (h1 : T ≤ 4190208) (h2 : -4190208 ≤ T) : Zq.modPM (T : Zq) = T := by
  have hc := Zq.modPM_cast (T : Zq)
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (Zq.modPM (T : Zq)) T q).1 hc
  have hl := modPM_lower ((T : Zq).val : Int) q (by decide)
  have hu := modPM_upper ((T : Zq).val : Int) q (by decide)
  have hq : ((q : Nat) : Int) = 8380417 := rfl
  have hl' : -4190208 ≤ Zq.modPM (T : Zq) := by
    have : (((q + 1) / 2 : Nat) : Int) = 4190209 := rfl
    unfold Zq.modPM; omega
  have hu' : Zq.modPM (T : Zq) ≤ 4190208 := by
    have : ((q / 2 : Nat) : Int) = 4190208 := rfl
    unfold Zq.modPM; omega
  rw [hq] at hd
  obtain ⟨t, ht⟩ := hd
  omega

theorem ScalarVectorNTT_get {ℓ : Nat} (C : Poly) (V : Vector Poly ℓ) (i : Nat) (hi : i < ℓ) :
    (ScalarVectorNTT C V)[i] = MultiplyNTT C V[i] := by
  have h1 : ScalarVectorNTT C V =
      (List.range' 0 ℓ).foldl (fun (c : Vector Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero) := by
    simp [Spec.ScalarVectorNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have key : ∀ n, n ≤ ℓ → ∀ i (hi : i < ℓ),
      ((List.range' 0 n).foldl (fun (c : Vector Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero))[i] = if i < n then MultiplyNTT C V[i] else Poly.zero := by
    intro n
    induction n with
    | zero => intro _ i hi; simp
    | succ n ih =>
      intro hn i hi
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [Nat.zero_add, Nat.one_mul]
      have ih' := ih (by omega) i hi
      generalize (List.foldl (fun (c : Vector Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero) (List.range' 0 n)) = F at ih' ⊢
      show (F.setIfInBounds n (MultiplyNTT C V[n]!))[i] = _
      rw [Vector.getElem_setIfInBounds hi, ih']
      by_cases h : n = i
      · subst h; simp [vgetG V hi]
      · rw [if_neg h]
        by_cases h2 : i < n
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
  rw [h1, key ℓ le_rfl i hi, if_pos hi]

/-- **The norm bound for `c s₁` and `c s₂` (Algorithm 7, steps 18-19).**
For a challenge `c` whose coefficients are in `{-1, 0, 1}` with at most `τ` of them nonzero, and a vector `s` of
polynomials with `‖s‖∞ ≤ η`, the product `c s` computed as in the signer,
`NTT⁻¹(ĉ ∘ ŝ)` with `ĉ = NTT c` and `ŝ = NTT s`, has `‖c s‖∞ ≤ τ η`. The side condition `2 τ η < q` says there is
no wraparound modulo `q`; it holds for all three parameter sets (`τ η ≤ 196`). -/
theorem cs_norm_bound {n : Nat} (τ η : Nat) (c : RPoly) (s : Vector RPoly n)
    (hc : ∀ i, i < 256 → c[i]! = 0 ∨ c[i]! = 1 ∨ c[i]! = -1)
    (hτ : ((Finset.range 256).filter (fun i => c[i]! ≠ 0)).card ≤ τ)
    (hs : ‖s‖∞ ≤ η) (hbound : 2 * (τ * η) < q) :
    ‖NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (s.map RPoly.toZq)))‖∞ ≤ τ * η := by
  rw [ntt_infNorm_vec_le_iff]
  intro i hi
  have hsi := (ntt_infNorm_vec_le_iff s η).1 hs i hi
  have hcoef : ∀ j, j < 256 → (s[i][j]!).natAbs ≤ η := by
    intro j hj
    have := (ntt_infNorm_vec_le_iff s[i] η).1 hsi j hj
    rw [vgetG _ hj]; exact this
  have hel : (NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (s.map RPoly.toZq))))[i] =
      negaMul c.toZq s[i].toZq := by
    simp only [NTTInvVec, NTTVec, Vector.getElem_map, ScalarVectorNTT_get _ _ i hi]
    exact NTTInv_MultiplyNTT _ _
  rw [hel, ntt_infNorm_vec_le_iff]
  intro k hk
  show (Zq.modPM (negaMul c.toZq s[i].toZq)[k]).natAbs ≤ τ * η
  rw [← vget! _ hk, negaMul_toZq_get c s[i] k hk]
  have hb := convZ_abs c s[i] τ η hc hτ hcoef k hk
  have hq : (q : Nat) = 8380417 := rfl
  have hb2 := abs_le.1 hb
  rw [modPM_intCast _ (by push_cast at hb2; omega) (by push_cast at hb2; omega)]
  have := Int.abs_eq_natAbs (convZ c s[i] k)
  push_cast at hb
  omega

/-- `cs_norm_bound` with the parameter-set names of Algorithm 7: `‖c s‖∞ ≤ β` for `β = τ η`. -/
theorem cs_norm_bound_params {n : Nat} (p : Params) (c : RPoly) (s : Vector RPoly n)
    (hc : ∀ i, i < 256 → c[i]! = 0 ∨ c[i]! = 1 ∨ c[i]! = -1)
    (hτ : ((Finset.range 256).filter (fun i => c[i]! ≠ 0)).card ≤ p.τ)
    (hs : ‖s‖∞ ≤ p.η) (hbound : 2 * p.β < q) :
    ‖NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (s.map RPoly.toZq)))‖∞ ≤ p.β :=
  cs_norm_bound p.τ p.η c s hc hτ hs hbound

end Proofs.Corr
