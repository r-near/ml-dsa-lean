import Spec
import OcamlPq
import Mathlib.Tactic

/-!
# Algorithm 41 (`NTT`) against ocaml-pq's `MLDSA.nttSpec`

Ours is a `Vector Zq 256` updated with `set!` inside `for` loops; theirs is an index function `ℕ → Zq`
updated with `Function.update` inside `while` loops written as well-founded recursions.  The adapter is
`I v = fun i => v[i]!`.  The proof is a simulation: one inner iteration, one layer (block loop), and the
eight layers.  The rewriting of our loops into `foldl`s (`nttLayer_eq`, `NTT_eq_layers`) is the one in
`lean/Proofs/CorrNTT.lean`.
-/

open Spec

namespace XSpec

/-- The index function of a polynomial (zero beyond 256). -/
def I (v : Poly) : ℕ → Zq := fun i => v[i]!

theorem vget!' (w : Poly) {i : Nat} (hi : i < 256) : w[i]! = w[i] :=
  getElem!_pos w i (by simpa using hi)

theorem get!_set! (w : Poly) (i : Nat) (x : Zq) (k : Nat) :
    (w.set! i x)[k]! = if i = k ∧ k < 256 then x else w[k]! := by
  have hs : w.set! i x = w.setIfInBounds i x := rfl
  by_cases hk : k < 256
  · rw [vget!' _ hk, hs, Vector.getElem_setIfInBounds hk]
    by_cases hik : i = k <;> simp [hik, hk]
  · have h1 : ¬ (i = k ∧ k < 256) := fun h => hk h.2
    rw [if_neg h1]
    rw [getElem!_neg (w.set! i x) k (by simpa using hk), getElem!_neg w k (by simpa using hk)]

theorem I_set (v : Poly) {j : ℕ} (hj : j < 256) (x : Zq) :
    I (v.set! j x) = Function.update (I v) j x := by
  funext k
  simp only [I, get!_set!, Function.update_apply]
  by_cases h : k = j
  · subst h; simp [hj]
  · have : ¬ (j = k ∧ k < 256) := fun ⟨h1, _⟩ => h h1.symm
    simp [h, this]

/-! ## Twiddle factors -/

theorem bitRev8_eq (m : ℕ) : BitRev8 m = OcamlPq.MLDSA.bitRev8 m := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [BitRev8, OcamlPq.MLDSA.bitRev8, h8, Nat.shiftRight_eq_div_pow, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem zeta_eq (m : ℕ) : zeta m = OcamlPq.MLDSA.zetaSpec m := by
  simp only [zeta, OcamlPq.MLDSA.zetaSpec, bitRev8_eq]
  rfl

/-! ## Our loops as folds (as in `lean/Proofs/CorrNTT.lean`) -/

/-- One iteration of the inner `for j` loop of `nttLayer`. -/
def fwdStep (len : Nat) (z : Zq) (w : Poly) (j : Nat) : Poly :=
  (w.set! (j + len) (w[j]! - z * w[j + len]!)).set! j
    ((w.set! (j + len) (w[j]! - z * w[j + len]!))[j]! + z * w[j + len]!)

/-- One iteration of the block loop of `nttLayer`, on the state `(ŵ, m, start)`. -/
def fwdBlockF (len : Nat) (b : Poly × Nat × Nat) (_a : Nat) : Poly × Nat × Nat :=
  ((List.range' b.2.2 len).foldl (fwdStep len (zeta (b.2.1 + 1))) b.1, b.2.1 + 1, b.2.2 + 2 * len)

/-- The block loop state after `i` blocks. -/
def fwdBlockFold (len m0 : Nat) (w0 : Poly) (i : Nat) : Poly × Nat × Nat :=
  (List.range' 0 i).foldl (fwdBlockF len) (w0, m0, 0)

theorem nttLayer_eq (len : Nat) (w : Poly) (m : Nat) :
    nttLayer len w m =
      ((fwdBlockFold len m w (256 / (2 * len))).1, (fwdBlockFold len m w (256 / (2 * len))).2.1) := by
  unfold nttLayer fwdBlockFold
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  constructor <;> rfl

theorem fwdBlockFold_succ (len m0 : Nat) (w0 : Poly) (i : Nat) :
    fwdBlockFold len m0 w0 (i + 1) = fwdBlockF len (fwdBlockFold len m0 w0 i) i := by
  simp [fwdBlockFold, List.range'_concat, List.foldl_append]

theorem fwdBlockFold_zero (len m0 : Nat) (w0 : Poly) : fwdBlockFold len m0 w0 0 = (w0, m0, 0) := rfl

theorem fwdBlockFold_fst (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (fwdBlockFold len m0 w0 i).2.1 = m0 + i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [fwdBlockFold_succ]; simp [fwdBlockF, ih]; omega

theorem fwdBlockFold_start (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (fwdBlockFold len m0 w0 i).2.2 = 2 * len * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [fwdBlockFold_succ]; simp [fwdBlockF, ih]; ring

theorem nttLayer_snd (len : Nat) (w : Poly) (m : Nat) :
    (nttLayer len w m).2 = m + 256 / (2 * len) := by
  rw [nttLayer_eq, fwdBlockFold_fst]

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

/-! ## The simulation -/

/-- Their inner-loop body (`nttSpecInner`) as a function of the state and the offset. -/
def G (len : ℕ) (z : Zq) (w : ℕ → Zq) (j : ℕ) : ℕ → Zq :=
  let t := z * w (j + len)
  let w1 := Function.update w (j + len) (w j - t)
  Function.update w1 j (w1 j + t)

theorem fwdStep_I (len : ℕ) (z : Zq) (hlen : 0 < len) (W : Poly) (j : ℕ) (hj : j + len < 256) :
    I (fwdStep len z W j) = G len z (I W) j := by
  have h2 : ((W.set! (j + len) (W[j]! - z * W[j + len]!))[j]!) = W[j]! := by
    rw [get!_set!]
    have : ¬ (j + len = j ∧ j < 256) := by omega
    rw [if_neg this]
  unfold fwdStep
  rw [h2, I_set _ (by omega), I_set _ (by omega)]
  simp only [G, I]
  have hne : j ≠ j + len := by omega
  have hl : len ≠ 0 := by omega
  simp [Function.update_apply, hne, hl]
  rfl

theorem inner_sim (len : ℕ) (z : Zq) (hlen : 0 < len) (s : ℕ) (hs : s + 2 * len ≤ 256) (W : Poly) :
    ∀ n, n ≤ len → I ((List.range' s n).foldl (fwdStep len z) W) =
      (List.range n).foldl (fun w i => G len z w (s + i)) (I W) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show s + 1 * n = s + n by ring, fwdStep_I len z hlen _ (s + n) (by omega), ih (by omega)]

theorem block_sim (len m : ℕ) (hlen : 1 ≤ len) (B : ℕ) (hB : 2 * len * B = 256) (w : Poly) :
    ∀ d i, i + d = B →
      OcamlPq.MLDSA.nttSpecMiddle len hlen (2 * len * i) (m + i) (I (fwdBlockFold len m w i).1) =
        (I (fwdBlockFold len m w B).1, m + B) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have : i = B := by omega
    subst this
    rw [OcamlPq.MLDSA.nttSpecMiddle, if_neg (by omega)]
  | succ d ih =>
    intro i hi
    have hiB : i < B := by omega
    have hlt : 2 * len * i < 256 := by
      rw [← hB]; exact (Nat.mul_lt_mul_left (by omega)).2 hiB
    rw [OcamlPq.MLDSA.nttSpecMiddle, if_pos hlt]
    dsimp only
    have key : I (fwdBlockFold len m w (i + 1)).1 =
        OcamlPq.MLDSA.nttSpecInner (OcamlPq.MLDSA.zetaSpec (m + i + 1)) len (2 * len * i)
          (I (fwdBlockFold len m w i).1) := by
      rw [fwdBlockFold_succ]
      simp only [fwdBlockF, fwdBlockFold_fst, fwdBlockFold_start]
      rw [inner_sim len _ (by omega) (2 * len * i) (by nlinarith) _ len le_rfl, ← zeta_eq]
      unfold OcamlPq.MLDSA.nttSpecInner G
      rfl
    have ih' := ih (i + 1) (by omega)
    rw [key] at ih'
    have e1 : 2 * len * (i + 1) = 2 * len * i + 2 * len := by ring
    have e2 : m + (i + 1) = m + i + 1 := by ring
    rw [e1, e2] at ih'
    exact ih'

theorem layer_sim (len B m : ℕ) (hlen : 1 ≤ len) (hB : 2 * len * B = 256) (w : Poly) :
    OcamlPq.MLDSA.nttSpecMiddle len hlen 0 m (I w) =
      (I (nttLayer len w m).1, (nttLayer len w m).2) := by
  have hB' : 256 / (2 * len) = B := by
    rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  have := block_sim len m hlen B hB w B 0 (by omega)
  rw [nttLayer_eq, hB']
  simpa [fwdBlockFold_zero, fwdBlockFold_fst] using this

theorem outer_step (len len2 B m : ℕ) (hlen : 1 ≤ len) (hB : 2 * len * B = 256) (h2 : len2 = len / 2)
    (w : Poly) :
    OcamlPq.MLDSA.nttSpecOuter len m (I w) =
      OcamlPq.MLDSA.nttSpecOuter len2 (nttLayer len w m).2 (I (nttLayer len w m).1) := by
  rw [OcamlPq.MLDSA.nttSpecOuter, dif_pos hlen, layer_sim len B m hlen hB w, h2]

/-- **Algorithm 41.** Our `NTT` is ocaml-pq's `nttSpec`, on every index. -/
theorem nttSpec_eq (w : Poly) : OcamlPq.MLDSA.nttSpec (I w) = I (NTT w) := by
  rw [NTT_eq_layers]
  unfold OcamlPq.MLDSA.nttSpec
  rw [outer_step 128 64 1 0 (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 64 32 2 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 32 16 4 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 16 8 8 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 8 4 16 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 4 2 32 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 2 1 64 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [outer_step 1 0 128 _ (by norm_num) (by norm_num) (by norm_num)]
  rw [OcamlPq.MLDSA.nttSpecOuter, dif_neg (by norm_num)]

end XSpec
