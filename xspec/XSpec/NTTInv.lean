import XSpec.NTT

/-!
# Algorithm 42 (`NTT⁻¹`) against ocaml-pq's `MLDSA.invNttSpec`

Same simulation as `XSpec.NTT`: one inner iteration, one layer, eight layers, then the scaling loop.
-/

open Spec

namespace XSpec

theorem get!_set!_self (w : Poly) {i : ℕ} (hi : i < 256) (x : Zq) : (w.set! i x)[i]! = x := by
  rw [get!_set!, if_pos ⟨rfl, hi⟩]

/-! ## Our loops as folds -/

/-- One iteration of the inner `for j` loop of `nttInvLayer`. -/
def invStep (len : Nat) (z : Zq) (w : Poly) (j : Nat) : Poly :=
  let w1 := w.set! j (w[j]! + w[j + len]!)
  let w2 := w1.set! (j + len) (w[j]! - w1[j + len]!)
  w2.set! (j + len) (z * w2[j + len]!)

/-- One iteration of the block loop of `nttInvLayer`, on the state `(w, m, start)`. -/
def invBlockF (len : Nat) (b : Poly × Nat × Nat) (_a : Nat) : Poly × Nat × Nat :=
  ((List.range' b.2.2 len).foldl (invStep len (-zeta (b.2.1 - 1))) b.1, b.2.1 - 1, b.2.2 + 2 * len)

def invBlockFold (len m0 : Nat) (w0 : Poly) (i : Nat) : Poly × Nat × Nat :=
  (List.range' 0 i).foldl (invBlockF len) (w0, m0, 0)

theorem nttInvLayer_eq (len : Nat) (w : Poly) (m : Nat) :
    nttInvLayer len w m =
      ((invBlockFold len m w (256 / (2 * len))).1, (invBlockFold len m w (256 / (2 * len))).2.1) := by
  unfold nttInvLayer invBlockFold
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, -neg_mul]
  constructor <;> rfl

theorem invBlockFold_succ (len m0 : Nat) (w0 : Poly) (i : Nat) :
    invBlockFold len m0 w0 (i + 1) = invBlockF len (invBlockFold len m0 w0 i) i := by
  simp [invBlockFold, List.range'_concat, List.foldl_append]

theorem invBlockFold_zero (len m0 : Nat) (w0 : Poly) : invBlockFold len m0 w0 0 = (w0, m0, 0) := rfl

theorem invBlockFold_fst (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (invBlockFold len m0 w0 i).2.1 = m0 - i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [invBlockFold_succ]; simp [invBlockF, ih]; omega

theorem invBlockFold_start (len m0 : Nat) (w0 : Poly) (i : Nat) :
    (invBlockFold len m0 w0 i).2.2 = 2 * len * i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [invBlockFold_succ]; simp [invBlockF, ih]; ring

def scaleF (b : Poly) (a : Nat) : Poly := Vector.set! b a (8347681 * b[a]!)

/-- Algorithm 42 is its eight layers followed by the scaling loop. -/
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

/-! ## The simulation -/

/-- Their inner-loop body (`invSpecInner`) as a function of the state and the offset. -/
def Ginv (len : ℕ) (z : Zq) (w : ℕ → Zq) (j : ℕ) : ℕ → Zq :=
  let t := w j
  let w1 := Function.update w j (t + w (j + len))
  let w2 := Function.update w1 (j + len) (t - w1 (j + len))
  Function.update w2 (j + len) (z * w2 (j + len))

theorem invStep_I (len : ℕ) (z : Zq) (hlen : 0 < len) (W : Poly) (j : ℕ) (hj : j + len < 256) :
    I (invStep len z W j) = Ginv len z (I W) j := by
  have e1 : (W.set! j (W[j]! + W[j + len]!))[j + len]! = W[j + len]! := by
    rw [get!_set!, if_neg (by omega)]
  unfold invStep
  dsimp only
  rw [e1, get!_set!_self _ hj, I_set _ hj, I_set _ hj, I_set _ (by omega)]
  have hne : j ≠ j + len := by omega
  have hl : len ≠ 0 := by omega
  simp only [Ginv, I]
  simp [Function.update_apply, hne, hl]
  rfl

theorem inv_inner_sim (len : ℕ) (z : Zq) (hlen : 0 < len) (s : ℕ) (hs : s + 2 * len ≤ 256) (W : Poly) :
    ∀ n, n ≤ len → I ((List.range' s n).foldl (invStep len z) W) =
      (List.range n).foldl (fun w i => Ginv len z w (s + i)) (I W) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show s + 1 * n = s + n by ring, invStep_I len z hlen _ (s + n) (by omega), ih (by omega)]

theorem inv_block_sim (len m : ℕ) (hlen : 1 ≤ len) (B : ℕ) (hB : 2 * len * B = 256) (w : Poly) :
    ∀ d i, i + d = B →
      OcamlPq.MLDSA.invSpecMiddle len hlen (2 * len * i) (m - i) (I (invBlockFold len m w i).1) =
        (I (invBlockFold len m w B).1, m - B) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have : i = B := by omega
    subst this
    rw [OcamlPq.MLDSA.invSpecMiddle, if_neg (by omega)]
  | succ d ih =>
    intro i hi
    have hiB : i < B := by omega
    have hlt : 2 * len * i < 256 := by
      rw [← hB]; exact (Nat.mul_lt_mul_left (by omega)).2 hiB
    rw [OcamlPq.MLDSA.invSpecMiddle, if_pos hlt]
    dsimp only
    have key : I (invBlockFold len m w (i + 1)).1 =
        OcamlPq.MLDSA.invSpecInner (-OcamlPq.MLDSA.zetaSpec (m - i - 1)) len (2 * len * i)
          (I (invBlockFold len m w i).1) := by
      rw [invBlockFold_succ]
      simp only [invBlockF, invBlockFold_fst, invBlockFold_start]
      rw [inv_inner_sim len _ (by omega) (2 * len * i) (by nlinarith) _ len le_rfl, ← zeta_eq]
      unfold OcamlPq.MLDSA.invSpecInner Ginv
      rfl
    have ih' := ih (i + 1) (by omega)
    rw [key] at ih'
    have e1 : 2 * len * (i + 1) = 2 * len * i + 2 * len := by ring
    have e2 : m - (i + 1) = m - i - 1 := by omega
    rw [e1, e2] at ih'
    have e3 : m - i - 1 = m - i - 1 := rfl
    exact ih'

theorem inv_layer_sim (len B m : ℕ) (hlen : 1 ≤ len) (hB : 2 * len * B = 256) (w : Poly) :
    OcamlPq.MLDSA.invSpecMiddle len hlen 0 m (I w) =
      (I (nttInvLayer len w m).1, (nttInvLayer len w m).2) := by
  have hB' : 256 / (2 * len) = B := by
    rw [← hB]; exact Nat.mul_div_cancel_left B (by omega)
  have := inv_block_sim len m hlen B hB w B 0 (by omega)
  rw [nttInvLayer_eq, hB']
  simpa [invBlockFold_zero, invBlockFold_fst] using this

theorem inv_outer_step (len len2 B m : ℕ) (hlen : 1 ≤ len) (hlt : len < 256) (hB : 2 * len * B = 256)
    (h2 : len2 = 2 * len) (hlen2 : 1 ≤ len2) (w : Poly) :
    OcamlPq.MLDSA.invSpecOuter len hlen m (I w) =
      OcamlPq.MLDSA.invSpecOuter len2 hlen2 (nttInvLayer len w m).2 (I (nttInvLayer len w m).1) := by
  rw [OcamlPq.MLDSA.invSpecOuter, if_pos hlt, inv_layer_sim len B m hlen hB w]
  subst h2
  rfl

theorem scale_sim (X : Poly) : ∀ n, n ≤ 256 →
    I ((List.range' 0 n).foldl scaleF X) =
      (List.range n).foldl (fun w j => Function.update w j ((8347681 : Zq) * w j)) (I X) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih (by omega)]
    simp only [scaleF, Nat.zero_add, Nat.one_mul]
    rw [I_set _ (by omega)]
    rfl

/-- **Algorithm 42.** Our `NTTInv` is ocaml-pq's `invNttSpec`, on every index. -/
theorem invNttSpec_eq (w : Poly) : OcamlPq.MLDSA.invNttSpec (I w) = I (NTTInv w) := by
  rw [NTTInv_eq_layers]
  unfold OcamlPq.MLDSA.invNttSpec
  rw [inv_outer_step 1 2 128 256 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 2 4 64 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 4 8 32 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 8 16 16 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 16 32 8 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 32 64 4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 64 128 2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [inv_outer_step 128 256 1 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rw [OcamlPq.MLDSA.invSpecOuter, if_neg (by norm_num)]
  dsimp only
  rw [scale_sim _ 256 le_rfl]

end XSpec
