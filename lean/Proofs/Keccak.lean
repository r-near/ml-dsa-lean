import Proofs.KeccakSponge

/-!
# The SHAKE interface for the samplers, KeyGen, Sign and Verify

`Proofs/KeccakPerm.lean` proves `keccak_f1600_spec`: the extracted permutation is `Spec.KeccakF1600` on lanes.
`Proofs/KeccakSponge.lean` proves the `absorb`, `finalize`, `squeeze` specs against two relations on the extracted
context `Impl.keccak.Shake`. This file adds the constructors, the corollaries callers use, and the headline forms.

## The relations (defined in `Proofs/KeccakSponge.lean`)

* `ShakeAbs st r M`: `st` is a fresh SHAKE context of rate `r` bytes (168 = SHAKE128 = `G`, 136 = SHAKE256 = `H`)
  that has absorbed exactly the bytes `M`.
* `ShakeSqz st r M n`: `st` has been finalized after absorbing `M` and has squeezed exactly `n` bytes.

## The specs (all `@[step]`, so `step*` chains a whole sponge computation)

| Rust | Spec |
|---|---|
| `Shake::shake128()` / `shake256()` | `ShakeAbs _ 168 []` / `ShakeAbs _ 136 []` |
| `absorb st s`   | `ShakeAbs st r M → ShakeAbs st' r (M ++ bytes s)` |
| `finalize st`   | `ShakeAbs st r M → ShakeSqz st' r M 0` |
| `squeeze st out`| `ShakeSqz st r M pos → ShakeSqz st' r M (pos + out.len) ∧ bytes out' = (sponge r M (pos + out.len)).drop pos` |

`squeeze_G_spec` / `squeeze_H_spec` restate the last line for `r = 168` / `136` with `Spec.SHAKE128` / `SHAKE256`
and any stream length `N ≥ pos + out.len` (the shape `Spec.Ctx.Squeeze` reads: `((SHAKE M N).drop pos).take n`).

## Satisfiability

The premises are satisfiable: `shake128_abs` / `shake256_abs` exhibit a context with `ShakeAbs _ 168 []` /
`ShakeAbs _ 136 []` (the constructors), and `finalize_exists` exhibits a context with `ShakeSqz _ 136 [] 0`
(finalizing a fresh one). `shake256_correct` is the end-to-end statement for one-shot SHAKE256.

## Advice for callers

* Keep the context's invariant as a hypothesis (`ShakeAbs ctx 168 M`, later `ShakeSqz ctx 168 M n`) and let
  `step*` use the specs; the message `M` and the offset `n` are found by unification with that hypothesis.
* Several `absorb` calls compose: `ShakeAbs … (M ++ bytes a ++ bytes b)`; `absorb_append_eq` says absorbing `a`
  then `b` gives the same context as absorbing any `c` with `bytes c = bytes a ++ bytes b`.
* Squeezing in pieces composes by the offset: after `squeeze` of `n₁` then `n₂` bytes the context is
  `ShakeSqz … (pos + n₁ + n₂)` and the pieces are consecutive slices of the stream.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Constructors (witness `ShakeAbs`) -/

@[step]
theorem shake128_spec : keccak.Shake.shake128 ⦃ st => ShakeAbs st 168 [] ⦄ := by
  unfold keccak.Shake.shake128
  simp only [WP.spec_ok]
  refine ⟨by decide, by decide, rfl, rfl, ?_⟩
  show toLanes (Array.repeat 25#usize 0#u64) = _
  rw [toLanes_repeat_zero, KM.absSt_nil]

@[step]
theorem shake256_spec : keccak.Shake.shake256 ⦃ st => ShakeAbs st 136 [] ⦄ := by
  unfold keccak.Shake.shake256
  simp only [WP.spec_ok]
  refine ⟨by decide, by decide, rfl, rfl, ?_⟩
  show toLanes (Array.repeat 25#usize 0#u64) = _
  rw [toLanes_repeat_zero, KM.absSt_nil]

/-- Satisfiability witness: `shake128()` returns a context with `ShakeAbs _ 168 []`. -/
theorem shake128_abs : ∃ st, keccak.Shake.shake128 = ok st ∧ ShakeAbs st 168 [] := by
  obtain ⟨st, h, hs⟩ := WP.spec_imp_exists shake128_spec
  exact ⟨st, h, hs⟩

/-- Satisfiability witness: `shake256()` returns a context with `ShakeAbs _ 136 []`. -/
theorem shake256_abs : ∃ st, keccak.Shake.shake256 = ok st ∧ ShakeAbs st 136 [] := by
  obtain ⟨st, h, hs⟩ := WP.spec_imp_exists shake256_spec
  exact ⟨st, h, hs⟩

/-- Satisfiability witness for `ShakeSqz`: finalizing a fresh SHAKE256 context. -/
theorem finalize_exists :
    ∃ st st', keccak.Shake.shake256 = ok st ∧ keccak.Shake.finalize st = ok st' ∧ ShakeSqz st' 136 [] 0 := by
  obtain ⟨st, h, hs⟩ := shake256_abs
  obtain ⟨st', h', hs'⟩ := WP.spec_imp_exists (finalize_spec st 136 [] hs)
  exact ⟨st, st', h, h', hs'⟩

/-! ## Squeeze -/

/-- **Squeeze.** From a finalized context that has squeezed `pos` bytes, squeezing `out.len` more bytes writes
`(sponge r M (pos + out.len)).drop pos`, the next bytes of the stream, and advances the offset. -/
@[step]
theorem squeeze_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (pos : Nat) (out : Slice U8)
    (h : ShakeSqz st r M pos) :
    keccak.Shake.squeeze st out ⦃ p =>
      ShakeSqz p.1 r M (pos + out.val.length) ∧
      bytes p.2 = (Spec.Keccak.sponge r M (pos + out.val.length)).drop pos ⦄ := by
  unfold keccak.Shake.squeeze
  exact squeeze_loop_spec st r M pos out h

/-- The next bytes of the stream are a window of any longer prefix (the prefix lemma). -/
theorem sponge_window (r : Nat) (hr : 0 < r) (M : List UInt8) (pos n N : Nat) (hN : pos + n ≤ N) :
    (Spec.Keccak.sponge r M (pos + n)).drop pos = ((Spec.Keccak.sponge r M N).drop pos).take n := by
  have h := Spec.Keccak.squeeze_prefix r hr (pos + n) (N - (pos + n))
    (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M))
  have e : pos + n + (N - (pos + n)) = N := by omega
  rw [e] at h
  show (Spec.Keccak.squeeze r (pos + n) _).drop pos = _
  rw [h, List.drop_take]
  show (List.take (pos + n - pos) (List.drop pos (Spec.Keccak.squeeze r N _))) = _
  congr 1
  omega

/-- **Squeeze for `G = SHAKE128`** (rate 168): the bytes are the window `[pos, pos + n)` of `SHAKE128 M N`
for every `N ≥ pos + n`. -/
theorem squeeze_G_spec (st : keccak.Shake) (M : List UInt8) (pos : Nat) (out : Slice U8)
    (h : ShakeSqz st 168 M pos) :
    keccak.Shake.squeeze st out ⦃ p =>
      ShakeSqz p.1 168 M (pos + out.val.length) ∧
      bytes p.2 = (Spec.SHAKE128 M (pos + out.val.length)).drop pos ∧
      ∀ N, pos + out.val.length ≤ N →
        bytes p.2 = ((Spec.SHAKE128 M N).drop pos).take out.val.length ⦄ := by
  apply WP.spec_mono (squeeze_spec st 168 M pos out h)
  rintro p ⟨h1, h2⟩
  exact ⟨h1, h2, fun N hN => by rw [h2]; exact sponge_window 168 (by omega) M pos _ N hN⟩

/-- **Squeeze for `H = SHAKE256`** (rate 136). -/
theorem squeeze_H_spec (st : keccak.Shake) (M : List UInt8) (pos : Nat) (out : Slice U8)
    (h : ShakeSqz st 136 M pos) :
    keccak.Shake.squeeze st out ⦃ p =>
      ShakeSqz p.1 136 M (pos + out.val.length) ∧
      bytes p.2 = (Spec.SHAKE256 M (pos + out.val.length)).drop pos ∧
      ∀ N, pos + out.val.length ≤ N →
        bytes p.2 = ((Spec.SHAKE256 M N).drop pos).take out.val.length ⦄ := by
  apply WP.spec_mono (squeeze_spec st 136 M pos out h)
  rintro p ⟨h1, h2⟩
  exact ⟨h1, h2, fun N hN => by rw [h2]; exact sponge_window 136 (by omega) M pos _ N hN⟩

/-! ## Absorbing in pieces -/

/-- A context is determined by its absorbed message. -/
theorem ShakeAbs.unique {s t : keccak.Shake} {r : Nat} {M : List UInt8} (hs : ShakeAbs s r M)
    (ht : ShakeAbs t r M) : s = t := by
  cases s with
  | mk ss sp sr =>
    cases t with
    | mk ts tp tr =>
      have h1 : ss = ts := toLanes_inj (hs.state.trans ht.state.symm)
      have h2 : sp = tp := UScalar.eq_of_val_eq (hs.pos.trans ht.pos.symm)
      have h3 : sr = tr := UScalar.eq_of_val_eq (hs.rate.trans ht.rate.symm)
      subst h1 h2 h3
      rfl

/-- Absorbing `a` then `b` is absorbing `M ++ bytes a ++ bytes b`. -/
theorem absorb_two_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (a b : Slice U8)
    (h : ShakeAbs st r M) :
    (do let s1 ← keccak.Shake.absorb st a; keccak.Shake.absorb s1 b) ⦃ s =>
      ShakeAbs s r (M ++ (bytes a ++ bytes b)) ⦄ := by
  step*

/-- **Two-slice absorb.** Absorbing `a` then `b` yields the same context as absorbing any `c` with
`bytes c = bytes a ++ bytes b`. (Used for `M' = m_prefix ‖ m`.) -/
theorem absorb_append_eq (st : keccak.Shake) (r : Nat) (M : List UInt8) (a b c : Slice U8)
    (h : ShakeAbs st r M) (hc : bytes c = bytes a ++ bytes b) :
    ∃ s, keccak.Shake.absorb st c = ok s ∧
      (do let s1 ← keccak.Shake.absorb st a; keccak.Shake.absorb s1 b) = ok s := by
  obtain ⟨s, hs, hsa⟩ := WP.spec_imp_exists (absorb_spec st r M c h)
  obtain ⟨t, ht, hta⟩ := WP.spec_imp_exists (absorb_two_spec st r M a b h)
  rw [hc] at hsa
  have : s = t := ShakeAbs.unique hsa hta
  subst this
  exact ⟨s, hs, ht⟩

/-- **Squeezing in pieces.** Two consecutive squeezes read consecutive windows of the one stream: the
concatenation of the two outputs is `(sponge r M (pos + n₁ + n₂)).drop pos`, and the final context has offset
`pos + n₁ + n₂`. (The pattern of `sample_in_ball`: 8 bytes, then single bytes.) -/
theorem squeeze_twice_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (pos : Nat) (o1 o2 : Slice U8)
    (h : ShakeSqz st r M pos) :
    (do let p ← keccak.Shake.squeeze st o1
        let q ← keccak.Shake.squeeze p.1 o2
        ok (q.1, p.2, q.2)) ⦃ t =>
      ShakeSqz t.1 r M (pos + o1.val.length + o2.val.length) ∧
      bytes t.2.1 ++ bytes t.2.2 =
        (Spec.Keccak.sponge r M (pos + o1.val.length + o2.val.length)).drop pos ⦄ := by
  have hr := h.1
  step*
  refine ⟨q_post1, ?_⟩
  rw [p_post2, q_post2]
  rw [sponge_window r hr M pos o1.val.length (pos + o1.val.length + o2.val.length) (by omega),
    ← List.drop_drop]
  exact List.take_append_drop _ _

/-! ## End to end: one-shot SHAKE256 -/

/-- `SHAKE256` through the extracted API: init, absorb one slice, finalize, squeeze `out.len` bytes. -/
theorem shake256_correct (m out : Slice U8) :
    ∃ out', (do
        let ctx ← keccak.Shake.shake256
        let ctx ← keccak.Shake.absorb ctx m
        let ctx ← keccak.Shake.finalize ctx
        let p ← keccak.Shake.squeeze ctx out
        ok p.2) = ok out' ∧
      bytes out' = Spec.SHAKE256 (bytes m) out.val.length := by
  have h : (do
        let ctx ← keccak.Shake.shake256
        let ctx ← keccak.Shake.absorb ctx m
        let ctx ← keccak.Shake.finalize ctx
        let p ← keccak.Shake.squeeze ctx out
        ok p.2) ⦃ out' => bytes out' = Spec.SHAKE256 (bytes m) out.val.length ⦄ := by
    step*
    simp only [List.nil_append, Nat.zero_add, List.drop_zero] at p_post2
    exact p_post2
  obtain ⟨o, ho, hb⟩ := WP.spec_imp_exists h
  exact ⟨o, ho, hb⟩

end Proofs
