import Proofs.Repr
import Spec.Keccak

/-!
# Keccak: the lane view of an extracted state

`toLanes a` is the spec's `Spec.Keccak.State = Vector UInt64 25` denoted by an extracted `[u64; 25]`.
Everything in `Proofs/KeccakPerm.lean` (the permutation) and `Proofs/KeccakSponge.lean` (the sponge) speaks
through it.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-- The `UInt64` with the same bits as an extracted `U64`. -/
def toU64 (x : U64) : UInt64 := ⟨x.bv⟩

/-- The lanes of an extracted Keccak state, as the spec's state. -/
def toLanes (a : Array U64 25#usize) : Spec.Keccak.State :=
  Vector.ofFn fun i : Fin 25 => toU64 (a.val[i.val]'(by rw [a.property]; exact i.isLt))

theorem len25 (a : Array U64 25#usize) : a.val.length = 25 := a.property

theorem toU64_xor (x y : U64) : toU64 (x ^^^ y) = toU64 x ^^^ toU64 y := by
  simp [toU64]

theorem toLanes_get (a : Array U64 25#usize) (k : Nat) (hk : k < 25) :
    (toLanes a)[k] = toU64 (a.val[k]'(by rw [len25 a]; exact hk)) := by
  simp [toLanes]

theorem toLanes_getElem! (a : Array U64 25#usize) (k : Nat) (hk : k < a.val.length) :
    (toLanes a)[k]! = toU64 a.val[k] := by
  have hk' : k < 25 := by have := len25 a; omega
  rw [getElem!_pos _ _ (by simpa using hk'), toLanes_get a k hk']

theorem toLanes_set (a : Array U64 25#usize) (i : Usize) (x : U64) :
    toLanes (a.set i x) = (toLanes a).set! i.val (toU64 x) := by
  apply Vector.ext
  intro k hk
  rw [set!_eq', Vector.getElem_setIfInBounds hk]
  simp only [toLanes, Vector.getElem_ofFn, Array.set_val_eq]
  by_cases h : i.val = k
  · subst h; simp
  · simp [h]

theorem toLanes_repeat_zero : toLanes (Array.repeat 25#usize 0#u64) = Spec.Keccak.zeroState := by
  apply Vector.ext
  intro k hk
  simp only [toLanes, Spec.Keccak.zeroState, Vector.getElem_ofFn, Vector.getElem_replicate, Array.repeat_val,
    List.getElem_replicate]
  rfl

theorem toLanes_inj {a b : Array U64 25#usize} (h : toLanes a = toLanes b) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [len25 a, len25 b])
  intro k h1 h2
  have hk : k < 25 := by rw [len25 a] at h1; exact h1
  have := congrArg (fun p : Spec.Keccak.State => p[k]) h
  simp only [toLanes, Vector.getElem_ofFn, toU64] at this
  have := congrArg UInt64.toBitVec this
  exact UScalar.eq_of_val_eq (by simpa [UScalar.bv_toNat] using congrArg BitVec.toNat this) |>.symm ▸ rfl

end Proofs
