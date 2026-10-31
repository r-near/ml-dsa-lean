import Aeneas

/-!
# Partial correctness and panic-freedom for the unbounded loops

## The gap

The spec samplers (`RejNTTPoly`, `SampleInBall`, `RejBoundedPoly`) are fuel-bounded and return `Option`; the Rust
loops are unbounded (Aeneas `loop`, a `partial_fixpoint`). The older theorems read "if the spec returns `some x`
at fuel `F`, the Rust returns (the representation of) `x`": total correctness on the inputs where the spec's fuel
suffices. This development proves the converse direction for every input:

* (a) the Rust never returns `fail` (it never panics), and
* (b) if the Rust returns `ok r`, then `r` represents the spec's answer at some fuel `F`.

For Verify (`PartialAPI.lean`, `verify_NN_exact`, `verify_internal_NN_exact`), together with the old theorems,
the Rust agrees with the fuel-bounded spec taken as the limit over fuel: the same answer whenever either side
terminates, and divergence exactly when the spec returns `none` at every fuel (this last part follows from the
three conjuncts of `_exact`; it is not a separate theorem). KeyGen and Sign use the same lemmas in
`PartialKeyGen.lean` (with `PartialSampleS.lean`) and `PartialSign.lean`.

## The notation

Aeneas has a divergence-tolerant triple, `x ⦃ r => P r ⦄div` (`WP.dspec`): `ok r` needs `P r`, `fail _` is
false, `div` is true. So `x ⦃ P ⦄div` says exactly "(a) and (b)" (partial correctness plus panic-freedom). The
Aeneas `step` tactic understands it (`dspec_bind'`), and every total triple `x ⦃ P ⦄` gives `x ⦃ P ⦄div`
(`WP.spec_dspec`; `step` inserts the conversion itself). A `div`-triple composes with `dspec_bind'` like a total
one, so a function body whose only unbounded parts are `loop`s is proved by the same `step*` script as before,
with the `div`-versions of the loop lemmas at the loops.

## The recipe

1. **Generic lemma** (below): `loop.dspec_rel`, and its special case `loop.dspec_inv`. For
   `loop body x` with an invariant `I` it asks only for the *body*: for every `s` with `I s`, `body s ⦃ … ⦄div`
   where a `done r` must satisfy `Φ s r` and a `cont s'` must satisfy `I s'` and `Φ s' r → Φ s r`. No
   termination measure, no fuel. It is proved once by `loop.fixpoint_induct`: the predicate
   "`f s ⦃ Φ s ⦄div` for all `s` with `I s`" is admissible because it holds of `div`, the bottom of the flat
   order on `RustM`.
2. **The relation `Φ s r`**. For a loop that has the answer `a` of a spec fold in its accumulator, take
   `Φ s r := (the spec reaches r from the state s)`; the usual case is a relation that is closed backwards
   under one loop step (`Φ s' r → Φ s r`), which is a direct consequence of the per-iteration lemma already used
   in the total proof. For an accumulator-style loop (`I s` says "the state is the spec's state after `n`
   iterations, with `n` a ghost") it is enough to take `Φ s r := Q r` (`loop.dspec_inv`) and let `Q` say
   "there is a fuel at which the spec returns `some` of the abstraction of `r`".
3. **The fuel**. The existing total proofs fix one fuel. Here the invariant carries `∃ F`, and each step needs
   fuel *monotonicity* of the spec (`some` at `F` gives the same `some` at `F' ≥ F`), so that the fuel of the
   previous iterations and the fuel needed by the new one can be combined with `max`. The per-sampler
   monotonicity lemmas are in `PartialSample.lean` (`RejNTTPoly_mono`, `ExpandA_mono`) and `PartialBall.lean`
   (sampler-level: `sibFind_mono`, `sibStep_mono`, `runTo_mono`), `PartialSampleS.lean` (`RejBoundedPoly_mono`,
   `ExpandS_mono`) and `PartialSign.lean` (`sampleInBall_fuel_mono`).
4. **Composition.** Callers prove `f … ⦃ r => ∃ F, spec … F = some (abs r) ⦄div` by the same `step*` script as the
   total theorem, using the `div` versions of the sampler theorems; at the end the fuels of the (independent)
   samplers are combined into the fields of `Spec.Fuel`.

For KeyGen and Sign the recipe applies as described: `RejBoundedPoly`/`ExpandS` follow `RejNTTPoly`/`ExpandA`
(`PartialSampleS.lean`), `SampleInBall` inside Sign is `sample_in_ball_partial`, and Sign's rejection loop is bounded
by the κ budget, so it needs only the fuel monotonicity of the attempts (`PartialSign.lean`).
-/

open Aeneas Aeneas.Std RustM

/-- `split_pair`: destructure the most recent *anonymous* local of product type (the result `(_, s1)` of a call
whose first component the Rust code ignores). Aeneas' `step` introduces it but, for `div`-triples, leaves the
`let (_, s1) := _✝` match unreduced. Follow it with `rename_i a b` to name the two components. -/
elab "split_pair" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let lctx ← Lean.getLCtx
  let mut found : Option Lean.FVarId := none
  for d in lctx do
    if d.isImplementationDetail then continue
    if d.userName.hasMacroScopes || d.userName.isInaccessibleUserName || d.userName == `_ then
      let ty ← Lean.Meta.whnf d.type
      if ty.isAppOf ``Prod then found := some d.fvarId
  match found with
  | none => Lean.throwError "split_pair: no anonymous pair in the context"
  | some fv =>
    let subgoals ← g.cases fv
    Lean.Elab.Tactic.replaceMainGoal (subgoals.toList.map (·.mvarId))

namespace Proofs

/-- **Generic partial-correctness lemma for `loop`** (relational form). If, for every state `s` satisfying the
invariant `I`, one execution of the body is not a `fail` and every outcome it can have is either a `done r`
with `Φ s r`, or a `cont s'` with `I s'` and `Φ s' r → Φ s r` for all `r`, then `loop body s` is not a `fail`
and every `ok r` it returns satisfies `Φ s r`. No termination argument is needed: divergence is allowed. -/
theorem loop.dspec_rel {α β : Type} (body : α → RustM (ControlFlow α β)) (I : α → Prop) (Φ : α → β → Prop)
    (hbody : ∀ s, I s → body s ⦃ c =>
      match c with
      | .done r => Φ s r
      | .cont s' => I s' ∧ ∀ r, Φ s' r → Φ s r ⦄div) :
    ∀ s, I s → loop body s ⦃ r => Φ s r ⦄div := by
  have key := loop.fixpoint_induct body (fun f => ∀ s, I s → WP.dspec (f s) (Φ s)) ?adm ?step
  · exact key
  · apply Lean.Order.admissible_pi_apply (fun s (y : RustM β) => I s → WP.dspec y (Φ s))
    intro s
    apply Lean.Order.admissible_flatOrder
    intro _
    simp [WP.dspec]
  · intro f hf s hs
    have hb := hbody s hs
    show WP.dspec (match body s with
      | ok r => (match r with | ControlFlow.cont x => f x | ControlFlow.done x => ok x)
      | fail e => fail e
      | div => div) (Φ s)
    cases hbs : body s with
    | ok c =>
      rw [hbs] at hb
      cases c with
      | cont s' =>
        obtain ⟨h1, h2⟩ := hb
        have := hf s' h1
        simp only [WP.dspec] at this ⊢
        cases hfs : f s' with
        | ok r => rw [hfs] at this; exact h2 r this
        | fail e => rw [hfs] at this; exact this
        | div => trivial
      | done r => exact hb
    | fail e => rw [hbs] at hb; exact hb.elim
    | div => trivial

/-- **Generic partial-correctness lemma for `loop`** (invariant form). If the invariant `I` holds of `x` and, for
every state `s` with `I s`, the body is not a `fail`, every `cont s'` it returns satisfies `I s'`, and every
`done r` satisfies `Q r`, then `loop body x` is not a `fail` and every `ok r` it returns satisfies `Q r`. -/
theorem loop.dspec_inv {α β : Type} (body : α → RustM (ControlFlow α β)) (I : α → Prop) (Q : β → Prop)
    (hbody : ∀ s, I s → body s ⦃ c =>
      match c with
      | .done r => Q r
      | .cont s' => I s' ⦄div)
    (x : α) (hx : I x) :
    loop body x ⦃ r => Q r ⦄div := by
  refine loop.dspec_rel body I (fun _ r => Q r) ?_ x hx
  intro s hs
  refine WP.dspec_mono' (hbody s hs) ?_
  rintro (s' | r) h
  · exact ⟨h, fun r hr => hr⟩
  · exact h

/-- **Generic partial-correctness lemma for `loop`** (ghost form). Like `loop.dspec_rel`, but the relation between
a state and the final result is indexed by a *ghost* `g` (a loop counter, a stream position, …) that is not a
function of the state: `I g s` says that `s` is the state for the ghost `g`, and a step `s ↦ s'` may move to a
new ghost `g'` with `I g' s'` and `Φ g' r → Φ g r`. -/
theorem loop.dspec_ghost {α β γ : Type} (body : α → RustM (ControlFlow α β)) (I : γ → α → Prop)
    (Φ : γ → β → Prop)
    (hbody : ∀ g s, I g s → body s ⦃ c =>
      match c with
      | .done r => Φ g r
      | .cont s' => ∃ g', I g' s' ∧ ∀ r, Φ g' r → Φ g r ⦄div) :
    ∀ g s, I g s → loop body s ⦃ r => Φ g r ⦄div := by
  have key := loop.fixpoint_induct body (fun f => ∀ g s, I g s → WP.dspec (f s) (Φ g)) ?adm ?step
  · exact key
  · apply Lean.Order.admissible_pi
    intro g
    apply Lean.Order.admissible_pi_apply (fun s (y : RustM β) => I g s → WP.dspec y (Φ g))
    intro s
    apply Lean.Order.admissible_flatOrder
    intro _
    simp [WP.dspec]
  · intro f hf g s hs
    have hb := hbody g s hs
    show WP.dspec (match body s with
      | ok r => (match r with | ControlFlow.cont x => f x | ControlFlow.done x => ok x)
      | fail e => fail e
      | div => div) (Φ g)
    cases hbs : body s with
    | ok c =>
      rw [hbs] at hb
      cases c with
      | cont s' =>
        obtain ⟨g', h1, h2⟩ := hb
        have := hf g' s' h1
        simp only [WP.dspec] at this ⊢
        cases hfs : f s' with
        | ok r => rw [hfs] at this; exact h2 r this
        | fail e => rw [hfs] at this; exact this
        | div => trivial
      | done r => exact hb
    | fail e => rw [hbs] at hb; exact hb.elim
    | div => trivial

/-- Fuel monotonicity lifts through `foldlM` in `Option`: if each step `f F` is monotone in the fuel `F`, so is the
whole fold. (Used to combine the fuels of the iterations of a loop: take the maximum.) -/
theorem foldlM_fuel_mono {α : Type} (f : Nat → α → Nat → Option α)
    (hf : ∀ F F' x i y, F ≤ F' → f F x i = some y → f F' x i = some y) (l : List Nat) :
    ∀ x y F F', F ≤ F' → l.foldlM (f F) x = some y → l.foldlM (f F') x = some y := by
  induction l with
  | nil => intro x y F F' _ h; simpa using h
  | cons i l ih =>
    intro x y F F' hF h
    rw [List.foldlM_cons] at h ⊢
    cases hx : f F x i with
    | none => rw [hx] at h; simp at h
    | some x' =>
      rw [hx] at h
      rw [hf F F' x i x' hF hx]
      exact ih x' y F F' hF h

end Proofs
