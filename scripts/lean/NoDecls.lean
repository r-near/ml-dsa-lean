/- Body of the Lean half of scripts/check-no-decls.sh. The script writes a file that imports `Lean` and every module of
   lean/Impl, lean/Spec and lean/Proofs, appends this text, and runs it with `lake env lean`.

   It looks at the constants those modules declare (their `ModuleData`), not at the dependencies of a few chosen
   theorems, and fails if any of them is

   * an `axiom` or an `opaque` (`partial def` makes an `opaque`, too),
   * marked `@[implemented_by]` or `@[extern]`/`@[export]`,
   * a user of an axiom other than propext, Classical.choice and Quot.sound, directly (`sorryAx` is what `sorry`/`admit`
     elaborate to; `native_decide` adds an axiom `<theorem>._native.native_decide.ax_…` to the module, and older Lean used
     `Lean.ofReduceBool`), or
   * a constant whose transitive closure reaches such an axiom (`collectAxioms`, which reads the closure Lean stored per
     constant in each module's `.olean`).

   The scope is chosen by module, not by constant name: the four `core.iter.range.Step.*.default` axioms that this was
   written for are named `core.…` but declared in `Impl.FunsExternal`. -/
open Lean

namespace NoDecls

def okAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def inScope (m : Name) : Bool := m.getRoot == `Impl || m.getRoot == `Spec || m.getRoot == `Proofs

/-- The violations as lines, and (modules, constants) scanned. -/
def scan : CoreM (Array String × Nat × Nat) := do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut nmods := 0
  let mut nconsts := 0
  for i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    unless inScope mod do continue
    nmods := nmods + 1
    let data := env.header.moduleData[i]!
    for ci in data.constants do
      nconsts := nconsts + 1
      let n := ci.name
      match ci with
      | .axiomInfo _ => bad := bad.push s!"axiom {n} (module {mod})"
      | .opaqueInfo _ => bad := bad.push s!"opaque {n} (module {mod})"
      | _ => pure ()
      if (Compiler.getImplementedBy? env n).isSome then
        bad := bad.push s!"implemented_by on {n} (module {mod})"
      if isExtern env n then
        bad := bad.push s!"extern/export on {n} (module {mod})"
      -- Direct uses first, so the report names the constant that wrote `sorry` or `native_decide`.
      let mut direct := false
      for u in ci.getUsedConstantsAsSet.toList do
        if let some (.axiomInfo _) := env.find? u then
          unless okAxioms.contains u do
            direct := true
            bad := bad.push s!"{n} uses axiom {u} (module {mod})"
      -- The transitive closure (Lean precomputes it per imported constant), for constants that reach one through a lemma.
      unless direct || (match ci with | .axiomInfo _ => true | _ => false) do
        for a in (← collectAxioms n) do
          unless okAxioms.contains a do
            bad := bad.push s!"{n} depends on axiom {a} (module {mod})"
  return (bad, nmods, nconsts)

end NoDecls

#eval show CoreM Unit from do
  let (bad, nmods, nconsts) ← NoDecls.scan
  if nmods == 0 then throwError "NODECLS FAIL (env): no Impl/Spec/Proofs module is imported"
  for b in bad do
    IO.println s!"NODECLS FAIL (env): {b}"
  IO.println s!"no-decls env scan: {nmods} modules, {nconsts} constants, {bad.size} violations"
  if bad.size > 0 then throwError "NODECLS FAIL (env): {bad.size} violation(s)"
  IO.println "NODECLS ENV OK"
