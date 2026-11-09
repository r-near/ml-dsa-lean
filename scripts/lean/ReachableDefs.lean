/- Body of scripts/reachable-defs.sh. The script writes a file that imports `Impl.Funs` and appends this text, and runs it with
   `lake env lean`.

   It counts the extracted declarations that the verify entry points of the public API reach, by walking the constants of the
   Lean environment: from each root, the constants its kernel term mentions (`ConstantInfo.getUsedConstantsAsSet`: its type and its
   value), transitively, restricted to the namespace `Impl` (the extraction). It does not read source text, so it follows every
   reference the elaborator resolved, including `_root_.`-qualified and «»-escaped names, names used after an `open`, and
   references from a type. A missing root, and a mentioned constant that the environment cannot find, are errors.

   A "declaration" is a `def` (including `abbrev`s, instances and loop bodies) or a type (`structure`, `inductive`) of `Impl`;
   the constants Lean derives from one (constructors, field projections, recursors, matchers, equation lemmas, `proof_n`) are walked
   through but not counted. -/
import Lean
open Lean

namespace ReachableDefs

def verifyRoots : List Name :=
  ["verify", "verify_internal", "verifying_key", "verify_prepared", "verify_internal_prepared"].flatMap fun op =>
    ["44", "65", "87"].map fun nn => Name.mkStr (Name.mkStr `Impl "api") s!"{op}_{nn}"

/-- Whether `n` is a name Lean generated for a declaration rather than a declaration of the extraction: an internal name, a
matcher, or the projection function of a structure field. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail || Lean.Meta.isMatcherCore env n || env.isProjectionFn n

def inImpl (n : Name) : Bool := n.getRoot == `Impl

end ReachableDefs

open ReachableDefs in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut errors : Array String := #[]
  let mut seen : NameSet := {}
  let mut todo : List Name := []
  for r in verifyRoots do
    match env.find? r with
    | none => errors := errors.push s!"root {r} is not in the environment"
    | some _ => todo := r :: todo; seen := seen.insert r
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      let some ci := env.find? n | errors := errors.push s!"{n} is mentioned but not in the environment"; continue
      for u in ci.getUsedConstantsAsSet.toList do
        unless inImpl u do continue
        if seen.contains u then continue
        seen := seen.insert u
        todo := u :: todo
  let mut defs := 0
  let mut types := 0
  let mut ntt : Array Name := #[]
  let mut sorted : Array Name := #[]
  for n in seen.toList do
    let some ci := env.find? n | continue
    if isAuxiliary env n then continue
    match ci with
    | .defnInfo _ => defs := defs + 1; sorted := sorted.push n
    | .inductInfo _ => types := types + 1; sorted := sorted.push n
    | _ => pure ()
    if n.components.length ≥ 2 && n.components[1]! == `ntt then ntt := ntt.push n
  for e in errors do
    IO.println s!"REACHABLE FAIL: {e}"
  if !errors.isEmpty then throwError "REACHABLE FAIL: {errors.size} error(s)"
  IO.println s!"reachable: {defs + types} extracted declarations reachable from the {verifyRoots.length} verify entry points of api ({defs} def/abbrev, {types} types); ntt.* among them: {ntt.toList.map (·.toString)}"
  IO.println s!"reachable (walked, auxiliary included): {seen.size} constants in Impl"
  if (← IO.getEnv "REACHABLE_LIST").isSome then
    for n in sorted.qsort (·.toString < ·.toString) do IO.println s!"  {n}"
  IO.println "REACHABLE OK"
