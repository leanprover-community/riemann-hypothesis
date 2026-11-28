import Lean

/-!
# Compare elaborated declarations

Build the same module in both worktrees with the same Lean toolchain, then run
`lake env lean --run scripts/CompareDecls.lean BEFORE.olean AFTER.olean`.
Use object files from trusted builds. For Lean modules, keep each `.olean` alongside
its `.olean.server` and `.olean.private`.

The comparison reports added or removed names, changes in declaration kind or type,
and changes in definition bodies, including private definitions. It ignores theorem
proof bodies and compares expressions up to alpha equivalence. Compiler-generated
constant names are compared literally, so renumbering can produce a difference.
-/

open Lean System

/-- Read the complete, private declaration data when the file uses the module system. -/
private def declarations (file : FilePath) : IO ModuleData := do
  let exported ← readModuleData file
  if !exported.1.isModule then
    return exported.1
  let server := OLeanLevel.server.adjustFileName file
  let privatePart := OLeanLevel.private.adjustFileName file
  for part in #[server, privatePart] do
    unless ← part.pathExists do
      throw <| IO.userError s!"Missing object file {part}"
  let parts ← readModuleDataParts #[file, server, privatePart]
  let some (data, _) := parts.back?
    | throw <| IO.userError s!"No declaration data in {file}"
  return data

/-- The bodies of definitions and opaque declarations, excluding theorem proofs. -/
private def definitionBody : ConstantInfo → Option Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | _ => none

/-- Compare declaration kinds even when their types happen to be the same. -/
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive type"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def main (args : List String) : IO UInt32 := do
  let [before, after] := args
    | throw <| IO.userError "usage: CompareDecls.lean BEFORE.olean AFTER.olean"
  let old ← declarations before
  let new ← declarations after
  let oldByName := old.constants.foldl (fun table decl => table.insert decl.name decl)
    ({} : NameMap ConstantInfo)
  let newByName := new.constants.foldl (fun table decl => table.insert decl.name decl)
    ({} : NameMap ConstantInfo)
  let mut differs := false
  for (name, previous) in oldByName.toArray do
    match newByName.find? name with
    | none =>
      IO.println s!"removed {name}"
      differs := true
    | some current =>
      let kindChanged := kind previous != kind current
      let typeChanged := previous.levelParams != current.levelParams || previous.type != current.type
      let bodyChanged := definitionBody previous != definitionBody current
      if kindChanged then
        IO.println s!"kind changed {name}"
      if typeChanged then
        IO.println s!"type changed {name}"
      if bodyChanged then
        IO.println s!"definition body changed {name}"
      differs := differs || kindChanged || typeChanged || bodyChanged
  for (name, _) in newByName.toArray do
    if !oldByName.contains name then
      IO.println s!"added {name}"
      differs := true
  return if differs then 1 else 0
