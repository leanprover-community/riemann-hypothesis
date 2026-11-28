import Mathlib.Tactic.Linter.TextBased

open Lean Lean.Linter Mathlib.Linter.TextBased

/-- Recover the module name from an explicit path relative to `src`. -/
private def moduleName (path : String) : Name :=
  (path.dropEnd 5).toString.splitOn "/" |>.foldl Name.str Name.anonymous

/-- Mathlib's text and module-name linters over explicit paths relative to `src`. -/
def main (args : List String) : IO UInt32 := do
  let opts : LinterOptions := { toOptions := {}, linterSets := {} }
  match args with
  | "text" :: root :: paths =>
    IO.Process.setCurrentDir root
    let _ ← lintModules opts #[] (paths.toArray.map moduleName) .exceptionsFile false
    return 0
  | "names" :: paths =>
    let names := paths.toArray.map moduleName
    let casing ← modulesNotUpperCamelCase opts names
    let forbidden ← modulesOSForbidden opts names
    return if casing + forbidden == 0 then 0 else 1
  | _ => throw <| IO.userError "usage: LintStyle.lean text ROOT FILE... | names FILE..."
