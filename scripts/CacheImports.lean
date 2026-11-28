import Init.System.IO
import Lean.Elab.Import
import Lean.Parser.Module
import Lean.Data.Json.FromToJson

open Lean

private structure ImportResult where
  path : String
  imports : Array String := #[]
  error : Option String := none
  deriving ToJson

private def isTauCeti (name : String) : Bool :=
  name == "TauCeti" || name.startsWith "TauCeti."

private def taucetiImports (header : TSyntax ``Parser.Module.header) : Array String :=
  (Lean.Elab.headerToImports header (includeInit := false)).filterMap fun imp =>
    let name := imp.module.toString
    if isTauCeti name then some name else none

private def sourceFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let paths ← root.walkDir
  pure <| paths.filter fun path => path.extension == some "lean"

private def modulePath (source : System.FilePath) (modName : String) : System.FilePath :=
  ((modName.splitOn ".").foldl (· / ·) source).withExtension "lean"

private def parse (path : System.FilePath) : IO ImportResult := do
  try
    let input := Parser.mkInputContext (← IO.FS.readFile path) path.toString
    let (header, _, messages) ← Parser.parseHeader input
    if messages.hasErrors then
      pure { path := path.toString, error := some "Lean reported a module-header parse error" }
    else
      pure { path := path.toString, imports := taucetiImports header }
  catch error =>
    pure { path := path.toString, error := some error.toString }

/-- Print, as JSON, the direct Tau Ceti imports of every source file, `Challenge.lean`, and every
reachable Tau Ceti module under `.lake/packages/TauCeti`. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.head?.getD "."
  let files ← sourceFiles (root / "src")
  let srcResults ← files.mapM parse
  let challengeResult ← parse (root / "Challenge.lean")
  let mut results := srcResults.push challengeResult
  let taucetiSource := root / ".lake" / "packages" / "TauCeti"
  let mut pending : Array String := #[]
  for res in srcResults do
    pending := pending ++ res.imports
  let mut seen : Std.HashSet String := {}
  while !pending.isEmpty do
    let modName := pending.back!
    pending := pending.pop
    if !seen.contains modName then
      seen := seen.insert modName
      let path := modulePath taucetiSource modName
      if ← path.pathExists then
        let res ← parse path
        results := results.push res
        pending := pending ++ res.imports
  IO.println <| (toJson results).compress
  pure 0
