import Main
import Lib.Cite.Export

/-!
Writes a Literature Links annotation for every citation that `Main` imports, one per line (see
`Lib.Cite.Export`). Run it from the root of the repository, with `Main` and
`Lib.Cite.Export` built:

    CITATIONS_COMMIT=$(git rev-parse HEAD) lake env lean scripts/cite/Export.lean

`CITATIONS_COMMIT`, the commit that the Lean ends point to, is required. The output file is
`CITATIONS_OUT`, by default `citations.jsonl`, and the repository `CITATIONS_REPO`, by default
`https://github.com/leanprover-community/riemann-hypothesis`.
-/

run_cmd do
  let some commit := (← IO.getEnv "CITATIONS_COMMIT").filter (!·.isEmpty)
    | throwError "set `CITATIONS_COMMIT` to the commit that the Lean ends point to"
  let repo := (← IO.getEnv "CITATIONS_REPO").getD
    "https://github.com/leanprover-community/riemann-hypothesis"
  let out := (← IO.getEnv "CITATIONS_OUT").getD "citations.jsonl"
  Lean.Elab.Command.liftCoreM <| Lib.Cite.exportCitations out repo commit
