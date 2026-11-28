module

public meta import Lean.Elab.Command
public meta import Lib.Cite
public meta import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Init

/-!
# The citations that a declaration depends on

`#citations d` lists the citations of `d` and of every declaration that `d` depends on through
types, values and proofs: those that `@[cite]` records, and Mathlib's cross-references
`@[stacks]`, `@[kerodon]`, `@[wikidata]` and the others. It groups them by work, gives the
declarations that cite each part, and says who checked each `@[cite]` citation. It ends with the
number of citations that nobody has checked. Mathlib's cross-references have no such field.

Then it lists the declarations among them whose citation states a form other than `same`: those
that are not the cited definition or statement, with what differs and the theorem that compares
the two, if the citation names one. It warns when that name is not a declaration, or is one
whose statement does not mention the citing declaration.

In a file that starts with `module`, the proofs of imported theorems are not loaded, so the
command only follows their statements, and it says so. To follow the proofs, run it from a file
without `module`, as `scripts/cite/Citations.lean` does for `riemannHypothesis`.
-/

public meta section

open Lean Elab Command

namespace Lib.Cite

/-- The declarations that `root` depends on, itself included: the constants in their types and
values, and the constructors of the inductive types among them. -/
def dependencies (env : Environment) (root : Name) : NameHashSet := Id.run do
  let mut seen : NameHashSet := {}
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | continue
    todo := info.getUsedConstantsAsSet.foldl (init := todo) fun todo m =>
      if seen.contains m then todo else todo.push m
    if let .inductInfo v := info then todo := todo ++ v.ctors.toArray
  return seen

/-- Every cross-reference of Mathlib's `@[stacks]` and the other cross-reference attributes. -/
def crossRefs (env : Environment) : Array Mathlib.CrossRef.Tag :=
  let tags := PersistentEnvExtension.getState Mathlib.CrossRef.tagExt env
  tags.2.flatten.appendList tags.1

/-- The title of a cited work, as `#citations` lists it. -/
def workTitle (env : Environment) : CitedSource → String
  | .bib key => key
  | .source name => match sourceDecls env name with
    | #[s] => s!"{s.title} ({name})"
    | _ => name.toString

/-- The comment `c` on one line, in parentheses unless it already is, after a space; or nothing. -/
def showComment (c : String) : String :=
  let c := squash c
  if c.isEmpty then "" else if c.startsWith "(" && c.endsWith ")" then s!" {c}" else s!" ({c})"

/-- `n` followed by `word`, with an `s` unless `n` is one. -/
def count (n : Nat) (word : String) : String := s!"{n} {word}{if n == 1 then "" else "s"}"

/-- `#citations d` lists the citations that the declaration `d` depends on. -/
syntax (name := citationsCmd) "#citations " ident : command

@[command_elab citationsCmd]
def elabCitations : CommandElab
  | `(command| #citations $id:ident) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    if env.header.isModule then
      logWarning "This file starts with `module`, so the proofs of imported theorems are not \
        loaded and only their statements are followed. Run `#citations` from a file without \
        `module` to follow the proofs."
    let deps := dependencies env root
    let cites := (citations env).filter (deps.contains ·.declName)
    let tags := (crossRefs env).filter (deps.contains ·.declName)
    let mut lines := #[s!"Citations that `{root}` depends on, among {deps.size} declarations:"]
    -- `@[cite]` citations, by work, then by locator and declaration
    let works := (cites.map (workTitle env ·.source)).toList.eraseDups.toArray.qsort (· < ·)
    for w in works do
      lines := lines.push s!"\n{w}"
      let here := (cites.filter (workTitle env ·.source == w)).qsort fun a b =>
        a.id < b.id || (a.id == b.id && a.declName.toString < b.declName.toString)
      for c in here do
        let check := if c.checkedBy.isEmpty then "not checked" else s!"checked by {c.checkedBy}"
        let form := if c.form == .unstated then "" else s!", {c.form.word}"
        lines := lines.push s!"  {c.id}{showComment c.comment}: {c.declName}, {check}{form}"
    -- Mathlib's cross-references, by database, then by tag and declaration
    let dbs := (tags.map (·.database.label)).toList.eraseDups.toArray.qsort (· < ·)
    for db in dbs do
      lines := lines.push s!"\n{db} (Mathlib)"
      let here := (tags.filter (·.database.label == db)).qsort fun a b =>
        a.tag < b.tag || (a.tag == b.tag && a.declName.toString < b.declName.toString)
      for t in here do
        lines := lines.push s!"  {t.tag}{showComment t.comment}: {t.declName}"
    let unchecked := (cites.filter (·.checkedBy.isEmpty)).size
    lines := lines.push s!"\n{count cites.size "citation"} of {count works.size "work"}, \
      {unchecked} of them not checked against the work; \
      {count tags.size "cross-reference"} to {count dbs.size "database"}."
    -- the citations whose declaration is not the cited definition or statement, by form
    let departures := cites.filter (·.form.departs)
    unless departures.isEmpty do
      lines := lines.push s!"\nNot in the cited form ({departures.size}):"
      for (word, form) in Form.words do
        let here := (departures.filter (·.form == form)).qsort
          (·.declName.toString < ·.declName.toString)
        for c in here do
          let proved := if c.comparison.isAnonymous then "no comparison proved here"
            else s!"compared by {c.comparison}"
          lines := lines.push s!"  {word}: {c.declName}, {workTitle env c.source}, \
            {c.id}{showComment c.comment}, {proved}"
    logInfo (String.intercalate "\n" lines.toList)
    -- the theorems named as comparisons must exist and be about the citing declaration
    for c in cites do
      unless c.comparison.isAnonymous do
        match env.find? c.comparison with
        | none => logWarning m!"The citation of `{c.declName}` names `{c.comparison}` as its \
            comparison, which is not a declaration."
        | some info =>
          unless info.type.getUsedConstantsAsSet.contains c.declName do
            logWarning m!"The citation of `{c.declName}` names `{c.comparison}` as its comparison, \
              whose statement does not mention `{c.declName}`."
  | _ => throwUnsupportedSyntax

end Lib.Cite
