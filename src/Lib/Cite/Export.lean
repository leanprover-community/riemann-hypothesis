module

public meta import Lean.Data.Json.Elab
public meta import Lean.Elab.Command
public meta import Lib.Cite
public import Mathlib.Init

/-!
# Citations as Literature Links annotations

`exportCitations` writes one
[Literature Links](https://github.com/mathlib-initiative/literature-links) annotation per line
(JSONL) for every citation that `@[cite]` recorded in the environment, sorted by `id` and then by
declaration. An annotation's subject is the cited work and its object the declaration, at a commit
of this repository. `scripts/cite/Export.lean` runs it with `Main` imported.

* The subject of a citation of a BibTeX entry carries the entry as a CSL-JSON `citation`, and the
  locator as its `title`. Its address is the entry's `url`, else its DOI, arXiv identifier, zbMATH
  number or MathSciNet number. The CSL-JSON fields are the BibTeX ones without their braces: LaTeX
  in them, such as the accent in `P\'eriodes`, is kept as it is written.
* The subject of a citation of a declared source is the entry's address. Its `type` is the source's
  field `type`, which must be one of `endTypes`, and otherwise `html` when the entries have
  addresses of their own and `generic` when they share the source's. A source's field `registry`
  goes in `identifiers`.
* The subject keeps the citation as recorded, with its comment, quote and checker, in its
  `extensions`, under `citeExtension`.

The export reads the BibTeX file again and checks every cited entry as `@[cite]` does, writing
nothing if one fails. This catches a change to the file after which Lake did not rebuild a citing
module.
-/

public meta section

open Lean Elab Command Json

namespace Lib.Cite

/-- The Literature Links types of an end: the kind of document that holds it. -/
def endTypes : List String := ["pdf", "latex", "html", "lean", "generic"]

/-- Whether `key` is a valid `identifiers` key: nonempty, and without the whitespace, controls,
bidirectional and zero-width marks excluded by *References* in the Literature Links spec. -/
def isIdentifiersKey (key : String) : Bool :=
  !key.isEmpty && key.all fun c =>
    let n := c.toNat
    !(n ≤ 0x20 || (0x7f ≤ n && n ≤ 0xa0) || n == 0x61c || n == 0x1680 ||
      (0x2000 ≤ n && n ≤ 0x200f) || (0x2028 ≤ n && n ≤ 0x202f) ||
      (0x205f ≤ n && n ≤ 0x206f) || n == 0x3000 || n == 0xfeff || n == 0xfffe || n == 0xffff)

/-- `s`, unless it is empty. -/
def nonempty? (s : String) : Option String := if s.isEmpty then none else some s

/-- The extension key, on the subject end, for a citation as recorded. -/
def citeExtension : String := "org.leanprover-community.riemann-hypothesis.cite"

/-- `title` followed by `comment` in parentheses, as the docstring line shows it. -/
def withComment (title comment : String) : String :=
  if comment.isEmpty then title else s!"{title} ({comment})"

/-! ### CSL-JSON -/

/-- `s` without its braces. -/
def unbrace (s : String) : String := (s.replace "{" "").replace "}" ""

/-- The pieces of `s` between the characters satisfying `sep` outside braces. -/
def splitTop (s : String) (sep : Char → Bool) : List String :=
  let (parts, cur, _) := s.foldl (init := (#[], "", 0)) fun (parts, cur, depth) c =>
    if depth == 0 && sep c then (parts.push cur, "", depth)
    else (parts, cur.push c, if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth)
  (parts.push cur).toList

/-- A CSL-JSON name: `family` and `given` from `Last, First` or `First Last`, else `literal`. -/
def cslName (words : List String) : Json :=
  let name := " ".intercalate words
  let literal := json% { literal : $(unbrace name) }
  let person (family given : String) :=
    let family := squash (unbrace family)
    let given := squash (unbrace given)
    if family.isEmpty || given.isEmpty then literal
    else json% { family : $(family), given : $(given) }
  match splitTop name (· == ','), words.dropLast, words.getLast? with
  | [family, given], _, _ => person family given
  | [_], given@(_ :: _), some family => person family (" ".intercalate given)
  | _, _, _ => literal

/-- The CSL-JSON names of a BibTeX name list: names separated by ` and ` outside braces. -/
def cslNames (names : String) : Array Json :=
  let words := (splitTop (squash names) (· == ' ')).filter (!·.isEmpty)
  ((words.splitOn "and").filter (!·.isEmpty)).toArray.map cslName

/-- The CSL-JSON type of a BibTeX entry type. -/
def cslType : String → String
  | "article" => "article-journal"
  | "book" => "book"
  | "incollection" | "inbook" => "chapter"
  | "inproceedings" => "paper-conference"
  | "phdthesis" | "mastersthesis" => "thesis"
  | "techreport" => "report"
  | _ => "document"

/-- The value of the identifier `name` of the entry, when it has a well-formed one. -/
def BibEntry.identifier? (e : BibEntry) (name : String) : Option String :=
  match e.identifiers with
  | .ok ids => (ids.find? (·.1 == name)).map (·.2)
  | .error _ => none

/-- The CSL-JSON item of a BibTeX entry. -/
def BibEntry.csl (e : BibEntry) : Json :=
  let year := (e.field? "year").map squash |>.filter fun y => !y.isEmpty && y.all Char.isDigit
  (json% { id : $(e.key), type : $(cslType e.type) }).mergeObj <| Json.mkObj <|
    opt "title" ((e.field? "title").map fun t => squash (unbrace t)) ++
    opt "author" ((e.field? "author").map cslNames) ++
    opt "editor" ((e.field? "editor").map cslNames) ++
    opt "container-title" (((e.field? "journal").orElse fun _ => e.field? "booktitle").map
      fun t => squash (unbrace t)) ++
    opt "collection-title" ((e.field? "series").map fun t => squash (unbrace t)) ++
    opt "volume" ((e.field? "volume").orElse (fun _ => e.field? "number") |>.map squash) ++
    opt "page" ((e.field? "pages").map fun p => (squash p).replace "--" "–") ++
    opt "publisher" ((e.field? "publisher").map fun t => squash (unbrace t)) ++
    opt "issued" (year.map fun y => json% { "date-parts" : [[$(y.toNat!)]] }) ++
    opt "DOI" (e.identifier? "doi") ++
    opt "URL" ((e.field? "url").map squash)

/-- The address of a BibTeX entry: its `url`, else the address of one of its identifiers. -/
def BibEntry.uri (e : BibEntry) : Option String :=
  ((e.field? "url").map squash).orElse fun _ =>
  ((e.identifier? "doi").map (s!"https://doi.org/{·}")).orElse fun _ =>
  ((e.identifier? "eprint").map (s!"https://arxiv.org/abs/{·}")).orElse fun _ =>
  ((e.identifier? "zbl").map (s!"https://zbmath.org/?q=an:{·}")).orElse fun _ =>
  (e.identifier? "mrnumber").map (s!"https://mathscinet.ams.org/mathscinet-getitem?mr={·}")

/-! ### Annotations -/

/-- The type of the entries of `s`: its field `type`, else `html` or, without `{id}`, `generic`. -/
def endType (s : Source) : String :=
  (s.field? "type").getD <| if s.uri.contains "{id}" then "html" else "generic"

/-- The Lean end of an annotation: the declaration `decl` of `module`, at `commit` of `repo`. -/
def leanEnd (decl : String) (module : Name) (repo commit : String) : Json :=
  json% { type : "lean", uri : $(repo), version : $(commit),
    location : { declaration : $(decl), module : $(module.toString) } }

/-- The citation `c` as recorded, for the subject's `extensions`. -/
def Citation.recorded (c : Citation) : Json :=
  let src := match c.source with
    | .bib key => [("key", toJson key), ("locator", toJson c.id)]
    | .source name => [("source", toJson (name.toString (escape := false))), ("id", toJson c.id)]
  Json.mkObj <| src ++ opt "comment" (nonempty? c.comment) ++ opt "quote" (nonempty? c.quote) ++
    opt "checkedBy" (nonempty? c.checkedBy)

/-- The `id` and subject end of the citation `c`, given the BibTeX entries `bib`. -/
def subject (bib : Array BibEntry) (c : Citation) : CoreM (String × Json) := do
  let extensions := Json.mkObj [(citeExtension, c.recorded)]
  match c.source with
  | .source name =>
    let s ← findSource name
    let type := endType s
    unless endTypes.contains type do
      throwError "the field `type` of the source `{name}` is `{type}`, not one of \
        {", ".intercalate endTypes}"
    if let some key := s.field? "registry" then
      unless isIdentifiersKey key do
        throwError "the registry `{key}` of the source `{name}` is not a valid identifiers key"
    let subjectEnd := json% { type : $(type), uri : $(s.entryUri c.id),
      title : $(withComment s!"{s.title} {c.id}" c.comment), extensions : $(extensions) }
    return (s!"{name.toString (escape := false)}:{c.id}", subjectEnd.mergeObj <| Json.mkObj <|
      opt "identifiers" ((s.field? "registry").map fun key => Json.mkObj [(key, toJson c.id)]))
  | .bib key =>
    let some e := bib.find? (·.key == key)
      | throwError "the BibTeX file has no entry `{key}`"
    let some uri := e.uri
      | throwError "the entry `{key}` has no `url` and no identifier with an address"
    let subjectEnd := json% { type : $(if uri.toLower.endsWith ".pdf" then "pdf" else "html"),
      uri : $(uri), title : $(withComment c.id c.comment), citation : $(e.csl),
      extensions : $(extensions) }
    return (s!"{key}:{c.id}", subjectEnd)

/-- The annotations of every citation in the environment, one JSON line each, sorted by `id`, then
by declaration. Every cited BibTeX entry is checked again, as `@[cite]` checks it. -/
def annotations (repo commit : String) : CoreM (Array String) := do
  let env ← getEnv
  let cites := citations env
  let keys := (cites.filterMap fun c => match c.source with
    | .bib key => some key
    | .source _ => none).toList.eraseDups
  let mut errors := #[]
  for key in keys do
    try discard <| citedEntry key catch e => errors := errors.push (← e.toMessageData.toString)
  unless errors.isEmpty do
    throwError "cannot export the citations: {" ".intercalate errors.toList}"
  let bib ← if keys.isEmpty then pure #[] else readBib
  let mut lines := #[]
  for c in cites do
    try
      let (id, subjectEnd) ← subject bib c
      let decl := (privateToUserName c.declName).toString
      let module := match env.getModuleIdxFor? c.declName with
        | some idx => env.allImportedModuleNames[idx.toNat]!
        | none => env.mainModule
      let annotation := json% { id : $(id), subject : [$(subjectEnd)],
        object : [$(leanEnd decl module repo commit)] }
      lines := lines.push (id, decl, annotation.compress)
    catch e => errors := errors.push (← e.toMessageData.toString)
  unless errors.isEmpty do
    throwError "cannot export the citations: {"; ".intercalate errors.toList.eraseDups}"
  -- a canonical order, by `id`, then declaration, keeps the published file stable
  let sorted := lines.qsort fun a b =>
    (compare a.1 b.1 |>.then (compare a.2.1 b.2.1) |>.then (compare a.2.2 b.2.2)).isLT
  return sorted.map (·.2.2)

/-- Write the annotations of every citation in the environment to the file `out`, one per line,
with the Lean ends at `commit` of `repo`. -/
def exportCitations (out : System.FilePath) (repo commit : String) : CoreM Unit := do
  let lines ← annotations repo commit
  IO.FS.writeFile out (String.join (lines.toList.map (· ++ "\n")))
  logInfo m!"Wrote {lines.size} Literature Links annotations to {out}"

end Lib.Cite
