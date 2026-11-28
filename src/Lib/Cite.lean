module

public meta import Lean.Elab.Command
public meta import Lib.Cite.Bib
public import Mathlib.Init

/-!
# Citations

A *citation* records that a declaration formalizes a part of a work. The work is either an entry
of the BibTeX file `docs/references.bib`, named by its key, or an entry of a source declared in
Lean with `cite_source`, such as a web database whose entries have addresses of their own.

* `@[cite "key" "locator"]` cites the part `locator` of the BibTeX entry `key`, such as
  `"§3.1, Definition 3.1, p. 244"`. The locator is required: a citation must say where in the work
  the result is. The entry must exist and have an identifier under which a catalogue lists the
  work (see `Lib.Cite.Bib`), and otherwise the attribute is an error.
* `@[cite src "id"]` cites the entry `id` of the source `src`.
* Either form takes a comment after the locator or the id, such as
  `@[cite "key" "§1.3.3, p. 66" "with `K = ℚ_[p]`"]`, and two optional fields:
  - `(quote := "…")`, the words of the work at that place, as they are printed there;
  - `(checked := "name")`, the person who compared the citation with the work. A citation without
    this field has not been checked by anyone.

The attribute appends a line to the declaration's docstring, such as
`[key], §3.1, Definition 3.1, p. 244. Checked against the work by …`, where doc-gen4 links
`[key]` to the bibliography, and records the citation, which `citations` reads back. It runs after
compilation, when the declaration's own docstring has been written, so the line is appended to it.
A theorem's docstring is written on its own elaboration branch: in the theorem's file the line is
missing, and files that import it see it.

* `cite_source name "title" (uri := "…{id}…") (key := "value")*` declares a source, optionally
  with a docstring. In the address `uri`, `{id}` stands for the entry's percent-encoded
  identifier; without `{id}`, all entries share the address. The other fields, such as
  `(type := "pdf")`, are free-form and kept for exports. Sources are declared in Lean, rather than
  in a data file, so that Lake knows which modules depend on them.

The BibTeX file is the option `cite.bibFile`, by default `docs/references.bib`, relative to the
working directory, which is the root of the repository for Lake and the editor. Lake does not
track this read: a module that cites an entry is not rebuilt when the file changes. The export
`scripts/cite/Export.lean` reads the file again and checks every citation.

`#citations` (`Lib.Cite.Report`) lists the citations that a declaration depends on, together
with Mathlib's cross-references such as `@[stacks]`.
-/

public meta section

open Lean Elab Command

namespace Lib.Cite

/-! ### Sources -/

/-- A work that declarations cite, declared by `cite_source`. -/
structure Source where
  /-- The name that citations use, such as `nlab`. -/
  name : Name
  /-- A readable title, such as `the nLab`. -/
  title : String
  /-- The address of an entry, in which `{id}` stands for the entry's identifier. -/
  uri : String
  /-- The source's other fields, as `cite_source` was given them, such as `("type", "pdf")`. -/
  fields : Array (String × String) := #[]
  /-- The source's docstring, kept for exports. -/
  doc : String := ""
  /-- The module that declared the source. -/
  module : Name := .anonymous
  deriving Inhabited, Repr

/-- The value of the source's field `key`, when it has one. -/
def Source.field? (s : Source) (key : String) : Option String :=
  (s.fields.find? (·.1 == key)).map (·.2)

/-- The address of the entry `id` of the source `s`, with `id` percent-encoded. -/
def Source.entryUri (s : Source) (id : String) : String :=
  s.uri.replace "{id}" (System.Uri.escapeUri id)

/-- Add the source `s` to a registry of sources by name. -/
def insertSource (registry : NameMap (Array Source)) (s : Source) : NameMap (Array Source) :=
  registry.insert s.name (((registry.find? s.name).getD #[]).push s)

/-- The environment extension storing the declared sources, by name. -/
initialize sourceExt : SimplePersistentEnvExtension Source (NameMap (Array Source)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries insertSource {}
    addEntryFn := insertSource
  }

/-- The declarations of the source `name`: several when modules not importing each other do. -/
def sourceDecls (env : Environment) (name : Name) : Array Source :=
  ((sourceExt.getState env).find? name).getD #[]

/-- Every declared source, imported or of the current module, ordered by name. -/
def sources (env : Environment) : Array Source :=
  (sourceExt.getState env).toArray.flatMap (·.2) |>.qsort (·.name.lt ·.name)

/-- The source named `name`, or an error unless exactly one module declares it. -/
def findSource {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (name : Name) :
    m Source := do
  match sourceDecls (← getEnv) name with
  | #[s] => return s
  | #[] => throwError "Unknown source `{name}`; declare it with `cite_source`."
  | ss => throwError "The source `{name}` is declared in several modules: \
      {", ".intercalate (ss.toList.map fun s => s!"`{s.module}`")}."

/-- Declare `s` as a source of the current module, or throw if its name is already taken. -/
def addSource {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (s : Source) : m Unit := do
  if let some old := (sourceDecls (← getEnv) s.name)[0]? then
    throwError "The source `{s.name}` is already declared, in module `{old.module}`."
  modifyEnv (sourceExt.addEntry · { s with module := (← getEnv).mainModule })

/-! ### Citations -/

/-- The work of a citation: a source declared with `cite_source`, or an entry of the BibTeX
file. -/
inductive CitedSource where
  /-- The source declared with `cite_source` under this name. -/
  | source (name : Name)
  /-- The entry of the BibTeX file with this key. -/
  | bib (key : String)
  deriving Inhabited, Repr, BEq

/-- A citation: the declaration `declName` formalizes a part of a work. -/
structure Citation where
  /-- The declaration that cites the work. -/
  declName : Name
  /-- The cited work. -/
  source : CitedSource
  /-- The locator in a BibTeX entry, such as `Theorem 2.3`, or the entry of a declared source. -/
  id : String
  /-- A comment on the citation, or empty. -/
  comment : String := ""
  /-- The words of the work at that place, or empty. -/
  quote : String := ""
  /-- The person who compared the citation with the work, or empty if nobody has. -/
  checkedBy : String := ""
  deriving Inhabited, Repr, BEq

/-- The environment extension storing all citations. -/
initialize citeExt : SimplePersistentEnvExtension Citation (Array (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    -- the imported citations are kept as they are, to avoid an overhead at initialization
    addImportedFn citations := citations
    addEntryFn citations _ := citations
  }

/-- Every citation: those of the imported modules, then those of the current one, in order. -/
def citations (env : Environment) : Array Citation :=
  let (currentModule, imported) := PersistentEnvExtension.getState citeExt env
  imported.flatten ++ currentModule.reverse.toArray

/-! ### The BibTeX file -/

/-- The BibTeX file whose keys `@[cite "key" "locator"]` cites, relative to the working
directory. -/
register_option cite.bibFile : String := {
  defValue := "docs/references.bib"
  descr := "the BibTeX file whose keys `@[cite \"key\" \"locator\"]` cites"
}

/-- The entries of the BibTeX file `cite.bibFile`, or an error if it cannot be read or parsed. -/
def readBib : CoreM (Array BibEntry) := do
  let path : System.FilePath := ⟨cite.bibFile.get (← getOptions)⟩
  let .ok text ← (IO.FS.readFile path).toBaseIO
    | throwError "Cannot read the BibTeX file `{path}` from `{← IO.currentDir}`; \
        `cite.bibFile` names it relative to the root of the repository."
  match parseBib text with
  | .ok entries => return entries
  | .error msg => throwError "The BibTeX file `{path}` is malformed: {msg}"

/-- The entry `key` of the BibTeX file, which must exist and have an identifier. -/
def citedEntry (key : String) : CoreM BibEntry := do
  if key.isEmpty || key.any fun (c : Char) => c.isWhitespace || "\"\\{}[],".contains c then
    throwError "`{key}` is not a valid BibTeX key."
  let some e := (← readBib).find? (·.key == key)
    | throwError "No entry `{key}` in the BibTeX file `{cite.bibFile.get (← getOptions)}`."
  match e.identifiers with
  | .error msg => throwError "The entry `{key}` cannot be cited: {msg}."
  | .ok #[] => throwError "The entry `{key}` cannot be cited: it has no `doi`, `zbl`, \
      `mrnumber` or arXiv `eprint`, so nobody can look the work up in a catalogue."
  | .ok _ => return e

/-! ### The `cite_source` command and the `@[cite]` attribute -/

/-- A named field of a source or a citation: `(uri := "https://oeis.org/{id}")`. -/
syntax citeField := "(" ident " := " str ")"

/-- The fields `fields`, as names and values, or an error on one given twice or not in
`allowed` (when it is given). -/
def readFields (fields : Array (TSyntax ``citeField)) (allowed : Option (List String) := none) :
    CoreM (Array (String × String)) := do
  let mut values := #[]
  for field in fields do
    let `(citeField| ($key:ident := $value:str)) := field | throwUnsupportedSyntax
    let name := key.getId.eraseMacroScopes.toString
    if let some names := allowed then
      unless names.contains name do
        throwErrorAt key "Unknown field `{name}`; a citation takes \
          {" and ".intercalate (names.map (s!"`{·}`"))}."
    if values.any (·.1 == name) then throwErrorAt key "The field `{name}` is given twice."
    if value.getString.all Char.isWhitespace then
      throwErrorAt value "The field `{name}` cannot be empty."
    values := values.push (name, value.getString)
  return values

/-- `cite_source name "title" (uri := "…{id}…") (key := "value")*` declares a citable source. -/
syntax (name := citeSource) (docComment)? "cite_source " Lean.Parser.rawIdent ppSpace str
  (ppSpace citeField)* : command

/-- Elaborate `cite_source`: read the fields and declare the source. -/
@[command_elab citeSource]
def elabCiteSource : CommandElab
  | `(command| $[$doc]? cite_source $name:ident $title:str $fields*) => do
    let fields ← liftCoreM <| readFields fields
    let some uri := (fields.find? (·.1 == "uri")).map (·.2)
      | throwError "A source needs an address: `(uri := \"https://…\")`."
    withRef name <| addSource {
      name := name.getId.eraseMacroScopes
      title := title.getString
      uri
      fields := fields.filter (·.1 != "uri")
      doc := (← doc.mapM getDocStringText).getD "" |>.trimAscii.toString }
  | _ => throwUnsupportedSyntax

/-- Escape the ASCII punctuation in `s`, so that Markdown shows it as written. -/
def escapeFormatting (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.toNat < 128 && !c.isAlphanum && !c.isWhitespace then acc.push '\\' |>.push c
    else acc.push c

/-- Append the paragraph `text` to the Markdown docstring of `decl`. -/
def appendDocString (decl : Name) (text : String) : CoreM Unit := do
  if doc.verso.get (← getOptions) then
    throwError "`@[cite]` only supports Markdown docstrings, not `doc.verso`."
  -- trimmed, since some versions of Lean keep the space before the closing `-/`
  let oldDoc := ((← findDocString? (← getEnv) decl).getD "").trimAscii.toString
  addDocStringCore decl ("\n\n".intercalate ([oldDoc, text].filter (· != "")))

/-- The line that `@[cite]` appends to the docstring for the citation `c`, whose work is linked
by `link`. -/
def docLine (c : Citation) (link : String) : String :=
  let comment := if c.comment.isEmpty then "" else s!" ({c.comment})"
  let check := if c.checkedBy.isEmpty then "Not yet checked against the work."
    else s!"Checked against the work by {c.checkedBy}."
  s!"{link}{comment}. {check}"

/-- `@[cite "key" "locator" "comment"? (field := "…")*]` cites a part of an entry of the BibTeX
file, and `@[cite src "id" "comment"? (field := "…")*]` an entry of a declared source. The fields
are `quote` and `checked`. -/
syntax (name := citeAttr) &"cite" ppSpace (Lean.Parser.rawIdent <|> str)
  (ppSpace str (ppSpace str)?)? (ppSpace citeField)* : attr

initialize Lean.registerBuiltinAttribute {
  name := `citeAttr
  descr := "Cite a part of an entry of the BibTeX file, or an entry of a declared source."
  add decl stx attrKind := do
    unless attrKind == .global do throwAttrMustBeGlobal `cite attrKind
    let str (s? : Option (TSyntax `str)) := (s?.map (·.getString)).getD ""
    let (source, srcRef, id?, comment?, fields) ← match stx with
      | `(attr| cite $src:ident $[$id $[$comment]?]? $fields*) =>
        pure (CitedSource.source src.getId.eraseMacroScopes, src.raw, id, comment.join, fields)
      | `(attr| cite $key:str $[$locator $[$comment]?]? $fields*) =>
        pure (CitedSource.bib key.getString, key.raw, locator, comment.join, fields)
      | _ => throwUnsupportedSyntax
    let fields ← readFields fields (allowed := ["quote", "checked"])
    let field (name : String) := ((fields.find? (·.1 == name)).map (·.2)).getD ""
    let c : Citation := {
      declName := decl, source, id := str id?, comment := str comment?
      quote := field "quote", checkedBy := field "checked" }
    let link ← withRef srcRef do
      match source with
      | .bib key =>
        if c.id.all Char.isWhitespace then
          throwError "A citation must say where in the work the result is: \
            `@[cite \"{key}\" \"Theorem 2.3\"]`."
        discard <| citedEntry key
        -- doc-gen4 links a `[key]` of the bibliography, so the key is not escaped
        pure s!"[{key}], {escapeFormatting c.id}"
      | .source name =>
        let s ← findSource name
        if c.id.all Char.isWhitespace then throwError "The cited entry cannot be empty."
        pure s!"[{escapeFormatting s.title} {escapeFormatting c.id}]({s.entryUri c.id})"
    appendDocString decl (docLine c link)
    modifyEnv (citeExt.addEntry · c)
  applicationTime := .afterCompilation
}

end Lib.Cite
