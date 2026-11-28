module

public meta import Lean.Data.Position
public meta import Std.Internal.Parsec
public import Mathlib.Init

/-!
# The BibTeX file

`parseBib` reads a BibTeX file, such as `docs/references.bib`, into its entries. `@[cite]`
(`Lib.Cite`) reads the entry that it cites, and the export `scripts/cite/Export.lean` turns
the entries into CSL-JSON.

The parser accepts what a file like ours uses: braced and quoted values, numbers, the month
abbreviations, `#` between pieces of a value, and `@comment`. As in BibTeX, text between entries
is ignored, and so is an `@` there that no entry type follows. It rejects `@string`, `@preamble`,
any other macro, and a key or a field given twice. Entry types and field names are read in
lowercase. Values are kept as written, without their outer braces or quotes.

## Identifiers

A cited entry must carry an identifier under which a catalogue lists the work, so that its
metadata can be checked against that catalogue: a `doi`, a zbMATH number `zbl` (such as
`0940.14012`), a MathSciNet number `mrnumber`, or an arXiv `eprint`. `BibEntry.identifiers`
returns those of an entry, and fails on one that is malformed. A zbMATH document number `zbmath`
alone does not count: the `zbl` number is the one that zbMATH's addresses use.
-/

public meta section

open Lean Std.Internal.Parsec String

namespace Lib.Cite

/-- An entry of a BibTeX file: its type and field names in lowercase, its key, its fields. -/
structure BibEntry where
  /-- The entry type, such as `article`. -/
  type : String
  /-- The key that citations use. -/
  key : String
  /-- The fields, with their values as written but for the outer braces or quotes. -/
  fields : Array (String × String)
  deriving Inhabited, Repr

/-- The value of the field `name` of the entry, when it has one. -/
def BibEntry.field? (e : BibEntry) (name : String) : Option String :=
  (e.fields.find? (·.1 == name)).map (·.2)

namespace BibParser

/-- The characters from the current position on that satisfy `p`. -/
def takeWhile (p : Char → Bool) : Parser String := manyChars (satisfy p)

/-- Move past the character `c`, or fail. -/
def expect (c : Char) : Parser Unit := do
  if (← peek?) == some c then skip else fail s!"expected '{c}'"

/-- The text up to `close`, outside braces, which closes a `{` or a `"` already read. -/
partial def delimited (close : Char) (depth : Nat := 0) (acc : String := "") : Parser String := do
  let opener := if close == '}' then '{' else close
  let some c ← peek? | fail s!"a '{opener}' is never closed"
  if close == '"' && c == '}' && depth == 0 then fail "a '}' inside quotes closes nothing"
  skip
  if c == close && depth == 0 then return acc
  delimited close (if c == '{' then depth + 1 else if c == '}' then depth - 1 else depth)
    (acc.push c)

/-- The month abbreviations that BibTeX defines: the only bare words a value may be. -/
def months : List String :=
  ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]

/-- One piece of a field's value: braced, quoted, a number or a month abbreviation. -/
def piece : Parser String := do
  match ← peek? with
  | some '{' => skip; delimited '}'
  | some '"' => skip; delimited '"'
  | some c =>
    if c.isDigit then takeWhile Char.isDigit
    else if c.isAlpha then
      let word ← takeWhile Char.isAlphanum
      if months.contains word.toLower then pure word.toLower
      else fail s!"the macro `{word}` is not supported"
    else fail s!"expected a value, but found '{c}'"
  | none => fail "expected a value, but the file ends"

/-- A field's value: pieces joined by `#`. -/
def value : Parser String := do
  let mut v ← piece
  ws
  while (← peek?) == some '#' do
    skip; ws
    v := v ++ (← piece)
    ws
  return v

/-- Whether `c` can be part of an entry type or a field name. -/
def isNameChar (c : Char) : Bool := c.isAlphanum || "-_.:+".contains c

/-- One `@type{key, field = value, …}`; `none` for a `@comment`, or for an `@` that no entry type
follows, which is text between entries. -/
def entry : Parser (Option BibEntry) := do
  expect '@'; ws
  let type := (← takeWhile Char.isAlpha).toLower
  if type.isEmpty then return none
  ws
  if type == "comment" then
    expect '{'; discard <| delimited '}'
    return none
  if type == "string" || type == "preamble" then fail s!"`@{type}` is not supported"
  expect '{'; ws
  let key ← takeWhile fun c => !c.isWhitespace && !",{}()\"#%'=".contains c
  if key.isEmpty then fail "expected the key of an entry"
  ws; expect ','
  let mut fields := #[]
  repeat
    ws
    if (← peek?) == some '}' then skip; break
    let name := (← takeWhile isNameChar).toLower
    if name.isEmpty then fail s!"expected a field of the entry `{key}`"
    if fields.any (·.1 == name) then fail s!"the field `{name}` of `{key}` is given twice"
    ws; expect '='; ws
    fields := fields.push (name, ← value)
    ws
    match ← peek? with
    | some ',' => skip
    | some '}' => skip; break
    | _ => fail s!"expected ',' or '}' after the field `{name}` of `{key}`"
  return some { type, key, fields }

/-- Every entry of a BibTeX file. As in BibTeX, the text between entries is ignored. -/
def bibFile : Parser (Array BibEntry) := do
  let mut entries := #[]
  repeat
    discard <| takeWhile (· != '@')
    if (← peek?).isNone then break
    if let some e ← entry then
      if entries.any (·.key == e.key) then fail s!"the key `{e.key}` is given twice"
      entries := entries.push e
  return entries

end BibParser

/-- The entries of the BibTeX file whose contents are `text`, or the reason it is malformed. -/
def parseBib (text : String) : Except String (Array BibEntry) :=
  match BibParser.bibFile ⟨text, text.startPos⟩ with
  | .success _ entries => .ok entries
  | .error ⟨s, pos⟩ err =>
    .error s!"line {((FileMap.ofString s).toPosition pos.offset).line}: {err}"

/-- `s` with each run of whitespace turned into one space, and none at the ends. -/
def squash (s : String) : String :=
  " ".intercalate ((s.splitToList Char.isWhitespace).filter (!·.isEmpty))

/-! ### Identifiers -/

/-- Whether `l` is nonempty and made of ASCII digits. -/
def allDigits (l : List Char) : Bool := !l.isEmpty && l.all Char.isDigit

/-- Whether `s` is a DOI: `10.`, a registrant code of at least four digits and dots, `/`, and a
suffix without whitespace. -/
def isDoi (s : String) : Bool :=
  match s.toList with
  | '1' :: '0' :: '.' :: rest =>
    let registrant := rest.takeWhile (· != '/')
    let suffix := (rest.dropWhile (· != '/')).drop 1
    registrant.length ≥ 4 && registrant.all (fun c => c.isDigit || c == '.') &&
      !suffix.isEmpty && suffix.all (!·.isWhitespace)
  | _ => false

/-- Whether `s` is a zbMATH number, four digits, a dot and five digits, such as `0940.14012`. -/
def isZbl (s : String) : Bool :=
  let l := s.toList
  l.length == 10 && allDigits (l.take 4) && l[4]? == some '.' && allDigits (l.drop 5)

/-- Whether `s` is a MathSciNet number: digits, after an optional `MR`. -/
def isMrNumber (s : String) : Bool :=
  let l := s.toList
  allDigits (if l.take 2 == ['M', 'R'] then l.drop 2 else l)

/-- `l` without a version suffix, a `v` followed by digits, when it has one. -/
def dropVersion (l : List Char) : List Char :=
  let r := l.reverse
  let digits := r.takeWhile Char.isDigit
  match r.drop digits.length with
  | 'v' :: rest => if digits.isEmpty then l else rest.reverse
  | _ => l

/-- Whether `s` is an arXiv identifier, with or without a version: `YYMM.NNNN` or `YYMM.NNNNN`
since 2007, `archive/YYMMNNN` or `archive.XX/YYMMNNN` before. -/
def isArxivId (s : String) : Bool :=
  let l := dropVersion s.toList
  let isNew := match l.drop 4 with
    | '.' :: num => allDigits (l.take 4) && (num.length == 4 || num.length == 5) && allDigits num
    | _ => false
  let archive := l.takeWhile (· != '/')
  let isOld := match l.drop archive.length with
    | '/' :: num =>
      !archive.isEmpty && archive.all (fun c => c.isAlpha || c == '-' || c == '.') &&
        num.length == 7 && allDigits num
    | _ => false
  isNew || isOld

/-- The DOI `d` without the resolver address that some entries write before it. -/
def bareDoi (d : String) : String :=
  let resolvers := ["https://doi.org/", "http://doi.org/", "https://dx.doi.org/",
    "http://dx.doi.org/"]
  match resolvers.find? fun (r : String) => d.startsWith r with
  | some r => (d.drop r.length).toString
  | none => d

/-- The fields that can identify an entry, with a test of the value and what the value should
be. -/
def identifierFields : List (String × (String → Bool) × String) := [
  ("doi", isDoi, "a DOI such as `10.1007/s10240-019-00102-z`"),
  ("zbl", isZbl, "a zbMATH number such as `0940.14012`"),
  ("mrnumber", isMrNumber, "a MathSciNet number: digits, after an optional `MR`"),
  ("eprint", isArxivId, "an arXiv identifier: `YYMM.NNNNN` or `archive/YYMMNNN`")]

/-- The identifiers of the entry: `(field, value)` for each of `doi`, `zbl`, `mrnumber` and an
arXiv `eprint` that it has, in this order, or an error naming the first that is malformed. An
`eprint` counts when the entry has no `archiveprefix`, or `arXiv`. A DOI is given without a
resolver address, and a MathSciNet number without `MR`. -/
def BibEntry.identifiers (e : BibEntry) : Except String (Array (String × String)) := do
  let arxiv := ((e.field? "archiveprefix").map (squash · |>.toLower)).all (· == "arxiv")
  let mut ids := #[]
  for (name, isValid, expected) in identifierFields do
    if name == "eprint" && !arxiv then continue
    let some v := e.field? name | continue
    let v := squash v
    let v := if name == "doi" then bareDoi v
      else if name == "mrnumber" && v.startsWith "MR" then (v.drop 2).toString else v
    unless isValid v do
      throw s!"the field `{name}` of `{e.key}` is `{v}`, which is not {expected}"
    ids := ids.push (name, v)
  return ids

end Lib.Cite
