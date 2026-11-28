import Lib.Cite.Export
import Lib.Cite.Report

/-!
Tests of `@[cite]`, `cite_source`, `#citations` and the export. Run them from the root of the
repository, with `Lib.Cite.Export` and `Lib.Cite.Report` built:

    lake env lean scripts/cite/Test.lean

They pass when the file elaborates without errors. The BibTeX file of these tests is
`scripts/cite/test.bib`.
-/

set_option cite.bibFile "scripts/cite/test.bib"

open Lean Elab Command Lib.Cite

/-- `#doc n` shows the docstring of `n`. -/
elab "#doc " n:ident : command => do
  let some d ← findDocString? (← getEnv) n.getId | logInfo "no docstring"
  logInfo d

/-! ### Citations of the BibTeX file -/

/-- A definition. -/
@[cite "testDoi" "Theorem 2.3" "with a comment"]
def a : Nat := 1

/--
info: A definition.

[testDoi], Theorem 2\.3 (with a comment). Not yet checked against the work.
-/
#guard_msgs in #doc a

@[cite "testZbl" "§1, p. 2" (quote := "Every test passes.") (checked := "A. Reader")]
def b : Nat := a + 1

/-- info: [testZbl], §1\, p\. 2. Checked against the work by A. Reader. -/
#guard_msgs in #doc b

@[cite "testArxiv" "Lemma 1", cite "testOldArxiv" "p. 3"]
def c : Nat := b + 1

/--
info: [testArxiv], Lemma 1. Not yet checked against the work.

[testOldArxiv], p\. 3. Not yet checked against the work.
-/
#guard_msgs in #doc c

@[cite "testResolver" "p. 1", cite "testMr" "p. 2"]
def d : Nat := 0

/--
info: [testResolver], p\. 1. Not yet checked against the work.

[testMr], p\. 2. Not yet checked against the work.
-/
#guard_msgs in #doc d

/-! ### Errors -/

/-- error: A citation must say where in the work the result is: `@[cite "testDoi" "Theorem 2.3"]`. -/
#guard_msgs in @[cite "testDoi"] def noLocator : Nat := 0

/-- error: A citation must say where in the work the result is: `@[cite "testDoi" "Theorem 2.3"]`. -/
#guard_msgs in @[cite "testDoi" " "] def blankLocator : Nat := 0

/-- error: No entry `missing` in the BibTeX file `scripts/cite/test.bib`. -/
#guard_msgs in @[cite "missing" "p. 1"] def missingKey : Nat := 0

/-- error: `bad key` is not a valid BibTeX key. -/
#guard_msgs in @[cite "bad key" "p. 1"] def badKey : Nat := 0

/--
error: The entry `testNone` cannot be cited: it has no `doi`, `zbl`, `mrnumber` or arXiv `eprint`, so nobody can look the work up in a catalogue.
-/
#guard_msgs in @[cite "testNone" "p. 1"] def noIdentifier : Nat := 0

/--
error: The entry `testZbmath` cannot be cited: it has no `doi`, `zbl`, `mrnumber` or arXiv `eprint`, so nobody can look the work up in a catalogue.
-/
#guard_msgs in @[cite "testZbmath" "p. 1"] def onlyZbmath : Nat := 0

/--
error: The entry `testBadDoi` cannot be cited: the field `doi` of `testBadDoi` is `11.5555/bad`, which is not a DOI such as `10.1007/s10240-019-00102-z`.
-/
#guard_msgs in @[cite "testBadDoi" "p. 1"] def badDoi : Nat := 0

/--
error: The entry `testOtherArchive` cannot be cited: it has no `doi`, `zbl`, `mrnumber` or arXiv `eprint`, so nobody can look the work up in a catalogue.
-/
#guard_msgs in @[cite "testOtherArchive" "p. 1"] def otherArchive : Nat := 0

/--
error: The entry `testBadArxiv` cannot be cited: the field `eprint` of `testBadArxiv` is `2101.1`, which is not an arXiv identifier: `YYMM.NNNNN` or `archive/YYMMNNN`.
-/
#guard_msgs in @[cite "testBadArxiv" "p. 1"] def badArxiv : Nat := 0

/--
error: The entry `testBadZbl` cannot be cited: the field `zbl` of `testBadZbl` is `940.14012`, which is not a zbMATH number such as `0940.14012`.
-/
#guard_msgs in @[cite "testBadZbl" "p. 1"] def badZbl : Nat := 0

/-- error: Unknown field `page`; a citation takes `quote`, `checked`, `form` and `comparison`. -/
#guard_msgs in @[cite "testDoi" "p. 1" (page := "1")] def unknownField : Nat := 0

/-- error: The field `checked` is given twice. -/
#guard_msgs in
@[cite "testDoi" "p. 1" (checked := "A") (checked := "B")] def fieldTwice : Nat := 0

/-- error: The field `checked` cannot be empty. -/
#guard_msgs in @[cite "testDoi" "p. 1" (checked := "")] def emptyField : Nat := 0

def later : Nat := 0

/-- error: Invalid attribute scope: Attribute `[cite]` must be global, not `local` -/
#guard_msgs in attribute [local cite "testDoi" "p. 1"] later

-- the message names the working directory, so only its start is compared
/-- info: true -/
#guard_msgs in
run_cmd do
  let msg ← try
      liftCoreM <| withOptions (cite.bibFile.set · "scripts/cite/missing.bib") <|
        discard <| citedEntry "testDoi"
      pure ""
    catch e => e.toMessageData.toString
  logInfo m!"{msg.startsWith "Cannot read the BibTeX file `scripts/cite/missing.bib` from"}"

/-! ### Declared sources -/

/-- A source for the tests. -/
cite_source testdb "the test database" (uri := "https://example.com/entry/{id}") (type := "html")
  (registry := "test-db")

cite_source testpdf "a test book" (uri := "https://example.com/book.pdf") (type := "pdf")

@[cite testdb "A 1/2" "a comment"]
def e : Nat := c + 1

/--
info: [the test database A 1\/2](https://example.com/entry/A%201/2) (a comment). Not yet checked against the work.
-/
#guard_msgs in #doc e

@[cite testpdf "Chapter 3" (checked := "B. Writer")]
def f : Nat := e + 1

/--
info: [a test book Chapter 3](https://example.com/book.pdf). Checked against the work by B. Writer.
-/
#guard_msgs in #doc f

/-- error: Unknown source `unknowndb`; declare it with `cite_source`. -/
#guard_msgs in @[cite unknowndb "1"] def unknownSource : Nat := 0

/-- error: The cited entry cannot be empty. -/
#guard_msgs in @[cite testdb ""] def emptyEntry : Nat := 0

/-- error: The source `testdb` is already declared, in module `scripts.cite.Test`. -/
#guard_msgs in cite_source testdb "again" (uri := "https://example.com")

/-- error: A source needs an address: `(uri := "https://…")`. -/
#guard_msgs in cite_source nouri "a source without an address"

/-- error: The field `uri` is given twice. -/
#guard_msgs in
cite_source twice "a source" (uri := "https://example.com") (uri := "https://example.org")

/-! ### `#citations` -/

@[stacks 0BR2]
theorem t : True := trivial

theorem g : f = 5 ∧ True := ⟨rfl, t⟩

/--
info: Citations that `g` depends on, among 43 declarations:

a test book (testpdf)
  Chapter 3: f, checked by B. Writer

testArxiv
  Lemma 1: c, not checked

testDoi
  Theorem 2.3 (with a comment): a, not checked

testOldArxiv
  p. 3: c, not checked

testZbl
  §1, p. 2: b, checked by A. Reader

the test database (testdb)
  A 1/2 (a comment): e, not checked

Stacks Tag (Mathlib)
  0BR2: t

6 citations of 6 works, 4 of them not checked against the work; 1 cross-reference to 1 database.
-/
#guard_msgs in #citations g

/--
info: Citations that `a` depends on, among 8 declarations:

testDoi
  Theorem 2.3 (with a comment): a, not checked

1 citation of 1 work, 1 of them not checked against the work; 0 cross-references to 0 databases.
-/
#guard_msgs in #citations a

/-! ### The form of a citation -/

@[cite "testDoi" "Definition 1.1" (form := "same")]
def h : Nat := 2

/-- info: [testDoi], Definition 1\.1. In the cited form. Not yet checked against the work. -/
#guard_msgs in #doc h

@[cite "testDoi" "Definition 1.2" "as a sum" (form := "equivalent") (comparison := "i_eq")]
def i : Nat := 1 + 1

theorem i_eq : i = 2 := rfl

/--
info: [testDoi], Definition 1\.2 (as a sum). Equivalent to the cited form; the comparison is `i_eq`. Not yet checked against the work.
-/
#guard_msgs in #doc i

@[cite "testZbl" "§2" "over the naturals only" (form := "special case") (checked := "A. Reader")]
theorem i_pos : 0 < i := Nat.succ_pos 1

@[cite "testZbl" "§3" "a different object" (form := "substitute") (comparison := "h")]
def j : Nat := i + h

/--
info: [testZbl], §3 (a different object). Used in place of the cited object; the comparison is `h`. Not yet checked against the work.
-/
#guard_msgs in #doc j

@[cite "testArxiv" "Lemma 2" "one direction" (form := "weaker") (comparison := "missing_thm")]
def k : Nat := j

theorem uses : k = 4 ∧ 0 < i := ⟨rfl, i_pos⟩

/--
info: Citations that `uses` depends on, among 75 declarations:

testArxiv
  Lemma 2 (one direction): k, not checked, weaker

testDoi
  Definition 1.1: h, not checked, same
  Definition 1.2 (as a sum): i, not checked, equivalent

testZbl
  §2 (over the naturals only): i_pos, checked by A. Reader, special case
  §3 (a different object): j, not checked, substitute

5 citations of 3 works, 4 of them not checked against the work; 0 cross-references to 0 databases.

Not in the cited form (4):
  equivalent: i, testDoi, Definition 1.2 (as a sum), compared by i_eq
  special case: i_pos, testZbl, §2 (over the naturals only), no comparison proved here
  weaker: k, testArxiv, Lemma 2 (one direction), compared by missing_thm
  substitute: j, testZbl, §3 (a different object), compared by h
---
warning: The citation of `j` names `h` as its comparison, whose statement does not mention `j`.
---
warning: The citation of `k` names `missing_thm` as its comparison, which is not a declaration.
-/
#guard_msgs in #citations uses

/--
error: Unknown form `close`; the forms are `same`, `equivalent`, `special case`, `generalisation`, `weaker` and `substitute`.
-/
#guard_msgs in @[cite "testDoi" "p. 1" "a comment" (form := "close")] def unknownForm : Nat := 0

/--
error: A citation of the form `weaker` must say what differs, in a comment after the locator.
-/
#guard_msgs in @[cite "testDoi" "p. 1" (form := "weaker")] def noDifference : Nat := 0

/--
error: The field `comparison` names the theorem that compares the declaration with the cited form, so it needs a `form` other than `same`.
-/
#guard_msgs in
@[cite "testDoi" "p. 1" (form := "same") (comparison := "i_eq")] def sameCompared : Nat := 0

/-- error: `i eq` is not the name of a declaration. -/
#guard_msgs in
@[cite "testDoi" "p. 1" "a comment" (form := "weaker") (comparison := "i eq")]
def badComparison : Nat := 0

/-! ### The export -/

/--
info: Wrote 13 Literature Links annotations to scripts/cite/test-out.jsonl
---
info: {"id":"testArxiv:Lemma 1","object":[{"location":{"declaration":"c","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testArxiv","title":"A test entry with an arXiv identifier","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"key":"testArxiv","locator":"Lemma 1"}},"title":"Lemma 1","type":"html","uri":"https://arxiv.org/abs/2101.00001v2"}]}
{"id":"testArxiv:Lemma 2","object":[{"location":{"declaration":"k","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testArxiv","title":"A test entry with an arXiv identifier","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"comment":"one direction","comparison":"missing_thm","form":"weaker","key":"testArxiv","locator":"Lemma 2"}},"title":"Lemma 2 (one direction)","type":"html","uri":"https://arxiv.org/abs/2101.00001v2"}]}
{"id":"testDoi:Definition 1.1","object":[{"location":{"declaration":"h","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"DOI":"10.5555/test-entry","author":[{"family":"Reader","given":"Anne"},{"family":"Writer","given":"Bo"}],"id":"testDoi","issued":{"date-parts":[[2001]]},"title":"A test entry with a DOI","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"form":"same","key":"testDoi","locator":"Definition 1.1"}},"title":"Definition 1.1","type":"html","uri":"https://doi.org/10.5555/test-entry"}]}
{"id":"testDoi:Definition 1.2","object":[{"location":{"declaration":"i","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"DOI":"10.5555/test-entry","author":[{"family":"Reader","given":"Anne"},{"family":"Writer","given":"Bo"}],"id":"testDoi","issued":{"date-parts":[[2001]]},"title":"A test entry with a DOI","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"comment":"as a sum","comparison":"i_eq","form":"equivalent","key":"testDoi","locator":"Definition 1.2"}},"title":"Definition 1.2 (as a sum)","type":"html","uri":"https://doi.org/10.5555/test-entry"}]}
{"id":"testDoi:Theorem 2.3","object":[{"location":{"declaration":"a","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"DOI":"10.5555/test-entry","author":[{"family":"Reader","given":"Anne"},{"family":"Writer","given":"Bo"}],"id":"testDoi","issued":{"date-parts":[[2001]]},"title":"A test entry with a DOI","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"comment":"with a comment","key":"testDoi","locator":"Theorem 2.3"}},"title":"Theorem 2.3 (with a comment)","type":"html","uri":"https://doi.org/10.5555/test-entry"}]}
{"id":"testMr:p. 2","object":[{"location":{"declaration":"d","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testMr","title":"A test entry with a MathSciNet number","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"key":"testMr","locator":"p. 2"}},"title":"p. 2","type":"html","uri":"https://mathscinet.ams.org/mathscinet-getitem?mr=0000001"}]}
{"id":"testOldArxiv:p. 3","object":[{"location":{"declaration":"c","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testOldArxiv","title":"A test entry with an old arXiv identifier","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"key":"testOldArxiv","locator":"p. 3"}},"title":"p. 3","type":"html","uri":"https://arxiv.org/abs/math.AG/0601001"}]}
{"id":"testResolver:p. 1","object":[{"location":{"declaration":"d","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"DOI":"10.5555/resolved","id":"testResolver","title":"A test entry whose DOI is an address","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"key":"testResolver","locator":"p. 1"}},"title":"p. 1","type":"html","uri":"https://doi.org/10.5555/resolved"}]}
{"id":"testZbl:§1, p. 2","object":[{"location":{"declaration":"b","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testZbl","title":"A test entry with a zbMATH number","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"checkedBy":"A. Reader","key":"testZbl","locator":"§1, p. 2","quote":"Every test passes."}},"title":"§1, p. 2","type":"html","uri":"https://zbmath.org/?q=an:0000.00000"}]}
{"id":"testZbl:§2","object":[{"location":{"declaration":"i_pos","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testZbl","title":"A test entry with a zbMATH number","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"checkedBy":"A. Reader","comment":"over the naturals only","form":"special case","key":"testZbl","locator":"§2"}},"title":"§2 (over the naturals only)","type":"html","uri":"https://zbmath.org/?q=an:0000.00000"}]}
{"id":"testZbl:§3","object":[{"location":{"declaration":"j","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"citation":{"id":"testZbl","title":"A test entry with a zbMATH number","type":"document"},"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"comment":"a different object","comparison":"h","form":"substitute","key":"testZbl","locator":"§3"}},"title":"§3 (a different object)","type":"html","uri":"https://zbmath.org/?q=an:0000.00000"}]}
{"id":"testdb:A 1/2","object":[{"location":{"declaration":"e","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"comment":"a comment","id":"A 1/2","source":"testdb"}},"identifiers":{"test-db":"A 1/2"},"title":"the test database A 1/2 (a comment)","type":"html","uri":"https://example.com/entry/A%201/2"}]}
{"id":"testpdf:Chapter 3","object":[{"location":{"declaration":"f","module":"scripts.cite.Test"},"type":"lean","uri":"https://example.com/repo","version":"abc123"}],"subject":[{"extensions":{"org.leanprover-community.riemann-hypothesis.cite":{"checkedBy":"B. Writer","id":"Chapter 3","source":"testpdf"}},"title":"a test book Chapter 3","type":"pdf","uri":"https://example.com/book.pdf"}]}
-/
#guard_msgs in
run_cmd do
  liftCoreM <| exportCitations "scripts/cite/test-out.jsonl" "https://example.com/repo" "abc123"
  logInfo (← IO.FS.readFile "scripts/cite/test-out.jsonl")
  IO.FS.removeFile "scripts/cite/test-out.jsonl"

/--
error: cannot export the citations: No entry `missing` in the BibTeX file `scripts/cite/test.bib`.
-/
#guard_msgs in
run_cmd do
  modifyEnv (citeExt.addEntry · { declName := ``a, source := .bib "missing", id := "p. 1" })
  liftCoreM <| exportCitations "scripts/cite/test-out.jsonl" "https://example.com/repo" "abc123"
