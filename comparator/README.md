# The second Comparator setup: formal-conjectures

These notes were written by people checking the proof, not by its author. They are brought over
from the branch `alpoge`, whose
[`verification/NOTES.md`](https://github.com/leanprover-community/riemann-hypothesis/blob/756a70250dcba9162b99d4ea35c186558434c17e/verification/NOTES.md)
has the notes on the proof as it was first published, and updated for `main`.

The first Comparator setup, `Challenge.lean`, `comparator.json` and `export-targets.txt` at the
root, judges the proof against its own five statements: Mathlib's `RiemannHypothesis` and four
that came with the proof. `Challenge.lean` imports only Mathlib and repeats their definitions,
and `src/Statements.lean` has them for the solution. The second setup, in this folder, judges
the proof against statements written elsewhere and earlier:
[`FormalConjectures/Millennium/RiemannHypothesis.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/Millennium/RiemannHypothesis.lean)
in google-deepmind/formal-conjectures, at commit `d8d031d4` (2026-11-19). It follows
[issue #34](https://github.com/leanprover-community/riemann-hypothesis/issues/34), which proved
the equivalence used here against that commit.

This folder holds a challenge, a config, a list of export targets, and three files for the
solution side. [#88](https://github.com/leanprover-community/riemann-hypothesis/pull/88) added
them on `alpoge`. The Lean files are as they were there, except that two docstrings now point to
this file, so they still call the proof under `src/` "the submission". The config has the form
of the first setup's `comparator.json`, so both setups run the same checkers.

**The statements.**

- `RiemannHypothesis.riemannHypothesis` is Mathlib's `RiemannHypothesis`, as our
  `riemannHypothesis` is.
- `GRH.generalized_riemann_hypothesis` says: for every modulus q ≥ 1, every primitive character
  χ mod q and every s in ℂ, if L(χ, s) = 0 and s is not in `GRH.trivialZeros χ`, then
  Re s = 1/2. The trivial zeros are −2(n+1) for q = 1, −2n−1 for odd χ, and −2n for even χ with
  q ≠ 1, n ranging over ℕ.
- On its face that is more than `PrimitiveDirichletLZerosOnLine`, which speaks only of
  0 < Re s < 1: none of our three Dirichlet statements says anything about zeros with
  Re s ≤ 0. The bridge below shows that nothing is lost.
- The statement of the theorem has had the same text since it was added on 2025-11-06, and the
  definition of `trivialZeros` since 2025-11-07; only its docstring changed after that. We
  compared every commit that has touched the file, up to `9097e2f9` (2026-11-24).
- On 2026-11-24, after the commit copied here, formal-conjectures marked both theorems as
  solved, with links to this repository
  ([#8111](https://github.com/google-deepmind/formal-conjectures/pull/8111)). For GRH it links
  to `comparator/FormalConjecturesBridge.lean` and `src/Main.lean` at commit `d27f7134`, which
  is on `alpoge`. The statements did not change.

**Credit.** These statements are the work of the formal-conjectures authors, and what is copied
from them here is under their Apache 2.0 license.

| Date | Who | What, with the formal-conjectures pull request |
|---|---|---|
| 2025-11-06 | Salvatore Mercuri | wrote `GRH.trivialZeros`, `GRH.generalized_riemann_hypothesis`, the test that GRH for the character mod 1 is Mathlib's `RiemannHypothesis`, and the `Decidable` instances for odd and even characters ([#1176](https://github.com/google-deepmind/formal-conjectures/pull/1176)) |
| 2025-11-07 | Salvatore Mercuri | corrected the sign in the odd case of `trivialZeros` ([#1184](https://github.com/google-deepmind/formal-conjectures/pull/1184)) |
| 2026-01-15 | mirefek | corrected the docstring of `trivialZeros` ([#1677](https://github.com/google-deepmind/formal-conjectures/pull/1677)) |
| 2026-03-01 | franzhusch | added `riemannHypothesis`, stated with Mathlib's `RiemannHypothesis` ([#2378](https://github.com/google-deepmind/formal-conjectures/pull/2378)) |
| 2026-04-24 | Moritz Firsching | put it in the namespace `RiemannHypothesis` ([#3827](https://github.com/google-deepmind/formal-conjectures/pull/3827)) |

Between and after these, Yaël Dillies, Moritz Firsching, Robert Joseph, Felix Pernegger and
Sylvester Kaczmarek moved, restructured or extended the two files the declarations are in.

**A copy, not an import.** Comparator needs the challenge and the solution to be built against
the same Mathlib. This project is on Lean `v4.37.0-rc1` and Mathlib `31ce06ea`, and
formal-conjectures on Lean `v4.33.1` and Mathlib `0df444a3`. So the challenge is
[`FormalConjecturesChallenge.lean`](FormalConjecturesChallenge.lean), a copy that
imports only Mathlib and is built against this project's pins. It differs from
formal-conjectures' text at commit `d8d031d4` in three ways:

- The instance has no name there. The name Lean generates for it there ends in
  `_formalConjecturesForMathlib`, and the copy writes that name out, because Comparator matches
  constants by name.
- `trivialZeros` is marked `noncomputable`, which Lean `v4.36.0` and later require. It does not
  change the definition the kernel sees: Lean `v4.35.0` accepts the definition with it or
  without, and exports the same bytes for it either way.
- formal-conjectures' own `category` and `AMS` attributes are left out.

Two declarations of those files are not copied, because the statements do not use them: the
test `GRH.implies_riemannHypothesis` and the `Decidable` instance for even characters.

CI fetches the two formal-conjectures files at that commit and checks that each copied
declaration is their text, with those three differences and no others. It also checks that
the copy holds nothing else but comments, its import, and the `module`, `section` and
`namespace` lines: no `open`, no option, no declaration of its own. On `alpoge` the copy was
also built on formal-conjectures' own pins and judged against the export of formal-conjectures'
own file; the notes there have that run.

**What the solution has to copy.** Comparator compares, by name, every constant that the
challenge's statements use. For `GRH.generalized_riemann_hypothesis`, three of them are not in
Mathlib:

| Constant | Where formal-conjectures defines it |
|---|---|
| `GRH.trivialZeros` | `FormalConjectures/Millennium/RiemannHypothesis.lean` |
| `DirichletCharacter.instDecidablePredOddOfDecidableEq_formalConjecturesForMathlib` | `FormalConjecturesForMathlib/NumberTheory/DirichletCharacter/Basic.lean`; the `if χ.Odd` in `trivialZeros` uses it |
| the same name with `._proof_1` | generated by Lean for the `by rfl` in that instance |

The solution cannot import the challenge, which declares the theorems it has to prove. So
[`FormalConjecturesStatement.lean`](FormalConjecturesStatement.lean) repeats the
first two, as the challenge has them. Both files are `module`s, as the upstream files are, and
that matters: in a `module`, Lean states `_proof_1` as `ψ (-1) = -1 ↔ ψ.Odd`, and in an ordinary
file as `ψ (-1) = -1 ↔ ψ (-1) = -1`. On `alpoge` a first version of the copy was an ordinary
file, and `lake comparator` rejected it:
`Const does not match between challenge and target '…_formalConjecturesForMathlib._proof_1'`.

**Where the solution states the theorem.** The solution must state the theorem as the challenge
does. On its side the statement is written once, in the signature of
`FormalConjecturesBridge.generalized_riemann_hypothesis_of_primitive`, and
`FormalConjecturesSolution.lean` takes it from there with `type_of%`.

- It is not written in `FormalConjecturesSolution.lean`, because that file imports the proof.
  Lean would elaborate the statement with every instance of the proof in scope, and one of
  those could be chosen in place of Mathlib's. Comparator would reject that, but only after the
  build. `Statements.lean` is safe from this for the same reason the bridge is: no proof under
  `src/` is imported.
- It is not a definition that the solution unfolds, either. The `2` in `1 / 2` carries a proof
  of `Nat.AtLeastTwo 2`. In the body of a definition Lean moves that proof into a constant of
  its own, and in the statement of a theorem it leaves it in place. On `alpoge`,
  `lake comparator` rejected that version too:
  `Challenge and solution theorem statement do not match: 'GRH.generalized_riemann_hypothesis'`.

Nobody has to trust the solution's copies. Comparator rejects a solution in which the statement
or any of the three constants differs from the challenge.

**The bridge.**
[`FormalConjecturesBridge.lean`](FormalConjecturesBridge.lean) proves
`PrimitiveDirichletLZerosOnLine ↔` formal-conjectures' GRH. It imports `Statements.lean` and
Mathlib, and none of the proofs under `src/`.

- Re s ≥ 1: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, and `riemannZeta_one_ne_zero`
  for q = 1 and s = 1.
- 0 < Re s < 1: the proof's statement.
- Re s ≤ 0: χ⁻¹ is primitive too. The functional equation and L(χ⁻¹, 1 − s) ≠ 0 give
  Λ(χ, s) ≠ 0, so L(χ, s) = 0 only at a pole of the Gamma factor, and those are the trivial
  zeros. The root number is not needed.
- The converse holds because the trivial zeros are integers ≤ 0.

[`FormalConjecturesSolution.lean`](FormalConjecturesSolution.lean) then
proves the two theorems, under formal-conjectures' names, by applying the bridge to
`LFunction_eq_zero_re_of_isPrimitive` and by `riemannHypothesis`, both from `src/Main.lean`.

**No Lake library.** The files in `comparator/` are in no library of `lakefile.toml` and not
under `src/`. A library for them would mean a change to `lakefile.toml`, which is one of the
inputs the build cache is selected by ([CACHE.md](../CACHE.md)) and which says what the first
setup builds. So this setup cannot use plain `lake comparator`, which has Lake build both
modules. It compiles the files with `lake env lean`, into `.lake/comparator/`, and gives
Comparator exports. The `[leanOptions]` of the lakefile do not apply to files compiled this way.

**Checking it.** `lake comparator` needs Linux with
[bubblewrap](https://github.com/containers/bubblewrap). To have Lean check every proof on your
machine, build the proof from source, without `lake exe cache get` ([CACHE.md](../CACHE.md)).

```bash
export LEAN_ABORT_ON_PANIC=1        # as Comparator does

# in a clone where the proof has not been compiled, after `lake exe mathlib/cache get`
mkdir -p .lake/comparator
lake env lean --root=comparator \
  -o .lake/comparator/FormalConjecturesChallenge.olean comparator/FormalConjecturesChallenge.lean
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport FormalConjecturesChallenge -- \
  $(cat comparator/formal-conjectures-export-targets.txt) > fc-challenge.export

# wherever you build the proof, after `lake build Main`
mkdir -p .lake/comparator
for m in FormalConjecturesStatement FormalConjecturesBridge FormalConjecturesSolution; do
  LEAN_PATH="$PWD/.lake/comparator" lake env lean --root=comparator \
    -o ".lake/comparator/$m.olean" "comparator/$m.lean"
done
LEAN_PATH="$PWD/.lake/comparator" lake env leanexport FormalConjecturesSolution -- \
  $(cat comparator/formal-conjectures-export-targets.txt) > fc-solution.export

# in the clone: `lake comparator` looks on PATH for the checkers that come with Lean
export PATH="$(lean --print-prefix)/bin:$PATH"

# then from an empty directory, with the two exports and a copy of
# comparator/formal-conjectures.json
lake comparator --config formal-conjectures.json \
  --challenge-from-export fc-challenge.export --solution-from-export fc-solution.export
```

The export of `FormalConjecturesSolution` contains the whole proof, as the export of `Main`
does, plus the bridge. Making it and judging it cost what exporting and judging `Main` cost.

**Rehearsal.** The real run needs the built proof, and CI does not make it. The workflow
[`comparator.yml`](../.github/workflows/comparator.yml) runs the steps above with a placeholder
`Main.lean`, which states the five theorems of `src/Main.lean` and proves them by `sorry`. The
exports are made in the job, so the judge runs with `--inadvisably-no-sandbox`. It must give
these verdicts:

| Config | Verdict |
|---|---|
| `formal-conjectures.json` | rejected, with `Illegal axiom detected: 'sorryAx'` and nothing else |
| the same, with `sorryAx` permitted | nanoda and Lean's kernel accept: `Your solution is okay!` |

So the solution's statement and its three constants match the challenge's, and the kernels
accept the bridge. The rehearsal does not compile `FormalConjecturesSolution.lean` against the
real `Main.lean`. That needs `riemannHypothesis` and `LFunction_eq_zero_re_of_isPrimitive`,
which `Main.lean` has, and no declaration under `src/` with a name the files here use.

The workflow rehearses the first setup in the same way, with `comparator.json`, the export of
`Challenge.lean` and the export of the placeholder. There the verdicts say that the definitions
in `Challenge.lean` and in `src/Statements.lean` are the same.

The workflow runs when something it reads changes: `Challenge.lean`, `comparator.json`,
`export-targets.txt`, `comparator/`, `src/Statements.lean`, `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`, or the workflow itself. No other change can alter its
result, so pull requests that touch only the proof, the scripts or the documentation do not run
it. GitHub looks at the first 3,000 changed files only, so a larger pull request that changes
one of these needs a manual run.

**Frozen files.** Three files say what the proof is judged against in this setup:
`FormalConjecturesChallenge.lean`, `formal-conjectures.json` and
`formal-conjectures-export-targets.txt`. A pull request may not change them.
[`challenge-files.yml`](../.github/workflows/challenge-files.yml) lists them with the first
setup's files. GitHub runs the default branch's copy of that workflow for every pull request,
and it fails if one of them differs between where the pull request branched off and its head.

The pins are not frozen. So `comparator.yml`, which runs when a pin changes, also checks the
checksums of both challenge exports. For Lean `v4.37.0-rc1` and Mathlib `31ce06ea`:

| Export | Bytes | sha256 |
|---|---|---|
| `challenge.export`, of `Challenge.lean` | 363,237,517 | `bb37c4bb518fe68a13f12aa3929dd62dfecb663f0c063ad8c338e39601f28a60` |
| `fc-challenge.export`, of `FormalConjecturesChallenge.lean` | 363,240,200 | `d08f9a601253ac28f09d7a64f674fd4227e665d573eae437a582f41f0ecb262c` |

Those are the pins `alpoge` ended on, and its CI checked the same two values. A change of pins
changes the exports, the job fails, and its summary shows the new checksums to put in the
workflow and here. An export also records the line each `sorry` of its challenge is on, so the
checksum changes if a line is added above one, even in a comment.
