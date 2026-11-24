# AGENTS.md

Read [README.md](README.md) first. It says what this repository is for, which changes are
welcome and how the proof is checked. Base your work on `main`; the `original` branch only
preserves the first published version of the proof. The rules below are the ones an agent is
most likely to break.

## Building

A full build takes hours, so fetch the cache before anything else:

```bash
lake exe cache get
lake build --no-build
```

The cached files were compiled elsewhere, so Lean does not re-check them. To check the proof
itself, follow [Checking the proof yourself](README.md#checking-the-proof-yourself).

## Pull requests

Don't open a pull request until the change is finished and you have checked that it compiles.
If you open one before then, open it as a draft (`gh pr create --draft`) and mark it ready for
review once it is done. A draft stays out of the maintainers' review queue.

To check that it compiles, bring your branch up to date with `main`, fetch the cache and run
`lake build`. Lake rebuilds the files you changed and every file that imports them, so this also
catches a lemma you removed that is still used somewhere else. It must finish without errors.

Keep each pull request to one change. Small pull requests are quicker to review and easier to
combine into a batch than one large one.

Titles follow [Mathlib's convention](https://leanprover-community.github.io/contribute/commit.html):

```
<type>(<optional-scope>): <subject>
```

The type is one of `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf` and `ci`.
The scope, if you give one, is the directory or file the change is in, without `src/`. Write the
subject in the imperative, start it with a lowercase letter and don't end it with a full stop.
For example:

```
refactor: reuse Mathlib lemmas in the primitive-character reflection proof
perf(GroundTheory/ArithmeticGeometry): speed up the acyclic Čech comparison in RelativeSerre
doc: document the Schrödinger and metaplectic representations over ℝ
```

Use this for the description:

```markdown
<What the pull request changes and why, in a few sentences. Name any declarations it
removes, renames or moves.>

---

- [ ] depends on: #123
```

Drop the part from `---` on if the pull request depends on no other.

## Do not

- change the Comparator challenge files: `src/Challenge.lean`, `comparator.json`,
  `export-targets.txt`, `comparator/FormalConjecturesChallenge.lean`,
  `comparator/formal-conjectures.json` and `comparator/formal-conjectures-export-targets.txt`.
  CI rejects any pull request that does.
- add axioms or `sorry`. `src/Main.lean` may use only `propext`, `Quot.sound` and
  `Classical.choice`.
- rewrite the proof along a substantially different path, or add files the proof does not need.
- report the results of your own builds or Comparator runs in a pull request. Check that your
  change compiles, but don't write that it builds on your machine; maintainers build pull
  requests themselves.

## Mistakes we keep seeing

These are changes agents often make that we don't want. Most of them hide a problem in one file
instead of fixing it where it comes from. We add to this list as we find more.

### Rewriting `nlinarith` by hand

Replacing `nlinarith` with `linarith` or `positivity` when that is enough is fine. Replacing it
with several `have` steps or a `calc` block to save a second or two is not: the longer proof is
harder to read, for people and for other agents. Try giving `nlinarith` the products it needs
first, or a short tactic such as `grind`.

### Old tactics

Your training data is older than the Lean and Mathlib this repository uses, so check what is
available in the versions pinned in `lean-toolchain` and `lake-manifest.json`. In new proofs,
use `lia` for linear arithmetic over `ℕ` and `ℤ` rather than `omega`, and try `grind` before
writing a long proof by hand. Don't open a pull request that only swaps one tactic for another.

### Switching off instances

Don't speed up a file by switching instances off with `attribute [-instance]` or promoting
others with `attribute [local instance high]`. That hides a slow instance search instead of
fixing it, and it ties the file to instances declared elsewhere, so it is hard to undo later.
Find the instance that sends the search the wrong way, for example with
`set_option trace.Meta.synthInstance true in` on the slow declaration, and fix it there.

### Small speed-ups to the CI scripts

We get many pull requests that shave a fraction of a second off a script in `scripts/` or
`tools/ci_native/`, such as reading a file once instead of twice or batching a few `git` calls.
Each one still needs a review from someone who knows the CI, and the time it saves disappears in
a build that takes hours, so please don't open these. Changes to the CI are welcome when they fix
a bug, close a gap in what is checked, or save time someone will notice, measured on the data the
step really handles rather than on a small fixture.
