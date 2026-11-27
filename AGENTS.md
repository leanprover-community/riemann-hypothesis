# AGENTS.md

Read [README.md](README.md) and [GUIDE.md](GUIDE.md) first. `main` is the readable edition of the
proof, and what we want now is a proof that people can read. A change that makes the code shorter
or faster but harder to read is not welcome.

If you have agent time to spare and no particular change in mind, work on the GRH roadmap of
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) instead.

## Changes we want

- Using a result from Mathlib or Tau Ceti in place of our own proof of it, and deleting ours.
- Deleting declarations that nothing uses.
- Proving once, as a lemma, an argument that appears several times.
- Splitting a long proof into lemmas with names and docstrings.
- A more general lemma in place of an old one, if its proof is about as easy. Move the callers to
  it and delete the old one.
- Fixing linter warnings, wrong docstrings and open issues.

## Changes we don't want

- Inlining a lemma into its only caller, or folding helper lemmas into one long proof. A lemma
  used once still tells the reader what that step proves.
- Cutting an `iff` down to one direction, or dropping conclusions from a lemma, because no caller
  needs them.
- Replacing `simp` with a long `simp only [...]` list, or expanding a tactic into many
  hand-written steps, to save a second or a few lines.
- Adding or changing a reference to the literature without checking it against the source. Say
  which edition you checked and give the theorem number.

## Pull requests

Keep each pull request to one change; fixing linter warnings in the files you edit doesn't count
as a second one. Check that it compiles (`lake exe cache get`, then `lake build`) before you open
it, but don't write in it that it builds or that nothing else changed: CI checks the build. Titles
follow [Mathlib's convention](https://leanprover-community.github.io/contribute/commit.html). In
the description, say in two or three sentences what the change does and why it makes the proof
easier to read. Leave out timings and heartbeat counts unless speed is the reason for the change;
then give the few numbers a maintainer needs to decide, and say how you measured them.

If you want to make the same kind of change in many places, open one pull request first and wait
for a maintainer to say we want it before you open the others.

A pull request is merged only after a reviewer (Triage role or more) has approved its current head
commit. When a reviewer hands it back to you with the `awaiting-author` label, make the changes
and then comment `ready`, with nothing else in the comment.

## Batches

A batch takes only pull requests that a reviewer has approved on their current head commit, and
none labelled `awaiting-author` or held by a maintainer. Merge each with its own merge commit. To
take one out, rebuild the batch without it and force-push; don't revert its merge commit. List the
pull requests you left out in the batch's description, with the reason for each.
