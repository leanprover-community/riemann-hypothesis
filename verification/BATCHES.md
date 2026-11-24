# Batches assembled by hand

A batch merges many pull requests into one branch so that they are built and landed together.
The batch-queue workflow (`.github/workflows/batch-queue.yml`, which runs
`scripts/batch-queue-sync.py`) assembles batches of its own from the queue. It also keeps the
labels and comments of a batch assembled by hand in step, as long as the batch follows the rules
below. This page is for whoever assembles one.

## Rules

1. **Use a branch of this repository named `batch/...`**, such as `batch/b9-on-1313`, and open
   its pull request against `main`. Don't use the name `batch/` followed by a date and time,
   such as `batch/2026-11-23-041230`: that form belongs to the workflow's own batches.
2. **Merge each pull request's head commit into the branch with a merge commit.** The workflow
   reads what a batch contains from its branch, not from its description: a pull request is in
   the batch when its head commit is. A squash, cherry-pick or rebase of a pull request makes new
   commits, so the pull request is not counted as in the batch, and GitHub does not mark it
   merged when the batch lands.
3. **Take pull requests that target `main`.** When the batch lands, GitHub marks a pull request
   merged only if its head commit reaches the branch the pull request targets. The workflow
   closes a pull request whose head landed but that targets another branch, and comments on it
   to say where its commits went.
4. **Merge the batch's pull request with a merge commit**, not a squash or a rebase, so that the
   head commits of the pull requests in it reach `main`.
5. **To take a pull request out, rebuild the branch without it and force-push.** Don't revert
   it: the reverted pull request's head commit would still be in the branch, so GitHub would mark
   it merged when the batch lands, although its changes did not land. After a force-push, the
   workflow looks through the branch again. A pull request that is no longer in it loses its
   labels, goes back to `batch queue` if it was queued, and is told that it can push again.
   - A force-push does not stop a build of the old head: `build-pr.yml` gives each head commit
     a concurrency group of its own and does not cancel runs in progress.
   - Most of what was already built is still used. The shared cache is keyed by each module's
     inputs, not by commit. Fragment builds publish the modules they finished even when they
     fail or are cancelled (see `scripts/rh-buildq/README.md`). So the new head rebuilds only
     the modules that depend on what was taken out. That is the same cost as reverting it.
6. **To add a pull request, merge its head commit in and push.** The workflow looks through the
   branch again on every push.
7. **List what is left out, and why, in the description.** People read the description to see
   which pull requests a batch contains. The workflow reads it only for what it leaves out:
   - A heading is a line of its own, not part of a list, that ends with a colon. Pull requests
     listed under a heading that contains "left out" or "not included" (in any letter case) are
     left out. For example: `Left out because they conflict with a PR earlier in the batch:`.
   - Each one is a list entry starting with `- ` and then a link to the pull request, either
     `#123` or its full URL. The rest of the entry is the reason. Lines indented under an entry,
     and entries that don't start with a link, are not read.
   - A list ends at the next heading or paragraph.

   Each pull request left out is sent a comment quoting the heading and its entry, and is
   labelled `awaiting-author`. Write the entry for its author: it is what they see. A pull
   request that an earlier batch, or an earlier version of the description, left out under the
   same heading (ignoring anything in parentheses) is not told again. Its comment is edited to
   show the new entry, which notifies nobody, so that `ready` is not undone every time a batch
   leaves it out for the same kind of reason. Keep the headings the same from one batch to the
   next for this to work. A pull request that is in the branch is never told it is left out,
   whatever the description says.
8. **Edit the description whenever the batch changes.** The workflow reads it again on every
   edit. A pull request listed under a new heading is sent a comment as above, one whose entry
   changed under the same heading has its comment brought up to date, and one whose entry is
   removed is told so.

## What the workflow does

While the batch's pull request is open, it is labelled `building`. Each open pull request whose
head commit is in the branch is labelled `batch-building` and `frozen`, in place of
`batch queue`. Each is asked once, in a comment, not to push until the batch has landed or been
closed. The workflow lists them in a comment of its own on the batch's pull request.

A pull request that is pushed to after the batch took its commit stays in the batch at the old
commit. It is told that the batch lands only that commit, and is labelled `awaiting-author`. If
its new head is merged into the branch, the batch holds that one instead.

When the batch is merged, what it contained loses `batch-building` and `frozen`. A pull request
whose head has moved on since the batch took it stays open, and is told what landed and what did
not. When the batch is closed without being merged, what it contained loses its labels too, is
told it can push again, and goes back to `batch queue` if it was queued.

A pull request queued with a `batch` comment is labelled `frozen` too, since the queue also takes
only the commit that was queued. `-batch` takes `frozen` off again, unless a batch being built
holds the pull request. A pull request that leaves a batch assembled by hand and goes back to the
queue stays `frozen`. After every run the workflow puts `frozen` back on a queued pull request
that has lost it, and takes `frozen` and `batch-building` off one that is neither queued nor in a
batch being built.

`batch-building`, `frozen` and `awaiting-author` keep a pull request out of the inbox (see
`.github/workflows/inbox.yml`). The label names are in `scripts/batch-labels.py`, and the `if:`
of the sync job in `.github/workflows/batch-queue.yml` and of `.github/workflows/conflict-labels.yml`
name some of them as well.

## Conflicts with main and with the batch

Another workflow (`.github/workflows/conflict-labels.yml`, which runs
`scripts/conflict-labels.py`) labels the open pull requests into `main` that are not drafts and
not batches:

- `main-conflict`: GitHub says the pull request conflicts with `main`. There is no comment,
  because GitHub shows the conflict too. A pull request that depends on an open batch does not
  get it (see below).
- `batch-conflict`: the pull request conflicts with the head of a batch being built, one labelled
  `building`. git cannot merge a file that both change since they left `main`, or one of the two
  deletes a Lean file that the other starts to import. The pull requests in the batch, labelled
  `batch-building`, never get it. The first time a pull request gets it for a batch, it is also
  labelled `awaiting-author` and told in a comment which files conflict and what to do.

Both labels come off by themselves once the reason has gone: the conflict was resolved, the pull
request was closed or joined the batch, or the batch was merged or closed. `awaiting-author` stays
until the author comments `ready`. `batch-conflict` keeps a pull request out of the inbox;
`main-conflict` does not, since a pull request that conflicts with `main` still needs a first look.

The workflow finds these conflicts from the branches alone, whatever the batch's description says.
A pull request that the description leaves out because it conflicts is told twice: once by the
batch queue, quoting its entry, and once by this workflow.

### If your pull request is labelled `batch-conflict`

1. Merge the batch's branch (`batch/...`, named in the comment) into your branch, or rebase onto
   it, and resolve the conflicts.
2. Add this line at the top of the description, where #123 is the batch's pull request:

   ```
   - [ ] depends on: #123
   ```

   Your pull request now carries the batch's changes, and may conflict with `main`, until the
   batch lands. The line says that this is expected, and keeps `main-conflict` off it.
3. Comment `ready`.

Or wait until the batch has landed, then merge `main` into your branch and resolve the conflicts
there.

A line counts as a dependency when it starts with `depends on`, `depend on` or `depends upon`,
optionally after `- [ ]` or `- [x]`, and names the batch's pull request as `#123` or by its
address.

## Several batches at once

A batch whose branch contains the head of another batch's pull request is built as part of it.
The other batch is treated as one of the pull requests it contains. If more than one batch
assembled by hand is open on `main`, the workflow's own batch is built on `main`, because it
cannot tell which of them lands first. The workflow cannot yet tell a batch that is being built
from one that waits for another to land: every open batch assembled by hand counts as being
built.
