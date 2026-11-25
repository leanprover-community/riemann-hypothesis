# Batches assembled by hand

A batch merges many pull requests into one branch so that they are built and landed together.
The batch queue is a list of approvals, and maintainers assemble batches from it by hand. The
batch-queue workflow (`.github/workflows/batch-queue.yml`, which runs
`scripts/batch-queue-sync.py`) assembles none of its own: that code is switched off by `ASSEMBLE`
in the script. It keeps the labels and comments of a batch assembled by hand in step, as long as
the batch follows the rules below. This page is for whoever assembles one.

## Labels at a glance

The sections below give the details. A row marked *(planned)* describes a label that a pull
request still under review adds. Until it lands, the label exists but nothing puts it on.

| Label | On | Put on when | Taken off when |
|---|---|---|---|
| `building` | the pull request of a batch assembled by hand | its branch holds the head of an open pull request | the batch is merged or closed, once its members are tidied up after |
| `batch-building` | each pull request in that batch | the batch takes its head commit | it leaves the branch; the batch is merged or closed; it is closed |
| `frozen` | each pull request in that batch, and each queued pull request | with `batch-building`, or with `batch queue` on a `batch` comment | it is neither queued nor in a batch being built: `-batch`, it leaves the batch, the batch is merged or closed, it is closed |
| `changed after frozen` *(planned, #1697)* | a frozen pull request whose head has moved on from the commit taken | it is pushed to after a batch or the queue took a commit of it | its head is that commit again, or it is no longer frozen |
| `batch queue` | a pull request wanted in a batch | a maintainer or reviewer comments `batch` or `p` | `-batch`; it joins a batch assembled by hand (in exchange for `batch-building`); its queued commit lands; it is closed |
| `priority` | a queued pull request that goes first | `p` | by hand |
| `awaiting-author` | a pull request handed back to its author | `aa`; it is pushed to while in a batch; the description leaves it out; a batch lands an older commit of it; `batch-conflict` is first put on it *(planned, #1700)* | `ready`, by the author or a maintainer |
| `main-conflict` *(planned, #1700)* | a pull request that conflicts with `main` | GitHub says so, unless it declares `depends on:` a batch being built | the conflict is gone, or it declares that dependency |
| `batch-conflict` *(planned, #1700)* | a pull request that conflicts with a batch being built | git cannot merge it with the batch's head | the conflict is gone; the batch lands or is closed; it joins the batch |

`batch queue`, `building`, `batch-building`, `frozen` and `awaiting-author` keep a pull request
out of the inbox (`inbox`, see `.github/workflows/inbox.yml`), and so will `batch-conflict`
*(planned, #1700)*. The names are in `scripts/batch-labels.py`.

Also planned *(#1707)*: a check of each batch's description against its branch, posted on the
batch's pull request. It reports pull requests listed as included that aren't in the branch, members the
description doesn't mention, and pull requests reverted in the branch.

## Rules

1. **Use a branch of this repository named `batch/...`**, such as `batch/b9-on-1313`, and open
   its pull request against `main`. Don't use the name `batch/` followed by a date and time,
   such as `batch/2026-11-23-041230`: that form belongs to the workflow's own batches, which
   are switched off for now.
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
   whatever the description says. The comment puts `#123` and links to pull requests of this
   repository in code spans, so that quoting an entry does not mention every pull request it
   names. A batch that was being built before the workflow read descriptions tells nobody what
   its description leaves out at that point: only entries added or changed afterwards are told.
8. **Edit the description whenever the batch changes.** The workflow reads it again on every
   edit. A pull request newly listed as left out is sent a comment as above. One whose entry
   changed, under the same heading or another, has this batch's comment brought up to date,
   which notifies nobody, so fixing a typo in a heading tells no one again. One whose entry is
   removed is told so. A new comment, and `awaiting-author` again, comes only when another batch
   leaves a pull request out under a different kind of heading.

## What the workflow does

While the batch's pull request is open, it is labelled `building`. Each open pull request whose
head commit is in the branch is labelled `batch-building` and `frozen`, in place of
`batch queue`. Each is asked once, in a comment, not to push until the batch has landed or been
closed. The workflow lists them in a comment of its own on the batch's pull request.

A pull request that is pushed to after the batch took its commit stays in the batch at the old
commit. As soon as the push comes in, it is told that the batch lands only that commit, and is
labelled `awaiting-author`: a push to a `frozen` pull request runs only this, not a whole sync.
If its new head is merged into the branch, the batch holds that one instead.

When the batch is merged, what it contained loses `batch-building` and `frozen`. A pull request
whose head has moved on since the batch took it stays open, and is told what landed and what did
not. When the batch is closed without being merged, what it contained loses its labels too, is
told it can push again, and goes back to `batch queue` if it was queued. If the batch is reopened,
what it contains is labelled and told it is frozen again. A batch that gets `building` back
otherwise, say after someone took the label off, tells no one again.

A pull request queued with a `batch` comment is labelled `frozen` too, since the queue also takes
only the commit that was queued. `-batch` takes `frozen` off again, unless a batch being built
holds the pull request. A pull request that leaves a batch assembled by hand and goes back to the
queue stays `frozen`. After every run the workflow puts `frozen` back on a queued pull request
that has lost it, and takes `frozen` and `batch-building` off one that is neither queued nor in a
batch being built.

"Labels at a glance" lists the labels that keep a pull request out of the inbox (see
`.github/workflows/inbox.yml`). The label names are in `scripts/batch-labels.py`, and the `if:`
of the sync job in `.github/workflows/batch-queue.yml` names some of them as well.

A batch that was already being built before the workflow first told anyone (its record on the
pull request is older than these notices) is not announced afresh: its pull requests are
labelled, but neither told they are frozen nor told what the description leaves out. Pull requests
that join it later, and entries added or changed later, are.

## Several batches at once

A batch whose branch contains the head of another batch's pull request is built as part of it.
The other batch is treated as one of the pull requests it contains. The workflow cannot yet tell
a batch that is being built from one that waits for another to land: every open batch assembled
by hand counts as being built.
