# Batches assembled by hand

A batch merges many pull requests into one branch so that they are built and landed together.
The batch queue is a list of approvals, and maintainers assemble batches from it by hand. The
batch-queue workflow (`.github/workflows/batch-queue.yml`, which runs
`scripts/batch-queue-sync.py`) assembles none of its own: that code is switched off by `ASSEMBLE`
in the script. It keeps the labels and comments of a batch assembled by hand in step, as long as
the batch follows the rules below. This page is for whoever assembles one.

## Labels at a glance

The sections below give the details.

| Label | On | Put on when | Taken off when |
|---|---|---|---|
| `building` | the pull request of a batch assembled by hand | its branch holds the head of an open pull request | the batch is merged or closed, once its members are tidied up after |
| `latest batch` | the pull request of the outermost batch of a stack, the one no other batch is stacked on | it is `building` and nothing is stacked on it | a batch is stacked on it; it is merged or closed |
| `batch-building` | each pull request in that batch, or in the lowest batch of a stack that holds it | the batch takes its head commit | it leaves every batch being built; its batch is merged or closed; it is closed |
| `frozen` | each pull request in that batch, and each queued pull request | with `batch-building`, or with `batch queue` on a `batch` comment | it is neither queued nor in a batch being built: `-batch`, it leaves the batch, the batch is merged or closed, it is closed |
| `changed after frozen` | a frozen pull request whose head has moved on from the commit taken | it is pushed to after a batch or the queue took a commit of it | its head is that commit again, or it is no longer frozen |
| `batch queue` | a pull request wanted in a batch | a maintainer or reviewer comments `batch` or `p` | `-batch`; it joins a batch assembled by hand (in exchange for `batch-building`); its queued commit lands; it is closed |
| `priority` | a queued pull request that goes first | `p` | by hand |
| `awaiting-author` | a pull request handed back to its author | `aa`; it is pushed to while in a batch, with a commit the batch does not have; a batch lands an older commit of it; `batch-conflict` is put on it; a batch it builds on is rebuilt without a pull request it carries | `ready`, by the author or a maintainer; the batch takes the new head of a pull request it was put on for a push, or it is pushed back |
| `main-conflict` | a pull request that conflicts with `main` | GitHub says so, unless it declares `depends on:` an open batch | the conflict is gone, or it declares that dependency |
| `batch-conflict` | a pull request that conflicts with a batch being built, the outermost of its stack | git cannot merge it with the batch's head | the conflict is gone; the batch lands or is closed; it joins the batch |

`batch queue`, `building`, `batch-building`, `frozen`, `awaiting-author` and `batch-conflict`
keep a pull request out of the inbox (`inbox`, see `.github/workflows/inbox.yml`). The names are in `scripts/batch-labels.py`.

Besides the labels, the workflow checks each batch's description against its branch, in a
comment on the batch's pull request: pull requests listed as included that aren't in the branch,
members the description doesn't mention, and pull requests reverted in the branch (see "What
the workflow does").

## Rules

1. **Use a branch of this repository named `batch/...`**, such as `batch/b9`, and open its pull
   request against `main`. Don't use the name `batch/` followed by a date and time, such as
   `batch/2026-11-23-041230`: that form belongs to the workflow's own batches, which are
   switched off for now. A batch stacked on another one, say #1313, is named
   `batch/<anything>-on-1313`, such as `batch/b9-on-1313`, and its description says so in a line
   `- [ ] depends on: #1313` (see [Several batches at once](#several-batches-at-once)).
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
   it merged when the batch lands, although its changes did not land. That happened to the 78
   pull requests reverted in batch 10b (#1796), #1673 among them. The workflow notices a revert,
   says so on the batch's pull request, and tells the reverted pull request what will happen,
   unless it is labelled `deferred`. After a force-push, the workflow looks through the branch again. A pull request that is no longer in it loses its
   labels, goes back to `batch queue` if it was queued, and is told that it can push again.
   - A force-push does not stop a build of the old head: `build-pr.yml` gives each head commit
     a concurrency group of its own and does not cancel runs in progress.
   - Most of what was already built is still used. The shared cache is keyed by each module's
     inputs, not by commit. Fragment builds publish the modules they finished even when they
     fail or are cancelled (see `scripts/rh-buildq/README.md`). So the new head rebuilds only
     the modules that depend on what was taken out. That is the same cost as reverting it.
6. **To add a pull request, merge its head commit in and push.** The workflow looks through the
   branch again on every push.
7. **List what is included, and what is left out and why, in the description.** People read the
   description to see which pull requests a batch contains. The workflow reads what the batch
   contains from the branch, and reads the description for what it leaves out and to check it
   against the branch (see below):
   - A heading is a line of its own, not part of a list, that ends with a colon. Pull requests
     listed under a heading that contains "left out" or "not included" (in any letter case) are
     left out. For example: `Left out for other reasons:`. Those under a heading about conflicts
     with the batch, one that says "conflict with" and later "batch", such as `Left out because
     they conflict with a PR earlier in the batch:`, are not told anything from the description:
     the conflict-labels workflow finds conflicts from the branches and tells them itself (see
     below). A heading about conflicts with `main` is told like any other. Those listed under a
     heading that says "included" and does not leave them out, such as `Included:`, are
     included: the batch carries their changes. Those under any other heading, such as `Held by
     the maintainers:`, are neither: they are not checked against the branch as included, and are
     not told they are left out. A pull request listed as included is never told it conflicts
     with the batch or with `main`, even when its own head is not in the branch, as when it was
     pushed to after the batch merged it in. The description check still names it, since GitHub
     will not mark it merged.
   - Each one is a list entry starting with `- ` and then a link to the pull request, either
     `#123` or its full URL. The rest of the entry is the reason. Lines indented under an entry,
     and entries that don't start with a link, are not read.
   - A list ends at the next heading or paragraph.

   Each pull request left out is sent a comment quoting the heading and its entry. The comment
   only informs: it asks nothing of the author and changes no label, since many reasons, such as
   being `deferred`, are nothing the author can act on. Write the entry for its author: it is what
   they see. A pull request labelled `deferred` is not sent anything. A pull request that an
   earlier batch, or an earlier version of the description, left out under the same heading
   (ignoring anything in parentheses) is not told again. Its comment is edited to show the new
   entry, which notifies nobody, so that it is not told every time a batch leaves it out for the
   same kind of reason. Keep the headings the same from one batch to the next for this to work.
   A pull request that is in the branch, or in another batch being built,
   is never told it is left out, whatever the description says: a lower batch can list as left
   out what the batch stacked on it takes. The comment puts `#123` and links to pull requests of this
   repository in code spans, so that quoting an entry does not mention every pull request it
   names. A batch that was being built before the workflow read descriptions tells nobody what
   its description leaves out at that point: only entries added or changed afterwards are told.
8. **Edit the description whenever the batch changes.** The workflow reads it again on every
   edit. A pull request newly listed as left out is sent a comment as above. One whose entry
   changed, under the same heading or another, has this batch's comment brought up to date,
   which notifies nobody, so fixing a typo in a heading tells no one again. One whose entry is
   removed is told so. When three or more pull requests leave the left-out lists at once and are
   still listed elsewhere in the description, as when a heading is reworded so that it no longer
   says "left out", none of them is told: the workflow only notes it in its log. A new comment
   comes only when another batch leaves a pull request out under a different kind of heading.

## What the workflow does

While the batch's pull request is open, it is labelled `building`. Each open pull request whose
head commit is in the branch is labelled `batch-building` and `frozen`, in place of
`batch queue`. Each is asked once, in a comment that names the commit the batch took, not to push
until the batch has landed or been closed. That comment is kept up to date: when the batch takes
a newer head of the pull request, the comment is edited to name it, and no new one is posted. The
workflow lists them in a comment of its own on the batch's pull request. In a stack
of batches, what the branch shares with a batch it is stacked on belongs to that batch instead
(see [Several batches at once](#several-batches-at-once)).

The workflow also compares the description with the branch, and says where they disagree in a
comment of its own on the batch's pull request. It names:

- pull requests listed as included that are merged already, which should come off the list;
- pull requests listed as included that are closed without being merged, or are no pull request,
  and which of them are still in the branch. The changes of those land with the batch, but GitHub
  does not mark a closed pull request merged. The workflow asks GitHub once what became of each;
- pull requests listed as included whose head commit is not in the branch. That includes one
  pushed to after it was merged in but before the workflow first looked through the batch: the
  workflow cannot count its old commit as in the batch, and GitHub would not mark it merged. Merge
  its new head in. To leave it out instead, rebuild the branch without it, since its old commit
  would still land, and take it off the list; one that is not in the branch at all only needs to
  come off the list;
- pull requests in the branch that the description does not list at all. This is left out when
  the description lists nothing as included, so a batch that does not follow this format is not
  flooded;
- pull requests in the branch that the description lists as left out;
- pull requests whose merge into the branch was reverted. The workflow knows a revert by the
  line git writes in its message, `This reverts commit <commit>`, naming the merge commit that
  brought in the commit of the pull request that the batch holds, whatever the revert's first line
  says. A batch's merge commit for the pull request, `Merge PR #123 into batch` or `Merge #123
  head (...) into batch/...`, also brought that commit in when what it merged only has it in it,
  as when `main` was merged into the pull request for the batch. A commit that is not a merge
  also counts when its message names that merge commit anywhere by its id, whole or abbreviated,
  as in "This undoes the merge of #1673 into the batch (6e812fc62dbc)". A revert of the revert
  puts the pull request back. A pull request merged in again at a new head is in the batch at
  that head, and a revert of its earlier merge no longer counts. Each pull request reverted is
  also told, once, that the batch would land it although its changes did not (rule 5), unless it
  is labelled `deferred`.

What is in the branch is what the workflow found there, at the commit it found, so a pull request
pushed to after it was merged in is not named. In a stack, the description of a batch need list
only its own pull requests: what a batch under it contains is never named as not listed, and is
in the branch if the description lists it as well. The comment is posted once there is something to
say. After that it is edited in place, also to say that all is well again, and only when what it
says changes.

A pull request that is pushed to after the batch took its commit stays in the batch at the old
commit. As soon as the push comes in, it is told that the batch lands only that commit, and is
labelled `awaiting-author`: a push to a `frozen` pull request runs only this, not a whole sync.
If the batch's branch has the new head already, and the new head has the commit the batch took
in it, as when the merge of `main` the batch was built from is pushed to the pull request
afterwards, nothing new is said, and the batch's record takes the new head. A push back to an
earlier commit is told even though the branch has that commit, since the batch still lands the
one it took. If its new head is merged into the branch later, the batch holds that one instead.
Either way, the comment that said the pull request is frozen is edited to name the new head, and
so is the one that said it was pushed to, if there was one: it then says that the batch builds and
lands the new head and nothing more is needed. `awaiting-author` comes off again, as it does when
the pull request is pushed back to the commit the batch took. Only a label the workflow put on for
the push comes off: one a person put on stays.

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

A frozen pull request whose head has moved on from the commit that was taken, by its own batch
or by the queue, is labelled `changed after frozen` as soon as the push comes in, or by the next
sync if that was missed: what was pushed since is not part of what is built. A new head that its
own batch's branch has already, with the commit taken in it, such as the merge of `main` that the
batch was built from, counts as the commit taken. In a stack, its own batch is the lowest that holds it, even
when a batch on top of it has merged in the new head. The label comes off when the head is the
commit that was taken again, and when the pull request is no longer frozen. On a queued pull
request, another `batch` comment does that: the queue takes the new head. On a pull request in a
batch, a `batch` comment changes nothing; the label comes off once its own batch merges in the
new head, or when the pull request is pushed back to the commit its batch took.

"Labels at a glance" lists the labels that keep a pull request out of the inbox (see
`.github/workflows/inbox.yml`). The label names are in `scripts/batch-labels.py`, and the `if:`
of the sync job in `.github/workflows/batch-queue.yml` and of `.github/workflows/conflict-labels.yml`
name some of them as well.

## Conflicts with main and with the batch

*Switched off until a maintainer switches it on:* the workflow below runs only when the
repository variable `CONFLICT_LABELS` is `on`. Until then, it writes nothing, and the batch queue
tells pull requests listed under a heading about conflicts with the batch what the description
says, as it does for any other heading. To switch it on, start the workflow by hand (Actions → conflict labels →
Run workflow) with `dry_run` ticked, as it is by default, and no pull request number. Its summary
lists every label and comment a real run would add. If that looks right, set the variable to `on`
(Settings → Secrets and variables → Actions → Variables). A dry run can be started whether or not
the variable is set.

Another workflow (`.github/workflows/conflict-labels.yml`, which runs
`scripts/conflict-labels.py`) labels the open pull requests into `main` that are not drafts and
not batches:

- `main-conflict`: GitHub says the pull request conflicts with `main`. There is no comment,
  because GitHub shows the conflict too. A pull request that depends on an open batch does not
  get it (see below).
- `batch-conflict`: the pull request conflicts with the head of a batch being built, one labelled
  `building`. Of a stack of batches, only the outermost one, labelled `latest batch`, is compared
  with: its branch holds the batches under it, and the stack lands as a whole, so that is the
  batch to merge and to depend on. git cannot merge a file that both change since they left
  `main`, or one of the two deletes a Lean file that the other starts to import. The pull requests
  in the batch, labelled `batch-building`, never get it. Each time a pull request gets it, the
  first time or again after it was fixed, it is also labelled `awaiting-author` and told in a
  comment which files conflict and what to do. While it keeps the label, it is told about each
  batch it conflicts with once.

Both labels come off by themselves once the reason has gone: the conflict was resolved, the pull
request was closed or joined the batch, or the batch was merged or closed. `awaiting-author` stays
until the author comments `ready`. `batch-conflict` keeps a pull request out of the inbox;
`main-conflict` does not, since a pull request that conflicts with `main` still needs a first look.

The workflow finds these conflicts from the branches alone, whatever the batch's description says.
A pull request that the description leaves out because it conflicts is told only by this
workflow, and only if it still conflicts: the batch queue does not repeat entries under a
heading about conflicts with the batch.

### If your pull request is labelled `batch-conflict`

1. Merge the batch's branch (`batch/...`, named in the comment) into your branch, rather than
   rebasing onto it, and resolve the conflicts. If the batch's branch is rebuilt without a pull
   request before it lands, as rule 5 asks for taking one out, your branch still carries the
   pull request that was taken out, and the workflow tells you so. Then make a new branch from
   the new batch branch, copy only your own commits onto it with `git cherry-pick`, and push that
   to your pull request. If a pull request is taken out by reverting its merge instead, you are
   not told, and need do nothing: the batch's branch is not rewritten.
2. Add this line at the end of the description, under a line `---`, as the template in
   [AGENTS.md](../AGENTS.md#pull-requests) has it, where #123 is the batch's pull request:

   ```
   - [ ] depends on: #123
   ```

   Your pull request now carries the batch's changes, and may conflict with `main`, until the
   batch lands. The line says that this is expected, and keeps `main-conflict` off it.
3. Comment `ready`.

Or wait until the batch has landed, then merge `main` into your branch, resolve the conflicts
there and comment `ready`.

A line counts as a dependency when it starts with `depends on`, `depend on` or `depends upon`,
optionally after `- [ ]` or `- [x]`, and names the batch's pull request as `#123` or by its
address.

### If the batch you build on is rebuilt

A pull request that merged a batch's branch carries the batch's commits. If the batch is then
rebuilt without one of its pull requests, your branch still carries that one's commits: when
your pull request lands, they land too, and GitHub marks the pull request that was taken out
merged. Every sweep of the workflow looks for this in the pull requests that depend on an open
batch, or share commits with a batch's branch: their branches are searched for the batch's merge
commits, `Merge PR #123 into batch` or `Merge #123 head (...) into batch/...`, for pull requests
that the batch's current branch no longer has. Your pull request is then labelled
`awaiting-author` and told which pull requests it carries, once for each such set: a batch rebuilt
again, or under a new number, tells it nothing new while it carries the same ones. Make a
new branch from the batch's current branch, copy only your own commits onto it with
`git cherry-pick`, push that to your pull request and comment `ready`. From then on, merge the
batch's branch into yours; never rebase onto it.

A batch that was already being built before the workflow first told anyone (its record on the
pull request is older than these notices) is not announced afresh: its pull requests are
labelled, but neither told they are frozen nor told what the description leaves out. Pull requests
that join it later, and entries added or changed later, are.

## Several batches at once

Batches can be stacked: the branch of the upper batch merges the branch of the lower one, so it
holds the lower batch's pull requests too, and it lands right after it.

- **Say which batch it is stacked on.** The workflow reads a line of the upper batch's
  description such as `- [ ] depends on: #1313`, ticked or not: the same `depends on` line any
  pull request uses. Whoever assembles batches should add one. A batch can be stacked on more
  than one. Until its description has such a line naming an open batch that is being built, the
  branch name is read instead: `batch/<anything>-on-<number>`, such as `batch/b9-on-1313`, is
  stacked on #1313. Only open batches labelled `building` count, and batches that say they are
  stacked on each other in a circle are taken to be stacked on none. The workflow warns in its
  log when a batch's branch shares no commit beyond `main` with the batch it says it is stacked
  on.
- **Batches at the same commit** hold the same pull requests. Whatever they say about each
  other, each is taken to be stacked on the one with the next lower number: the lowest holds
  their members, and the highest is `latest batch`. What they say about other batches still
  counts. The workflow warns in its log on every run that sees them.
- **Each pull request belongs to the lowest batch that holds it.** A pull request whose head
  commit is in several batches of a stack is a member of the lowest one only: it is listed in
  that batch's record, and its comments (that it is frozen, that it was pushed to, that it left
  the batch, what landed) name that batch. The upper batch's members are what its branch adds.
  A pull request that holds a batch is never a member of another batch. All batches are looked
  through, lowest first, before any label changes, so a pull request that moves from one batch
  of a stack to another keeps `batch-building` and `frozen` throughout. It is told which batch it
  is in now.
- **`latest batch`** goes on the outermost batch of each stack, the one no other batch is stacked
  on. A batch stacked on nothing, with nothing stacked on it, is a stack of its own. The label
  comes off when another batch is stacked on it, or when it is merged or closed.
- **When the lower batch is merged**, its members land and the upper batch simply stops being
  stacked on it. Its `depends on` line can stay.
- **When the lower batch is closed without being merged**, the upper batch is told once, in a
  comment, that its branch still carries the closed batch's commits. The open pull requests of
  the closed batch that are still in the upper branch become members of the upper batch and keep
  `batch-building` and `frozen`; they are told they are frozen in the upper batch. The rest are
  told they can push again, as for any closed batch. Whoever assembles the upper batch should
  rebuild it on `main` or on another batch, and change its `depends on` line or branch name to
  match.

Records written before batches were stacked list the lower batch, and everything in it, as
members of the upper batch. The workflow reads them all the same: a batch is never taken for a
member, and its own labels never change through membership.

The workflow cannot yet tell a batch that is being built from one that waits for another to
land: every open batch assembled by hand counts as being built.

## The status issue

The issue titled "Batch status" shows, in one place, which batches are being built and what each
contains, which pull requests are in the batch queue, and what each batch leaves out. The batch
status workflow (`.github/workflows/batch-status.yml`, which runs `scripts/batch-status.py`) keeps
it up to date. It looks every 15 minutes and whenever the batch queue workflow has changed
something, and rewrites the description when what it says changes. The footer says when that last
happened, and when a run last found it up to date: that "last checked" time is brought up to date
at least every six hours, so one older than that means the workflow's runs are failing. The
footer also shows the workflow's status badge, which shows a failing run at once. The
workflow opens the issue the first time, and a maintainer pins it by hand. It is found by
`<!-- batch-status -->` anywhere in its description, in an issue the workflow opened, so a line
added above it does no harm.

- **Batches being built** are the open pull requests from a `batch/...` branch of this
  repository that are labelled `building`. The batch labelled `latest batch` comes first, then the
  others by number, newest first: that order is approximate. What a batch contains is read from
  the batch queue workflow's record comment on its pull request, so it is what is in its branch,
  not what its description says. A batch that contains another batch being built lists only the
  pull requests it adds.
- **The batch queue** is the open pull requests labelled `batch queue` that no batch being built
  contains, in three groups. Each goes in the first that applies: *Pushed to since approval*
  (`changed after frozen`), *Conflicts* (`batch-conflict` or `main-conflict`), and *Ready*
  otherwise. `priority` pull requests come first in each group. `priority` and `awaiting-author`
  show as badges and do not change the group. While the conflict labels are switched off (the
  repository variable `CONFLICT_LABELS` is not `on`), there is no *Conflicts* group, and *Ready*
  says that it may hold pull requests that conflict.
- **Left out** lists, for each batch, the open pull requests its description lists as left out
  (see rule 7), by heading. The reasons are not repeated: they are in the batch's description and
  in the comment on each pull request.

The batches and the queue link to the same searches on GitHub, which are live where the issue is a
snapshot. No label marks what a batch leaves out, so that section has no such link.
When the description would be longer than GitHub allows, it is shortened, and says so at the top:
first badges become plain label names, then titles are cut shorter, then tables become lists of
numbers, and last the end is cut off.

### The block for agents and scripts

The description's second line is a hidden comment holding compact JSON. Read it rather than the
tables, which may change shape or be shortened:

```
<!-- batch-status {"batches":[...],"queue":[...],"left_out":{...},"labels":{...},"conflict_labels":true} -->
```

- `batches`: outermost first, as far as is known. Each is `{"number", "branch", "head",
  "latest", "members", "contains"}`: `head` is the full commit id of the batch's head, `latest`
  whether it is labelled `latest batch`, `members` the numbers of every pull request it contains,
  those in the batches it contains included, and `contains` the batches being built among them.
- `queue`: in the order shown, each `{"number", "group", "priority"}`, where `group` is `"ready"`,
  `"changed"` (pushed to since approval) or `"conflict"`.
- `left_out`: for each batch, by its number as a string, the numbers of the open pull requests its
  description leaves out.
- `labels`: for each open pull request named above, the batches too, by its number as a string,
  its labels. A queued pull request labelled `awaiting-author` has been handed back to its author.
- `conflict_labels`: whether the conflict labels are switched on. While they are not, no pull
  request is in the `"conflict"` group, and `"ready"` may hold some that conflict.

`--` inside the JSON is written `-\u002d`, so that nothing in it ends the comment. A JSON parser
reads it back as `--`. In the unlikely case that the block alone would take up half of what
GitHub allows, it is `{"truncated":true}` instead, and the description is cut off at the end.
