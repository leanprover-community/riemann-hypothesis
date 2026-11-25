#!/usr/bin/env python3
"""Keep the labels of the batch queue in step with the batches being built.

The batch-queue workflow runs this from its trusted checkout. Everything goes through GitHub's
API: GitHub performs the merges, and nothing from a pull request is checked out or run here.

The batch queue is a list of approvals, and maintainers assemble batches from it by hand. This
script assembles no batch of its own: the code that does is kept, switched off by `ASSEMBLE`, in
case we want a batch assembled by the queue again, and the comment there says what that needs.
What follows about the batch being assembled, the order queued commits go in and the note in its
pull request describes that code as it works with `ASSEMBLE` on. With it off, a branch this
script started is removed once its pull request is merged or closed, as before, and one without a
pull request, such as `batch/2026-11-24-142233`, is left alone. Everything about batches
assembled by hand, their members' labels and comments, and `frozen` runs either way.

Which commit goes into a batch. A maintainer queues one commit of a pull request by commenting
`batch`: the commit that was its head when the comment was posted, or one named in the comment.
The workflow's label job records that commit in a comment of its own, and it is the only one a
batch takes. The `batch queue` label alone queues nothing, and commits pushed afterwards wait
for another `batch`. The label job labels a queued pull request `frozen` as well, and this
script keeps that label on it while it is queued.

A batch is a branch of this repository that this script started, normally with an open pull
request. Its name is `batch/` and the time it was started, such as `batch/2026-11-23-041230`,
with `-2` and so on after it when that name was taken. Other `batch/...` branches of this
repository, such as one a maintainer assembled by hand, are batches assembled by hand: nothing
is merged into them, their pull requests' text is left alone, and they are never deleted.

The batch being assembled takes each queued commit for as long as its pull request is open, and
a pull request that GitHub cannot merge into it is told so in a comment. Once the batch's pull
request is merged or closed, its branch is removed. What it contained and is still open stays
queued, and the next run starts a new batch with it.

Queued commits are merged in pull request number order, except that those of pull requests
labelled `priority` go first: when one of them and another pull request cannot both be merged,
the other one is left out. The order counts when a batch is started or rebuilt. After that, a
newly queued commit is merged on top of what is already there, and one that was left out stays
out until the batch is rebuilt or a new commit of it is queued, labelled `priority` or not.

A batch assembled by hand is being built for as long as its pull request is open and its branch
holds the head commit of an open pull request, and this script labels its pull request
`building` to say so. One that is labelled `batch queue` itself waits in the queue like any
other pull request instead.

Batches assembled by hand can be stacked: the branch of the upper batch merges the branch of the
one it is stacked on, so it holds that batch's commits too, and it is to be merged right after
it. A batch says which batch it is stacked on with a line of its description such as

    - [ ] depends on: #1739

the same `depends on` line any pull request uses (read by `pr-dependencies.py`), ticked or not.
Until its description has one that names an open batch that is being built, its branch name is
read instead: `batch/<anything>-on-<number>`, such as `batch/b11-on-1739`, is stacked on that
number if it is such a batch. A batch can be stacked on more than one. Batches that say they are
stacked on each other in a circle are taken to be stacked on none. Only git checks the claim:
when a batch's branch shares no commit beyond main with the branch of a batch it says it is
stacked on, the run warns about it. Batches whose branches are at the same commit contain the
same pull requests, so whatever they say about each other, each is taken to be stacked on the one
with the next lower number: the lowest holds what they contain, and the highest is the
outermost. The run warns about them every time it sees them.

What a batch contains of its own, its members, is every open pull request whose head commit is
in its branch, queued or not, into main or into another branch, unless a batch it is stacked on,
directly or not, contains it: a pull request belongs to the lowest batch of a stack that holds
it. A pull request that holds a batch is never part of another batch. The members are labelled
`batch-building` and `frozen`, in place of `batch queue` for those that had it, and each is told
once in a comment, naming its own batch and the commit of it that the batch took, not to push
until the batch has landed. That comment is kept up to date when the batch takes a new head of
the pull request (see `retell`). This script
records them in a comment of its own on the batch's pull request, and looks through the branch
again when its head moves, or when a batch under it moves or the batches under it change. All
batches are looked through, lowest first, before any label changes, so a pull request that moves
from one batch of a stack to another keeps its labels throughout. A pull request that has left
every batch by then loses both labels and is told so, and so does everything in a batch once it
is merged or closed. Those that had `batch queue` before get it back, unless the batch was
merged.

The outermost batch of each stack, the one that no other open batch assembled by hand is stacked
on, is labelled `latest batch` as well. A batch that is stacked on nothing and has nothing
stacked on it is a stack of its own. The label comes off when another batch is stacked on it, or
when it is merged or closed.

When the batch underneath is merged, GitHub marks what it contained as merged, and the batch on
top simply stops being stacked on it. When it is closed without being merged, the batch on top is
told so once, in a comment: its branch still carries the commits of the closed batch, so the open
pull requests among them are now its own members and stay `batch-building` and `frozen`, and
whoever assembles it should rebuild it on main or on another batch and change its `depends on`
line or branch name to match.

A pull request that is pushed to after the batch took its commit is still in the batch, at that
commit. It is told that the batch lands only that commit, and is labelled `awaiting-author`, as
soon as the push comes in (see `pushed`) or else by the next sync, unless the batch's branch has
the new head already, and the new head has the commit the batch took in it, as when the merge of
main the batch was built from is pushed to the pull request afterwards: then the record takes the
new head. A push back to an earlier commit is told even though the branch has that commit: the
batch still lands the one it took. If the batch then takes its new head, or
it is pushed back to the commit the batch took, `awaiting-author` comes off again, but only if
this workflow put it on along with that comment: a label a person put on stays. Whenever the
record takes a member's new head, nothing new is posted: the comment that told it it is frozen is
edited to name the new head, and so is one that told it it was pushed to, which then says that
nothing more is needed. When
the batch is merged, GitHub marks merged each pull request whose head commit is in it and whose
base is main. One whose head has moved on stays open: it is told what landed and what did not,
and keeps `awaiting-author`. One whose head landed but whose base is another branch is closed,
with a comment saying where its commit went, since GitHub does not mark it merged.

The description of a batch assembled by hand lists pull requests under headings ending with a
colon. Those listed under a heading that says "left out" or "not included" are told so in a
comment quoting the heading and their entry. The comment only informs: no label changes, and
`batch queue` stays on them. One labelled `deferred` is not told. The quote puts the pull requests it names in code spans, so that it does not
mention each of them. A pull request this batch told before, whatever its entry and heading say
now, or another batch told it is left out under the same heading, is not told again: that comment
is brought up to date instead, which notifies nobody.
One whose entry is removed from the description is told that too, unless three or more leave the
left-out lists at once while the description still lists them: a heading was most likely
reworded, and the run only logs it. A pull request that a batch
being built contains, this one or another, is never told it is left out: the lower batch of a
stack usually lists as left out what the batch on top of it takes.

A batch whose record is older than these notices was under way before this script told anyone
anything. When this script first reads it, it labels the pull requests the batch contains but
tells none of them they are frozen, and tells nobody what its description leaves out: only pull
requests that join it, and entries added or changed, after that. Each batch of a stack is
treated so by its own record.

After every run, `frozen` is put on each open pull request a maintainer's `batch` stands for, and
`frozen` and `batch-building` are taken off any that is neither queued nor in a batch being built.
A frozen pull request whose head has moved on from the commit that was taken, by its own batch or
by the queue, is labelled `changed after frozen` until its head is that commit again or it is no
longer frozen; `pushed` adds the label as soon as the push comes in, and every sync looks again.
A new head that its batch's branch has already, with the commit taken in it, counts as the
commit taken (see `takes`).
Which pull requests a batch contains is read from its branch, never from its description. The names of the labels are in
`batch-labels.py`, and `verification/BATCHES.md` says what someone assembling a batch by hand
should do for all this to work.

The description is also compared with the branch, in a comment of its own on the batch's pull
request. It names the pull requests listed under a heading that says "included", and not "not
included", that are merged already, or closed without being merged, and which of those the
branch still holds, or whose head commit is not in the branch; those in the branch that the
description does not list, unless it lists nothing as included; those in the branch that it
lists as left out; and those the branch merged and then reverted, read from the messages and
parents of its commits. Pull requests under any other heading are neither checked as included nor
told they are left out. Each one reverted is told once that the batch would land it although its
changes did not, unless it is labelled `deferred`. The comment is posted once there is something
to say, and edited in place after that, also to say that all is well again. The note remembers a digest of it, so a run that would say
the same costs nothing.

The batch being assembled is built on top of the batch assembled by hand labelled `latest batch`,
when exactly one into main is: its branch starts at that batch's head, and its pull request is
to be merged after that batch's. When the batch underneath moves on, its new head is merged in.
When it is rebuilt, closed without being merged, or replaced by another, the batch being
assembled is rebuilt as well: its branch is reset to the new base, or to main, and every queued
commit is merged in again. Once the batch underneath has landed on main there is nothing to do.

A batch assembled by hand that was merged or closed is found by its pull request, which keeps
`building` until this script has tidied up after it. Its branch may already have been deleted by
then.

Taking a pull request out of the queue never changes a batch. Commits already merged into one
stay there, and the batch's description says so. No batch is rebuilt for that.

A pull request that is closed, whether merged or not, loses `batch queue`, `building`,
`batch-building`, `frozen` and `changed after frozen`: it is neither waiting for a build nor in
one any more. The pull request of a batch assembled by hand is the exception, because it keeps
`building` until it has been tidied up after. When a pull request is reopened, `batch queue`
comes back if this workflow was the last to take a label off, and the pull request was not taken
out of the queue with `-batch` meanwhile. A label a person took off stays off.

The workflow's token has an hourly allowance of requests, shared with every other workflow here:
what is left of it is the "left this hour" at the end of each run's log. A sync costs a few
hundred, so a push to a frozen pull request runs `pushed`, at about ten, instead of a whole sync.
A note in each batch pull request's text remembers what was merged and which pull requests were
already looked at. The note is a cache: it is used only while the batch's head
and each pull request's update time are what they were, and everything in it can be read again
from the branch and the comments.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")
_deps = _rest.load("pr-dependencies.py")
# Reading a batch's description and its branch's commit messages, which makes no requests.
_description = _rest.load("batch-description.py")

QUEUED, BUILDING, MEMBER, FROZEN = _labels.QUEUED, _labels.BUILDING, _labels.MEMBER, _labels.FROZEN
CHANGED, LATEST = _labels.CHANGED, _labels.LATEST
# A maintainer's label: pull requests that carry it go into a batch before the others.
PRIORITY, WAITING = _labels.PRIORITY, _labels.WAITING
# What a pull request in a batch assembled by hand carries (see `batch-labels.py`).
IN_BATCH = _labels.IN_BATCH
# A pull request the maintainers want left out of batches for now, labelled by hand (see the
# `## Batches` section of AGENTS.md). It is never told that a batch leaves it out.
DEFERRED = "deferred"
PREFIX = _labels.PREFIX
# The name `start` gives a batch branch. Any other `batch/...` branch is not this script's.
OWN_BATCH = re.compile(r"batch/[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{6}(?:-[0-9]+)?")
# The name of a batch assembled by hand that says which batch it is stacked on, such as
# `batch/b11-on-1739`, when its description does not say so in a `depends on` line.
ON_BATCH = re.compile(r"batch/.+-on-([0-9]+)")
BOT = "github-actions[bot]"
# Stop early when fewer requests than this are left for the hour (see `github-rest.py`).
RESERVE = _rest.RESERVE
# What was read from a pull request is remembered only once the pull request has been quiet for
# this long. GitHub's update times are whole seconds, so two changes in one second look like one.
SETTLE = datetime.timedelta(seconds=120)

# Whether the sync assembles a batch of its own from the queue: starts a `batch/<date-time>`
# branch, merges each queued commit into it, opens and describes its pull request, and rebuilds it
# on top of a batch assembled by hand (`start`, `recall`, `restack`, `publish` and the end of
# `sync`). It does not: the queue is a list of approvals, which maintainers assemble batches from
# by hand. The code is kept, and tested with this on, in case we want a batch assembled by the
# queue again. Running it taught us what that needs:
#
# - GitHub Actions may not create pull requests in this repository. That is a repository setting:
#   Settings > Actions > General > "Allow GitHub Actions to create and approve pull requests". So
#   the queue's branch `batch/2026-11-24-142233` never got a pull request, and every sync run
#   ended in `Refused` at `publish`: the job failed, its summary showed only the refusal, and
#   anything that runs after `publish` would not run. Run 45503694341 shows it. `assemble` now
#   logs that refusal and goes on, and the run still fails.
# - The batches maintainers assemble by hand already take every open pull request that is not a
#   draft, touches `src/` and merges cleanly, queued or not, so a second batch assembled from the
#   queue largely builds them again.
# - Batches assembled by hand are stacked: #1739 (`batch/b10b-on-1410`) is built on #1410, and
#   takes each new head of #1410 while #1410 is being repaired. A batch of the queue would have
#   to go on the outermost of them and be rebuilt whenever a batch below it moves. `restack`
#   now follows the batch labelled `latest batch` when a single one into main is, and goes back
#   to main when there are more.
# - Requests: a sync run that assembled cost about 300 REST requests. Run 45503694341 ended with
#   "304 requests to GitHub; 4721 left this hour".
#
# To revive it: allow GitHub Actions to create pull requests, check that going on the
# `latest batch` is still what we want, and set this back to True.
ASSEMBLE = False

# Comments the workflow's label job leaves when a maintainer queues or unqueues a pull request.
# They count only at the very start of a comment written by the workflow itself.
APPROVED = re.compile(r"<!-- batch-queue-approved ([0-9a-f]{40}) -->")
WITHDRAWN = "<!-- batch-queue-withdrawn -->"
# Comments this script leaves on a pull request, each once.
REFUSAL = "<!-- batch-queue-refused {branch} {sha} -->"
REFUSAL_ON = "<!-- batch-queue-refused {branch} {sha} on #{base} -->"
MOVED = "<!-- batch-queue-moved {sha} -->"
STAYS = "<!-- batch-queue-stays {branch} -->"
# On a batch assembled by hand, when a batch it is stacked on is closed without being merged.
STRANDED = "<!-- batch-queue-stranded {number} -->"
# The comment on a batch assembled by hand that records what it contains.
BY_HAND = re.compile(r"<!-- batch-queue-by-hand (\{.*\}) -->")
# Comments this script leaves on what a batch assembled by hand contains or leaves out.
FROZEN_NOTE = "<!-- batch-queue-frozen {number} {sha} -->"
# `sha` is the commit the batch took. When the batch takes the member's new head instead, the
# comment is edited to name that one, marker and all (see `retell`).
PUSHED = "<!-- batch-queue-pushed-while-frozen {number} {sha} -->"
# On the line after `PUSHED` when the workflow put `awaiting-author` on along with that comment, so
# that it takes off only a label it put on itself (see `handed_back`).
HANDED_BACK = "<!-- batch-queue-handed-back -->"
# What `PUSHED` becomes once the batch has taken the new head after all. `sha` is still the commit
# the batch took before, and the line after it keeps `HANDED_BACK` if that comment had it.
TAKEN = "<!-- batch-queue-pushed-then-taken {number} {sha} -->"
DROPPED = "<!-- batch-queue-dropped {number} {sha} -->"
UNFROZEN = "<!-- batch-queue-unfrozen {number} -->"
LANDED_BEFORE_PUSH = "<!-- batch-queue-landed-before-push {number} {sha} -->"
LANDED_ELSEWHERE = "<!-- batch-queue-landed-elsewhere {number} {sha} -->"
LEFT_OUT = re.compile(r"<!-- batch-queue-left-out (\{.*?\}) -->")
NO_LONGER_LEFT_OUT = "<!-- batch-queue-no-longer-left-out {number} -->"
REVERTED = "<!-- batch-queue-reverted {number} {sha} -->"
# The comment on a batch assembled by hand that compares its description with its branch, a
# left-out heading for conflicts, and what reads the description and the branch's commit messages
# (see `batch-description.py`).
CHECK, CONFLICT_HEADING = _description.CHECK, _description.CONFLICT_HEADING
left_out, entry_digest, left_out_digest = _description.left_out, _description.entry_digest, _description.left_out_digest
reverts, description_check = _description.reverts, _description.description_check
# The workflow that labels conflicts, started once at the end of a run in which a batch is first
# labelled `building` or `latest batch`: those labels are put on with the workflow's token, which
# starts no run of it by itself.
CONFLICT_WORKFLOW = "conflict-labels.yml"
# When this many pull requests leave the left-out lists of a batch's description at once and the
# description still lists them, a heading was most likely reworded: they are not told that they
# are no longer left out (see `tell_left_out`).
REWORDED = 3
# In a batch pull request's text: the part this script writes, and its note to itself.
BODY = "<!-- batch-queue -->"
STATE = re.compile(r"<!-- batch-queue-state (\{.*\}) -->")
# The merge commit that adds a pull request to a batch, and the one that brings the batch
# underneath up to date.
ADDED = re.compile(r"Add #(\d+) to the batch\n\nMerged at ([0-9a-f]{40})\.")
UPDATED = "Bring #{number} up to date\n\nMerged at {sha}."


Refused = _rest.Refused
quoted = _rest.quoted


class GitHub(_rest.GitHub):
    """The repository's REST API through `gh` (see `github-rest.py`), with a clock that the tests
    can set."""

    def __init__(self, repo, dry_run=False):
        super().__init__(repo, dry_run)
        # Lines saying which label changes GitHub refused (see `relabel`).
        self.refused = []

    def now(self):
        return datetime.datetime.now(datetime.timezone.utc)


def open_pulls(gh):
    """Every open pull request, by number. Two requests cover a couple of hundred of them."""
    found = {}
    for info in gh.pages("pulls?state=open"):
        found[info["number"]] = {
            "number": info["number"], "sha": info["head"]["sha"], "ref": info["head"]["ref"],
            "batch": holds_batch(gh, info), "base": info["base"]["ref"],
            "labels": {label["name"] for label in info["labels"]},
            "updated": info["updated_at"], "body": info.get("body") or "", "draft": bool(info.get("draft"))}
    return found


def holds_batch(gh, info):
    """Whether a pull request, as GitHub's REST API gives it, holds a batch (see `batch-labels.py`)."""
    head = info["head"]
    return _labels.holds_batch(gh.repo, (head.get("repo") or {}).get("full_name"), head["ref"])


def own_batch(ref):
    """Whether a branch name is one `start` gives a batch."""
    return OWN_BATCH.fullmatch(ref) is not None


def is_batch(pr):
    """Whether a pull request holds a batch that `start` began."""
    return pr["batch"] and own_batch(pr["ref"])


def by_hand(pr):
    """Whether a pull request holds a batch assembled by hand: a `batch/...` branch of this
    repository under another name than the ones `start` gives."""
    return pr["batch"] and not own_batch(pr["ref"])


def names(given):
    """A label, several of them, or None, as a list."""
    return [given] if isinstance(given, str) else [name for name in (given or ()) if name]


def relabel(gh, pr_or_number, add=None, remove=None):
    """Change labels on GitHub, and on our own copy of the pull request when we hold one.

    `add` and `remove` are a label each or several. With our own copy, only the labels it is
    missing are added and only those it carries are removed. Without one, `remove` is sent as
    it is, and should name only labels the pull request carries. Returns whether GitHub took
    every change. A change it refused, other than for the rate limit, which stops the run, is
    added to `gh.refused`: the run's log ends with those lines, since a line its caller logs may
    say the label changed.
    """
    number = pr_or_number["number"] if isinstance(pr_or_number, dict) else pr_or_number
    add, remove = names(add), [name for name in names(remove) if name not in names(add)]
    if isinstance(pr_or_number, dict):
        have = pr_or_number["labels"]
        add, remove = [name for name in add if name not in have], [name for name in remove if name in have]
    done = True
    for name in add:
        # Adding a label that does not exist would create it. One renamed on GitHub should be
        # noticed instead, not started again under the old name.
        if not gh.label_exists(name):
            raise Refused(f"There is no `{name}` label in {gh.repo}. Was it renamed? See `batch-labels.py`.")
    if add:
        status = gh.write("POST", f"issues/{number}/labels", {"labels": add})[0]
        if status not in (0, 200):
            gh.refused.append(f"#{number}: GitHub answered {status} to adding "
                              f"{', '.join(f'`{name}`' for name in add)}, so it was not added")
            done, add = False, []
    taken = []
    for name in remove:
        # A label that is not there any more answers 404, which is what was wanted.
        status = gh.write("DELETE", f"issues/{number}/labels/{quoted(name)}")[0]
        if status in (0, 200, 404):
            taken.append(name)
        else:
            gh.refused.append(f"#{number}: GitHub answered {status} to removing `{name}`, so it is still on")
            done = False
    if isinstance(pr_or_number, dict):
        pr_or_number["labels"] = (pr_or_number["labels"] | set(add)) - set(taken)
    return done


def unlabel(gh, number, have, gone):
    """Take the labels `gone` off a closed pull request that carries `have`, in one request when
    there are several: setting its labels replaces them all. Another workflow may change them in
    the meantime, inbox-sync taking `inbox` off for one, and a label it took off would come back.
    That is rare, and the other workflow takes it off again on its next run, so saving a request
    for each pull request a batch lands is worth it."""
    gone = sorted(set(gone) & set(have))
    if len(gone) > 1:
        status = gh.write("PUT", f"issues/{number}/labels", {"labels": sorted(set(have) - set(gone))})[0]
    elif gone:
        status = gh.write("DELETE", f"issues/{number}/labels/{quoted(gone[0])}")[0]
    else:
        return
    # As in `relabel`: a label that is not there any more answers 404.
    if status not in (0, 200, 404):
        gh.refused.append(f"#{number}: GitHub answered {status} to removing "
                          f"{', '.join(f'`{name}`' for name in gone)}, so it is still on")


def unfrozen(back):
    """The labels a pull request leaving a batch assembled by hand loses. One that goes back to
    the queue stays `frozen`: the queue, too, takes only the commit that was queued."""
    return (MEMBER, BUILDING) if back else IN_BATCH


def thawed(back):
    """What a pull request leaving a batch assembled by hand is told about pushing."""
    if back:
        return (f"It is back in the batch queue, at the commit that was queued, and stays `{FROZEN}`: a commit "
                "pushed now waits for another `batch` comment.")
    return f"This pull request is no longer `{FROZEN}`, and you can push to it again."


def say(gh, number, marker, text):
    """Leave a comment on a pull request without looking for an earlier one, for things the
    caller keeps track of itself. Returns whether GitHub took it."""
    return gh.write("POST", f"issues/{number}/comments", {"body": f"{marker}\n{text}\n"})[0] in (0, 201)


def by_workflow(comment):
    return (comment.get("user") or {}).get("login") == BOT


def look(gh, pr, seen):
    """What a maintainer queued on a pull request: (commit or None, its comments or None).

    The comments are read only if the pull request has changed since it was last looked at.
    When it has not, the earlier answer stands, there is nothing new to say to it, and None is
    returned in place of the comments.
    """
    key = str(pr["number"])
    if key in seen and seen[key][0] == pr["updated"]:
        return seen[key][1] or None, None
    comments = gh.pages(f"issues/{pr['number']}/comments")
    sha = None
    for comment in comments:
        body = comment.get("body") or ""
        if not by_workflow(comment):
            continue
        match = APPROVED.match(body)
        if match:
            sha = match.group(1)
        elif body.startswith(WITHDRAWN):
            sha = None
    if settled(gh, pr["updated"]):
        seen[key] = [pr["updated"], sha or ""]
    else:
        seen.pop(key, None)
    return sha, comments


def settled(gh, updated):
    """Whether a pull request has been left alone long enough for its update time to be trusted."""
    try:
        when = datetime.datetime.strptime(updated, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=datetime.timezone.utc)
    except (TypeError, ValueError):
        return False
    return gh.now() - when >= SETTLE


def tell(gh, number, comments, marker, text):
    """Leave a comment on a pull request, unless the workflow has left that one before."""
    if comments is None:
        comments = gh.pages(f"issues/{number}/comments")
    # At the start only: a comment can quote text someone else wrote, markers included.
    if any((comment.get("body") or "").startswith(marker) for comment in comments if by_workflow(comment)):
        return False
    return say(gh, number, marker, text)


# ---------------------------------------------------------------------------------------------
# Batches.


def batches(gh, pulls):
    """The batches that can still be merged, as {ref, sha, number, body}, and the batch branches
    left behind by a pull request that was merged or closed, as {ref, sha, pull}, with that pull
    request as GitHub gives it.

    `number` is None for a branch whose pull request has not been opened yet. A `batch/...`
    branch under any other name than the ones `start` gives is not looked at.
    """
    owner = gh.repo.split("/")[0]
    live = {pr["ref"]: pr for pr in pulls.values() if is_batch(pr)}
    found, leftover = [], []
    for ref in gh.get(f"git/matching-refs/heads/{PREFIX}"):
        name = ref["ref"][len("refs/heads/"):]
        if not own_batch(name):
            continue
        batch = {"ref": name, "sha": ref["object"]["sha"], "number": None, "body": ""}
        if name in live:
            pr = live[name]
            batch.update(number=pr["number"], body=pr["body"])
        else:
            closed = gh.get(f"pulls?state=all&head={owner}:{name}")
            if closed:
                leftover.append({"ref": name, "sha": batch["sha"], "pull": closed[0]})
                continue
        found.append(batch)
    return found, leftover


def finished(gh, closed_building, hand, pulls):
    """Batches assembled by hand that were merged or closed and not yet tidied up after, with a
    `fate`, the pull requests they contained as `members`, {number: commit}, those of them that
    were labelled `batch queue` before as `queued`, and their own `labels`.

    They are found by their pull requests, which keep `building` until `finish` is done with
    them. That works whether or not someone has already deleted the branch. `closed_building`
    is every closed issue or pull request that still carries `building`.

    Telling a batch assembled by hand from any other pull request takes a request, so what the
    open batches `hand` are known to contain is not asked about. Neither is what a batch just
    found contained, and the newest are looked at first, because a batch is opened after what it
    contains. A record written before batches were stacked lists the batch underneath among the
    members, so a number a batch may be stacked on (see `named_below`) is asked about all the same.
    """
    known, found = set(), []
    for batch in hand:
        pr = pulls[batch["number"]]
        known |= set(members(batch["note"])) - {str(number) for number in named_below(gh, pr["ref"], pr["body"],
                                                                                         batch["note"])}
    for item in sorted(closed_building, key=lambda item: -item["number"]):
        if "pull_request" not in item or str(item["number"]) in known:
            continue
        info = gh.get(f"pulls/{item['number']}")
        if not holds_batch(gh, info) or own_batch(info["head"]["ref"]):
            continue
        comment, note, _ = read_record(gh, info["number"])
        batch = {"number": info["number"], "fate": "merged" if info.get("merged") else "closed",
                 "members": members(note), "queued": queued_before(note), "comment": comment, "note": note,
                 "labels": {label["name"] for label in info["labels"]}}
        below = named_below(gh, info["head"]["ref"], info.get("body") or "", note)
        known |= set(batch["members"]) - {str(number) for number in below}
        found.append(batch)
    return found


def added(gh, batch, main_sha, stop=None, limit=400):
    """What this workflow merged into a batch, as {number: commit}, read from the branch itself.

    Follows first parents from the batch's head back to main, or to `stop`, the commit the
    branch was started from when it was started on top of another batch: the walk would
    otherwise go on through every commit of that one. Commits a maintainer pushed on top are
    stepped over.
    """
    merged, sha = {}, batch["sha"]
    for _ in range(limit):
        if sha == stop:
            break
        commit = gh.get(f"git/commits/{sha}")
        match = ADDED.match(commit["message"])
        if match and len(commit["parents"]) == 2:
            merged.setdefault(match.group(1), match.group(2))
        elif not commit["parents"] or gh.get(f"compare/{main_sha}...{sha}?per_page=1")["ahead_by"] == 0:
            break
        sha = commit["parents"][0]["sha"]
    return merged


def recall(gh, batch, main_sha, under=None):
    """What is known about a batch: {"merged": {number: commit}, "refused": {...}, "seen": {...},
    "base": ...}.

    `merged` and `refused` come from the note in the pull request's text when the note was
    written for the batch's present head. Otherwise `merged` is read again from the branch.
    `base` is the batch it is built on, as {number, sha, start}: the head of that batch it was
    last brought up to date with, and the commit its own branch was started from. It is None
    for a batch built on main. Without a note, as while the batch has no pull request, the walk
    back through the branch stops at `under` instead, the head of the batch it should be built
    on, in case it was started there.
    """
    state = {"merged": {}, "refused": {}, "seen": {}, "base": None}
    match = STATE.search(batch["body"])
    try:
        note = json.loads(match.group(1)) if match else {}
    except ValueError:
        note = {}
    if isinstance(note.get("seen"), dict):
        state["seen"] = note["seen"]
    if isinstance(note.get("base"), dict):
        state["base"] = note["base"]
    if note.get("head") == batch["sha"] and isinstance(note.get("merged"), dict):
        state["merged"], state["refused"] = note["merged"], dict(note.get("refused") or {})
    else:
        state["merged"] = added(gh, batch, main_sha, (state["base"] or {}).get("start") or under)
    return state


def describe(batch, state, members, also=(), refused=(), unapproved=(), stack=()):
    """The text of a batch pull request. `stack` is what to say about the batch it is built on."""
    lines = [BODY, "The batch-queue workflow assembles this pull request. When a maintainer comments "
             "`batch` on a pull request, the commit that was its head at that moment is merged in here."]
    if stack:
        lines += [""] + list(stack)
    lines += ["", "In this batch:", ""]
    lines += [f"- #{number} at `{sha[:10]}`" for number, sha in members] or ["- nothing yet"]
    if also:
        lines += ["", "Also in this branch:", ""] + [f"- #{number}, {why}" for number, why in also]
    if refused:
        lines += ["", "Left out, because GitHub could not merge them into this branch: "
                  + ", ".join(f"#{number}" for number in refused) + "."]
    if unapproved:
        lines += ["", f"Labelled `{QUEUED}` but not queued, because no maintainer has commented `batch` on them: "
                  + ", ".join(f"#{number}" for number in unapproved) + "."]
    lines += ["", "Merge this with a merge commit, not a squash, so that GitHub marks the pull "
              "requests above as merged."]
    note = {"head": batch["sha"], "merged": state["merged"], "refused": state["refused"], "seen": state["seen"]}
    if state.get("base"):
        note["base"] = state["base"]
    lines += ["", f"<!-- batch-queue-state {json.dumps(note, sort_keys=True)} -->"]
    return "\n".join(lines) + "\n"


def publish(gh, batch, main, text):
    """Open the batch's pull request if it has none, and bring its text up to date. A refusal to
    open it raises `Refused`, which `assemble` logs and goes on from."""
    if batch["number"]:
        if text != batch["body"]:
            gh.write("PATCH", f"pulls/{batch['number']}", {"body": text})
        return
    title = "Batch " + batch["ref"][len(PREFIX):]
    status, data = gh.write("POST", "pulls", {"title": title, "head": batch["ref"], "base": main, "body": text})
    if status == 201:
        batch["number"] = data["number"]
    elif status:
        raise Refused(
            f"GitHub would not let this workflow open a pull request for `{batch['ref']}` "
            f"({status}: {(data or {}).get('message', 'no reason given')}). The branch is ready. Open the pull "
            f"request by hand at https://github.com/{gh.repo}/compare/{main}...{batch['ref']}?expand=1 and it "
            "will be picked up, or allow GitHub Actions to create pull requests in the repository settings.")


def start(gh, main, head, now, log, on=None):
    """Create the branch for a new batch at `head`, under a name no other batch has. `on` is the
    number of the batch whose head that is, when it is not main's."""
    stamp = (now or datetime.datetime.now(datetime.timezone.utc)).strftime("%Y-%m-%d-%H%M%S")
    status, data = None, None
    for name in [PREFIX + stamp] + [f"{PREFIX}{stamp}-{count}" for count in range(2, 6)]:
        status, data = gh.write("POST", "git/refs", {"ref": f"refs/heads/{name}", "sha": head})
        if status in (0, 201):
            log.append(f"started `{name}` on top of #{on}" if on else f"started `{name}` from `{main}`")
            return {"ref": name, "sha": head, "number": None, "body": ""}
        if status != 422:
            break
    raise Refused(f"GitHub would not create a batch branch ({status}: {(data or {}).get('message', 'no reason given')}).")


# ---------------------------------------------------------------------------------------------
# Batches assembled by hand.


def read_record(gh, number):
    """This script's comments on a batch assembled by hand, as (comment, note, check): the one
    that records what it contains, what that one notes, and the one that compares its description
    with its branch. A comment is None, and the note empty, until there is one."""
    record, note, check = None, {}, None
    for comment in gh.pages(f"issues/{number}/comments"):
        body = comment.get("body") or ""
        if not by_workflow(comment):
            continue
        match = BY_HAND.match(body)
        if match and record is None:
            record, note = comment, load_note(match.group(1))
        elif body.startswith(CHECK) and check is None:
            check = comment
    return record, note, check


# The note of a batch assembled by hand: what `look_through`, `keep_in_step` and the functions it
# calls remember from one run to the next. `save` writes it into this script's record comment on
# the batch's pull request, with `dump_note`, and `read_record` reads it back, with `load_note`.
# In memory, numbers are strings, and a key may be missing from a note written before it was:
#
#   head      the branch's head when `members` was found.
#   members   what the batch contains of its own, as {number: the commit of it that is in the
#             branch}: not what a batch it is stacked on contains. A note written before batches
#             were stacked may list a batch here; it is never taken for a member.
#   queued    the members that were labelled `batch queue` before the batch took them. They go
#             back to the queue if the batch is closed without being merged. A note without it
#             is from before it was written down, and held only queued pull requests.
#   below     the batches this one is stacked on, directly or not, as {number: the head of that
#             batch when its own members were found}. Missing when there are none. When it
#             changes, the branch is looked through again, because what this batch contains of
#             its own changes with it.
#   labelled  the members this batch labelled `batch-building` and `frozen`, once each.
#   told      {number: commit}: the members told that they are frozen, at that commit. When the
#             batch takes a member's new head, the comment is edited to name it (see `retell`).
#   pushed    {number: commit}: the members told that they were pushed to after the batch took
#             that commit, and labelled `awaiting-author`.
#   waiting   the members that this batch labelled `awaiting-author` when it told them they were
#             pushed to, and that still carry it. It comes off once the batch holds their head
#             again (see `unwait`). One that lost the label meanwhile leaves the list: a label put
#             on later is a person's.
#   left      {number: digest}: the pull requests told that the description leaves them out, with
#             a digest of the entry they were told about (see `tell_left_out`).
#   reverted  {number: commit}: the members that the branch reverts, with the commit that does
#             (see `reverts`). Missing in a note from before it was written down, which makes
#             `look_through` list the branch again.
#   warned    {number: commit}: the members told that the branch reverts them, in that commit
#             (see `tell_reverted`).
#   fates     {number: "merged" or "closed"}: what became of the pull requests the description
#             lists as included that are not open, each asked of GitHub once (see
#             `check_description`).
#   check     a digest of what the comment comparing the description with the branch says (see
#             `check_description`), or "" before there is one.
#   telling   true from just before the first comment of a round of telling (`tell_members` and
#             `tell_left_out`) until the round is over. A run that finds it still set looks for
#             each comment before it posts it (see `announce`): the run before was cut short, and
#             may have posted comments its note does not show.
#
# An entry of `told` or `pushed` counts only while its commit is the member's, and one of `warned`
# only while its commit is the one `reverted` names: `keep_in_step` drops the others. On GitHub,
# where a comment holds at most 65,536 characters, the note is compact JSON and keeps only the
# entries that count, `warned` too, as lists of numbers. `queued`, `labelled` and `told` are each
# kept as that list or as the list of the members it leaves out (`unqueued`, `unlabelled`,
# `untold`), whichever is shorter: a batch usually labels and tells nearly all of its members.
# `below` is kept as it is in memory, and `waiting` as a list of numbers, each only when it is not
# empty. What is left is about 50 characters for each member, nearly all of it `members` with its
# full commit ids. `load_note` also reads the notes written before `dump_note`, which kept every
# key as it is in memory.


def dump_note(note):
    """A note as it is kept on GitHub: compact JSON, with only the keys the note has."""
    found = note.get("members") or {}
    kept = {name: note[name] for name in ("head", "members", "left", "reverted", "check") if name in note}
    if note.get("fates"):
        kept["fates"] = note["fates"]
    if note.get("below"):
        kept["below"] = note["below"]

    def shorter(name, keys):
        keys = {key for key in keys if key in found}
        rest = {key for key in found if key not in keys}
        if len(rest) < len(keys):
            kept["un" + name] = sorted(int(key) for key in rest)
        else:
            kept[name] = sorted(int(key) for key in keys)

    def counting(entries):
        return {key for key, commit in entries.items() if found.get(key) == commit}

    if "queued" in note:
        shorter("queued", note["queued"])
    if "labelled" in note:
        shorter("labelled", note["labelled"])
    if "told" in note:
        shorter("told", counting(note["told"]))
    if "pushed" in note:
        kept["pushed"] = sorted(int(key) for key in counting(note["pushed"]))
    if "warned" in note:
        kept["warned"] = sorted(int(key) for key, undo in note["warned"].items()
                                if (note.get("reverted") or {}).get(key) == undo)
    if note.get("waiting"):
        kept["waiting"] = sorted(int(key) for key in note["waiting"] if key in found)
    if note.get("telling"):
        kept["telling"] = True
    return json.dumps(kept, sort_keys=True, separators=(",", ":"))


def load_note(text):
    """A note as `dump_note` wrote it, or as notes were written before it, in memory. Anything
    that is not a note reads as an empty one."""
    try:
        kept = json.loads(text)
    except ValueError:
        return {}
    if not isinstance(kept, dict):
        return {}

    def numbers(name):
        found = kept.get(name)
        return {str(key) for key in found} if isinstance(found, list) else None

    def mapping(name):
        return {str(key): value for key, value in kept[name].items()}

    note = {"head": kept["head"]} if "head" in kept else {}
    for name in ("members", "left", "reverted", "fates"):
        if isinstance(kept.get(name), dict):
            note[name] = mapping(name)
    if isinstance(kept.get("check"), str):
        note["check"] = kept["check"]
    if isinstance(kept.get("below"), dict) and kept["below"]:
        note["below"] = mapping("below")
    found = note.get("members", {})
    for name in ("queued", "labelled", "told"):
        listed, rest = numbers(name), numbers("un" + name)
        if rest is not None:
            listed = {key for key in found if key not in rest}
        if listed is None:
            if name == "told" and isinstance(kept.get(name), dict):
                note[name] = mapping(name)
        elif name == "told":
            note[name] = {key: found[key] for key in sorted(listed, key=int) if key in found}
        else:
            note[name] = sorted(listed, key=int)
    if numbers("pushed") is not None:
        note["pushed"] = {key: found[key] for key in sorted(numbers("pushed"), key=int) if key in found}
    elif isinstance(kept.get("pushed"), dict):
        note["pushed"] = mapping("pushed")
    if numbers("warned") is not None:
        undone = note.get("reverted", {})
        note["warned"] = {key: undone[key] for key in sorted(numbers("warned"), key=int) if key in undone}
    elif isinstance(kept.get("warned"), dict):
        note["warned"] = mapping("warned")
    if numbers("waiting"):
        note["waiting"] = sorted(numbers("waiting"), key=int)
    if kept.get("telling") is True:
        note["telling"] = True
    return note


def members(note):
    """What a note says a batch assembled by hand contains, as {number: commit}."""
    found = note.get("members")
    return dict(found) if isinstance(found, dict) else {}


def queued_before(note):
    """Which of those were labelled `batch queue` before they were labelled `building`. A note
    from before this was written down holds only queued pull requests."""
    if isinstance(note.get("queued"), list):
        return {str(key) for key in note["queued"]}
    return set(members(note))


def branch_commits(gh, base, head, pages=20):
    """The commits of a branch whose head is `head` that `base` does not have, or None if GitHub
    did not list them all. A request for each hundred of them. They come as {commit: (message,
    parents)}, oldest first, so that what the branch reverts is read from the same requests."""
    found = {}
    for page in range(1, pages + 1):
        status, data = gh.call("GET", f"compare/{base}...{head}?per_page=100&page={page}")
        if status != 200 or not isinstance(data, dict) or not isinstance(data.get("commits"), list):
            return None
        for commit in data["commits"]:
            found[commit["sha"]] = ((commit.get("commit") or {}).get("message") or "",
                                    [parent.get("sha") for parent in commit.get("parents") or ()])
        if len(found) >= data.get("total_commits", 0):
            return found
        if len(data["commits"]) < 100:
            return None
    return None


def inside(batch, pulls, commits):
    """The open pull requests whose head commit is one of a batch's `commits`, as {number: commit}.
    No pull request that holds a batch is ever in another batch: one batch is stacked on another
    instead (see `stack`). A pull request into another branch counts too: it is built along with
    the batch, even though GitHub will not mark it merged when the batch is."""
    return {str(pr["number"]): pr["sha"] for pr in pulls.values() if not pr["batch"] and pr["sha"] in commits}


def built_by_hand(gh, pulls, log):
    """The open batches assembled by hand that are being built, as {ref, sha, number, base,
    comment, note, check, commits}.

    One labelled `building` is being built. One that is not is looked through, at a request or
    so, and labelled `building` once its branch holds the head commit of an open pull request:
    the label is how it is found again after it is closed. One labelled `batch queue` and not
    `building` is waiting in the queue like any other pull request, and is not looked at. Reading
    the note costs a request for each, and finds the comment that compares the description with
    the branch (`check`) as well. `commits` is what the branch was found to hold, or None when it
    was not looked through.
    """
    found = []
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if not by_hand(pr) or (QUEUED in pr["labels"] and BUILDING not in pr["labels"]):
            continue
        commits = None
        if BUILDING not in pr["labels"]:
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: did not look through the batch "
                           f"#{pr['number']}, and the next run does")
                continue
            commits = branch_commits(gh, pr["base"], pr["sha"])
            if commits is None:
                log.append(f"GitHub did not list every commit of the batch #{pr['number']}: the next run looks again")
                continue
            if not inside(pr, pulls, commits):
                continue
            if not relabel(gh, pr, add=BUILDING):
                continue
            log.append(f"#{pr['number']} is a batch assembled by hand with open pull requests in it: now `{BUILDING}`")
        # Labelled `building` just now, for the first time or again, the note is kept: what it says
        # was told still was, and `look_through` looks through the branch again. A batch closed without
        # being merged and reopened had its members told they could push again, and `finish`
        # cleared what they were told then, so they are told they are frozen again.
        comment, note, check = read_record(gh, pr["number"])
        found.append({"ref": pr["ref"], "sha": pr["sha"], "number": pr["number"], "base": pr["base"],
                      "comment": comment, "note": note, "check": check, "commits": commits})
    return found


def stacked_on(gh, pr, batches):
    """Which of `batches`, a set of numbers, the batch held by `pr` says it is stacked on, and
    where it says so: (set of numbers, "a `depends on` line" or "its branch name" or None).

    A `depends on` line of its description that names one of them counts, ticked or not (see
    `pr-dependencies.py`). When none does, a branch named `batch/<anything>-on-<number>` is
    stacked on that number, if it is one of them. A batch is never stacked on itself.
    """
    others = set(batches) - {pr["number"]}
    named = _deps.dependencies(pr["body"], gh.repo) & others
    if named:
        return named, "a `depends on` line"
    match = ON_BATCH.fullmatch(pr["ref"])
    if match and int(match.group(1)) in others:
        return {int(match.group(1))}, "its branch name"
    return set(), None


def named_below(gh, ref, body, note):
    """Every number that a batch assembled by hand, with branch `ref`, description `body` and note
    `note`, names as a batch it may be stacked on, open or not: in a `depends on` line, in its
    branch name or in the note's `below`."""
    named = set(_deps.dependencies(body, gh.repo)) | {int(key) for key in note.get("below") or {}}
    match = ON_BATCH.fullmatch(ref)
    if match:
        named.add(int(match.group(1)))
    return named


def twins(hand, log):
    """Stack batches whose branches are at the same commit on one another, in number order.

    Two such batches contain the same pull requests, and so does a branch that contains another's
    head while the other contains its head: the two heads are one commit. Whatever they say about
    each other, each is taken to be stacked on the one with the next lower number, which holds
    what they share, and the one with the highest number is the outermost. What they say about
    other batches still counts. Sets `same` on each batch, the batch it is stacked on for that
    reason, and warns on every run that sees such batches.
    """
    for batch in hand:
        batch["same"] = set()
    heads = {}
    for batch in hand:
        heads.setdefault(batch["sha"], []).append(batch)
    for head, group in sorted(heads.items(), key=lambda item: min(batch["number"] for batch in item[1])):
        if len(group) < 2:
            continue
        group.sort(key=lambda batch: batch["number"])
        numbers = {batch["number"] for batch in group}
        for lower, upper in zip(group, group[1:]):
            upper["same"] = {lower["number"]}
        for batch in group:
            batch["under"] = (batch["under"] - numbers) | batch["same"]
            if not batch["under"] - batch["same"]:
                batch["how"] = None
        names = ", ".join(f"#{batch['number']}" for batch in group)
        order = ", ".join(f"#{upper['number']} on #{lower['number']}" for lower, upper in zip(group, group[1:]))
        log.append(f"warning: the batches {names} are at the same commit `{head[:10]}`: whatever they say about "
                   f"each other, each is taken to be stacked on the one with the next lower number ({order})")


def stacking(batch):
    """Which batches a batch is stacked on directly, and why, in words, or "" when it is stacked on
    none: "#1018, as its branch name says"."""
    same = batch.get("same", set())
    claimed = sorted(set(batch.get("under", ())) - same)
    parts = []
    if claimed:
        parts.append(", ".join(f"#{number}" for number in claimed) + f", as {batch['how']} says")
    if same:
        parts.append(", ".join(f"#{number}" for number in sorted(same))
                     + ", whose branch is at the same commit and whose number is lower")
    return ", and on ".join(parts)


def stack(gh, hand, pulls, log):
    """Put the open batches assembled by hand that are being built in order, the lowest first.

    Sets on each `under`, the batches it is stacked on directly, `how`, where it says so, `same`,
    those of them it is stacked on because their branches are at the same commit (see `twins`),
    and `below`, every batch under it, directly or not, all as numbers of batches in `hand`.
    Batches that say they are stacked on each other in a circle are taken to be stacked on none,
    except for `same`, and the run says so. Each batch comes after every batch under it.
    """
    numbers = {batch["number"] for batch in hand}
    by = {batch["number"]: batch for batch in hand}
    for batch in hand:
        batch["under"], batch["how"] = stacked_on(gh, pulls[batch["number"]], numbers)
    twins(hand, log)

    def close():
        for batch in hand:
            seen, todo = set(), list(batch["under"])
            while todo:
                number = todo.pop()
                if number not in seen:
                    seen.add(number)
                    todo += by[number]["under"]
            batch["below"] = seen

    close()
    circle = sorted(batch["number"] for batch in hand if batch["number"] in batch["below"])
    if circle:
        # What `twins` stacks never makes a circle by itself, so none is left once the rest goes.
        log.append("the batches " + ", ".join(f"#{number}" for number in circle) + " say they are stacked on "
                   "each other in a circle: none of them is taken to be stacked on another batch"
                   + (", except one at the same commit" if any(by[number]["same"] for number in circle) else ""))
        for number in circle:
            by[number]["under"], by[number]["how"] = set(by[number]["same"]), None
        close()
    # A batch has more batches under it than any batch under it has.
    return sorted(hand, key=lambda batch: (len(batch["below"]), batch["number"]))


def outermost(hand):
    """The numbers of the batches in `hand`, put in order by `stack`, that no other is stacked on."""
    return {batch["number"] for batch in hand} - set().union(*(batch["under"] for batch in hand))


def holders(hand):
    """Which batches assembled by hand contain each pull request, as {number: {batch numbers}}."""
    held = {}
    for batch in hand:
        for key in members(batch["note"]):
            held.setdefault(key, set()).add(batch["number"])
    return held


def holding(hand):
    """The commit at which each pull request's own batch holds it, as {number: commit}. `hand` is
    put in order by `stack`, so a pull request that a record written before batches were stacked
    holds as well keeps the commit of the lowest batch."""
    held = {}
    for batch in hand:
        for key, commit in members(batch["note"]).items():
            held.setdefault(key, commit)
    return held


def contains(gh, head, commit):
    """Whether a branch whose head is `head` has `commit` in it, or None if GitHub did not say."""
    status, data = gh.call("GET", f"compare/{head}...{commit}?per_page=1")
    if status != 200 or not isinstance(data, dict) or "ahead_by" not in data:
        return None
    return data["ahead_by"] == 0


def merge_base(gh, one, other):
    """The commit that GitHub takes as the merge base of two commits, or None if it did not say."""
    status, data = gh.call("GET", f"compare/{one}...{other}?per_page=1")
    if status != 200 or not isinstance(data, dict):
        return None
    return (data.get("merge_base_commit") or {}).get("sha")


def shares(gh, batch, other, by, commits):
    """Whether a batch, whose branch holds `commits` beyond main, shares a commit beyond main with
    the batch `other` that it says it is stacked on. Usually it holds the head of `other`, or the
    commit of a pull request that `other` or a batch under it contains. Otherwise GitHub is asked
    for the merge base of the two. When GitHub does not say, they are taken to share one."""
    if other["sha"] in commits:
        return True
    for number in other["below"] | {other["number"]}:
        if any(commit in commits for commit in members(by[number]["note"]).values()):
            return True
    base = merge_base(gh, other["sha"], batch["sha"])
    return base is None or base in commits


def kept(note, name):
    """A map the note keeps, as {number: value}, or an empty one."""
    found = note.get(name)
    return dict(found) if isinstance(found, dict) else {}


def save(gh, batch):
    """Write the note of a batch assembled by hand to this script's comment on its pull request,
    if it has changed. A note that cannot be written stops the run: everything else relies on it."""
    text, comment = describe_by_hand(batch["note"], stacking(batch)), batch["comment"]
    if comment is None:
        status, data = gh.write("POST", f"issues/{batch['number']}/comments", {"body": text})
        if status in (0, 201):
            batch["comment"] = {"id": (data or {}).get("id"), "body": text}
            return
    elif text != comment.get("body"):
        status, _ = gh.write("PATCH", f"issues/comments/{comment['id']}", {"body": text})
        if status in (0, 200):
            comment["body"] = text
            return
    else:
        return
    raise Refused(f"GitHub would not save the record of the batch #{batch['number']} ({status}).")


# Members told between two saves of the note, so that a run that stops halfway repeats little.
SAVE_EVERY = 10


def look_through(gh, batch, by, pulls, before, gone, log):
    """Find what a batch assembled by hand contains of its own.

    It contains each open pull request whose head commit is in its branch, queued or not, that
    no batch under it contains: a pull request in several batches of one stack belongs to the
    lowest. `by` is the batches being built, by number; those under this one have been looked
    through already. When the branch's head, or a batch under it, has moved since the note was
    written, the branch's commits are listed again, a request for each hundred of them, and so
    they are when the batch has just been labelled `building` again, or when the note is from
    before it recorded what the branch reverts. What has arrived is added. What was found before
    stays as long as the commit it was found at is still there, even after its author has pushed
    again, unless its new head is in the branch too and is not an earlier commit than that one,
    which costs a request (see `contains`). After a push back to an earlier commit, the branch has
    the new head only as part of the commit it was found at, which the batch still lands, and
    `tell_members` tells the pull request so. When GitHub does not say, nothing is set, as when
    the branch could not be listed. Which of them the branch reverts (`reverted`, see `reverts`) is
    read from the same list. `before` is the pull
    requests that some note says were labelled `batch queue` before a batch took them, and `gone`
    the batches assembled by hand that were merged or closed and are being tidied up after.

    Sets the batch's new `note`, with its `head`, `members`, `queued` and `below`, and `reverted`
    when the branch was listed, and `old`, the
    note it had, for `keep_in_step` to finish. Nothing is set when the branch could not be listed:
    the note keeps its old head, so the next run looks again, and `keep_in_step` leaves the batch
    alone. The note's keys are described above `dump_note`.
    """
    note, number = batch["note"], batch["number"]
    found, queued = members(note), queued_before(note)
    below = {str(other): by[other]["note"].get("head", "") for other in sorted(batch["below"])}
    taken = set().union(*(members(by[other]["note"]) for other in batch["below"]))
    # A batch labelled `building` just now was looked through already, and is looked at afresh.
    commits = None
    if note.get("head") != batch["sha"] or note.get("below", {}) != below or batch.get("commits") is not None \
            or "reverted" not in note:
        commits = batch.get("commits")
        if commits is None:
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: did not look through the batch #{number}, "
                           "and the next run does")
                return
            commits = branch_commits(gh, batch["base"], batch["sha"])
        if commits is None:
            log.append(f"GitHub did not list every commit of the batch #{number}: the next run looks again")
            return
        now = inside(batch, pulls, commits)
        for key, commit in found.items():
            if commit not in commits:
                continue
            if now.get(key, commit) != commit:
                earlier = contains(gh, commit, now[key])
                if earlier is None:
                    log.append(f"GitHub did not say whether #{key} was pushed back to an earlier commit than the one "
                               f"the batch #{number} took: the next run looks again")
                    return
                if earlier:
                    now[key] = commit
            now.setdefault(key, commit)
        found = now
        if set(below) != set(note.get("below", {})):
            log.append(f"#{number} is stacked on {stacking(batch)}" if batch["under"] else
                       f"#{number} is no longer stacked on another batch")
        for other in sorted(batch["under"] - batch.get("same", set())):
            if not shares(gh, batch, by[other], by, commits):
                log.append(f"warning: #{number} says in {batch['how']} that it is stacked on #{other}, but its branch "
                           f"shares no commit with that of #{other} beyond `main`")
    # A note written before batches were stacked lists what the batches under this one contain,
    # and those batches themselves, open or not, among its members.
    found = {key: commit for key, commit in found.items()
             if key not in taken and int(key) not in gone and not (pulls.get(int(key)) or {}).get("batch")}
    queued = {key for key in found
              if key in queued or key in before or QUEUED in (pulls.get(int(key)) or {}).get("labels", ())}
    batch["old"] = note
    batch["note"] = {"head": batch["sha"], "members": found, "queued": sorted(queued, key=int)}
    if below:
        batch["note"]["below"] = below
    if commits is not None:
        batch["note"]["reverted"] = reverts(commits, found)


def keep_in_step(gh, batch, pulls, held, main, log):
    """Record what `look_through` found in a batch assembled by hand, label it and tell it so.

    Whatever has left the batch loses `batch-building` and `frozen` unless another batch contains
    it, goes back to `batch queue` if it was queued before and still is, and is told so. `held`
    says, for each pull request, which batches contain it now, after every batch has been looked
    through: a pull request that moves from one batch of a stack to another keeps its labels.
    Returns whether anything was queued again.

    The note is written first, so that whatever carries `batch-building` because of this batch
    is in it when the batch is finished with. It then remembers what was done as it is done:
    which members were labelled (`labelled`), and who was told that they are frozen (`told`),
    that they were pushed to afterwards (`pushed`, which also labels them `awaiting-author`, and
    `waiting` when that label was this workflow's, see `unwait`), or what the description says
    about them being left out (`left`, see `tell_left_out`), who was told that the branch reverts
    them (`warned`, see `tell_reverted`), and what the comment comparing the description with the
    branch says (`check`, see `check_description`). Only what
    GitHub took counts as done, so what was refused or cut short is tried again by the next run,
    and nothing is done twice: a round of telling is marked in the note before its first comment
    (`telling`), and a run that finds the mark looks for each comment before it posts it, in case
    the note was not saved after it. A member is labelled once: a label taken off by hand stays off,
    except that a pull request queued again swaps `batch queue` for the labels of the batch. A
    member whose record moves to its new head, which the branch now has, is not told again: what it
    was told is edited to match (see `retell`). The note's keys are described above `dump_note`.
    """
    if "old" not in batch:
        return False
    old, note, number, requeued = batch["old"], batch["note"], batch["number"], False
    found = note["members"]
    # A round of telling that the last run started and did not finish.
    batch["resumed"] = bool(old.get("telling"))
    for key, commit in sorted(members(old).items(), key=lambda entry: int(entry[0])):
        pr = pulls.get(int(key))
        if key in found or pr is None or held.get(key) or not pr["labels"] & set(IN_BATCH):
            continue
        if pr["batch"]:
            # A batch that a note written before batches were stacked lists as a member carries
            # `building` for being built itself: its labels never change through membership.
            continue
        # Only what is still queued goes back: `-batch` may have been said meanwhile.
        back = key in queued_before(old) and look(gh, pr, {})[0] is not None
        relabel(gh, pr, add=(QUEUED, FROZEN) if back else None, remove=unfrozen(back))
        requeued |= back
        tell(gh, pr["number"], None, DROPPED.format(number=number, sha=commit),
             f"Commit `{commit[:10]}` of this pull request is no longer in batch #{number}: its "
             f"branch was changed without it. {thawed(back)}")
        log.append(f"#{key} is no longer in the batch #{number}: "
                   + (f"`{QUEUED}` again" if back else f"no longer `{MEMBER}`"))
    # What was done for a pull request that has been closed since is done again if it is reopened.
    labelled = sorted({key for key in old.get("labelled") or () if key in found and int(key) in pulls}, key=int)
    left = kept(old, "left")
    if batch["comment"] is not None and "left" not in old:
        # A record from before the description was read for what it leaves out. Its pull requests
        # were told about it by people, if at all, so what the description says now counts as told,
        # and only what is added or changed from here on is.
        left = {str(key): entry_digest(entry) for key, entry in left_out(pulls[number]["body"], gh.repo).items()
                if key in pulls and str(key) not in held}
        log.append(f"the record of the batch #{number} is older than the notices of what a batch leaves out: "
                   f"what its description leaves out now, {len(left)} pull request(s), is taken as told")
    told = {key: commit for key, commit in kept(old, "told").items() if found.get(key) == commit}
    if batch["comment"] is not None and "told" not in old:
        # A record from before members were told they are frozen. The batch was being built before
        # this script told anyone, so its members are labelled but not told: hundreds of comments
        # at once, about batches already under way, would only be noise. Pull requests that join
        # it from here on are told.
        told = dict(found)
        log.append(f"the record of the batch #{number} is older than the notices that a pull request is frozen: "
                   f"its {len(told)} pull request(s) are labelled but not told")
    else:
        # A member told at the commit the batch held, whose record moves to its new head now that
        # the branch has it: what it was told is brought up to date first. If that cannot be done,
        # it stays at the old commit, and the note keeps the old head so that the next run looks
        # through the branch again and tries again.
        before = members(old)
        for key, commit in sorted(kept(old, "told").items(), key=lambda entry: int(entry[0])):
            if found.get(key) in (None, commit) or before.get(key) != commit:
                continue
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: #{key} stays at `{commit[:10]}` in the "
                           f"record of the batch #{number} until the next run tells it of its new head")
                done = False
            else:
                done = retell(gh, batch, pulls[int(key)], commit, main, log)[0]
            if not done:
                found[key] = commit
                note["head"] = old.get("head", "")
            told[key] = found[key]
    # What the branch reverts is read with its commits (see `look_through`); otherwise it stands.
    reverted = note.get("reverted", {key: undo for key, undo in kept(old, "reverted").items() if key in found})
    # What became of a pull request stands while it is not open: one reopened is asked again.
    note["fates"] = {key: fate for key, fate in kept(old, "fates").items() if int(key) not in pulls}
    note.update(labelled=labelled, told=told, left=left, reverted=reverted,
                waiting=unwait(gh, batch, pulls, log),
                pushed={key: commit for key, commit in kept(old, "pushed").items() if found.get(key) == commit},
                warned={key: undo for key, undo in kept(old, "warned").items() if reverted.get(key) == undo},
                check=old.get("check") if isinstance(old.get("check"), str) else "")
    if batch["resumed"]:
        note["telling"] = True
    save(gh, batch)

    try:
        for key in sorted(found, key=int):
            pr = pulls.get(int(key))
            if pr is None or (key in labelled and not pr["labels"] & {QUEUED, BUILDING}):
                continue
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: stopped labelling what is in the batch "
                           f"#{number}, and the next run carries on")
                break
            if relabel(gh, pr, add=(MEMBER, FROZEN), remove=(QUEUED, BUILDING)):
                if key not in labelled:
                    labelled.append(key)
                log.append(f"#{key} is in the batch #{number}: now `{MEMBER}` and `{FROZEN}`")
        labelled.sort(key=int)
        done = tell_members(gh, batch, pulls, main, log) and tell_left_out(gh, batch, pulls, held, main, log)
        tell_reverted(gh, batch, pulls, main, log)
        check_description(gh, batch, pulls, held, log)
        if done:
            # The round is over: the note shows everything it said.
            note.pop("telling", None)
    finally:
        save(gh, batch)
    return requeued


def tell_members(gh, batch, pulls, main, log):
    """Tell each pull request in a batch assembled by hand, once, that it is frozen, and once that
    it was pushed to after the batch took it, if it was. The note remembers it. Returns whether
    everything was told, False when the run is cut short.

    A member whose head is not the commit the note holds may have been pushed to with a commit the
    batch already has, as when the merge of `main` that the batch was built from is pushed to the
    pull request afterwards. The batch is asked first (see `takes`). If it has the new head, and the
    new head has the commit in the note in it, the new head becomes the member's commit in the
    note, and no new comment is posted: if it was told it is frozen at the old one, that comment is edited to name the new head, and so is a comment of
    `pushed` about the old one, which also takes off the `awaiting-author` it put on (see
    `retell`). If they cannot be edited, the member stays at the old commit until the next run."""
    note, number, since = batch["note"], batch["number"], 0
    found, told, pushed, waiting = note["members"], note["told"], note["pushed"], note["waiting"]
    for key, commit in sorted(found.items(), key=lambda entry: int(entry[0])):
        pr = pulls.get(int(key))
        if pr is None or by_hand(pr) or (told.get(key) == commit and (pr["sha"] == commit or pushed.get(key) == commit)):
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped telling what is in the batch #{number}, "
                       "and the next run carries on")
            return False
        if pr["sha"] != commit and pushed.get(key) != commit:
            if key in (batch.get("handed") or {}):
                continue  # `keep_in_step` could not move it to its new head in this run (see `retell`)
            inside = takes(gh, batch, pr["sha"], commit)
            if inside is None:
                log.append(f"GitHub did not say whether the batch #{number} has the new head of #{key}, with "
                           f"`{commit[:10]}` in it: the next run asks again")
                continue
            if inside:
                if told.get(key) == commit:
                    done, handed = retell(gh, batch, pr, commit, main, log)
                    if not done:
                        continue  # the next run asks again
                    told[key] = pr["sha"]
                    # A comment of `pushed` that the note does not know of yet, or one it does.
                    if (handed or key in waiting) and WAITING in pr["labels"] and relabel(gh, pr, remove=WAITING):
                        log.append(f"#{key} is in the batch #{number} at its head again: `{WAITING}` removed")
                        if key in waiting:
                            waiting.remove(key)
                found[key] = pr["sha"]
                commit, since = pr["sha"], since + 1
                log.append(f"#{key} was pushed to with `{commit[:10]}`, which the batch #{number} has already: "
                           "recorded at that commit")
                if told.get(key) == commit:
                    continue
        if told.get(key) != commit and announce(gh, batch, pr["number"], FROZEN_NOTE.format(number=number, sha=commit),
                                                 frozen_text(number, commit, pr, main)):
            told[key], since = commit, since + 1
            log.append(f"told #{key} that it is frozen while the batch #{number} is built")
        if pr["sha"] != commit and pushed.get(key) != commit:
            done, handed = tell_pushed(gh, number, commit, pr, main, log)
            if done:
                pushed[key], since = commit, since + 1
            if done and handed and key not in waiting:
                waiting.append(key)
                waiting.sort(key=int)
        if since >= SAVE_EVERY:
            save(gh, batch)
            since = 0
    return True


def has_head(gh, batch, sha):
    """Whether the branch of `batch` has the commit `sha`: from its commits, when this run listed
    them, or else with one request. None when GitHub did not say."""
    if batch.get("commits") is not None:
        return sha in batch["commits"]
    return contains(gh, batch["sha"], sha)


def takes(gh, batch, sha, commit):
    """Whether a push of `sha` to a pull request that the batch `batch` took at `commit` brought in
    only commits the batch has already: whether its branch has `sha` (see `has_head`), and `sha`
    has `commit` in it, one more request. A push back to an earlier commit than `commit`, or of a
    rewritten one, does not count even when the branch has it: the batch still lands `commit`.
    None when GitHub did not say."""
    inside = has_head(gh, batch, sha)
    if not inside:
        return inside
    return contains(gh, sha, commit)


def announce(gh, batch, number, marker, text):
    """Leave a comment on a pull request for the batch assembled by hand `batch`, in a round of
    telling, and return whether it is there. The note is marked `telling` and saved before the
    round's first comment. In a round that the last run started and did not finish, the pull
    request's comments are read first, and one the workflow already left counts as told: that
    run may have posted it and then failed to save its note."""
    if not batch["note"].get("telling"):
        batch["note"]["telling"] = True
        save(gh, batch)
    if batch.get("resumed") and any((comment.get("body") or "").startswith(marker)
                                    for comment in gh.pages(f"issues/{number}/comments") if by_workflow(comment)):
        return True
    return say(gh, number, marker, text)


def tell_pushed(gh, number, commit, pr, main, log):
    """Tell a pull request that it was pushed to after the batch `number` took its commit `commit`,
    and label it `awaiting-author`, unless the workflow has told it so before. The label goes on
    first, so that a run cut short between the two leaves the label rather than the comment
    without it. Its comments are read to look for an earlier one: `pushed` tells it as soon as the
    push comes in, without writing the batch's note, and the sync takes that into its note.
    Returns whether it has been told, and whether the workflow put `awaiting-author` on along with
    the comment, which then says so (`HANDED_BACK`)."""
    marker = PUSHED.format(number=number, sha=commit)
    for comment in gh.pages(f"issues/{pr['number']}/comments"):
        body = comment.get("body") or ""
        if by_workflow(comment) and body.startswith(marker):
            return True, HANDED_BACK in body
    handed = WAITING not in pr["labels"] and relabel(gh, pr, add=WAITING)
    if not say(gh, pr["number"], marker, (f"{HANDED_BACK}\n" if handed else "") +
               f"This pull request was pushed to after batch #{number} took its commit `{commit[:10]}`. The batch "
               f"builds and lands `{commit[:10]}` only, not `{pr['sha'][:10]}`, so when it lands this pull request "
               f"stays open with what came after `{commit[:10]}`. Once the batch has landed, merge `{main}` into "
               "this branch and comment `ready`, or close this pull request if nothing is left to change."):
        return False, False
    log.append(f"told #{pr['number']} that it was pushed to after the batch #{number} took it: now `{WAITING}`")
    return True, handed


def handed_back(gh, number, key, commits):
    """Whether the workflow put `awaiting-author` on the pull request `key` when it told it that it
    was pushed to after the batch `number` took one of `commits`: that comment says so. A request."""
    markers = tuple(PUSHED.format(number=number, sha=commit) for commit in commits)
    return any(by_workflow(comment) and (comment.get("body") or "").startswith(markers)
               and HANDED_BACK in comment["body"] for comment in gh.pages(f"issues/{key}/comments"))


def retell(gh, batch, pr, old, main, log):
    """Bring what a member of a batch assembled by hand was told up to date when the batch takes its
    new head, so that its record moves from the commit `old` to `pr["sha"]`: when the branch is
    looked through again and has the new head (`keep_in_step`), or when `takes` finds it there
    (`tell_members`). It was told that it is frozen at `old`, and is not told so again: the last
    comment of the workflow's whose marker is this batch's `FROZEN_NOTE`, at whatever commit, is
    edited to name the new head, marker and all. One is posted only if there is none. A comment
    saying that it was pushed to after the batch took `old` (see `tell_pushed`), from a sync or from
    `pushed`, is edited too (`TAKEN`), to say that the batch holds the new head now and nothing more
    is needed. An edit notifies nobody.

    Its comments are read once. Returns whether both are up to date, and whether the workflow put
    `awaiting-author` on along with the second (`HANDED_BACK`), which is also kept in the batch's
    `handed` for `unwait`. The label is the caller's to take off."""
    number, key, new = batch["number"], str(pr["number"]), pr["sha"]
    comments = [comment for comment in gh.pages(f"issues/{key}/comments") if by_workflow(comment)]
    frozen = FROZEN_NOTE.partition("{sha}")[0].format(number=number)
    marker = FROZEN_NOTE.format(number=number, sha=new)
    told = [comment for comment in comments if (comment.get("body") or "").startswith(frozen)]
    if told:
        done = edit(gh, told[-1], marker, frozen_text(number, new, pr, main))
    else:
        done = say(gh, pr["number"], marker, frozen_text(number, new, pr, main))
    handed = False
    pushed = (PUSHED.format(number=number, sha=old), TAKEN.format(number=number, sha=old))
    for comment in comments:
        if not (comment.get("body") or "").startswith(pushed):
            continue
        back = HANDED_BACK in comment["body"]
        handed |= back
        done &= edit(gh, comment, TAKEN.format(number=number, sha=old), (f"{HANDED_BACK}\n" if back else "") +
                     f"This pull request was pushed to after batch #{number} took its commit `{old[:10]}`. The "
                     f"batch has since taken its new head `{new[:10]}`, and builds and lands that instead, so "
                     "nothing more is needed here.")
    batch.setdefault("handed", {})[key] = handed
    if done:
        log.append(f"#{key} is in the batch #{number} at its new head `{new[:10]}`: "
                   + ("its comments say so now" if told else "told that it is frozen at that commit"))
    else:
        log.append(f"GitHub would not bring up to date what #{key} was told about the batch #{number}: it stays at "
                   f"`{old[:10]}` until the next run")
    return done, handed


def edit(gh, comment, marker, text):
    """Make a comment of the workflow's say `text` under `marker`, as `say` writes it, unless it does
    already. Returns whether it does."""
    body = f"{marker}\n{text}\n"
    if comment.get("body") == body:
        return True
    if gh.write("PATCH", f"issues/comments/{comment['id']}", {"body": body})[0] not in (0, 200):
        return False
    comment["body"] = body
    return True


def unwait(gh, batch, pulls, log):
    """Take `awaiting-author` off each member of a batch assembled by hand whose head is the commit
    the batch holds again, if this workflow put it on when it told the member that it was pushed
    to after the batch took it: the batch has taken its new head, or it was pushed back. A label a
    person put on stays. Returns the note's new `waiting` (see `dump_note`).

    The note's `waiting` says which labels were the workflow's. When `pushed` told a member, the
    note does not know of it yet, so in the run where the batch takes a new head of a member that
    the note says nothing about, the member's comments are read instead (see `handed_back`), or
    what `retell` found in them when it read them in this run.
    """
    old, number, waiting = batch["old"], batch["number"], []
    found, before, told = batch["note"]["members"], members(batch["old"]), kept(batch["old"], "pushed")
    for key, commit in sorted(found.items(), key=lambda entry: int(entry[0])):
        pr = pulls.get(int(key))
        if pr is None or WAITING not in pr["labels"]:
            continue
        ours = key in (old.get("waiting") or ())
        if pr["sha"] != commit:
            if ours:
                waiting.append(key)
            continue
        if not ours and key not in told and before.get(key) not in (None, commit):
            # `retell` has read the comments already when it was told it is frozen at that commit.
            handed = batch.get("handed") or {}
            ours = handed[key] if key in handed else handed_back(gh, number, key, [before[key]])
        if not ours:
            continue
        if relabel(gh, pr, remove=WAITING):
            log.append(f"#{key} is in the batch #{number} at its head again: `{WAITING}` removed")
        else:
            waiting.append(key)
    return waiting


def frozen_text(number, commit, pr, main):
    """What a pull request in a batch assembled by hand is told when the batch takes it."""
    text = (f"Commit `{commit[:10]}` of this pull request is in batch #{number}, which is being built. Please "
            "don't push to this pull request until the batch has landed or been closed: the batch builds and lands "
            f"`{commit[:10]}`, and commits pushed after it are not part of it.")
    if pr["base"] == main:
        return text + " When the batch lands, GitHub marks this pull request merged."
    return (text + f" This pull request targets `{pr['base']}` rather than `{main}`, so GitHub will not mark it "
            "merged when the batch lands. If its head is still this commit then, this workflow closes it instead.")


def unlinked(text, repo):
    """Text quoted from a batch's description, with its references to pull requests and issues
    of `repo` put in code spans: `#123`, and links to them. GitHub turns neither into a link
    there, nor tells the pull request it names that it was mentioned, so quoting an entry does not
    cross-link every pull request it names. What is already in a code span is left as it is."""
    url = rf"https://github\.com/{re.escape(repo)}/(?:pull|issues)/\d+(?:[/#][\w/#-]*)?"
    link = re.compile(rf"\[([^\]]*)\]\(({url})\)", re.IGNORECASE)
    bare = re.compile(rf"(?<![\w`(]){url}|(?<![\w`/&#])#\d+\b", re.IGNORECASE)
    parts = re.split(r"(`+[^`]*`+)", text)
    for index in range(0, len(parts), 2):
        part = link.sub(lambda match: f"{match.group(1)} (`{match.group(2)}`)", parts[index])
        parts[index] = bare.sub(lambda match: f"`{match.group(0)}`", part)
    return "".join(parts)


def tell_left_out(gh, batch, pulls, held, main, log):
    """Tell each open pull request a batch's description lists as left out what it says.

    The comment quotes the heading and the pull request's entry, and only informs: it asks
    nothing of the author, whose pull request is not handed back, since many headings give a
    reason the author cannot act on. One labelled `deferred` is not told at all. One that this
    batch told before is not told again, whatever its
    entry or its heading now says, and neither is one whose latest such comment, from another
    batch, was for the same kind of reason (the same heading, see `left_out_digest`): that
    comment is brought up to date with what the description says now, which notifies nobody, so
    a pull request left out of batch after batch hears it once and still finds the latest reason
    there. Only a different batch leaving it out for a different kind of reason tells it again.
    The quote names pull requests and issues of this repository in code spans (see `unlinked`).
    One whose entry has gone from the description since it was told is told that, if this
    batch's comment told it, unless `REWORDED` or more leave the left-out lists at once while the
    description still lists them: a heading was most likely reworded, and they are only logged
    and taken off the note. What a batch being built contains, this one or another, as `held`
    says, is never told it is left out: the lower batch of a stack usually lists as left out what
    the batch on top of it takes. Neither is a pull request into `main` that is not a draft and is
    listed under a heading about conflicts with the batch (`CONFLICT_HEADING`), while the conflict
    labels are switched on (see
    `conflict_labels_on` in `batch-labels.py`): the conflict-labels workflow tells those itself, if
    git finds the conflict. The note's `left` remembers, for each pull request, a digest of the entry
    it was last told about for this batch, and is brought up to date as each is told.
    `keep_in_step` fills it in without telling anyone for a batch whose record is older than
    `left`. Returns whether everything was told, False when the run is cut short.
    """
    note, number, since = batch["note"], batch["number"], 0
    found, left = note["members"], note["left"]
    listed = left_out(pulls[number]["body"], gh.repo)
    conflicts = {other for other, (heading, _) in listed.items() if CONFLICT_HEADING.search(heading)}
    # No longer left out, but still in the description, as when a heading no longer says so.
    anywhere = {other for other, _, _ in _description.list_entries(pulls[number]["body"], gh.repo)}
    moved = sorted((key for key in left if int(key) not in listed and int(key) in anywhere and int(key) in pulls
                    and key not in found and not held.get(key) and not pulls[int(key)]["batch"]), key=int)
    if len(moved) >= REWORDED:
        log.append(f"the description of the batch #{number} no longer lists " + ", ".join(f"#{key}" for key in moved)
                   + " as left out, but still lists them: was a heading reworded? They were not told")
    else:
        moved = []
    for key in sorted(set(left) | {str(other) for other in listed}, key=int):
        pr = pulls.get(int(key))
        # The conflict-labels workflow looks only at pull requests into main that are not drafts.
        left_to_it = (_labels.conflict_labels_on() and int(key) in conflicts and pr is not None
                      and pr["base"] == main and not pr.get("draft"))
        if (pr is None or key in found or held.get(key) or pr["batch"] or left_to_it or key in moved
                or DEFERRED in pr["labels"]):
            left.pop(key, None)
            continue
        entry = listed.get(int(key))
        digest = left_out_digest(*entry) if entry else None
        seen = entry_digest(entry) if entry else None
        if left.get(key) == seen:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped telling what the batch #{number} leaves "
                       "out, and the next run carries on")
            return False
        comments = gh.pages(f"issues/{key}/comments")
        # The latest comment about being left out, the kind of reason it gave, and the latest one
        # from this batch.
        latest, previous, ours = None, None, None
        for comment in comments:
            match = LEFT_OUT.match(comment.get("body") or "") if by_workflow(comment) else None
            if match:
                try:
                    said = json.loads(match.group(1))
                except ValueError:
                    said = {}
                latest, previous = comment, said.get("digest") if isinstance(said, dict) else None
                if isinstance(said, dict) and said.get("batch") == number:
                    ours = comment
        if entry is None:
            # One that was never told it is left out, as when the note was filled in from an older
            # record, is not told that it no longer is either.
            if ours is not None and tell(
                    gh, pr["number"], comments, NO_LONGER_LEFT_OUT.format(number=number),
                    f"The description of batch #{number} no longer lists this pull request as left out."):
                log.append(f"told #{key} that the batch #{number} no longer lists it as left out")
            left.pop(key, None)
            continue
        heading, text = (unlinked(part, gh.repo) for part in entry)
        marker = f"<!-- batch-queue-left-out {json.dumps({'batch': number, 'digest': digest}, sort_keys=True)} -->"
        body = (f"{marker}\nBatch #{number} leaves this pull request out. Its description says:\n\n> {heading}\n>\n"
                f"> {text}\n\nThis is for your information: it changes no label of this pull request.\n")
        # This batch's own comment is brought up to date whatever its entry now says, its heading
        # too. So is another batch's for the same kind of reason.
        earlier = ours if ours is not None else latest if previous == digest else None
        if earlier is not None:
            if earlier.get("body") == body or gh.write(
                    "PATCH", f"issues/comments/{earlier['id']}", {"body": body})[0] in (0, 200):
                left[key] = seen
                log.append(f"brought up to date what #{key} was told about being left out, for the batch #{number}")
        elif announce(gh, batch, pr["number"], marker, body[len(marker) + 1:].rstrip("\n")):
            left[key], since = seen, since + 1
            log.append(f"told #{key} that the batch #{number} leaves it out")
        if since >= SAVE_EVERY:
            save(gh, batch)
            since = 0
    return True


def tell_reverted(gh, batch, pulls, main, log):
    """Tell each open pull request that a batch assembled by hand merged and then reverted, once,
    that it will be taken to have landed with the batch although its changes did not.

    Only one whose head is still the commit the batch holds is told: GitHub would mark it merged,
    or this workflow would close it if it targets another branch. One labelled `deferred` is told
    nothing: the maintainers took it out themselves, and the batch's pull request is where the
    revert is named (see `check_description`). The note's `warned` remembers
    who was told, so this costs nothing until the branch reverts another one. Before telling one,
    its comments are read once, so that a note that was lost does not make it hear this twice.
    """
    note, number = batch["note"], batch["number"]
    warned = note["warned"]
    for key, undo in sorted(note["reverted"].items(), key=lambda entry: int(entry[0])):
        pr, commit = pulls.get(int(key)), note["members"].get(key)
        if warned.get(key) == undo or pr is None or by_hand(pr) or pr["sha"] != commit or DEFERRED in pr["labels"]:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped telling what the batch #{number} "
                       "reverts, and the next run carries on")
            return
        marker = REVERTED.format(number=number, sha=undo)
        then = ("GitHub marks this pull request merged" if pr["base"] == main else
                f"this workflow closes this pull request, which targets `{pr['base']}`, as landed")
        if any(marker in (comment.get("body") or "") for comment in gh.pages(f"issues/{key}/comments")
               if by_workflow(comment)):
            warned[key] = undo
        elif say(gh, pr["number"], marker,
                 f"Batch #{number} took commit `{commit[:10]}` of this pull request and then reverted it in "
                 f"`{undo[:10]}`. The commit is still in the batch's branch, so if the batch lands as it is, {then} "
                 f"although its changes did not land. Its maintainers are asked on #{number} to rebuild the batch "
                 "without it instead. If it does land like this, open a new pull request with these changes."):
            warned[key] = undo
            log.append(f"told #{key} that the batch #{number} reverts it")


def check_description(gh, batch, pulls, held, log):
    """Compare the description of a batch assembled by hand with its branch, in a comment of its
    own on the batch's pull request (see `description_check`). `held` says which batches contain
    each pull request, so that what the batches under this one contain counts as in its branch.

    The comment is posted once there is something to say, and edited in place after that, also
    to say that all is well again. The note's `check` remembers a digest of what it says, so a
    run that would say the same thing makes no request at all. Nothing is posted just to say
    that all is well. A pull request the description lists as included that is not open is
    asked about once, a request, to say whether it was merged or closed; the note's `fates`
    remembers the answer.
    """
    note, number = batch["note"], batch["number"]
    under = set(batch.get("below", ()))
    below = {int(key) for key, owners in held.items() if owners & under}
    fates = note.setdefault("fates", {})
    for entry in sorted({entry for entry, heading, _ in _description.list_entries(pulls[number]["body"], gh.repo)
                         if heading and not _description.leaves_out(heading)} - {number}):
        if entry in pulls or str(entry) in fates:
            continue
        if gh.short():
            break
        status, data = gh.call("GET", f"pulls/{entry}")
        if status == 200 and isinstance(data, dict):
            fates[str(entry)] = "merged" if data.get("merged") or data.get("merged_at") else "closed"
    text, clear = description_check(number, pulls[number]["body"], gh.repo, note, pulls, below,
                                    {int(key): fate for key, fate in fates.items()})
    digest = hashlib.sha256(text.encode()).hexdigest()[:16]
    comment = batch.get("check")
    if note["check"] == digest:
        return
    if (comment is None and clear) or (comment is not None and comment.get("body") == text):
        note["check"] = digest
        return
    if gh.short():
        log.append(f"only {gh.remaining} requests left this hour: did not compare the description of the batch "
                   f"#{number} with its branch, and the next run does")
        return
    if comment is None:
        status, data = gh.write("POST", f"issues/{number}/comments", {"body": text})
        if status in (0, 201):
            batch["check"], note["check"] = {"id": (data or {}).get("id"), "body": text}, digest
            log.append(f"posted on the batch #{number} what its description and its branch disagree on")
    else:
        status, _ = gh.write("PATCH", f"issues/comments/{comment['id']}", {"body": text})
        if status in (0, 200):
            comment["body"], note["check"] = text, digest
            log.append(f"brought up to date what the batch #{number} is told about its description"
                       + (": all is well now" if clear else ""))


def describe_by_hand(note, under=""):
    """The comment that records what a batch assembled by hand contains. `under` says which
    batches it is stacked on directly, and why, as `stacking` puts it."""
    listed = ", ".join(f"#{key}" for key in sorted(note["members"], key=int)) or "nothing yet"
    stacked = ""
    if under:
        stacked = (f"This batch is stacked on {under}. A pull request that a batch under this one "
                   "contains is listed there, not here.\n\n")
    return (f"<!-- batch-queue-by-hand {dump_note(note)} -->\n"
            "While this pull request is open, the batch-queue workflow takes it to be a batch that is being built. "
            "It adds nothing to a batch assembled by hand and leaves its description alone, but it keeps the labels "
            "in step: each open pull request whose head commit is in this branch, and in no batch this one is "
            f"stacked on, is now `{MEMBER}` and `{FROZEN}`, in place of `{QUEUED}` if it had that, and is asked not "
            f"to push until this has landed. Those this description lists as left out are told why, unless they "
            f"are `{DEFERRED}` or a batch being built contains them: the comment only informs. Where the description "
            "and the branch disagree, or the branch reverts a pull request, it says so in another comment. When this "
            f"is merged the pull requests in it lose "
            f"`{MEMBER}` and `{FROZEN}`. If it is closed without being merged they lose them too, and the ones that "
            f"were queued go back to `{QUEUED}`, except those that a batch stacked on this one still holds. See "
            "`verification/BATCHES.md`.\n\n"
            f"{stacked}In this batch: {listed}.\n")


def stranded(gh, done, hand, pulls, log):
    """Tell each open batch assembled by hand that is stacked on a batch closed without being
    merged, once. Its branch still carries the commits of that batch, whose pull requests are now
    its own (see `look_through`), and whoever assembles it should rebuild it."""
    open_ = {batch["number"] for batch in hand}
    for gone in done:
        if gone["fate"] != "closed":
            continue
        for batch in hand:
            claimed, how = stacked_on(gh, pulls[batch["number"]], open_ | {gone["number"]})
            if gone["number"] not in claimed:
                continue
            if tell(gh, batch["number"], None, STRANDED.format(number=gone["number"]),
                    f"#{gone['number']}, which this batch is stacked on as {how} says, was closed without being "
                    f"merged. This batch's branch still carries the commits of #{gone['number']}, so the open pull "
                    f"requests of #{gone['number']} whose head commit is in this branch now count as part of this "
                    f"batch and stay `{MEMBER}` and `{FROZEN}`.\n\n"
                    "Whoever assembles this batch should rebuild it on `main` or on another batch, and update its "
                    "`depends on` line or its branch name to match."):
                log.append(f"told #{batch['number']} that #{gone['number']}, which it is stacked on, was closed "
                           "without merging")


def unsettled(gh, done, hand, pulls):
    """The batches among `done` closed without being merged that an open batch says it is stacked
    on, when that open batch could not be looked through in this run (see `look_through`). What
    such a batch contained may be held by the one stacked on it, which is not known yet: taking
    `building` off its members now would only see the next run put it back. They are left as
    they are, the closed batch keeping `building` itself, and the next run settles them."""
    open_ = {batch["number"] for batch in hand}
    return {gone["number"] for gone in done if gone["fate"] == "closed"
            for batch in hand
            if "old" not in batch and gone["number"] in stacked_on(gh, pulls[batch["number"]], open_ | {gone["number"]})[0]}


def mark_latest(gh, hand, pulls, log):
    """Label `latest batch` the outermost batch of each stack, and take the label off every
    other open pull request. A batch that was merged or closed loses it in `finish`. Returns
    whether a batch was labelled, which changes what the conflict-labels workflow compares pull
    requests with."""
    tops, added = outermost(hand), False
    for number in sorted(tops):
        pr = pulls[number]
        if LATEST in pr["labels"]:
            continue
        if not gh.label_exists(LATEST):
            log.append(f"there is no `{LATEST}` label in this repository: was it renamed?")
            break
        added = relabel(gh, pr, add=LATEST) or added
        log.append(f"#{number} is the outermost batch of its stack: now `{LATEST}`")
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if LATEST in pr["labels"] and pr["number"] not in tops:
            relabel(gh, pr, remove=LATEST)
            log.append(f"#{pr['number']} is not the outermost batch of a stack: `{LATEST}` removed")
    return added


def start_conflict_labels(gh, main, log):
    """Start the conflict-labels workflow, which compares pull requests with the batches being
    built, the outermost of each stack (see `conflict-labels.py`). A label put on with this
    workflow's token starts no run, so without this they would wait for its next sweep. Returns
    whether GitHub took it. Nothing is started while those labels are switched off (see
    `conflict_labels_on` in `batch-labels.py`). The run is a real one: a run started by hand is a
    dry run unless it says otherwise."""
    if not _labels.conflict_labels_on():
        return False
    status, _ = gh.write("POST", f"actions/workflows/{CONFLICT_WORKFLOW}/dispatches",
                         {"ref": main, "inputs": {"dry_run": "false"}})
    log.append(f"started {CONFLICT_WORKFLOW}" if status in (0, 204)
               else f"could not start {CONFLICT_WORKFLOW} ({status}): its next sweep looks at the batches")
    return status in (0, 204)


# ---------------------------------------------------------------------------------------------
# Building on a batch assembled by hand.


def restack(gh, batch, state, base, main_sha, log):
    """Keep the batch being assembled on top of `base`, {number, sha}, or on main when it is None.

    When the batch underneath has moved on from what this one was last brought up to date with,
    its new head is merged in. When it was rebuilt, or when this one should now sit on another
    batch or on main, this one is rebuilt: its branch is reset, and what it held is forgotten,
    so that every queued commit is merged in again. A batch underneath that has landed on main
    is already in this one, and needs nothing. Nothing is done when GitHub does not say whether
    one commit is in another.

    A batch with no note, as while it has no pull request, whose branch already holds the head
    of `base` is taken to have been started there.
    """
    have = state.get("base")
    if base is None and have is None:
        return
    if base and have is None and contains(gh, batch["sha"], base["sha"]):
        state["base"] = {"number": base["number"], "sha": base["sha"], "start": base["sha"]}
        return
    if base and have and base["number"] == have.get("number"):
        if base["sha"] == have.get("sha"):
            return
        ahead = contains(gh, base["sha"], have.get("sha"))
        if ahead is None:
            return
        if ahead:
            message = UPDATED.format(number=base["number"], sha=base["sha"])
            status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": base["sha"], "commit_message": message})
            if status in (0, 201, 204):
                if status == 201:
                    batch["sha"] = data["sha"]
                have["sha"] = base["sha"]
                log.append(f"brought `{batch['ref']}` up to date with #{base['number']} at `{base['sha'][:10]}`")
                return
            log.append(f"GitHub could not merge the new head of #{base['number']} into `{batch['ref']}` ({status})")
    elif base is None:
        landed = contains(gh, main_sha, have.get("sha"))
        if landed is None:
            return
        if landed:
            state["base"] = None
            log.append(f"#{have.get('number')}, which `{batch['ref']}` was built on, has landed on main")
            return
    head = base["sha"] if base else main_sha
    status, data = gh.write("PATCH", f"git/refs/heads/{batch['ref']}", {"sha": head, "force": True})
    if status not in (0, 200):
        raise Refused(f"GitHub would not reset `{batch['ref']}` ({status}: {(data or {}).get('message', 'no reason given')}).")
    batch["sha"] = head
    state["merged"], state["refused"] = {}, {}
    state["base"] = {"number": base["number"], "sha": head, "start": head} if base else None
    log.append(f"rebuilt `{batch['ref']}` " + (f"on top of #{base['number']} at `{head[:10]}`" if base else "on main"))


def on_top(state, crowded=()):
    """What a batch's description says about the batch it is built on. `crowded` lists the
    outermost batches assembled by hand into main, when there are too many to choose one."""
    base = state.get("base")
    if not base:
        if crowded:
            return [f"Built on `main`, because more than one batch assembled by hand into `main` is `{LATEST}`: "
                    + ", ".join(f"#{number}" for number in crowded) + "."]
        return []
    number = base["number"]
    return [f"Built on top of #{number} at `{base['sha'][:10]}`. Merge it after #{number}: merging it first "
            f"lands the pull requests of #{number} too."]


# ---------------------------------------------------------------------------------------------
# One run.


def finish(gh, pulls, held, leftover, main, main_sha, done, closed_labels, log):
    """Tidy up after batches that were merged or closed. `done` is the batches assembled by hand
    among them, as `finished` gives them. `held` is what the open batches assembled by hand
    contain, and a pull request one of them contains keeps its labels. That includes what a batch
    closed without being merged contained, when a batch stacked on it still holds it: it is a
    member of that batch now. `closed_labels` is what each closed pull request still labelled
    `building` or `batch-building` carries, by number.

    When a batch assembled by hand was merged, GitHub marks merged each pull request in it whose
    head commit landed and whose base is main. Of those still open, one whose head has moved on
    since the batch took it is told what landed and is labelled `awaiting-author`, and one whose
    head landed but whose base is another branch is closed, with a comment saying so. When the
    batch was closed without merging, what it contained is told it can push again. A batch that a
    note written before batches were stacked lists as a member is passed over: its labels are its
    own. The batch itself loses `latest batch` and, last, `building`.

    The branch of a batch this script assembled is removed once its pull request is merged or
    closed. When it was merged, GitHub marks what it contained as merged too, except a pull
    request pushed to after it was queued. That one loses `batch queue` here if the commit that
    landed is the one queued, since nothing is left of it to build.

    Returns whether anything was queued again, and the numbers whose labels were taken off.
    """
    requeued, cleared = False, set()
    gone_batches = {batch["number"] for batch in done}
    for batch in done:
        # Its `building` stays on until it is tidied up after, by this run or a later one.
        cleared.add(batch["number"])
        stopped = False
        for key in sorted(batch["members"], key=int):
            if gh.short():
                # The batch keeps `building`, so the next run comes back to it. Everything here
                # can be done again: labels already off are not taken off twice, and comments
                # are told once.
                log.append(f"only {gh.remaining} requests left this hour: stopped tidying up after batch "
                           f"#{batch['number']}, and the next run carries on")
                stopped = True
                break
            pr = pulls.get(int(key))
            if (pr and pr["batch"]) or int(key) in gone_batches:
                continue
            if pr is None:
                # Closed, or marked merged by GitHub along with the batch.
                gone = closed_labels.get(int(key), set()) & set(IN_BATCH)
                if gone:
                    unlabel(gh, int(key), closed_labels[int(key)], gone)
                    cleared.add(int(key))
                    log.append(f"#{key} landed with batch #{batch['number']}: "
                               + " and ".join(f"`{name}`" for name in sorted(gone)) + " removed")
            elif key in held:
                continue
            elif batch["fate"] == "merged":
                if pr["labels"] & set(IN_BATCH):
                    relabel(gh, pr, remove=IN_BATCH)
                    log.append(f"#{key} landed with batch #{batch['number']}: `{MEMBER}` and `{FROZEN}` removed")
                landed(gh, batch, key, pr, main, main_sha, log)
            elif pr["labels"] & set(IN_BATCH):
                # Only what is still queued goes back: `-batch` may have been said meanwhile.
                back = key in batch["queued"] and look(gh, pr, {})[0] is not None
                relabel(gh, pr, add=QUEUED if back else None, remove=unfrozen(back))
                requeued |= back
                tell(gh, pr["number"], None, UNFROZEN.format(number=batch["number"]),
                     f"Batch #{batch['number']} was closed without being merged. {thawed(back)}")
                log.append(f"batch #{batch['number']} was closed without merging: #{key} is "
                           + (f"`{QUEUED}` again" if back else f"no longer `{MEMBER}`"))
        if stopped:
            break
        if batch["fate"] == "closed" and batch["comment"] is not None:
            # Its members were told they can push again, and lost its labels. If it is reopened,
            # they are labelled and told they are frozen again; what the description leaves out
            # is brought up to date in this batch's comments, which notifies nobody.
            batch["note"] = dict(batch["note"], members=batch["members"], labelled=[], told={}, pushed={}, left={})
            batch["note"].pop("telling", None)
            save(gh, batch)
        # Taking `building` off the batch itself, last, marks it as dealt with.
        relabel(gh, batch["number"], remove=[name for name in (LATEST,) if name in batch["labels"]] + [BUILDING])
        log.append(f"tidied up after batch #{batch['number']}, which was assembled by hand")
    for item in leftover:
        info = item["pull"]
        if info.get("merged_at"):
            merged = recall(gh, {"sha": item["sha"], "body": info.get("body") or ""}, main_sha)["merged"]
            for key, commit in sorted(merged.items(), key=lambda entry: int(entry[0])):
                pr = pulls.get(int(key))
                if pr and QUEUED in pr["labels"] and look(gh, pr, {})[0] == commit:
                    relabel(gh, pr, remove=(QUEUED, FROZEN))
                    log.append(f"#{key} landed with batch #{info['number']} at the commit that was queued: "
                               f"`{QUEUED}` and `{FROZEN}` removed")
        gh.write("DELETE", f"git/refs/heads/{item['ref']}")
        log.append(f"removed the branch `{item['ref']}`")
    return requeued, cleared


def landed(gh, batch, key, pr, main, main_sha, log):
    """Deal with a pull request that is still open after the batch assembled by hand that
    contained it was merged. Nothing is said until the commit the batch took is seen on main:
    the batch may have been merged some other way, or into another branch."""
    number, commit = batch["number"], batch["members"][key]
    if pr["sha"] == commit and pr["base"] == main:
        return  # GitHub marks it merged, if it has not yet.
    if not contains(gh, main_sha, commit):
        log.append(f"#{key}: commit `{commit[:10]}`, which batch #{number} took, is not on `{main}`: left alone")
        return
    if pr["sha"] != commit:
        again = look(gh, pr, {})[0] == pr["sha"]
        # The labels first, so that a run cut short between the two leaves them rather than the
        # comment without them: the next run finds the comment and does not post it again.
        relabel(gh, pr, add=(WAITING, QUEUED, FROZEN) if again else WAITING)
        tell(gh, pr["number"], None, LANDED_BEFORE_PUSH.format(number=number, sha=commit),
             f"Batch #{number} has landed on `{main}` with commit `{commit[:10]}` of this pull request. What was "
             f"pushed here after it, up to `{pr['sha'][:10]}`, has not landed, so this pull request stays open. "
             + (f"That commit was queued, so it is back in the batch queue." if again else
                f"Merge `{main}` into this branch and comment `ready`, or close this pull request if nothing is left "
                "to change."))
        log.append(f"#{key} was pushed to after the batch #{number} took it: told what landed, now `{WAITING}`"
                   + (f" and `{QUEUED}` again" if again else ""))
    else:
        tell(gh, pr["number"], None, LANDED_ELSEWHERE.format(number=number, sha=commit),
             f"Batch #{number} has landed on `{main}`, and with it the head of this pull request, `{commit[:10]}`. "
             f"GitHub does not mark this pull request merged because it targets `{pr['base']}` rather than "
             f"`{main}`, so this workflow closes it. Nothing is lost: its commits are on `{main}`.")
        gh.write("PATCH", f"pulls/{pr['number']}", {"state": "closed"})
        log.append(f"#{key} landed with batch #{number} but targets `{pr['base']}`: closed")


def unlabel_closed(gh, closed, cleared, log):
    """Take `batch queue`, `building`, `batch-building` and `frozen` off pull requests that were
    closed, merged or not. `closed` is the closed issues and pull requests that carry `building`,
    `batch-building` or `frozen`, with their labels.

    `finish` has already taken the labels of a batch off the batches assembled by hand it tidied
    up after, and off what they contained. Those keep only `batch queue` to lose here.
    """
    seen = set()
    for item in gh.pages(f"issues?state=closed&labels={quoted(QUEUED)}") + list(closed):
        number = item["number"]
        if "pull_request" not in item or number in seen:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped taking labels off closed pull "
                       "requests, and the next run carries on")
            return
        seen.add(number)
        gone = {label["name"] for label in item.get("labels") or ()} & {QUEUED, CHANGED, *IN_BATCH}
        if number in cleared:
            gone -= set(IN_BATCH)
        if gone:
            unlabel(gh, number, {label['name'] for label in item.get('labels') or ()}, gone)
            log.append(f"#{number} is closed: " + " and ".join(f"`{name}`" for name in sorted(gone)) + " removed")


def reopened(gh, number):
    """Put `batch queue` back on a reopened pull request that lost it when it was closed.

    Only if this workflow took `batch queue` or the labels of a batch off after the pull request
    was last closed, nobody else took any of them off then, the pull request was queued, and no maintainer has taken it out of the queue with `-batch` since
    it was last queued. A label a person took off stays off. Whether the pull request then joins a
    batch again is decided by the next sync, as for any other queued pull request.
    """
    info = gh.get(f"pulls/{number}")
    if info["state"] != "open":
        return [f"#{number} is not open: nothing to put back"]
    if holds_batch(gh, info):
        return [f"#{number} holds a batch: nothing to put back"]
    if {label["name"] for label in info["labels"]} & {QUEUED, *IN_BATCH}:
        return [f"#{number} already carries `{QUEUED}` or the labels of a batch"]
    events = gh.pages(f"issues/{number}/events")
    closed = [event["created_at"] for event in events if event.get("event") == "closed"]
    removed = [event for event in events if event.get("event") == "unlabeled"
               and (event.get("label") or {}).get("name") in (QUEUED, *IN_BATCH)
               and closed and event["created_at"] >= closed[-1]]
    if not removed:
        return [f"#{number} had no label taken off when it was closed: nothing to put back"]
    # A person who took one of them off after it was closed meant it, whatever the workflow
    # took off besides.
    for event in reversed(removed):
        who = (event.get("actor") or {}).get("login") or "someone"
        if who != BOT:
            return [f"#{number}: `{event['label']['name']}` was taken off by {who}, so it stays off"]
    record = None
    for comment in gh.pages(f"issues/{number}/comments"):
        body = comment.get("body") or ""
        if by_workflow(comment):
            if APPROVED.match(body):
                record = "queued"
            elif body.startswith(WITHDRAWN):
                record = "withdrawn"
    if record == "withdrawn":
        return [f"#{number} was taken out of the queue with `-batch`: `{QUEUED}` stays off"]
    # The labels of a batch say nothing about the queue: a pull request a batch took without its
    # being queued gets them back from that batch, if it is still being built.
    if record is None and not any(event["label"]["name"] == QUEUED for event in removed):
        return [f"#{number} was never queued: nothing to put back"]
    relabel(gh, number, add=(QUEUED, FROZEN))
    return [f"#{number} was reopened: `{QUEUED}` and `{FROZEN}` put back"]


def reconcile(gh, pulls, held, approved, log):
    """Keep `frozen` and `changed after frozen` in step with `batch queue` and the batches being
    built, on open pull requests other than batches.

    A pull request in a batch being built is frozen at the commit its own batch took (`held`, as
    {number: commit}, see `holding`); `keep_in_step` labels it, and this only adds `changed after
    frozen` while it is still labelled `frozen`. A queued pull request that a maintainer's `batch`
    stands for is frozen at the commit that was queued (`approved`, the same), since the queue
    takes only that commit. One labelled `batch queue` by hand, or whose `batch` was not looked at in this run, is left
    as it is. A frozen pull request whose head has moved on from the commit it is frozen at is
    labelled `changed after frozen`, and loses that label again once its head is what is frozen:
    on a queued one, after another `batch`, which queues the new head; on one in a batch, once its
    own batch merges in the new head, or when it is pushed back to the commit its batch took (a
    `batch` comment changes nothing there). One that is neither queued nor in a batch being built
    loses `frozen`, `batch-building` and `changed after frozen`: whatever put them there is over.
    This writes nothing when every label is where it should be.
    """
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if is_batch(pr) or BUILDING in pr["labels"]:
            continue
        number, have = pr["number"], pr["labels"]
        inside = str(number) in held
        at = held.get(str(number)) or (approved.get(number) if QUEUED in have else None)
        if at is None and QUEUED in have:
            continue  # queued, but whether a `batch` stands for it was not looked at
        if at is None:
            add, gone = set(), have & {MEMBER, FROZEN, CHANGED}
        else:
            # `keep_in_step` labels what a batch contains, once: a label taken off by hand stays off.
            add = set() if inside else {FROZEN}
            if pr["sha"] != at and (FROZEN in have or not inside):
                add.add(CHANGED)
            # One no longer labelled `frozen`, taken off by hand, is not changed after it either.
            thawed = inside and FROZEN not in have
            add, gone = add - have, have & ({CHANGED} if pr["sha"] == at or thawed else set())
        if not add and not gone:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped bringing `{FROZEN}` up to date, "
                       "and the next run carries on")
            return
        relabel(gh, pr, add=sorted(add), remove=sorted(gone))
        if at is None:
            log.append(f"#{number} is neither queued nor in a batch being built: "
                       + " and ".join(f"`{name}`" for name in sorted(gone)) + " removed")
        elif CHANGED in add:
            log.append(f"#{number} was pushed to after `{at[:10]}` was taken: now `{CHANGED}`")
        elif CHANGED in gone:
            log.append(f"#{number} is at `{at[:10]}`, the commit that was taken: `{CHANGED}` removed")
        else:
            log.append(f"#{number} is queued: now `{FROZEN}`")


def approvals(gh, pulls, main, approved, log, every=False):
    """Fill in `approved` for the queued pull requests that are not labelled `frozen`, or are
    labelled `changed after frozen`, with the commit a maintainer's `batch` stands for on each, for
    `reconcile` to freeze them, to label them `changed after frozen` or to take that off again.
    With `every`, for every queued pull request: a sync asks for that, so that a queued pull
    request pushed to is labelled even when the `pushed` job for the push failed, and so does
    `pushed` for the one pushed to. With `ASSEMBLE` on, the batch being assembled looks at every
    queued pull request into main instead. Each costs a request or so, about five a sync for the
    queue as it is."""
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if QUEUED not in pr["labels"] or is_batch(pr) or pr["base"] != main:
            continue
        if not every and FROZEN in pr["labels"] and CHANGED not in pr["labels"]:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped looking at queued pull requests, "
                       "and the next run carries on")
            return
        sha = look(gh, pr, {})[0]
        if sha is not None:
            approved[pr["number"]] = sha


def pushed(gh, number):
    """What a push to a `frozen` pull request calls for, without a whole sync: the workflow runs this
    for each such push, and a sync costs a few hundred requests. This costs about ten.

    It reads the open pull requests and the records of the batches assembled by hand that are being
    built. The pull request's own batch is the lowest of them, in the order `stack` puts them in,
    whose record holds it: a record written before batches were stacked may hold it too, and
    otherwise one record does. If that batch holds it at another commit than its head, and its
    branch does not have the new head as well, with that commit in it (a request or two, see
    `takes`), it is told so and labelled `awaiting-author`, as `tell_members` does (see
    `tell_pushed`). If the branch has the new head, and the new head has that commit in it,
    nothing is said: the next sync records it at that commit, and edits the comments
    that named the old one, taking off an `awaiting-author` they put on (see `retell`). The note is
    not written here, so neither are they. If it was pushed
    back to that commit instead, `awaiting-author` comes off, if the workflow put it on when it told
    it so, as `unwait` does. Its labels are then brought in step, as `reconcile` does for every open
    pull request: one whose head has moved on from the commit its batch or the queue took is
    labelled `changed after frozen`. The batches' notes are left alone, so that this can run
    alongside a sync: the next sync finds the comment and notes it.
    Returns lines saying what was done."""
    log = []
    main = gh.get("")["default_branch"]
    pulls = open_pulls(gh)
    pr = pulls.get(number)
    if pr is None:
        return [f"#{number} is not open: nothing to do"]
    if pr["batch"]:
        return [f"#{number} holds a batch: the sync looks after it"]
    hand = [{"number": other["number"], "sha": other["sha"], "note": read_record(gh, other["number"])[1]}
            for other in sorted(pulls.values(), key=lambda other: other["number"])
            if by_hand(other) and BUILDING in other["labels"]]
    key = str(number)
    hand = stack(gh, hand, pulls, log)
    held_at = holding(hand)
    for batch in hand:
        commit = members(batch["note"]).get(key)
        if commit is None:
            continue
        if commit != pr["sha"] and kept(batch["note"], "pushed").get(key) != commit:
            inside = takes(gh, batch, pr["sha"], commit)
            if inside:
                # Frozen at the new head, as the next sync records it.
                held_at[key] = pr["sha"]
                log.append(f"#{key} was pushed to with `{pr['sha'][:10]}`, which the batch #{batch['number']} has "
                           "already: nothing to say")
            elif inside is None:
                log.append(f"GitHub did not say whether the batch #{batch['number']} has the new head of #{key}, "
                           f"with `{commit[:10]}` in it: the next sync asks again")
            else:
                tell_pushed(gh, batch["number"], commit, pr, main, log)
        elif commit == pr["sha"] and WAITING in pr["labels"] and (
                key in (batch["note"].get("waiting") or ()) or key not in kept(batch["note"], "pushed")
                and handed_back(gh, batch["number"], key, [commit])):
            # Pushed back to the commit the batch took, as `unwait` does in a sync.
            if relabel(gh, pr, remove=WAITING):
                log.append(f"#{key} is in the batch #{batch['number']} at its head again: `{WAITING}` removed")
        break
    approved = {}
    approvals(gh, {number: pr}, main, approved, log, every=True)
    reconcile(gh, {number: pr}, held_at, approved, log)
    return log or [f"#{number}: nothing to do"]


def sync(gh, now=None):
    """Bring batches and labels up to date. Returns lines saying what was done."""
    log, approved, pulls, _, held_at = assemble(gh, now)
    # Last, so that the batch is assembled first when requests run short, and only after a run
    # that went through: `held_at` is complete only then.
    before = len(log)
    reconcile(gh, pulls, held_at, approved, log)
    if len(log) > before and log[0] == "nothing to do":
        log.pop(0)
    return log


def assemble(gh, now):
    """The body of `sync`. Returns (log, approved, pulls, held, held_at) for `reconcile`: the
    lines saying what was done, the commit that a maintainer's `batch` is known to stand for on
    each queued pull request, by number, every open pull request, the batches being built that
    contain each pull request, and the commit at which its own batch, the lowest of them, holds it.

    With `ASSEMBLE` off, the batches assembled by hand are still kept in step and tidied up after,
    but no batch of the queue is started or added to. `approved` then holds only the queued pull
    requests not yet labelled `frozen`, the only ones `reconcile` needs it for."""
    log, approved = [], {}
    main = gh.get("")["default_branch"]
    main_sha = gh.get(f"git/ref/heads/{main}")["object"]["sha"]
    pulls = open_pulls(gh)
    found, leftover = batches(gh, pulls)
    hand = built_by_hand(gh, pulls, log)
    # A batch labelled `building` just now.
    new_batch = any(batch["commits"] is not None for batch in hand)
    closed_building = gh.pages(f"issues?state=closed&labels={quoted(BUILDING)}")
    closed = closed_building + [item for label in (MEMBER, FROZEN)
                                for item in gh.pages(f"issues?state=closed&labels={quoted(label)}")]
    closed_labels = {item["number"]: {label["name"] for label in item.get("labels") or ()} for item in closed}
    done = finished(gh, closed_building, hand, pulls)
    # The lowest batch first, so that what a batch contains of its own is found after what the
    # batches under it contain. A batch stacked on one closed just now takes over what that one
    # contained and its branch still holds. Labels change only once every batch has been looked
    # through, so that a pull request moving between batches of a stack keeps them throughout.
    hand = stack(gh, hand, pulls, log)
    before = set().union(*(queued_before(batch["note"]) for batch in hand), *(batch["queued"] for batch in done))
    by = {batch["number"]: batch for batch in hand}
    for batch in hand:
        look_through(gh, batch, by, pulls, before, {gone['number'] for gone in done}, log)
    held = holders(hand)
    requeued = False
    for batch in hand:
        requeued |= keep_in_step(gh, batch, pulls, held, main, log)
    # After `keep_in_step`, which records a member at a new head its batch has already.
    held_at = holding(hand)
    unsure = unsettled(gh, done, hand, pulls)
    for number in sorted(unsure):
        log.append(f"batch #{number} was closed without merging, and a batch stacked on it could not be looked "
                   "through: its pull requests keep their labels, and the next run settles them")
    more, cleared = finish(gh, pulls, held, leftover, main, main_sha,
                           [batch for batch in done if batch["number"] not in unsure], closed_labels, log)
    # `unlabel_closed` leaves these alone too.
    cleared |= unsure
    requeued |= more
    unlabel_closed(gh, closed, cleared, log)
    stranded(gh, done, hand, pulls, log)
    # The sweep compares pull requests with the batch labelled `latest batch`, so it is started
    # only once that label has moved. A run cut short before this leaves the new batch to the
    # next half-hourly sweep.
    if mark_latest(gh, hand, pulls, log) or new_batch:
        start_conflict_labels(gh, main, log)

    if not ASSEMBLE:
        # A batch of this script's own whose pull request was merged or closed was tidied up
        # after above. One that has none is left alone (see `ASSEMBLE`).
        approvals(gh, pulls, main, approved, log, every=True)
        return log or ["nothing to do"], approved, pulls, held, held_at
    if requeued:
        # Leave time to take the pull request that broke the build out of the queue first.
        log.append("not starting a new batch in this run: the next `batch` or `-batch` comment does")
        return log, approved, pulls, held, held_at

    # The batch being assembled goes on top of the outermost batch assembled by hand, the one
    # labelled `latest batch`, when just one into main is. With more than one it is not clear
    # which comes first, so it goes on main.
    tops = outermost(hand)
    under = [item for item in hand if item["number"] in tops and item["base"] == main]
    base = {"number": under[0]["number"], "sha": under[0]["sha"]} if len(under) == 1 else None
    crowded = sorted(item["number"] for item in under) if len(under) > 1 else []

    # The batch being assembled takes each commit a maintainer queued.
    assembling = sorted(found, key=lambda item: item["ref"])
    batch = assembling[-1] if assembling else None
    state = recall(gh, batch, main_sha, base and base["sha"]) if batch else {"merged": {}, "refused": {}, "seen": {}, "base": None}
    members, refused, unapproved, stopped, before = [], [], [], False, len(log)
    if batch:
        restack(gh, batch, state, base, main_sha, log)
    queued = sorted((pr for pr in pulls.values() if QUEUED in pr["labels"] and not is_batch(pr) and pr["base"] == main),
                    key=lambda pr: (PRIORITY not in pr["labels"], pr["number"]))
    for pr in queued:
        number, key = pr["number"], str(pr["number"])
        sha, comments = look(gh, pr, state["seen"])
        if sha is not None:
            approved[number] = sha
        if sha is None:
            unapproved.append(number)
            continue
        if sha != pr["sha"] and comments is not None and tell(
                gh, number, comments, MOVED.format(sha=sha),
                f"This pull request was queued at `{sha[:10]}` and its head is now `{pr['sha'][:10]}`. A batch takes "
                "only the commit that was queued. Comment `batch` again to queue the new one."):
            log.append(f"told #{number} that its head has moved since it was queued")
        if state["merged"].get(key) == sha:
            members.append((number, sha))
            continue
        if state["refused"].get(key) == sha:
            refused.append(number)
            continue
        if stopped:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped merging, and the next run carries on")
            stopped = True
            continue
        if batch is None:
            batch = start(gh, main, base["sha"] if base else main_sha, now, log, on=base and base["number"])
            if base:
                state["base"] = {"number": base["number"], "sha": base["sha"], "start": base["sha"]}
        message = f"Add #{number} to the batch\n\nMerged at {sha}."
        status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": sha, "commit_message": message})
        if status == 201:
            batch["sha"] = data["sha"]
        if status in (0, 201, 204):
            state["merged"][key] = sha
            members.append((number, sha))
            log.append(f"{'would add' if gh.dry_run else 'added'} #{number} at `{sha[:10]}` to `{batch['ref']}`")
            continue
        on = (state["base"] or {}).get("number")
        if status != 409:
            reason = f"GitHub refused the merge ({status}: `{(data or {}).get('message', 'no reason given')}`)."
        elif on:
            reason = (f"GitHub could not merge it with what is already there: #{on}, which this batch is built on, "
                      f"and the pull requests added before it. If it conflicts with #{on} itself, it is labelled "
                      f"`batch-conflict`, and the comment that comes with that label says what to do.")
        else:
            reason = "GitHub could not merge it with what is already there."
        link = f"#{batch['number']}" if batch["number"] else f"`{batch['ref']}`"
        marker = REFUSAL_ON.format(branch=batch["ref"], sha=sha, base=on) if on else REFUSAL.format(branch=batch["ref"], sha=sha)
        tell(gh, number, comments, marker,
             f"The commit `{sha[:10]}` of this pull request was not added to the batch {link}: {reason}\n\n"
             f"It keeps its `{QUEUED}` label. It is tried again when a maintainer queues a new commit, "
             "or when the next batch starts.")
        state["refused"][key] = sha
        refused.append(number)
        log.append(f"left #{number} out of `{batch['ref']}`: {reason}")

    if batch is None:
        if unapproved:
            log.append(f"labelled `{QUEUED}` but no commit of them is queued: "
                       + ", ".join(f"#{number}" for number in unapproved))
        return log or ["nothing to do"], approved, pulls, held, held_at

    # What the branch holds that the list above does not account for.
    listed, also = {number for number, _ in members}, []
    for key in sorted(state["merged"], key=int):
        number, pr = int(key), pulls.get(int(key))
        if number in listed:
            continue
        if pr is None:
            also.append((number, "closed since it was merged in"))
        elif QUEUED in pr["labels"]:
            also.append((number, "at an earlier commit than the one now queued"))
        elif MEMBER in pr["labels"] and held.get(key):
            # Being built in another batch: nothing to tell it.
            also.append((number, "being built in " + ", ".join(f"#{other}" for other in sorted(held[key]))))
        else:
            also.append((number, "no longer queued"))
            _, comments = look(gh, pr, state["seen"])
            if batch["number"] and comments is not None and tell(
                    gh, number, comments, STAYS.format(branch=batch["ref"]),
                    f"`{QUEUED}` was removed from this pull request, but its commits were already merged into "
                    f"the batch #{batch['number']} and are still there. That batch was not changed.\n\n"
                    f"To build without them, close #{batch['number']}. The next `batch` comment then assembles a "
                    "new batch from what is still queued."):
                log.append(f"told #{number} that its commits stay in batch #{batch['number']}")
    if members or batch["number"]:
        try:
            publish(gh, batch, main, describe(batch, state, members, also, refused, unapproved,
                                              on_top(state, crowded)))
        except Refused as error:
            # Such as when GitHub Actions may not open pull requests here. What was merged is in
            # the branch, so the next run picks it up, and `reconcile` still runs after this. The
            # run fails all the same, so that the refusal is seen.
            gh.failed = True
            log.append(str(error))
        else:
            if len(log) > before:
                log.append(f"batch pull request #{batch['number']} lists {len(members)} pull request(s)"
                           if batch["number"] else f"`{batch['ref']}` has no pull request yet")
    return log or ["nothing to do"], approved, pulls, held, held_at


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    parser.add_argument("--reopened", type=int, metavar="NUMBER",
                        help="only put `batch queue` back on this reopened pull request if it lost it when closed")
    parser.add_argument("--pushed", type=int, metavar="NUMBER",
                        help="only deal with a push to this frozen pull request, without a whole sync")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        if args.reopened:
            log = reopened(gh, args.reopened)
        elif args.pushed:
            log = pushed(gh, args.pushed)
        else:
            log = sync(gh)
    except Refused as error:
        log, failure = [str(error)], 1
    log += gh.refused
    failure = failure or (1 if gh.refused else None)
    left = f"; {gh.remaining} left this hour" if gh.remaining is not None else ""
    log.append(f"{gh.calls} requests to GitHub{left}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    # A refusal that did not stop the run (see `assemble`) fails it too.
    sys.exit(failure or (1 if gh.failed else None))


if __name__ == "__main__":
    main()
