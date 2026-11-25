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
other pull request instead. What it contains is every open pull request whose head commit is in
its branch, queued or not, into main or into another branch. They are labelled `batch-building`
and `frozen`, in place of `batch queue` for those that had it, and each is told once in a
comment not to push until the batch has landed. This script records them in a comment of its
own on the batch's pull request, and looks through the branch again when its head moves. A pull
request that has left the branch by then loses both labels and is told so, and so does
everything in it once the batch is merged or closed. Those that had `batch queue` before get it
back, unless the batch was merged.

A pull request that is pushed to after the batch took its commit is still in the batch, at that
commit. It is told that the batch lands only that commit, and is labelled `awaiting-author`. When
the batch is merged, GitHub marks merged each pull request whose head commit is in it and whose
base is main. One whose head has moved on stays open: it is told what landed and what did not,
and keeps `awaiting-author`. One whose head landed but whose base is another branch is closed,
with a comment saying where its commit went, since GitHub does not mark it merged.

The description of a batch assembled by hand lists pull requests under headings ending with a
colon. Those listed under a heading that says "left out" or "not included" are told so in a
comment quoting the heading and their entry, and are labelled `awaiting-author`. `batch queue`
stays on them. The quote puts the pull requests it names in code spans, so that it does not
mention each of them. A pull request told before, by any batch, that it is left out under the same
heading is not told again: that comment is brought up to date instead, which notifies nobody.
One whose entry is removed from the description is told that too. A batch whose record is older
than these notices tells nobody what its description leaves out when this script first reads it,
only what is added or changed after that. After every run, `frozen` is
put on each open pull request a maintainer's `batch` stands for, and `frozen` and
`batch-building` are taken off any that is neither queued nor in a batch being built. Which pull requests a batch
contains is read from its branch, never from its description. The names of the labels are in
`batch-labels.py`, and `verification/BATCHES.md` says what someone assembling a batch by hand
should do for all this to work.

The batch being assembled is built on top of the batch assembled by hand that is being built,
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
`batch-building` and `frozen`: it is neither waiting for a build nor in one any more. The pull
request of a batch assembled by hand is the exception, because it keeps `building` until it has
been tidied up after. When a pull
request is reopened, `batch queue` comes back if this workflow was the last to take a label off,
and the pull request was not taken out of the queue with `-batch` meanwhile. A label a person
took off stays off.

The workflow's token may make 1,000 requests an hour, shared with every other workflow here. A
note in each batch pull request's text therefore remembers what was merged and which pull
requests were already looked at. The note is a cache: it is used only while the batch's head
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

QUEUED, BUILDING, MEMBER, FROZEN = _labels.QUEUED, _labels.BUILDING, _labels.MEMBER, _labels.FROZEN
# A maintainer's label: pull requests that carry it go into a batch before the others.
PRIORITY, WAITING = _labels.PRIORITY, _labels.WAITING
# What a pull request in a batch assembled by hand carries (see `batch-labels.py`).
IN_BATCH = _labels.IN_BATCH
PREFIX = _labels.PREFIX
# The name `start` gives a batch branch. Any other `batch/...` branch is not this script's.
OWN_BATCH = re.compile(r"batch/[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{6}(?:-[0-9]+)?")
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
#   follows one batch assembled by hand into main, and goes back to main when there are more.
# - Requests: a sync run that assembled cost about 300 REST requests. Run 45503694341 ended with
#   "304 requests to GitHub; 4721 left this hour".
#
# To revive it: allow GitHub Actions to create pull requests, decide how a batch of the queue
# relates to stacked batches assembled by hand, and set this back to True.
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
# The comment on a batch assembled by hand that records what it contains.
BY_HAND = re.compile(r"<!-- batch-queue-by-hand (\{.*\}) -->")
# Comments this script leaves on what a batch assembled by hand contains or leaves out.
FROZEN_NOTE = "<!-- batch-queue-frozen {number} {sha} -->"
PUSHED = "<!-- batch-queue-pushed-while-frozen {number} {sha} -->"
DROPPED = "<!-- batch-queue-dropped {number} {sha} -->"
UNFROZEN = "<!-- batch-queue-unfrozen {number} -->"
LANDED_BEFORE_PUSH = "<!-- batch-queue-landed-before-push {number} {sha} -->"
LANDED_ELSEWHERE = "<!-- batch-queue-landed-elsewhere {number} {sha} -->"
LEFT_OUT = re.compile(r"<!-- batch-queue-left-out (\{.*?\}) -->")
NO_LONGER_LEFT_OUT = "<!-- batch-queue-no-longer-left-out {number} -->"
# A heading in a batch's description under which the pull requests listed are left out.
LEFT_OUT_HEADING = re.compile(r"\b(?:left out|not included)\b", re.IGNORECASE)
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
            "updated": info["updated_at"], "body": info.get("body") or ""}
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
    every change.
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
        done = gh.write("POST", f"issues/{number}/labels", {"labels": add})[0] in (0, 200)
    for name in remove:
        # A label that is not there any more answers 404, which is what was wanted.
        done = gh.write("DELETE", f"issues/{number}/labels/{quoted(name)}")[0] in (0, 200, 404) and done
    if isinstance(pr_or_number, dict):
        pr_or_number["labels"] = (pr_or_number["labels"] | set(add)) - set(remove)
    return done


def unlabel(gh, number, have, gone):
    """Take the labels `gone` off a closed pull request that carries `have`, in one request when
    there are several: setting its labels replaces them all. Another workflow may change them in
    the meantime, inbox-sync taking `inbox` off for one, and a label it took off would come back.
    That is rare, and the other workflow takes it off again on its next run, so saving a request
    for each pull request a batch lands is worth it."""
    gone = sorted(set(gone) & set(have))
    if len(gone) > 1:
        gh.write("PUT", f"issues/{number}/labels", {"labels": sorted(set(have) - set(gone))})
    elif gone:
        gh.write("DELETE", f"issues/{number}/labels/{quoted(gone[0])}")


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


def finished(gh, closed_building, known):
    """Batches assembled by hand that were merged or closed and not yet tidied up after, with a
    `fate`, the pull requests they contained as `members`, {number: commit}, and those of them
    that were labelled `batch queue` before as `queued`.

    They are found by their pull requests, which keep `building` until `finish` is done with
    them. That works whether or not someone has already deleted the branch. `closed_building`
    is every closed issue or pull request that still carries `building`.

    Telling a batch assembled by hand from any other pull request takes a request, so `known`,
    the pull requests some open batch is known to contain, are not asked about. Neither is what
    a batch just found contained, and the newest are looked at first, because a batch is opened
    after what it contains.
    """
    found, known = [], set(known)
    for item in sorted(closed_building, key=lambda item: -item["number"]):
        if "pull_request" not in item or str(item["number"]) in known:
            continue
        info = gh.get(f"pulls/{item['number']}")
        if not holds_batch(gh, info) or own_batch(info["head"]["ref"]):
            continue
        note = read_record(gh, info["number"])[1]
        batch = {"number": info["number"], "fate": "merged" if info.get("merged") else "closed",
                 "members": members(note), "queued": queued_before(note)}
        known |= set(batch["members"])
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
    """This script's comment on a batch assembled by hand, as (comment, note). The comment is
    None, and the note empty, until there is one."""
    for comment in gh.pages(f"issues/{number}/comments"):
        match = BY_HAND.match(comment.get("body") or "") if by_workflow(comment) else None
        if match:
            return comment, load_note(match.group(1))
    return None, {}


# The note of a batch assembled by hand: what `hold` and the functions it calls remember from one
# run to the next. `save` writes it into this script's record comment on the batch's pull request,
# with `dump_note`, and `read_record` reads it back, with `load_note`. In memory, numbers are
# strings, and a key may be missing from a note written before it was:
#
#   head      the branch's head when `members` was found.
#   members   what the batch contains, as {number: the commit of it that is in the branch}.
#   queued    the members that were labelled `batch queue` before the batch took them. They go
#             back to the queue if the batch is closed without being merged. A note without it
#             is from before it was written down, and held only queued pull requests.
#   labelled  the members this batch labelled `batch-building` and `frozen`, once each.
#   told      {number: commit}: the members told that they are frozen, at that commit.
#   pushed    {number: commit}: the members told that they were pushed to after the batch took
#             that commit, and labelled `awaiting-author`.
#   left      {number: digest}: the pull requests told that the description leaves them out, with
#             a digest of the entry they were told about (see `tell_left_out`).
#
# An entry of `told` or `pushed` counts only while its commit is the member's: `hold` drops the
# others. On GitHub, where a comment holds at most 65,536 characters, the note is compact JSON and
# keeps only the entries that count, as lists of numbers. `queued`, `labelled` and `told` are each
# kept as that list or as the list of the members it leaves out (`unqueued`, `unlabelled`,
# `untold`), whichever is shorter: a batch usually labels and tells nearly all of its members. What
# is left is about 50 characters for each member, nearly all of it `members` with its full commit
# ids. `load_note` also reads the notes written before `dump_note`, which kept every key as it is
# in memory.


def dump_note(note):
    """A note as it is kept on GitHub: compact JSON, with only the keys the note has."""
    found = note.get("members") or {}
    kept = {name: note[name] for name in ("head", "members", "left") if name in note}

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
    for name in ("members", "left"):
        if isinstance(kept.get(name), dict):
            note[name] = mapping(name)
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
    did not list them all. A request for each hundred of them."""
    found = set()
    for page in range(1, pages + 1):
        status, data = gh.call("GET", f"compare/{base}...{head}?per_page=100&page={page}")
        if status != 200 or not isinstance(data, dict) or not isinstance(data.get("commits"), list):
            return None
        found |= {commit["sha"] for commit in data["commits"]}
        if len(found) >= data.get("total_commits", 0):
            return found
        if len(data["commits"]) < 100:
            return None
    return None


def inside(batch, pulls, commits):
    """The open pull requests whose head commit is one of a batch's `commits`, as {number: commit}.
    The batch itself and batches this script started are left out. A pull request into another
    branch counts too: it is built along with the batch, even though GitHub will not mark it
    merged when the batch is."""
    return {str(pr["number"]): pr["sha"] for pr in pulls.values()
            if pr["number"] != batch["number"] and not is_batch(pr) and pr["sha"] in commits}


def built_by_hand(gh, pulls, log):
    """The open batches assembled by hand that are being built, as {ref, sha, number, base,
    comment, note, commits}.

    One labelled `building` is being built. One that is not is looked through, at a request or
    so, and labelled `building` once its branch holds the head commit of an open pull request:
    the label is how it is found again after it is closed. One labelled `batch queue` and not
    `building` is waiting in the queue like any other pull request, and is not looked at. Nor is
    one labelled `batch-building` and not `building`: another batch contains it, and it is built
    as part of that one. Reading the note costs a request for each. `commits` is what the branch
    was found to hold, or None when it was not looked through.
    """
    found = []
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if not by_hand(pr) or (pr["labels"] & {QUEUED, MEMBER} and BUILDING not in pr["labels"]):
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
        comment, note = read_record(gh, pr["number"])
        if commits is not None:
            # Labelled `building` just now: for the first time, or again after it was closed
            # without being merged and reopened. What the note says was done then has been
            # undone since, so it starts again.
            note = {}
        found.append({"ref": pr["ref"], "sha": pr["sha"], "number": pr["number"], "base": pr["base"],
                      "comment": comment, "note": note, "commits": commits})
    return found


def holders(hand):
    """Which batches assembled by hand contain each pull request, as {number: {batch numbers}}."""
    held = {}
    for batch in hand:
        for key in members(batch["note"]):
            held.setdefault(key, set()).add(batch["number"])
    return held


def contains(gh, head, commit):
    """Whether a branch whose head is `head` has `commit` in it, or None if GitHub did not say."""
    status, data = gh.call("GET", f"compare/{head}...{commit}?per_page=1")
    if status != 200 or not isinstance(data, dict) or "ahead_by" not in data:
        return None
    return data["ahead_by"] == 0


def kept(note, name):
    """A map the note keeps, as {number: value}, or an empty one."""
    found = note.get(name)
    return dict(found) if isinstance(found, dict) else {}


def save(gh, batch):
    """Write the note of a batch assembled by hand to this script's comment on its pull request,
    if it has changed. A note that cannot be written stops the run: everything else relies on it."""
    text, comment = describe_by_hand(batch["note"]), batch["comment"]
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


def hold(gh, batch, pulls, held, main, log):
    """Find what a batch assembled by hand contains, record it, label it and tell it so.

    It contains each open pull request whose head commit is in its branch, queued or not. When
    the branch's head has moved since the note was written, its commits are listed again, a
    request for each hundred of them. What has arrived is added. What was found before stays as
    long as the commit it was found at is still there, even after its author has pushed again,
    unless its new head is in the branch too. Whatever has left loses `batch-building` and
    `frozen` unless another batch contains it, goes back to `batch queue` if it was queued before
    and still is, and is told so. `held` says, for each pull request, which batches contain it.
    Returns whether anything was queued again.

    The note is written first, so that whatever carries `batch-building` because of this batch
    is in it when the batch is finished with. It then remembers what was done as it is done:
    which members were labelled (`labelled`), and who was told that they are frozen (`told`),
    that they were pushed to afterwards (`pushed`, which also labels them `awaiting-author`), or
    what the description says about them being left out (`left`, see `tell_left_out`). Only what
    GitHub took counts as done, so what was refused or cut short is tried again by the next run,
    and nothing is done twice. A member is labelled once: a label taken off by hand stays off,
    except that a pull request queued again swaps `batch queue` for the labels of the batch. The
    note's keys are described above `dump_note`.
    """
    note, number, requeued = batch["note"], batch["number"], False
    found, queued, new = members(note), queued_before(note), set()
    if note.get("head") != batch["sha"]:
        commits = batch.get("commits")
        if commits is None:
            if gh.short():
                # The note keeps the old head, so the next run looks again.
                log.append(f"only {gh.remaining} requests left this hour: did not look through the batch #{number}, "
                           "and the next run does")
                return False
            commits = branch_commits(gh, batch["base"], batch["sha"])
        if commits is None:
            log.append(f"GitHub did not list every commit of the batch #{number}: the next run looks again")
            return False
        now = inside(batch, pulls, commits)
        for key, commit in found.items():
            if commit in commits:
                now.setdefault(key, commit)
        for key in sorted(set(found) - set(now), key=int):
            pr = pulls.get(int(key))
            if pr and pr["labels"] & set(IN_BATCH) and not held.get(key, set()) - {number}:
                # Only what is still queued goes back: `-batch` may have been said meanwhile.
                back = key in queued and look(gh, pr, {})[0] is not None
                relabel(gh, pr, add=(QUEUED, FROZEN) if back else None, remove=unfrozen(back))
                requeued |= back
                if not by_hand(pr):
                    tell(gh, pr["number"], None, DROPPED.format(number=number, sha=found[key]),
                         f"Commit `{found[key][:10]}` of this pull request is no longer in batch #{number}: its "
                         f"branch was changed without it. {thawed(back)}")
                log.append(f"#{key} is no longer in the batch #{number}: "
                           + (f"`{QUEUED}` again" if back else f"no longer `{MEMBER}`"))
        new, found = set(now) - set(found), now
    queued = {key for key in found if key in queued or QUEUED in (pulls.get(int(key)) or {}).get("labels", ())}
    # What was done for a pull request that has been closed since is done again if it is reopened.
    labelled = sorted({key for key in note.get("labelled") or () if key in found and int(key) in pulls}, key=int)
    left = kept(note, "left")
    if batch["comment"] is not None and "left" not in note:
        # A record from before the description was read for what it leaves out. Its pull requests
        # were told about it by people, if at all, so what the description says now counts as told,
        # and only what is added or changed from here on is.
        left = {str(key): entry_digest(entry) for key, entry in left_out(pulls[number]["body"], gh.repo).items()
                if key in pulls and str(key) not in found}
        log.append(f"the record of the batch #{number} is older than the notices of what a batch leaves out: "
                   f"what its description leaves out now, {len(left)} pull request(s), is taken as told")
    batch["note"] = note = {
        "head": batch["sha"], "members": found, "queued": sorted(queued, key=int), "labelled": labelled,
        "told": {key: commit for key, commit in kept(note, "told").items() if found.get(key) == commit},
        "pushed": {key: commit for key, commit in kept(note, "pushed").items() if found.get(key) == commit},
        "left": left}
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
        tell_members(gh, batch, pulls, main, log)
        tell_left_out(gh, batch, pulls, log)
    finally:
        save(gh, batch)
    return requeued


def tell_members(gh, batch, pulls, main, log):
    """Tell each pull request in a batch assembled by hand, once, that it is frozen, and once that
    it was pushed to after the batch took it, if it was. The note remembers it."""
    note, number, since = batch["note"], batch["number"], 0
    told, pushed = note["told"], note["pushed"]
    for key, commit in sorted(note["members"].items(), key=lambda entry: int(entry[0])):
        pr = pulls.get(int(key))
        if pr is None or by_hand(pr) or (told.get(key) == commit and (pr["sha"] == commit or pushed.get(key) == commit)):
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped telling what is in the batch #{number}, "
                       "and the next run carries on")
            return
        if told.get(key) != commit and say(gh, pr["number"], FROZEN_NOTE.format(number=number, sha=commit),
                                            frozen_text(number, commit, pr, main)):
            told[key], since = commit, since + 1
            log.append(f"told #{key} that it is frozen while the batch #{number} is built")
        if pr["sha"] != commit and pushed.get(key) != commit and say(
                gh, pr["number"], PUSHED.format(number=number, sha=pr["sha"]),
                f"This pull request was pushed to after batch #{number} took its commit `{commit[:10]}`. The batch "
                f"builds and lands `{commit[:10]}` only, not `{pr['sha'][:10]}`, so when it lands this pull request "
                f"stays open with what came after `{commit[:10]}`. Once the batch has landed, merge `{main}` into "
                "this branch and comment `ready`, or close this pull request if nothing is left to change."):
            pushed[key], since = commit, since + 1
            relabel(gh, pr, add=WAITING)
            log.append(f"told #{key} that it was pushed to after the batch #{number} took it: now `{WAITING}`")
        if since >= SAVE_EVERY:
            save(gh, batch)
            since = 0


def frozen_text(number, commit, pr, main):
    """What a pull request in a batch assembled by hand is told when the batch takes it."""
    text = (f"Commit `{commit[:10]}` of this pull request is in batch #{number}, which is being built. Please "
            "don't push to this pull request until the batch has landed or been closed: the batch builds and lands "
            f"`{commit[:10]}`, and commits pushed after it are not part of it.")
    if pr["base"] == main:
        return text + " When the batch lands, GitHub marks this pull request merged."
    return (text + f" This pull request targets `{pr['base']}` rather than `{main}`, so GitHub will not mark it "
            "merged when the batch lands. If its head is still this commit then, this workflow closes it instead.")


def left_out(body, repo):
    """The pull requests a batch's description lists as left out, as {number: (heading, entry)}.

    A heading is a line of its own, not part of a list, that ends with a colon. The pull
    requests under it are the list entries that start with a link to one, `#123` or its full
    URL. Those under a heading that says "left out" or "not included" are the ones left out,
    up to the next heading or paragraph. A pull request listed twice keeps its first entry.
    """
    link = re.compile(rf"[-*]\s+(?:https://github\.com/{re.escape(repo)}/pull/|#)(\d+)\b", re.IGNORECASE)
    found, heading = {}, None
    for line in body.splitlines():
        text = line.strip()
        if not text or line[0].isspace():
            continue
        if line.startswith(("- ", "* ")):
            match = link.match(line)
            if heading and match:
                found.setdefault(int(match.group(1)), (heading, text[1:].strip()))
            continue
        heading = text if text.endswith(":") and LEFT_OUT_HEADING.search(text) else None
    return found


def entry_digest(entry):
    """A short digest of a pull request's (heading, entry) in a batch's description, which the
    note's `left` keeps."""
    return hashlib.sha256("\n".join(entry).encode()).hexdigest()[:16]


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


def left_out_digest(heading, entry):
    """What kind of reason a pull request is left out for, as a short digest: its heading, up to
    any parenthesis, in lower case. The entry itself is left out of it. The descriptions of
    batches are written afresh each time, so the same reason seldom comes back in the same
    words, while the headings stay put."""
    kind = re.split(r"[(:]", heading, maxsplit=1)[0]
    return hashlib.sha256(" ".join(kind.lower().split()).encode()).hexdigest()[:16]


def tell_left_out(gh, batch, pulls, log):
    """Tell each open pull request a batch's description lists as left out what it says.

    The comment quotes the heading and the pull request's entry, and the pull request is
    labelled `awaiting-author`. One whose latest such comment, from this batch or another, was
    for the same kind of reason (the same heading, see `left_out_digest`) is not told again:
    that comment is brought up to date with what the description says now, which notifies
    nobody, so a pull request left out of batch after batch hears it once and still finds the
    latest reason there. The quote names pull requests and issues of this repository in code
    spans (see `unlinked`). One whose entry has gone from the description since it was told is
    told that, if this batch's comment told it. What the batch contains is never told it is left
    out. The note's `left` remembers, for each pull request, a digest of the entry it was last
    told about for this batch, and is brought up to date as each is told. `hold` fills it in
    without telling anyone for a batch whose record is older than `left`.
    """
    note, number, since = batch["note"], batch["number"], 0
    found, left = note["members"], note["left"]
    listed = left_out(pulls[number]["body"], gh.repo)
    for key in sorted(set(left) | {str(other) for other in listed}, key=int):
        pr = pulls.get(int(key))
        if pr is None or key in found or is_batch(pr) or by_hand(pr):
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
            return
        comments = gh.pages(f"issues/{key}/comments")
        latest, previous = None, None
        for comment in comments:
            match = LEFT_OUT.match(comment.get("body") or "") if by_workflow(comment) else None
            if match:
                latest = comment
                try:
                    previous = json.loads(match.group(1)).get("digest")
                except ValueError:
                    previous = None
        if entry is None:
            # One that was never told it is left out, as when the note was filled in from an older
            # record, is not told that it no longer is either.
            if told_left_out(latest, number) and tell(
                    gh, pr["number"], comments, NO_LONGER_LEFT_OUT.format(number=number),
                    f"The description of batch #{number} no longer lists this pull request as left out. If you were "
                    "waiting on that, comment `ready`."):
                log.append(f"told #{key} that the batch #{number} no longer lists it as left out")
            left.pop(key, None)
            continue
        heading, text = (unlinked(part, gh.repo) for part in entry)
        marker = f"<!-- batch-queue-left-out {json.dumps({'batch': number, 'digest': digest}, sort_keys=True)} -->"
        body = (f"{marker}\nBatch #{number} leaves this pull request out. Its description says:\n\n> {heading}\n>\n"
                f"> {text}\n\nOnce you have dealt with that, comment `ready` to hand this pull request back to the "
                "maintainers.\n")
        if latest is not None and previous == digest:
            if latest.get("body") == body or gh.write(
                    "PATCH", f"issues/comments/{latest['id']}", {"body": body})[0] in (0, 200):
                left[key] = seen
                log.append(f"brought up to date what #{key} was told about being left out, for the batch #{number}")
        elif say(gh, pr["number"], marker, body[len(marker) + 1:].rstrip("\n")):
            left[key], since = seen, since + 1
            relabel(gh, pr, add=WAITING)
            log.append(f"told #{key} that the batch #{number} leaves it out: now `{WAITING}`")
        if since >= SAVE_EVERY:
            save(gh, batch)
            since = 0


def told_left_out(comment, number):
    """Whether a pull request's latest comment about being left out, or None, is from batch `number`."""
    match = LEFT_OUT.match((comment or {}).get("body") or "")
    try:
        return bool(match) and json.loads(match.group(1)).get("batch") == number
    except ValueError:
        return False


def describe_by_hand(note):
    """The comment that records what a batch assembled by hand contains."""
    listed = ", ".join(f"#{key}" for key in sorted(note["members"], key=int)) or "nothing yet"
    return (f"<!-- batch-queue-by-hand {dump_note(note)} -->\n"
            "While this pull request is open, the batch-queue workflow takes it to be a batch that is being built. "
            "It adds nothing to a batch assembled by hand and leaves its description alone, but it keeps the labels "
            f"in step: each open pull request whose head commit is in this branch is now `{MEMBER}` and `{FROZEN}`, "
            f"in place of `{QUEUED}` if it had that, and is asked not to push until this has landed. Those this "
            f"description lists as left out are told why and labelled `{WAITING}`. When this is merged the pull "
            f"requests in it lose `{MEMBER}` and `{FROZEN}`. If it is closed without being merged they lose them too, "
            f"and the ones that were queued go back to `{QUEUED}`. See `verification/BATCHES.md`.\n\n"
            f"In this batch: {listed}.\n")


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
    batches assembled by hand that are being built, when there are too many to choose one."""
    base = state.get("base")
    if not base:
        if crowded:
            return ["Built on `main`, because more than one batch assembled by hand is being built: "
                    + ", ".join(f"#{number}" for number in crowded) + "."]
        return []
    number = base["number"]
    return [f"Built on top of #{number} at `{base['sha'][:10]}`. Merge it after #{number}: merging it first "
            f"lands the pull requests of #{number} too."]


# ---------------------------------------------------------------------------------------------
# One run.


def finish(gh, pulls, held, leftover, main, main_sha, closed_building, closed_labels, log):
    """Tidy up after batches that were merged or closed. `held` is what the open batches
    assembled by hand contain, and a pull request one of them contains keeps its labels.
    `closed_labels` is what each closed pull request still labelled `building` or
    `batch-building` carries, by number.

    When a batch assembled by hand was merged, GitHub marks merged each pull request in it whose
    head commit landed and whose base is main. Of those still open, one whose head has moved on
    since the batch took it is told what landed and is labelled `awaiting-author`, and one whose
    head landed but whose base is another branch is closed, with a comment saying so. When the
    batch was closed without merging, what it contained is told it can push again.

    The branch of a batch this script assembled is removed once its pull request is merged or
    closed. When it was merged, GitHub marks what it contained as merged too, except a pull
    request pushed to after it was queued. That one loses `batch queue` here if the commit that
    landed is the one queued, since nothing is left of it to build.

    Returns whether anything was queued again, and the numbers whose labels were taken off.
    """
    requeued, cleared = False, set()
    for batch in finished(gh, closed_building, held):
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
                if not by_hand(pr):
                    landed(gh, batch, key, pr, main, main_sha, log)
            elif pr["labels"] & set(IN_BATCH):
                # Only what is still queued goes back: `-batch` may have been said meanwhile.
                back = key in batch["queued"] and look(gh, pr, {})[0] is not None
                relabel(gh, pr, add=QUEUED if back else None, remove=unfrozen(back))
                requeued |= back
                if not by_hand(pr):
                    tell(gh, pr["number"], None, UNFROZEN.format(number=batch["number"]),
                         f"Batch #{batch['number']} was closed without being merged. {thawed(back)}")
                log.append(f"batch #{batch['number']} was closed without merging: #{key} is "
                           + (f"`{QUEUED}` again" if back else f"no longer `{MEMBER}`"))
        if stopped:
            break
        # Taking the label off the batch itself marks it as dealt with.
        relabel(gh, batch["number"], remove=BUILDING)
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
        tell(gh, pr["number"], None, LANDED_BEFORE_PUSH.format(number=number, sha=commit),
             f"Batch #{number} has landed on `{main}` with commit `{commit[:10]}` of this pull request. What was "
             f"pushed here after it, up to `{pr['sha'][:10]}`, has not landed, so this pull request stays open. "
             + (f"That commit was queued, so it is back in the batch queue." if again else
                f"Merge `{main}` into this branch and comment `ready`, or close this pull request if nothing is left "
                "to change."))
        relabel(gh, pr, add=(WAITING, QUEUED, FROZEN) if again else WAITING)
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
        gone = {label["name"] for label in item.get("labels") or ()} & {QUEUED, *IN_BATCH}
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
    """Keep `frozen` in step with `batch queue` and the batches being built, on open pull
    requests other than batches. A queued pull request that a maintainer's `batch` stands for
    (`approved`) is frozen, since the queue takes only the commit that was queued; one labelled
    `batch queue` by hand is left as it is. One that is neither queued nor in a batch being built (`held`) loses
    `frozen` and `batch-building`: whatever put them there is over. This writes nothing when
    every label is where it should be."""
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if is_batch(pr) or BUILDING in pr["labels"]:
            continue
        queued, inside = QUEUED in pr["labels"], str(pr["number"]) in held
        stale = set() if queued or inside else pr["labels"] & {MEMBER, FROZEN}
        if (queued and pr["number"] in approved and FROZEN not in pr["labels"]) or stale:
            if gh.short():
                log.append(f"only {gh.remaining} requests left this hour: stopped bringing `{FROZEN}` up to date, "
                           "and the next run carries on")
                return
            if stale:
                relabel(gh, pr, remove=sorted(stale))
                log.append(f"#{pr['number']} is neither queued nor in a batch being built: "
                           + " and ".join(f"`{name}`" for name in sorted(stale)) + " removed")
            else:
                relabel(gh, pr, add=FROZEN)
                log.append(f"#{pr['number']} is queued: now `{FROZEN}`")


def approvals(gh, pulls, main, approved, log):
    """Fill in `approved` for the queued pull requests that are not labelled `frozen`, with the
    commit a maintainer's `batch` stands for on each, for `reconcile` to freeze them. With
    `ASSEMBLE` on, the batch being assembled looks at every queued pull request into main instead,
    frozen or not. Each costs a request or so, and `batch` labels what it queues `frozen` itself,
    so only a pull request labelled `batch queue` by hand is looked at again run after run."""
    for pr in sorted(pulls.values(), key=lambda pr: pr["number"]):
        if QUEUED not in pr["labels"] or FROZEN in pr["labels"] or is_batch(pr) or pr["base"] != main:
            continue
        if gh.short():
            log.append(f"only {gh.remaining} requests left this hour: stopped looking at queued pull requests, "
                       "and the next run carries on")
            return
        sha = look(gh, pr, {})[0]
        if sha is not None:
            approved[pr["number"]] = sha


def sync(gh, now=None):
    """Bring batches and labels up to date. Returns lines saying what was done."""
    log, approved, pulls, held = assemble(gh, now)
    # Last, so that the batch is assembled first when requests run short, and only after a run
    # that went through: `held` is complete only then.
    before = len(log)
    reconcile(gh, pulls, held, approved, log)
    if len(log) > before and log[0] == "nothing to do":
        log.pop(0)
    return log


def assemble(gh, now):
    """The body of `sync`. Returns (log, approved, pulls, held) for `reconcile`: the lines saying
    what was done, the commit that a maintainer's `batch` is known to stand for on each queued
    pull request, by number, every open pull request, and the batches being built that contain
    each pull request.

    With `ASSEMBLE` off, the batches assembled by hand are still kept in step and tidied up after,
    but no batch of the queue is started or added to. `approved` then holds only the queued pull
    requests not yet labelled `frozen`, the only ones `reconcile` needs it for."""
    log, approved = [], {}
    main = gh.get("")["default_branch"]
    main_sha = gh.get(f"git/ref/heads/{main}")["object"]["sha"]
    pulls = open_pulls(gh)
    found, leftover = batches(gh, pulls)
    # A batch assembled by hand that another one contains carries `batch-building` for that
    # reason alone. It is built as part of the other one, which contains what it contains too.
    hand = built_by_hand(gh, pulls, log)
    contained = holders(hand)
    hand = [batch for batch in hand if str(batch["number"]) not in contained]
    held = holders(hand)
    closed_building = gh.pages(f"issues?state=closed&labels={quoted(BUILDING)}")
    closed = closed_building + [item for label in (MEMBER, FROZEN)
                                for item in gh.pages(f"issues?state=closed&labels={quoted(label)}")]
    closed_labels = {item["number"]: {label["name"] for label in item.get("labels") or ()} for item in closed}
    requeued, cleared = finish(gh, pulls, held, leftover, main, main_sha, closed_building, closed_labels, log)
    unlabel_closed(gh, closed, cleared, log)
    # One that was inside a batch closed just now has gone back to `batch queue`.
    hand = [batch for batch in hand if BUILDING in pulls[batch["number"]]["labels"]]
    held = holders(hand)

    for batch in hand:
        requeued |= hold(gh, batch, pulls, held, main, log)
    held = holders(hand)

    if not ASSEMBLE:
        # A batch of this script's own whose pull request was merged or closed was tidied up
        # after above. One that has none is left alone (see `ASSEMBLE`).
        approvals(gh, pulls, main, approved, log)
        return log or ["nothing to do"], approved, pulls, held
    if requeued:
        # Leave time to take the pull request that broke the build out of the queue first.
        log.append("not starting a new batch in this run: the next `batch` or `-batch` comment does")
        return log, approved, pulls, held

    # The batch being assembled goes on top of the batch assembled by hand that is being built,
    # when there is just one into main. With more than one it is not clear which comes first, so
    # it goes on main.
    under = [item for item in hand if item["base"] == main]
    base = {"number": under[0]["number"], "sha": under[0]["sha"]} if len(under) == 1 else None
    crowded = [item["number"] for item in under] if len(under) > 1 else []

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
                      "and the pull requests added before it.")
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
        return log or ["nothing to do"], approved, pulls, held

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
    return log or ["nothing to do"], approved, pulls, held


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    parser.add_argument("--reopened", type=int, metavar="NUMBER",
                        help="only put `batch queue` back on this reopened pull request if it lost it when closed")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        log = reopened(gh, args.reopened) if args.reopened else sync(gh)
    except Refused as error:
        log, failure = [str(error)], 1
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
