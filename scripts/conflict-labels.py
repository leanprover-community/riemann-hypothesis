#!/usr/bin/env python3
"""Label the pull requests that conflict with main or with the batch being built.

The conflict-labels workflow runs this from its trusted checkout: for one pull request when it
is opened, reopened, pushed to, marked ready or edited, and for every open pull request when a
batch's pull request changes, when main moves on, and every half hour. Nothing from a pull
request is checked out or run. Pull requests are read through GitHub's GraphQL API, their
commits are fetched as git objects and compared with `git merge-tree`, and the only things
written to GitHub are labels and one kind of comment. The label names are in `batch-labels.py`.

Only an open pull request into main that is not a draft and not a batch can carry either label.
A batch is a pull request from a branch of this repository named `batch/...`: one of a fork
is not a batch (see `holds_batch` in `batch-labels.py`).

`main-conflict`: GitHub reports that the pull request conflicts with main. While GitHub has not yet
worked that out, the label stays as it is. A pull request the description of a batch being built
lists as included gets neither label: the batch carries its changes (see `included_in`). A pull
request whose description says that it depends on an open batch does not get the label, and loses
it: it is expected to carry the batch's changes, and so to conflict with main until the batch
lands. That is a line such as `- [ ] depends on: #123`, where #123 is the batch's pull request
(`pr-dependencies.py` has the forms such a line can take). There is no comment: GitHub already
shows the conflict on the pull request.

`batch-conflict`: the pull request conflicts with the head of an open batch labelled `building`.
When batches are stacked, the branch of the upper one merges the lower one's and lands right after
it, so a pull request is compared with the outermost batch of each stack only, the one the batch
queue labels `latest batch`: what it conflicts with there is what stands between it and main
once the stack has landed. Until the batch queue has labelled any batch being built `latest
batch`, every batch being built is compared with. A pull request labelled `batch-building` is in
a batch, and does not get it. The comparison is
the one `batch-queue-conflicts.py` makes: git cannot merge a file that both change since they
left main, or one of the two deletes a Lean file that the other starts to import. Most pull
requests change no file that the batch changes, and need no trial merge. When the comparison
cannot be made, the label stays as it is. The first time a pull request gets the label for a
batch, it is also labelled `awaiting-author` and sent a comment that says what conflicts and
what to do. A hidden marker in the comment names the batch, so it is sent once for each batch.

Both labels come off as soon as their reason has gone, whoever put them on: the pull request was
fixed or closed, it joined the batch, or the batch was merged or closed. `awaiting-author` never
comes off here. Its author takes it off by commenting `ready`, or a maintainer does.

A pull request that merged a batch's branch carries the batch's commits. When the batch is then
rebuilt without one of its pull requests, which is how a pull request is taken out of a batch,
the dependent pull request still carries that one's commits: landing it would land them too, and
GitHub would mark the pull request that was taken out merged. A sweep looks for this in each pull
request that depends on an open batch, or shares commits beyond main with a batch it is compared
with (see `stale_in`). When its branch holds commits of another open pull request that neither
main, nor any batch being built, nor a pull request it says it depends on holds, it is labelled
`awaiting-author` and told in a comment to make a new branch from the batch's current branch and
copy only its own commits onto it. A hidden marker in the comment names the batch and its head,
so it is sent once for each head of the batch.

Which batches a pull request was told about is read from its comments, once a run at most, and
only when it is about to be told something it may not have been told. What was read is kept from
one sweep to the next (`--state`, which the workflow keeps in the Actions cache), so that a sweep
in which nothing has changed reads no comments, however many batches are compared with. Without
it, a pull request already labelled `batch-conflict` that is compared with more than one batch
has its comments read on every sweep.

The workflow's token may make 1,000 REST requests an hour, shared with every other workflow
here, and the batch-queue workflow can use several hundred of them. So everything is read
through GraphQL, whose allowance is separate, and REST is used only to write, and only for a
change. Writes are spaced a second apart, and the run stops writing when few REST requests are
left this hour; the next run carries on. git fetches do not count against either allowance.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import time

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")
# The trial merge and its helpers, as the batch queue uses them to compare queued pull requests.
_conflicts = _rest.load("batch-queue-conflicts.py")
# The parser for the `depends on` lines of a description, shared with the batch queue.
_dependencies = _rest.load("pr-dependencies.py")
# The parser of a batch's description, shared with the batch queue.
_description = _rest.load("batch-description.py")
dependencies = _dependencies.dependencies
MAIN_CONFLICT, BATCH_CONFLICT = _labels.MAIN_CONFLICT, _labels.BATCH_CONFLICT
BUILDING, LATEST, MEMBER, WAITING = _labels.BUILDING, _labels.LATEST, _labels.MEMBER, _labels.WAITING
OURS = (MAIN_CONFLICT, BATCH_CONFLICT)
# How GraphQL names the workflow's own account, which REST calls github-actions[bot].
BOT = _rest.GRAPHQL_BOT
# Stop writing when fewer REST requests than this are left for the hour (see `github-rest.py`).
RESERVE = _rest.RESERVE
# GitHub works out whether a pull request conflicts with main in the background, after it is
# asked. Pull requests it has not worked out yet are read again this many times, this many
# seconds apart, after the git comparisons.
RETRIES, WAIT = 3, 15.0
# Hidden at the start of the comment sent to a pull request that conflicts with a batch.
MARKER = "<!-- conflict-labels-batch {number} -->"
TOLD = re.compile(r"<!-- conflict-labels-batch (\d+) -->")
# Hidden at the start of the comment sent to a pull request whose branch carries commits that the
# batch it builds on no longer has, once for each head of the batch.
STALE = "<!-- conflict-labels-stale {number} {sha} -->"
STALE_TOLD = re.compile(r"<!-- conflict-labels-stale (\d+) ([0-9a-f]{40}) -->")

FIELDS = """
  number state isDraft headRefName headRefOid baseRefName mergeable body
  headRepository { nameWithOwner }
  labels(first: 100) { nodes { name } }
"""
EVERY = """query($owner: String!, $name: String!, $after: String) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) {
    defaultBranchRef { name }
    pullRequests(states: OPEN, first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes { %s }
    }
  }
}""" % FIELDS
# One pull request, and the batches being built, which can only be told apart by their label.
ONE = """query($owner: String!, $name: String!, $number: Int!) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) {
    defaultBranchRef { name }
    pullRequest(number: $number) { %s }
    pullRequests(states: OPEN, labels: ["%s"], first: 100) { nodes { %s } }
  }
}""" % (FIELDS, BUILDING, FIELDS)
# Pull requests by number. `%s` is a list of `p123: pullRequest(number: 123) { ... }`.
SOME = """query($owner: String!, $name: String!) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) { %s }
}"""
COMMENTS = _rest.COMMENTS
CLOSED = """query($main: String!, $batch: String!) {
  rateLimit { cost remaining }
  main: search(query: $main, type: ISSUE, first: 100) { nodes { ... on PullRequest { number } } }
  batch: search(query: $batch, type: ISSUE, first: 100) { nodes { ... on PullRequest { number } } }
}"""


Refused = _rest.Refused


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with the queries this script reads pull
    requests with."""

    # Reading.

    def everything(self):
        """The default branch, and every open pull request as {number: pull request}."""
        found, after, main = {}, None, None
        while True:
            data = self.graphql(EVERY, owner=self.owner, name=self.name, after=after)["repository"]
            main = data["defaultBranchRef"]["name"]
            page = data["pullRequests"]
            for node in page["nodes"]:
                found[node["number"]] = pull(node, self.repo)
            if not page["pageInfo"]["hasNextPage"]:
                return main, found
            after = page["pageInfo"]["endCursor"]

    def one(self, number):
        """The default branch, and pull request `number` together with the batches it could
        conflict with or depend on, as {number: pull request}."""
        data = self.graphql(ONE, owner=self.owner, name=self.name, number=number)["repository"]
        main, node = data["defaultBranchRef"]["name"], data["pullRequest"]
        if node is None:
            raise Refused(f"There is no pull request #{number} in {self.repo}.")
        found = {node["number"]: pull(node, self.repo) for node in data["pullRequests"]["nodes"]}
        found[number] = pull(node, self.repo)
        named = sorted(dependencies(found[number]["body"], self.repo) - set(found))
        if named:
            found.update(self.some(named, FIELDS))
        return main, found

    def some(self, numbers, fields):
        """Pull requests by number, open or not, a hundred to a query. One that does not exist
        is left out."""
        found = {}
        for start in range(0, len(numbers), 100):
            chunk = numbers[start:start + 100]
            parts = " ".join(f"p{number}: pullRequest(number: {int(number)}) {{ {fields} }}" for number in chunk)
            data = self.graphql(SOME % parts, owner=self.owner, name=self.name)["repository"]
            for number in chunk:
                node = data.get(f"p{number}")
                if node:
                    found[number] = pull(node, self.repo)
        return found

    def mergeable(self, numbers):
        """Whether GitHub can merge each of these pull requests into its base, as {number: state}."""
        return {number: pr["mergeable"] for number, pr in self.some(sorted(numbers), "number mergeable").items()}

    def notices(self, number):
        """What this script has told pull request `number`, read from its comments once a run:
        {"told": the batches it was told it conflicts with, "stale": (batch, head) for each head of
        a batch it was told its branch carries commits that batch no longer has}."""
        cache = self.__dict__.setdefault("_notices", {})  # emptied by `sync` at the start of a run
        if number not in cache:
            found, after = {"told": set(), "stale": set()}, None
            while True:
                data = self.graphql(COMMENTS, owner=self.owner, name=self.name, number=number, after=after)
                page = data["repository"]["pullRequest"]["comments"]
                for comment in page["nodes"]:
                    author, body = comment.get("author") or {}, comment.get("body") or ""
                    if author.get("__typename") != "Bot" or author.get("login") != BOT:
                        continue
                    match = TOLD.match(body)
                    if match:
                        found["told"].add(int(match.group(1)))
                    match = STALE_TOLD.match(body)
                    if match:
                        found["stale"].add((int(match.group(1)), match.group(2)))
                if not page["pageInfo"]["hasNextPage"]:
                    break
                after = page["pageInfo"]["endCursor"]
            cache[number] = found
        return {key: set(value) for key, value in cache[number].items()}

    def closed_with_labels(self):
        """Closed pull requests that still carry one of the labels, as {label: [numbers]}."""
        query = f"repo:{self.repo} is:pr is:closed label:"
        data = self.graphql(CLOSED, main=query + MAIN_CONFLICT, batch=query + BATCH_CONFLICT)
        return {MAIN_CONFLICT: sorted(node["number"] for node in data["main"]["nodes"] if node),
                BATCH_CONFLICT: sorted(node["number"] for node in data["batch"]["nodes"] if node)}


def pull(node, repo):
    """What this script needs to know about a pull request, from GraphQL's answer."""
    home = (node.get("headRepository") or {}).get("nameWithOwner")
    return {
        "number": node["number"], "open": node.get("state", "OPEN") == "OPEN",
        "draft": node.get("isDraft", False), "ref": node.get("headRefName", ""),
        "batch": _labels.holds_batch(repo, home, node.get("headRefName", "")), "sha": node.get("headRefOid", ""),
        "base": node.get("baseRefName", ""), "mergeable": node.get("mergeable", "UNKNOWN"),
        "body": node.get("body") or "", "labels": {label["name"] for label in (node.get("labels") or {}).get("nodes", [])},
    }


# ---------------------------------------------------------------------------------------------
# Deciding, from what is known about a pull request. Nothing here asks GitHub or git.


def is_batch(pr):
    """Whether the pull request holds a batch (see `batch-labels.py`)."""
    return pr["batch"]


def unavailable(pr, main):
    """Why the pull request can carry neither label, or None if it can."""
    if not pr["open"]:
        return "it is closed"
    if pr["draft"]:
        return "it is a draft"
    if is_batch(pr):
        return "it is a batch"
    if pr["base"] != main:
        return f"it targets `{pr['base']}`"
    return None


def comparable(pr, main):
    """Whether the pull request is one to compare with the batches being built."""
    return unavailable(pr, main) is None and MEMBER not in pr["labels"]


def compared(batches):
    """The batches that pull requests are compared with, as sorted numbers, from every open batch
    as {number: pull request}: those being built (`building`) that are the outermost of their
    stack (`latest batch`). A batch under another is part of the one on top of it, which merges
    its branch. When no batch being built carries `latest batch`, as before the batch queue has
    labelled any, every batch being built."""
    building = [number for number, batch in batches.items() if BUILDING in batch["labels"]]
    latest = [number for number in building if LATEST in batches[number]["labels"]]
    return sorted(latest or building)


def included_in(batches, repo):
    """The pull requests whose changes a batch being built carries by its own account, as {number:
    {batch numbers}}: those its description lists as included, under a heading that does not leave
    them out (see `batch-description.py`).

    Such a pull request is not compared. Its changes land with the batch even when its own head is
    not in the branch, for instance when `main` was merged into it for the batch and the push to
    its branch was refused, so a conflict with the batch, or with `main`, is not its author's to
    fix. The batch queue's description check says when its head is not in the branch, since
    GitHub will not mark it merged then.
    """
    found = {}
    for number, batch in batches.items():
        if BUILDING not in batch["labels"]:
            continue
        for listed, heading, _ in _description.list_entries(batch["body"], repo):
            if heading and not _description.leaves_out(heading) and listed != number:
                found.setdefault(listed, set()).add(number)
    return found


def found_conflict(result):
    return result is not None and (result.kind == "conflict" or bool(result.stale))


def decide(pr, main, batches, results, carried=None):
    """What the labels of a pull request should be.

    `pr["depends"]` holds the pull requests its description says it depends on (see
    `pr-dependencies.py`). `batches` is every open batch as {number: pull request}, and `results`
    the pull request's comparison with each one it is compared with (see `compared`), as {batch
    number: Comparison, or None when it could not be made}. `carried` is what `stale_in` found
    in its branch, if anything. Returns {"main": wanted, "batch": wanted, "conflicts": {batch
    number: Comparison}, "stale": {batch number: {"head": its head, "prs": [numbers]}}, "why":
    {label: reason}}, where wanted is True or False, or None to leave the label as it is.
    """
    why = {}
    gone = unavailable(pr, main)
    if gone:
        return {"main": False, "batch": False, "conflicts": {}, "stale": {},
                "why": {MAIN_CONFLICT: gone, BATCH_CONFLICT: gone}}
    if pr.get("included"):
        said = "the description of " + ", ".join(f"#{number}" for number in sorted(pr["included"])) + " lists it as included"
        return {"main": False, "batch": False, "conflicts": {}, "stale": {},
                "why": {MAIN_CONFLICT: said, BATCH_CONFLICT: said}}
    stale = {}
    if carried and carried.get("prs"):
        stale = {number: {"head": batches[number]["sha"], "prs": sorted(carried["prs"])}
                 for number in sorted(carried["on"]) if number in batches}
    on = sorted(pr["depends"] & set(batches))
    if on:
        wanted_main, why[MAIN_CONFLICT] = False, f"it depends on the batch #{on[0]}"
    elif pr["mergeable"] == "CONFLICTING":
        wanted_main, why[MAIN_CONFLICT] = True, f"it conflicts with `{main}`"
    elif pr["mergeable"] == "MERGEABLE":
        wanted_main, why[MAIN_CONFLICT] = False, f"it merges into `{main}`"
    else:
        wanted_main, why[MAIN_CONFLICT] = None, "GitHub has not worked out whether it merges"

    building = compared(batches)
    conflicts = {number: results[number] for number in building if found_conflict(results.get(number))}
    if MEMBER in pr["labels"]:
        wanted_batch, why[BATCH_CONFLICT] = False, f"it is labelled `{MEMBER}`"
    elif not building:
        wanted_batch, why[BATCH_CONFLICT] = False, "no batch is being built"
    elif conflicts:
        wanted_batch = True
        why[BATCH_CONFLICT] = "it conflicts with " + ", ".join(f"#{number}" for number in conflicts)
    elif any(results.get(number) is None or results[number].kind in ("too many", "unknown") for number in building):
        unknown = [number for number in building
                   if results.get(number) is None or results[number].kind in ("too many", "unknown")]
        wanted_batch = None
        why[BATCH_CONFLICT] = "it could not be compared with " + ", ".join(f"#{number}" for number in unknown)
    else:
        wanted_batch, why[BATCH_CONFLICT] = False, "it merges with " + ", ".join(f"#{number}" for number in building)
    return {"main": wanted_main, "batch": wanted_batch, "conflicts": conflicts, "stale": stale, "why": why}


def needs_told(pr, decision, batches, known=None):
    """Whether to read a pull request's comments to see what it was told.

    That is only needed when it is about to be told something it may not have been told: it
    conflicts with a batch, and either does not carry the label yet or it is compared with more
    than one batch; or its branch carries commits that a batch it builds on no longer has. `known`
    is what an earlier run read or said, as `GitHub.notices` gives it, or None: what it shows the
    pull request was told is not read again.
    """
    known = known or {"told": set(), "stale": set()}
    new = set(decision["conflicts"]) - known["told"]
    if new and (BATCH_CONFLICT not in pr["labels"] or len(compared(batches)) > 1):
        return True
    return any((number, item["head"]) not in known["stale"] for number, item in decision.get("stale", {}).items())


def plan(pr, decision, told, batches, stale_told=None):
    """The changes to make: (labels to add, labels to take off, [(batch number, comment)]).

    `told` is the set of batches the pull request was already sent a comment about, and
    `stale_told` the (batch, head) it was told it carries commits of that the batch no longer
    has, both None when they were not read because nothing new is to be said (see `needs_told`).
    """
    add, remove, notes = set(), set(), []
    for label, wanted in ((MAIN_CONFLICT, decision["main"]), (BATCH_CONFLICT, decision["batch"])):
        if wanted and label not in pr["labels"]:
            add.add(label)
        elif wanted is False and label in pr["labels"]:
            remove.add(label)
    if decision["batch"] and told is not None:
        for number, result in sorted(decision["conflicts"].items()):
            if number not in told:
                notes.append((number, message(batches[number], result)))
    if stale_told is not None:
        for number, item in sorted(decision.get("stale", {}).items()):
            if (number, item["head"]) not in stale_told:
                notes.append((number, stale_message(batches[number], item["prs"])))
    if notes and WAITING not in pr["labels"]:
        add.add(WAITING)
    return add, remove, notes


# ---------------------------------------------------------------------------------------------
# The comment sent to a pull request that conflicts with a batch.


def message(batch, result):
    """What a pull request is told about its conflict with `batch`, given their Comparison."""
    show, listing = _conflicts.show, _conflicts.listing
    branch = show(batch["ref"].encode())
    lines = [MARKER.format(number=batch["number"])]
    found = []
    if result.conflicts:
        found.append(f"git cannot merge {_conflicts.count(len(result.conflicts), 'file')} that both change: "
                     f"{listing(result.conflicts)}")
    for who, target, path in result.stale[:_conflicts.LISTED]:
        if who == "ours":
            found.append(f"this pull request deletes {show(target)}, which #{batch['number']} starts to import "
                         f"in {show(path)}")
        else:
            found.append(f"#{batch['number']} deletes {show(target)}, which this pull request starts to import "
                         f"in {show(path)}")
    more = len(result.stale) - _conflicts.LISTED
    if more > 0:
        found.append(f"{more:,} more Lean files that one deletes and the other starts to import")
    lines.append(f"This pull request conflicts with #{batch['number']}, the batch being built from the branch "
                 f"{branch}: " + "; ".join(found) + ".")
    lines += [
        "",
        f"It cannot land after #{batch['number']} as it is. To fix that:",
        "",
        f"1. Merge the batch's branch {branch} into your branch and resolve the conflicts. Merge it rather than "
        "rebasing onto it. If #{n}'s branch is rebuilt before it lands, which is how a pull "
        "request is taken out of a batch, your branch still carries the pull request that was taken out. Then "
        "make a new branch from the new batch branch, copy only your own commits onto it with `git cherry-pick`, "
        "and push that to this pull request.".format(n=batch["number"]),
        "2. Add this line at the top of the pull request's description:",
        "",
        "   ```",
        f"   - [ ] depends on: #{batch['number']}",
        "   ```",
        "",
        f"   Your pull request then carries the batch's changes, and may conflict with `main`, until "
        f"#{batch['number']} lands. That line says this is expected.",
        "3. Comment `ready`.",
        "",
        f"Or wait until #{batch['number']} has landed, then merge `main` into your branch, resolve the "
        "conflicts there and comment `ready`.",
        "",
        f"This pull request is labelled `{BATCH_CONFLICT}` and `{WAITING}` meanwhile. `{BATCH_CONFLICT}` comes "
        "off by itself once the conflict is gone or the batch has landed or been closed. "
        "This compares text, and new imports against deleted Lean files: a pull request that passes both "
        "can still fail to build with the batch.",
    ]
    return "\n".join(lines) + "\n"


def stale_message(batch, prs):
    """What a pull request is told when its branch carries commits of the pull requests `prs` that
    `batch`, which it builds on, no longer has."""
    branch = _conflicts.show(batch["ref"].encode())
    names = ", ".join(f"#{number}" for number in prs)
    lines = [
        STALE.format(number=batch["number"], sha=batch["sha"]),
        f"This pull request's branch carries commits of {names} that #{batch['number']}, the batch it builds on, "
        f"no longer has: the batch's branch {branch} was rebuilt without them. If this pull request lands as it "
        f"is, they land with it, and GitHub marks {names} merged.",
        "",
        "To fix that:",
        "",
        f"1. Make a new branch from the batch's current branch {branch}.",
        "2. Copy only your own commits onto it with `git cherry-pick`, leaving out the merges and the commits "
        f"of {names}.",
        "3. Push that branch to this pull request, and comment `ready`.",
        "",
        f"From then on, bring this pull request up to date by merging {branch} into it, never by rebasing onto "
        "it.",
        "",
        f"This pull request is labelled `{WAITING}` meanwhile. It is told this once for each head of "
        f"#{batch['number']}.",
    ]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------------
# Comparing pull requests with the batches being built, in a clone without file contents.


def compare_all(repo, main, building, candidates, log, *, origin=None, watch=None, carried=None):
    """Compare each of `candidates` with each batch in `building` (both {number: pull request}).

    Returns {pull request number: {batch number: Comparison, or None if it could not be made}}.

    One fetch brings main and every head involved, as commits and trees without file contents.
    What each pull request changes since it left main is compared with what the batch changes
    since it did, and only pull requests that change a file the batch changes too are merged on
    trial. Before that, one more fetch brings the file contents that the check for deleted
    imports reads.

    `watch`, {pull request number: {"on": [batch numbers], "exclude": [numbers]}}, asks for the
    candidates that may carry commits a batch no longer has to be looked at, and `carried` is
    filled in with what was found (see `stale_in`). The heads of the pull requests in "on" and
    "exclude" are fetched as well.
    """
    watch = watch or {}
    git, merge_base = _conflicts.git, _conflicts.merge_base
    origin = origin or f"https://github.com/{repo}.git"
    results = {number: {} for number in candidates}
    with tempfile.TemporaryDirectory() as work:
        started = time.monotonic()
        git(work, "init", "--quiet")
        git(work, "remote", "add", "origin", origin)
        trunk = f"refs/remotes/origin/{main}"
        numbers = sorted(set(building) | set(candidates)
                         | {other for item in watch.values() for other in [*item["on"], *item["exclude"]]})
        # The `refs/pull/` refs stay there when a pull request is pushed to or closed while this
        # runs, so one fetch cannot fail for one pull request.
        git(work, "fetch", "--quiet", "--filter=blob:none", "--no-tags", "origin",
            f"+refs/heads/{main}:{trunk}", *(f"+refs/pull/{number}/head:refs/pr/{number}" for number in numbers))
        _, out = git(work, "for-each-ref", "--format=%(refname) %(objectname)", "refs/pr/")
        heads = {int(ref.rsplit("/", 1)[1]): sha for ref, sha in (line.split() for line in out.decode().splitlines())}
        log.append(f"fetched {len(heads)} heads and `{main}` in {time.monotonic() - started:.0f} s")

        changes = {}

        def changed(fork, head):
            if (fork, head) not in changes:
                changes[fork, head] = _conflicts.changed(work, fork, head)
            return changes[fork, head]

        # What each batch changes since it left main.
        sides = {}
        for number in sorted(building):
            head = heads.get(number)
            fork = merge_base(work, trunk, head) if head else None
            sides[number] = (fork, head) if fork else None
        # Which forks to measure from, for each pull request and batch. A pull request that holds
        # commits of the batch that are not on main yet (it merged an earlier head of the batch,
        # say) is measured from where the two parted, so that the batch's own changes are not
        # counted as its.
        pairs, sharing = {}, {}
        for number in sorted(candidates):
            head = heads.get(number)
            fork = merge_base(work, trunk, head) if head else None
            for batch in sorted(building):
                if not fork or not sides[batch]:
                    results[number][batch] = _conflicts.Comparison("unknown", note="no common ancestor with main")
                    continue
                base = merge_base(work, head, sides[batch][1])
                if base is None:
                    results[number][batch] = _conflicts.Comparison("unknown", note="no common ancestor")
                elif base == head:
                    # In the batch already, although not labelled so yet.
                    results[number][batch] = _conflicts.Comparison("clean", note="the batch holds its head")
                elif base == sides[batch][1]:
                    results[number][batch] = _conflicts.Comparison("clean", note="it holds the batch's head")
                    sharing.setdefault(number, set()).add(batch)
                elif git(work, "merge-base", "--is-ancestor", base, trunk, ok=(0, 1))[0] == 0:
                    pairs[number, batch] = (base, (fork, head), sides[batch])
                else:
                    pairs[number, batch] = (base, (base, head), (base, sides[batch][1]))
                    sharing.setdefault(number, set()).add(batch)
        if carried is not None:
            stale_in(work, trunk, heads, candidates, watch, sharing, carried, log)

        # The deleted-import check reads the import lines of the Lean files a pull request adds or
        # edits, when the other side deletes a Lean file. One request fetches all of them.
        started = time.monotonic()
        for batch in sorted(building):
            if sides[batch]:
                ours = [pair for (number, other), (_, pair, _) in sorted(pairs.items()) if other == batch]
                _conflicts.prefetch_imports(work, sides[batch], ours)
        seen, merged = {}, 0
        for (number, batch), (base, (fork, head), (batch_fork, batch_head)) in sorted(pairs.items()):
            try:
                if changed(fork, head) & changed(batch_fork, batch_head):
                    result = _conflicts.compare(work, base, head, batch_head, ours_fork=fork,
                                                theirs_fork=batch_fork, partial=True)
                    merged += 1
                else:
                    result = _conflicts.Comparison("apart")
                _conflicts.compare_imports(work, result, fork, head, batch_fork, batch_head, seen=seen)
                results[number][batch] = result
            except RuntimeError as error:
                results[number][batch] = None
                log.append(f"#{number} could not be compared with #{batch}: {error}")
        size = sum(path.stat().st_size for path in Path(work, ".git", "objects").rglob("*") if path.is_file())
        log.append(f"compared {_conflicts.count(len(pairs), 'pull request')} with the batch(es) being built "
                   f"({len(candidates) * len(building) - len(pairs)} more needed no comparison), {merged} by a "
                   f"trial merge, in {time.monotonic() - started:.0f} s; {size / 1e6:.0f} MB of git objects in all")
    return results


def stale_in(work, trunk, heads, candidates, watch, sharing, carried, log):
    """Find the candidates whose branch carries commits of another open pull request that a batch
    they build on no longer has, and fill in `carried` with {number: {"on": [batch numbers],
    "prs": [numbers]}} for each.

    A candidate builds on the batches `watch` names for it (those its description says it depends
    on) and, failing those, on the batches it shares commits beyond main with (`sharing`). Its
    commits that neither main, nor any head in its "exclude" (every batch being built, and every
    pull request it says it depends on), holds are what it carries of its own or from elsewhere.
    Those that are also among another candidate's own commits belong to that pull request: the
    batch was rebuilt without it, and the candidate still carries it. A pull request's own commits
    are those on its first-parent line beyond main that are not merges: what it carries from a
    batch, or from another pull request, came in through a merge. A candidate's own commits, and
    those of a pull request it says it depends on, are never counted.
    """
    git, theirs = _conflicts.git, {}

    def beyond(head, *options):
        code, out = git(work, "rev-list", *options, head, f"^{trunk}", ok=(0, 128))
        return set(out.decode().split()) if code == 0 else None

    for number in sorted(candidates):
        on = sorted(set((watch.get(number) or {}).get("on") or ()) or sharing.get(number) or ())
        head = heads.get(number)
        if not on or not head:
            continue
        exclude = {other for other in (watch.get(number) or {}).get("exclude") or ()} | set(on) | {number}
        own = beyond(head, *(f"^{heads[other]}" for other in sorted(exclude - {number}) if other in heads))
        if not own:
            continue
        prs = []
        for other in sorted(candidates):
            if other in exclude or other not in heads:
                continue
            if other not in theirs:
                theirs[other] = beyond(heads[other], "--first-parent", "--no-merges") or set()
            if theirs[other] & own:
                prs.append(other)
        if prs:
            carried[number] = {"on": on, "prs": prs}
            log.append(f"#{number} carries commits of " + ", ".join(f"#{other}" for other in prs) + " that "
                       + ", ".join(f"#{batch}" for batch in on) + " no longer has")


# ---------------------------------------------------------------------------------------------
# Putting it together.


def sync(gh, number=None, compare=compare_all, known=None):
    """Bring both labels up to date on one pull request, or on every open one. Returns a log.

    `known` is what earlier runs read from pull requests' comments or said in them, as
    {number: notices} (see `GitHub.notices`), and is brought up to date. A sweep keeps it to the
    open pull requests."""
    log = []
    known = {} if known is None else known
    # Comments are read at most once a run (see `GitHub.notices`).
    gh._notices = {}
    if number is None:
        main, pulls = gh.everything()
        targets = sorted(pulls)
    else:
        main, pulls = gh.one(number)
        targets = [number]
    for pr in pulls.values():
        pr["depends"] = dependencies(pr["body"], gh.repo)
    batches = {key: pr for key, pr in pulls.items() if pr["open"] and is_batch(pr)}
    included = included_in(batches, gh.repo)
    for key, pr in pulls.items():
        pr["included"] = included.get(key, set())
    building = {key: batches[key] for key in compared(batches)}
    candidates = {key: pulls[key] for key in targets if comparable(pulls[key], main) and not pulls[key]["included"]}
    if building:
        under = [key for key, pr in sorted(batches.items()) if BUILDING in pr["labels"] and key not in building]
        log.append("compared with the batches being built: "
                   + ", ".join(f"#{key} (`{pr['ref']}`)" for key, pr in sorted(building.items()))
                   + ("; not with " + ", ".join(f"#{key}" for key in under) + " on its own: a batch stacked on it "
                      "holds its changes" if under else ""))
    results, carried = {}, {}
    # Those that may carry commits a batch they build on no longer has. Only a sweep reads every
    # open pull request, and so knows whose commits they are.
    watch = {}
    if number is None:
        being_built = sorted(key for key, pr in batches.items() if BUILDING in pr["labels"])
        for key in candidates:
            on = sorted(pulls[key]["depends"] & set(batches))
            watch[key] = {"on": on, "exclude": sorted(set(being_built) | (pulls[key]["depends"] & set(pulls)))}
    if building and candidates:
        try:
            results = compare(gh.repo, main, building, candidates, log, watch=watch,
                              carried=carried if number is None else None)
        except RuntimeError as error:
            # `batch-conflict` then stays as it is everywhere, and `main-conflict` is still kept.
            gh.failed = True
            log.append(f"could not compare with the batch(es) being built: {error}")

    # GitHub may not have worked out yet whether a pull request merges into main, for instance
    # just after main moved on. Asking starts that, so ask again after a while.
    for attempt in range(RETRIES):
        unknown = [key for key in targets if unavailable(pulls[key], main) is None
                   and pulls[key]["mergeable"] == "UNKNOWN" and not pulls[key]["depends"] & set(batches)]
        if not unknown:
            break
        if attempt:
            time.sleep(WAIT)
        for key, state in gh.mergeable(unknown).items():
            pulls[key]["mergeable"] = state

    decisions = {key: decide(pulls[key], main, batches, results.get(key, {}), carried.get(key)) for key in targets}
    stopped = False
    for key in targets:
        pr, decision = pulls[key], decisions[key]
        try:
            told = stale_told = None
            if needs_told(pr, decision, batches, known.get(key)):
                known[key] = gh.notices(key)
                told, stale_told = known[key]["told"], known[key]["stale"]
            add, remove, notes = plan(pr, decision, told, batches, stale_told)
            if not (add or remove or notes):
                if number is not None:
                    log.append(f"#{key}: nothing to change ({'; '.join(decision['why'].values())})")
                continue
            if gh.remaining is None:
                gh.rate_limit()
            if gh.short():
                log.append(f"only {gh.remaining} REST requests left this hour: stopped before #{key}, "
                           "and the next run carries on")
                stopped = True
                break
            if number is None:
                # A sweep decided from what it read minutes ago. A pull request pushed to or
                # relabelled since is left to the run its own event started.
                fresh = gh.some([key], FIELDS).get(key)
                if fresh is None or fresh["sha"] != pr["sha"] or fresh["labels"] != pr["labels"]:
                    log.append(f"#{key}: changed during this sweep, so left to the run for it")
                    continue
            for label in sorted(add):
                # Asked once a run (see `github-rest.py`).
                if not gh.label_exists(label):
                    if not gh.dry_run:
                        raise Refused(f"There is no `{label}` label in {gh.repo}. Was it renamed?")
                    log.append(f"there is no `{label}` label yet, so a real run would stop here")
            for batch, text in notes:
                gh.comment(key, text)
                record = known.setdefault(key, {"told": set(), "stale": set()})
                if text.startswith(STALE.split("{", 1)[0]):
                    record["stale"].add((batch, batches[batch]["sha"]))
                else:
                    record["told"].add(batch)
            if add:
                gh.add_labels(key, add)
            for label in sorted(remove):
                gh.remove_label(key, label)
            pr["labels"] = (pr["labels"] | add) - remove
            verb = "would " if gh.dry_run else ""
            said = [f"{verb}add `{label}`, because {decision['why'].get(label, 'it is told about a batch')}"
                    for label in sorted(add)]
            said += [f"{verb}take `{label}` off, because {decision['why'][label]}" for label in sorted(remove)]
            said += [f"{verb}tell it that its branch carries commits #{batch} no longer has"
                     if text.startswith(STALE.split("{", 1)[0]) else f"{verb}tell it about the batch #{batch}"
                     for batch, text in notes]
            log.append(f"#{key}: " + "; ".join(said))
        except RuntimeError as error:
            # One pull request that cannot be read or labelled should not hold up the rest.
            gh.failed = True
            log.append(f"#{key}: skipped, because {error}")

    if number is None and not stopped:
        # A pull request closed with a label keeps it otherwise: closing starts no run here.
        try:
            for label, closed in gh.closed_with_labels().items():
                for key in closed:
                    if gh.short():
                        log.append(f"only {gh.remaining} REST requests left this hour: stopped taking labels off "
                                   "closed pull requests, and the next run carries on")
                        break
                    gh.remove_label(key, label)
                    log.append(f"#{key}: {'would take' if gh.dry_run else 'took'} `{label}` off, because it is closed")
        except RuntimeError as error:
            gh.failed = True
            log.append(f"closed pull requests: skipped, because {error}")
    if number is None:
        for key in [key for key in known if key not in pulls]:
            del known[key]
        for label in OURS:
            having = [key for key in targets if label in pulls[key]["labels"]]
            log.append(f"{len(having)} of {len(targets)} open pull requests "
                       f"{'would carry' if gh.dry_run else 'carry'} `{label}`"
                       + (": " + ", ".join(f"#{key}" for key in having) if having else ""))
    return log


def load_state(path):
    """What earlier runs read from pull requests' comments, as `sync` takes it, from the file
    `path`. A missing or unreadable file reads as nothing known."""
    try:
        kept = json.loads(path.read_text()) if path else {}
    except (OSError, ValueError):
        return {}
    known = {}
    for key, item in (kept.get("pulls") or {}).items() if isinstance(kept, dict) else ():
        try:
            known[int(key)] = {"told": {int(number) for number in item.get("told") or ()},
                               "stale": {(int(number), str(sha)) for number, sha in item.get("stale") or ()}}
        except (AttributeError, TypeError, ValueError):
            continue
    return known


def save_state(path, known):
    """Write what `load_state` reads."""
    pulls = {str(key): {"told": sorted(item["told"]), "stale": sorted([number, sha] for number, sha in item["stale"])}
             for key, item in sorted(known.items())}
    path.write_text(json.dumps({"pulls": pulls}, sort_keys=True) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", type=int, help="look at this pull request only")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    parser.add_argument("--state", type=Path,
                        help="what earlier runs read from pull requests' comments: read from this file if it is "
                             "there, and written back to it")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    started, failure = time.monotonic(), None
    if not _labels.CONFLICT_LABELS_ON and not args.dry_run:
        # Switched off in `batch-labels.py`; a dry run still shows what it would do.
        sys.stdout.write("- the conflict labels are switched off (`CONFLICT_LABELS_ON` in `batch-labels.py`): "
                         "nothing to do\n")
        return
    known = load_state(args.state)
    try:
        log = sync(gh, args.pr, known=known)
        failure = 1 if gh.failed else None
        if args.state and not args.dry_run:
            save_state(args.state, known)
    except (Refused, RuntimeError) as error:
        log, failure = [str(error)], 1
    left = f"; {gh.remaining} left this hour" if gh.remaining is not None else ""
    log.append(f"{time.monotonic() - started:.0f} s; {gh.calls} REST requests{left}; {gh.queries} GraphQL "
               f"queries costing {gh.points} points; {gh.wrote} {'writes that a real run would make' if gh.dry_run else 'writes'}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
