#!/usr/bin/env python3
"""Tick the `depends on` boxes in open pull requests' descriptions once the dependency is on main or
in a batch being built.

The dependencies workflow runs this from its trusted checkout: for the open pull requests whose
description names a pull request that was just closed, merged or not; for one pull request when
it is opened or reopened or its description is edited, since what it depends on may have landed
already; and for every open pull request every hour. Nothing from a pull request is checked out
or run. `pr-dependencies.py` says which lines declare a dependency, such as
`- [ ] depends on: #123`.

A pull request is on main when its head commit is in main, or when it was merged into main. Being
marked merged is not enough: one merged into a batch's branch, or into any other branch, is marked
merged long before its changes reach main. One compare request answers whether its head is in
main: the branch is `ahead_by` nothing on the head when the head is in it. A pull request that is
not open is compared with main, once a run. A pull request is in a batch being built when the
batch-queue workflow's record of an open pull request labelled `building` that holds a batch (see
`holds_batch` in `batch-labels.py`) lists it: any batch of a stack, each of which lists what it
contains of its own. A member pushed to after the batch took it still counts, since the batch
holds the commit it took, and a member the record says the branch reverts does not. A line marked
`(batched)` is not unticked while a batch closed without being merged less than an hour ago
(`GRACE`) held its pull requests: a batch is often closed and opened again, rebuilt, under a new
number within a minute or two, and a run in between would untick it, and the next one tick it
again. A line that is not ticked yet is not ticked for such a batch.

GitHub's task boxes have only two states, so a line the workflow ticks says why, in an annotation
before the pull requests it names, where GitHub shows them as their titles:

- `- [x] depends on: (batched) #123`: every pull request on the line is on main or in a batch being
  built, and at least one is not on main yet;
- `- [x] depends on: (main) #123`: every one of them is on main.

An empty box is ticked and annotated as soon as one of these holds, and `(batched)` becomes
`(main)` once the second does. A line marked `(batched)` whose pull requests no longer all are on
main or in a batch being built, because one left every batch before it reached main, is unticked
again and loses its annotation. A line marked `(main)` stays as it is, and so does a box ticked by
hand without an annotation.

A line that names a pull request holding a batch, and every line in the description of a pull
request that holds a batch, such as the line that stacks one batch on another, gets no annotation.
It is ticked, plainly, once every pull request it names is on main, and never unticked: a batch
that reached main stays there. A batch's changes are only on main once it has landed, so it never
counts as being in a batch.

Only the box's character and the annotation change: the rest of the description stays as it
was, byte for byte, line endings included. Lines without a box or with `[]`, lines in code or
comments and pull requests of other repositories are left alone. The description is read again
before the changes are worked out, and the changes are made on that fresh copy; nothing is
written if they change nothing. Once everything is worked out and the pause between writes has
passed, it is read once more, right before the write, and if it changed meanwhile nothing is
written and the next run looks again. So an author's edit is lost only if it falls in the moment
between that last read and the write.

What this cannot tell apart, since it keeps nothing between runs: an annotation typed by hand is
taken for the workflow's. A `(batched)` typed by hand is removed, along with the tick, when the
pull requests on its line leave every batch, and a `(main)` typed by hand is trusted for good. And
a dependency that GitHub marked merged because a batch carrying its head commit landed counts as
on main even if the batch reverted its changes before it landed: while the batch is open its
record says so, and the line is not ticked, but afterwards nothing does. Batches should be rebuilt
without a pull request rather than revert it (see `AGENTS.md`).

A pull request named on a line whose box is empty may have been closed without landing: neither
merged nor on main, nor in a batch being built. The pull request that depends on it is then
labelled `awaiting-author` and sent a comment: its branch probably still carries the closed pull
request's changes, so its author should merge main and take them out, or take over the work, then
edit the description and comment `ready`. A hidden marker in the comment names the closed pull
request, so it is sent once for each. Nothing is said about a dependency that is still open, that
was merged into a branch other than main, or that holds a batch, since a batch closed without
landing is usually opened again, rebuilt, under a new number; nor about one named on a line
without a box, which may be prose such as "Needs #123 first".

Pull requests and their descriptions are read through GitHub's GraphQL API, whose allowance is
separate from the REST requests that the workflow's token shares with every other workflow here.
What each named pull request is, which batches are being built, a page at a time, and their
records, and the comments of a pull request about to be told something are each read once a run.
REST is used for the compares and to write. Writes are spaced a second apart, the run stops when
few REST requests or GraphQL points are left this hour, and the next run carries on. A write
counts as done only once GitHub has accepted it. A dependency that cannot be looked up stops only
the pull requests that name it.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import datetime
import json
import importlib.util
from pathlib import Path
import re
import sys
import time

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")
_dependencies = _rest.load("pr-dependencies.py")
quoted = _rest.quoted
WAITING, BUILDING, LATEST = _labels.WAITING, _labels.BUILDING, _labels.LATEST
# How GraphQL names the workflow's own account, which REST calls github-actions[bot].
BOT = _rest.GRAPHQL_BOT
# Stop when fewer REST requests than this are left for the hour (see `github-rest.py`).
RESERVE = _rest.RESERVE
# Stop, too, when fewer GraphQL points than this are left for the hour: a run that reads every
# open pull request costs a few, and the other workflows here read through GraphQL as well.
GRAPHQL_RESERVE = 200
# How long a batch closed without being merged still counts for a line already marked `(batched)`:
# a batch is often closed and opened again under a new number within a minute or two, and a run in
# between would otherwise untick the line, and the next one tick it again.
GRACE = datetime.timedelta(hours=1)
# The batch-queue workflow's record of what a batch assembled by hand contains, at the start of
# one of its own comments on the batch's pull request (see `batch-queue-sync.py`).
RECORD = re.compile(r"<!-- batch-queue-by-hand (\{.*\}) -->")
# Hidden at the start of the comment sent about a dependency closed without landing.
MARKER = "<!-- dependency-ticks-closed {number} -->"
TOLD = re.compile(r"<!-- dependency-ticks-closed (\d+) -->")
# The annotations of a ticked line (see `pr-dependencies.py`).
BATCHED, MAIN = "batched", "main"

# What becomes of a pull request named on a line, and how the log says it: on main, in a batch being
# built, open, merged into another branch and in no batch being built, closed without landing, not
# known, or not a pull request.
LANDED, IN_BATCH, OPEN, ELSEWHERE, DROPPED, UNKNOWN, MISSING = (
    "landed", "in a batch", "open", "elsewhere", "dropped", "unknown", "missing")
# In the record of a batch closed without being merged less than GRACE ago, and of no batch being
# built: a line marked `(batched)` keeps its mark, and nothing else changes.
RECENT = "recently in a batch"

HEAD = "headRefName headRefOid headRepository { nameWithOwner }"
FIELDS = f"number state body {HEAD} labels(first: 100) {{ nodes {{ name }} }}"
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
ONE = """query($owner: String!, $name: String!, $number: Int!) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) {
    defaultBranchRef { name }
    pullRequest(number: $number) { %s }
  }
}""" % FIELDS
# The open pull requests labelled `building`, of which those that hold a batch are being built.
BUILT = """query($owner: String!, $name: String!, $after: String) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, labels: ["%s"], first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes { number %s labels(first: 100) { nodes { name } } }
    }
  }
}""" % (BUILDING, HEAD)
# The pull requests closed without being merged since a time, of which those that hold a batch
# were batches closed lately (see GRACE).
CLOSED = """query($q: String!) {
  rateLimit { cost remaining }
  search(query: $q, type: ISSUE, first: 100) { nodes { ... on PullRequest { number %s } } }
}""" % HEAD
# Issues and pull requests by number. `%s` is a list of `p123: issueOrPullRequest(number: 123)
# { ... }`, so that a number that is an issue is not an error.
STATES = """query($owner: String!, $name: String!) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) { %s }
}"""
STATE = f"__typename ... on PullRequest {{ number state baseRefName {HEAD} }}"
COMMENTS = _rest.COMMENTS


Refused = _rest.Refused


class Stopped(Exception):
    """Few REST requests are left this hour: the run stops, and the next one carries on."""


@dataclass(frozen=True)
class Fate:
    """What became of a pull request named on a line: one of LANDED, IN_BATCH, OPEN, ELSEWHERE,
    DROPPED, UNKNOWN and MISSING, why, for the log, and whether it holds a batch."""

    kind: str
    why: str
    batch: bool = False


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with the queries this script reads pull
    requests with. What it compares, and the batches being built, are kept for the run in `_compares`
    and `_built`."""

    def check(self):
        """Stop if the hour's allowance is nearly used up."""
        if self.remaining is None:
            self.rate_limit()
        if self.short():
            raise Stopped(f"only {self.remaining} REST requests left this hour")

    def check_graphql(self):
        """Stop before a query if the hour's GraphQL allowance is nearly used up."""
        if self.graphql_left is not None and self.graphql_left < GRAPHQL_RESERVE:
            raise Stopped(f"only {self.graphql_left} GraphQL points left this hour")

    def now(self):
        return datetime.datetime.now(datetime.timezone.utc)

    # Reading.

    def everything(self):
        """The default branch, and every open pull request as {number: pull request}."""
        found, after = {}, None
        while True:
            self.check_graphql()
            data = self.graphql(EVERY, owner=self.owner, name=self.name, after=after)["repository"]
            page = data["pullRequests"]
            for node in page["nodes"]:
                found[node["number"]] = pull(node, self.repo)
            if not page["pageInfo"]["hasNextPage"]:
                return data["defaultBranchRef"]["name"], found
            after = page["pageInfo"]["endCursor"]

    def one(self, number):
        """The default branch, and pull request `number`, open or not, or None if there is none."""
        self.check_graphql()
        data = self.graphql(ONE, missing=True, owner=self.owner, name=self.name, number=number)["repository"]
        node = data["pullRequest"]
        return data["defaultBranchRef"]["name"], (pull(node, self.repo) if node else None)

    def states(self, numbers):
        """What each of these numbers is, a hundred to a query, as {number: {"state", "base",
        "head", "batch"}}, or None for an issue or a number that names nothing. The state is
        GraphQL's `OPEN`, `CLOSED` or `MERGED`."""
        found = {}
        for start in range(0, len(numbers), 100):
            chunk = numbers[start:start + 100]
            parts = " ".join(f"p{number}: issueOrPullRequest(number: {int(number)}) {{ {STATE} }}" for number in chunk)
            self.check_graphql()
            data = self.graphql(STATES % parts, missing=True, owner=self.owner, name=self.name)["repository"]
            for number in chunk:
                node = data.get(f"p{number}") or {}
                if node.get("__typename") == "PullRequest":
                    found[number] = {"state": node["state"], "base": node.get("baseRefName") or "",
                                     "head": node.get("headRefOid") or "", "batch": is_batch(node, self.repo)}
                else:
                    found[number] = None
        return found

    def batches(self):
        """Which pull requests the batches being built hold, by the batch-queue workflow's records
        of them, read once a run: ({number: the batch whose record holds it}, {number: the batch
        closed lately whose record held it}). A member the record says the branch reverts is not
        held. The second covers batches closed without being merged less than GRACE ago, and leaves
        out what a batch being built holds."""
        if getattr(self, "_built", None) is None:
            nodes, after = [], None
            while True:
                self.check_graphql()
                page = self.graphql(BUILT, owner=self.owner, name=self.name, after=after)["repository"]["pullRequests"]
                nodes += page["nodes"]
                if not page["pageInfo"]["hasNextPage"]:
                    break
                after = page["pageInfo"]["endCursor"]
            held = {}
            for node in sorted(nodes, key=lambda node: node["number"]):
                if is_batch(node, self.repo):
                    for member in self.record(node["number"]):
                        held.setdefault(member, node["number"])
            since = (self.now() - GRACE).strftime("%Y-%m-%dT%H:%M:%SZ")
            self.check_graphql()
            closed = self.graphql(CLOSED, q=f"repo:{self.repo} is:pr is:closed is:unmerged closed:>={since}")
            recent = {}
            for node in sorted((node for node in closed["search"]["nodes"] if node), key=lambda node: node["number"]):
                if is_batch(node, self.repo):
                    for member in self.record(node["number"]):
                        if member not in held:
                            recent.setdefault(member, node["number"])
            self._built = held, recent
        return self._built

    def record(self, number):
        """The pull requests that the batch-queue workflow's record on the batch `number` says it
        contains, as a set of numbers, leaving out those it says the branch reverts. Empty when
        there is no record."""
        after = None
        while True:
            self.check_graphql()
            data = self.graphql(COMMENTS, owner=self.owner, name=self.name, number=number, after=after)
            page = data["repository"]["pullRequest"]["comments"]
            for comment in page["nodes"]:
                author = comment.get("author") or {}
                match = RECORD.match(comment.get("body") or "")
                if not match or author.get("__typename") != "Bot" or author.get("login") != BOT:
                    continue
                try:
                    note = json.loads(match.group(1))
                except ValueError:
                    return set()
                members = note.get("members") if isinstance(note, dict) else None
                reverted = note.get("reverted") if isinstance(note, dict) else None
                if not isinstance(members, dict):
                    return set()
                return {int(key) for key in members if str(key).isdigit()} - {
                    int(key) for key in (reverted if isinstance(reverted, dict) else {}) if str(key).isdigit()}
            if not page["pageInfo"]["hasNextPage"]:
                return set()
            after = page["pageInfo"]["endCursor"]

    def contains(self, base, head):
        """Whether commit `head` is in `base`, a branch or a commit, or None if GitHub does not know
        one of them. Asked once a run for each pair. Raises Stopped when few REST requests are
        left this hour."""
        cache = self.__dict__.setdefault("_compares", {})
        if (base, head) not in cache:
            self.check()
            status, found = self.call("GET", f"compare/{quoted(base)}...{head}?per_page=1")
            if status == 404:
                cache[base, head] = None
            elif status != 200 or not isinstance(found, dict) or "ahead_by" not in found:
                raise RuntimeError(f"GET compare/{base}...{head} answered {status}")
            else:
                cache[base, head] = found["ahead_by"] == 0
        return cache[base, head]

    def told(self, number):
        """The pull requests that pull request `number` has been sent this script's comment about."""
        return self.marked(number, TOLD)

    def describe(self, number, body, shown):
        status, _ = self.write("PATCH", f"pulls/{number}", {"body": body}, shown)
        if status not in (0, 200):
            raise RuntimeError(f"could not edit the description of #{number}: {status}")


def is_batch(node, repo):
    """Whether a pull request, as GraphQL gives it, holds a batch (see `batch-labels.py`)."""
    home = (node.get("headRepository") or {}).get("nameWithOwner")
    return _labels.holds_batch(repo, home, node.get("headRefName") or "")


def pull(node, repo):
    """What this script needs to know about a pull request, from GraphQL's answer."""
    return {"number": node["number"], "open": node.get("state", "OPEN") == "OPEN", "body": node.get("body") or "",
            "batch": is_batch(node, repo),
            "labels": {label["name"] for label in (node.get("labels") or {}).get("nodes", [])}}


# ---------------------------------------------------------------------------------------------
# Deciding.


def settled(line):
    """Whether nothing can change on a line, whatever becomes of its pull requests: it names none,
    its box is missing or `[]`, it is marked `(main)`, or it was ticked by hand."""
    return (not line.numbers or line.box not in (" ", "x", "X") or line.note == MAIN
            or (line.ticked and line.note is None))


def wanted(pr, repo):
    """The pull requests whose fate decides what happens to `pr`, as a sorted list: those named on
    its lines that are not ticked, which it may be told about, and on those marked `(batched)`,
    which may be marked `(main)` or unticked."""
    return sorted({number for line in _dependencies.declarations(pr["body"], repo)
                   if not line.ticked or line.note == BATCHED for number in line.numbers})


def resolve(gh, main, numbers, known):
    """Find out what became of each of `numbers` that is not in `known` yet, and record it there as
    {number: Fate}.

    One merged into main is on it. Any other with a head commit, unless it is open, is compared
    with main; then, unless it holds a batch, it is in a batch being built when the batch-queue
    workflow's record of one says so (see `GitHub.batches`): a member pushed to after the batch
    took it is still in the batch at the commit taken. Raises Stopped when few REST requests, or
    GraphQL points, are left this hour.
    """
    new = sorted(set(numbers) - set(known))
    if not new:
        return
    rest = []
    for number, info in sorted(gh.states(new).items()):
        if info is None:
            known[number] = Fate(MISSING, f"#{number} is not a pull request")
        elif info["state"] == "MERGED" and info["base"] == main:
            known[number] = Fate(LANDED, f"#{number} was merged into `{main}`", info["batch"])
        elif not info["head"]:
            known[number] = Fate(UNKNOWN, f"#{number} was closed, and GitHub names no head commit for it",
                                 info["batch"])
        else:
            rest.append((number, info))
    for number, info in rest:
        if info["state"] != "OPEN":
            found = gh.contains(main, info["head"])
            if found is None:
                known[number] = Fate(UNKNOWN, f"#{number} was closed, and GitHub no longer has its head commit",
                                     info["batch"])
                continue
            if found:
                known[number] = Fate(LANDED, f"#{number} was closed, and its head is in `{main}`", info["batch"])
                continue
        held, recent = gh.batches()
        holder = None if info["batch"] else held.get(number)
        if holder is not None:
            known[number] = Fate(IN_BATCH, f"#{number} is in the batch #{holder}, which is being built")
        elif not info["batch"] and number in recent:
            known[number] = Fate(RECENT, f"#{number} was in the batch #{recent[number]}, closed without being "
                                         "merged less than an hour ago")
        elif info["state"] == "OPEN":
            known[number] = Fate(OPEN, f"#{number} is open", info["batch"])
        elif info["state"] == "MERGED":
            known[number] = Fate(ELSEWHERE, f"#{number} was merged into `{info['base']}`, which is neither in "
                                            f"`{main}` nor in a batch being built", info["batch"])
        else:
            known[number] = Fate(DROPPED, f"#{number} was closed without landing", info["batch"])


def target(pr, line, known):
    """What the box and annotation of a line should be, as (box, note), given `known` (see
    `resolve`), or None to leave the line as it is."""
    if settled(line) or any(number not in known for number in line.numbers):
        return None
    fates = [known[number] for number in line.numbers]
    on_main = all(fate.kind == LANDED for fate in fates)
    if pr["batch"] or any(fate.batch for fate in fates):
        # A line about batches: ticked plainly once they are on main, and never unticked.
        return ("x", line.note) if on_main and line.tickable else None
    if on_main:
        return "x", MAIN
    if all(fate.kind in (LANDED, IN_BATCH) for fate in fates):
        return "x", BATCHED
    if line.ticked and line.note == BATCHED and all(fate.kind in (LANDED, IN_BATCH, RECENT) for fate in fates):
        # Its batch was closed lately, and may be opened again under a new number.
        return None
    if any(fate.kind == UNKNOWN for fate in fates):
        return None
    return " ", None


def plan(pr, repo, known):
    """What to change on an open pull request, given `known` (see `resolve`): (the new description,
    the changes made to it as [(Declaration, box, note)], and the pull requests named on lines whose
    box is empty afterwards that were closed without landing). Only a line with a box counts for
    that, and never a pull request that holds a batch: a batch closed without landing is usually
    opened again, rebuilt, under a new number, and a line in prose without a box, such as "Needs
    #123 first", may say anything."""
    lines = _dependencies.declarations(pr["body"], repo)
    changes = []
    for line in lines:
        wish = target(pr, line, known)
        if wish is not None and wish != ("x" if line.ticked else " ", line.note):
            changes.append((line, *wish))
    boxes = {line.index: box for line, box, _ in changes}
    dropped = sorted({number for line in lines if line.box in (" ", "x", "X")
                      and boxes.get(line.index, "x" if line.ticked else " ") != "x"
                      for number in line.numbers
                      if number in known and known[number].kind == DROPPED and not known[number].batch})
    return _dependencies.mark(pr["body"], changes), changes, dropped


def describe_change(line, box, note, known):
    """How the log says what was done to a line."""
    why = ", ".join(known[number].why for number in line.numbers)
    if box == " ":
        return f"untick line {line.index + 1}, because {why}"
    if line.ticked:
        return f"mark line {line.index + 1} `({note})`, because {why}"
    return f"tick line {line.index + 1}" + (f" as `({note})`" if note else "") + f", because {why}"


def idle(pr, repo, known):
    """Why nothing changes on a pull request, for the log of a run for that pull request alone."""
    lines = _dependencies.declarations(pr["body"], repo)
    if not any(line.numbers for line in lines):
        return "its description declares no dependency"
    why = sorted({known[number].why for line in lines if not settled(line) for number in line.numbers
                  if number in known and known[number].kind not in (LANDED, IN_BATCH)})
    if all(settled(line) for line in lines if line.numbers):
        why.insert(0, "every line that names a pull request is ticked by hand, marked `(main)`, or has no box")
    return "; ".join(why) or "it was told about every dependency closed without landing"


def message(number):
    """What a pull request is told when #`number`, which it depends on, was closed without landing."""
    return "\n".join([
        MARKER.format(number=number),
        f"#{number} was closed without its changes landing in `main`, but the description of this pull request "
        f"says that it depends on #{number}. This pull request's branch probably still carries the changes "
        f"of #{number}, and would land them with its own.",
        "",
        "To fix that, either:",
        "",
        f"1. merge `main` into your branch and take the changes of #{number} out of it, or",
        f"2. take over the work of #{number} here, and say so in the description.",
        "",
        f"Then edit the description so that it no longer says this pull request depends on #{number}, "
        "and comment `ready`. If those changes reached `main` some other way, only that last step is needed.",
        "",
        f"This pull request is labelled `{WAITING}` meanwhile.",
    ]) + "\n"


# ---------------------------------------------------------------------------------------------
# Putting it together.


def handle(gh, main, pr, known):
    """Tick, mark and untick what is due in one open pull request's description, and tell it about
    the pull requests it depends on that were closed without landing. Returns what was done, as a
    list of phrases for the log, empty if nothing was."""
    number, repo = pr["number"], gh.repo
    resolve(gh, main, wanted(pr, repo), known)
    _, changes, dropped = plan(pr, repo, known)
    if not (changes or dropped):
        return []
    # The description may have been edited since it was read, perhaps minutes ago in a sweep. The
    # changes are made on the copy read now, so that an edit made meanwhile is kept.
    _, fresh = gh.one(number)
    if fresh is None or not fresh["open"]:
        return ["skipped, because it was closed meanwhile"]
    resolve(gh, main, wanted(fresh, repo), known)
    body, changes, dropped = plan(fresh, repo, known)
    told = gh.told(number) if dropped else set()
    notes = [other for other in dropped if other not in told]
    if not (changes or notes):
        return []
    gh.check()
    verb, said = "would " if gh.dry_run else "", []
    if notes:
        # Asked once a run (see `github-rest.py`).
        if not gh.label_exists(WAITING):
            if not gh.dry_run:
                raise Refused(f"There is no `{WAITING}` label in {repo}. Was it renamed?")
            said.append(f"there is no `{WAITING}` label yet, so a real run would stop here")
    if changes:
        # Everything is worked out, and the pause between writes waited out, before the
        # description is read once more, right before it is written: an edit made since the copy
        # the changes were made on leaves it to the next run, rather than being overwritten.
        gh.pace()
        _, latest = gh.one(number)
        if latest is None or not latest["open"] or latest["body"] != fresh["body"]:
            return ["skipped, because its description changed while this run worked on it: the next run "
                    "looks again"]
        where = ", ".join(str(line.index + 1) for line, _, _ in sorted(changes, key=lambda change: change[0].index))
        gh.describe(number, body, f"(change line {where} of the description)")
        for line, box, note in sorted(changes, key=lambda change: change[0].index):
            said.append(verb + describe_change(line, box, note, known))
    if notes:
        # The label first: if a comment then fails, the next run sends it and finds the label there.
        if WAITING not in fresh["labels"]:
            gh.add_labels(number, [WAITING])
            said.append(f"{verb}add `{WAITING}`")
        for other in notes:
            gh.comment(number, message(other))
            said.append(f"{verb}tell it that {known[other].why}")
    return said


def sync(gh, number=None, closed=None):
    """Tick and tell on one pull request (`number`), on the open pull requests whose description
    names one that was just closed (`closed`), or on every open pull request. Returns a log."""
    log, known, counts = [], {}, {"changed": 0, "told": 0}
    # Compares and the batches being built are read at most once a run.
    gh._compares, gh._built = {}, None
    try:
        if number is not None:
            main, found = gh.one(number)
            if found is None:
                raise Refused(f"There is no pull request #{number} in {gh.repo}.")
            if not found["open"]:
                return [f"#{number}: nothing to change, because it is closed"]
            everyone, targets = None, [found]
        else:
            main, everyone = gh.everything()
            targets = [pr for _, pr in sorted(everyone.items())
                       if any(line.numbers for line in _dependencies.declarations(pr["body"], gh.repo))]
            if closed is not None:
                targets = [pr for pr in targets if closed in _dependencies.dependencies(pr["body"], gh.repo)]
                if targets:
                    log.append(f"open pull requests that depend on #{closed}: "
                               + ", ".join(f"#{pr['number']}" for pr in targets))
    except Stopped as error:
        return log + [f"{error}: stopped, and the next run carries on"]
    try:
        # Everything named at once: a hundred pull requests to a query, and each compared once. If
        # that fails, each pull request's own are looked up as it comes, so that one description
        # cannot stop the rest.
        try:
            resolve(gh, main, sorted({other for pr in targets for other in wanted(pr, gh.repo)}), known)
        except RuntimeError as error:
            log.append(f"could not look up every dependency at once, so each pull request's are looked up "
                       f"on their own: {error}")
        for pr in targets:
            try:
                said = handle(gh, main, pr, known)
            except RuntimeError as error:
                # One pull request that cannot be read or written should not hold up the rest.
                gh.failed = True
                log.append(f"#{pr['number']}: skipped, because {error}")
                continue
            if said:
                log.append(f"#{pr['number']}: " + "; ".join(said))
                counts["changed"] += sum(phrase.startswith(prefix) for phrase in said
                                         for prefix in ("tick", "untick", "mark", "would tick", "would untick",
                                                        "would mark"))
                counts["told"] += any(phrase.startswith(("tell", "would tell")) for phrase in said)
            elif number is not None:
                log.append(f"#{pr['number']}: nothing to change, because {idle(pr, gh.repo, known)}")
    except Stopped as error:
        log.append(f"{error}: stopped, and the next run carries on")
    except RuntimeError as error:
        gh.failed = True
        log.append(f"stopped, because {error}")
    if everyone is not None:
        would = "would be " if gh.dry_run else ""
        which = f"depend on #{closed}" if closed is not None else "declare dependencies"
        log.append(f"{len(targets)} of {len(everyone)} open pull requests {which}; {counts['changed']} lines "
                   f"{would}ticked, marked or unticked; {counts['told']} pull requests {would}told about a "
                   "dependency closed without landing")
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    which = parser.add_mutually_exclusive_group()
    which.add_argument("--pr", type=int, help="look at this pull request only")
    which.add_argument("--closed", type=int, help="look at the open pull requests that depend on this one")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    started, failure = time.monotonic(), None
    try:
        log = sync(gh, args.pr, args.closed)
        failure = 1 if gh.failed else None
    except (Refused, RuntimeError) as error:
        log, failure = [str(error)], 1
    left = f"; {gh.remaining} left this hour" if gh.remaining is not None else ""
    log.append(f"{time.monotonic() - started:.0f} s; {gh.calls} REST requests{left}; {gh.queries} GraphQL "
               f"queries costing {gh.points} points; {gh.wrote} {'writes that a real run would make' if gh.dry_run else 'writes'}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as file:
            file.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
