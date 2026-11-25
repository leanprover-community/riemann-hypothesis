#!/usr/bin/env python3
"""Tick the `depends on` boxes in open pull requests' descriptions once the dependency has landed.

The dependencies workflow runs this from its trusted checkout: for the open pull requests whose
description names a pull request that was just closed, merged or not; for one pull request when
it is opened or reopened or its description is edited, since what it depends on may have landed
already; and for every open pull request every hour. Nothing from a pull request is checked out
or run. `pr-dependencies.py` says which lines declare a dependency, such as
`- [ ] depends on: #123`.

A pull request has landed when it was merged, or when it was closed and its head commit is in
main. The second covers one whose commits landed through a batch, or through the pull request
that depends on it, and that was closed rather than marked merged. One compare request answers
that: main is `ahead_by` nothing on the head when the head is in main.

A line's box is ticked, `[ ]` becoming `[x]`, once every pull request it names has landed. Only
that one character changes: the rest of the description stays as it was, byte for byte, line
endings included. Nothing is ever unticked, and lines without a box, lines in code or comments
and pull requests of other repositories are left alone. The description is read again just
before it is written, the ticks are made on that fresh copy, and nothing is written if they
change nothing, so an author's edit made at the same time is lost only if it falls in those
few seconds.

A pull request named on a line that is not ticked may have been closed without landing. Its box
then stays empty, and the pull request that depends on it is labelled `awaiting-author` and sent
a comment: its branch probably still carries the closed pull request's changes, so its author
should merge main and take them out, or take over the work, then edit the description and
comment `ready`. A hidden marker in the comment names the closed pull request, so it is sent
once for each. Nothing is said about a dependency that is still open.

Pull requests and their descriptions are read through GitHub's GraphQL API, whose allowance is
separate from the 1,000 REST requests an hour that the workflow's token shares with every other
workflow here. What each named pull request is, merged, closed or open and with which head, is
read once a run. REST is used for the compare, once a run for each closed pull request that was
not merged, and to write. Writes are spaced a second apart, the run stops when few REST requests
are left this hour, and the next run carries on. A write counts as done only once GitHub has
accepted it.
"""
from __future__ import annotations

import argparse
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
WAITING = _labels.WAITING
# How GraphQL names the workflow's own account, which REST calls github-actions[bot].
BOT = _rest.GRAPHQL_BOT
# Stop when fewer REST requests than this are left for the hour (see `github-rest.py`).
RESERVE = _rest.RESERVE
# Hidden at the start of the comment sent about a dependency closed without landing.
MARKER = "<!-- dependency-ticks-closed {number} -->"
TOLD = re.compile(r"<!-- dependency-ticks-closed (\d+) -->")

# What becomes of a pull request named on a line, and how the log says it.
LANDED, OPEN, DROPPED, UNKNOWN, MISSING = "landed", "open", "dropped", "unknown", "missing"

FIELDS = "number state body labels(first: 100) { nodes { name } }"
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
# Issues and pull requests by number. `%s` is a list of `p123: issueOrPullRequest(number: 123)
# { ... }`, so that a number that is an issue is not an error.
STATES = """query($owner: String!, $name: String!) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) { %s }
}"""
STATE = "__typename ... on PullRequest { number state headRefOid }"
COMMENTS = _rest.COMMENTS


Refused = _rest.Refused


class Stopped(Exception):
    """Few REST requests are left this hour: the run stops, and the next one carries on."""


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with the queries this script reads pull
    requests with."""

    def check(self):
        """Stop if the hour's allowance is nearly used up."""
        if self.remaining is None:
            self.rate_limit()
        if self.short():
            raise Stopped(f"only {self.remaining} REST requests left this hour")

    # Reading.

    def everything(self):
        """The default branch, and every open pull request as {number: pull request}."""
        found, after = {}, None
        while True:
            data = self.graphql(EVERY, owner=self.owner, name=self.name, after=after)["repository"]
            page = data["pullRequests"]
            for node in page["nodes"]:
                found[node["number"]] = pull(node)
            if not page["pageInfo"]["hasNextPage"]:
                return data["defaultBranchRef"]["name"], found
            after = page["pageInfo"]["endCursor"]

    def one(self, number):
        """The default branch, and pull request `number`, open or not, or None if there is none."""
        data = self.graphql(ONE, missing=True, owner=self.owner, name=self.name, number=number)["repository"]
        node = data["pullRequest"]
        return data["defaultBranchRef"]["name"], (pull(node) if node else None)

    def states(self, numbers):
        """What each of these numbers is, a hundred to a query, as {number: (state, head commit)}.
        The state is GraphQL's `OPEN`, `CLOSED` or `MERGED`, or None for an issue or a number
        that names nothing."""
        found = {}
        for start in range(0, len(numbers), 100):
            chunk = numbers[start:start + 100]
            parts = " ".join(f"p{number}: issueOrPullRequest(number: {int(number)}) {{ {STATE} }}" for number in chunk)
            data = self.graphql(STATES % parts, missing=True, owner=self.owner, name=self.name)["repository"]
            for number in chunk:
                node = data.get(f"p{number}") or {}
                if node.get("__typename") == "PullRequest":
                    found[number] = (node["state"], node.get("headRefOid") or "")
                else:
                    found[number] = (None, "")
        return found

    def in_main(self, main, head):
        """Whether commit `head` is in branch `main`, or None if GitHub does not know the commit."""
        status, found = self.call("GET", f"compare/{quoted(main)}...{head}?per_page=1")
        if status == 404:
            return None
        if status != 200 or not isinstance(found, dict) or "ahead_by" not in found:
            raise RuntimeError(f"GET compare/{main}...{head} answered {status}")
        return found["ahead_by"] == 0

    def told(self, number):
        """The pull requests that pull request `number` has been sent this script's comment about."""
        return self.marked(number, TOLD)

    def describe(self, number, body, shown):
        status, _ = self.write("PATCH", f"pulls/{number}", {"body": body}, shown)
        if status not in (0, 200):
            raise RuntimeError(f"could not edit the description of #{number}: {status}")


def pull(node):
    """What this script needs to know about a pull request, from GraphQL's answer."""
    return {"number": node["number"], "open": node.get("state", "OPEN") == "OPEN", "body": node.get("body") or "",
            "labels": {label["name"] for label in (node.get("labels") or {}).get("nodes", [])}}


# ---------------------------------------------------------------------------------------------
# Deciding.


def wanted(pr, repo):
    """The pull requests whose fate decides what happens to `pr`: those named on its lines that
    are not ticked yet, as a sorted list."""
    return sorted({number for line in _dependencies.declarations(pr["body"], repo) if not line.ticked
                   for number in line.numbers})


def resolve(gh, main, numbers, known):
    """Find out what became of each of `numbers` that is not in `known` yet, and record it there as
    {number: (fate, why)}, where fate is LANDED, OPEN, DROPPED, UNKNOWN or MISSING.

    Each pull request that was closed without being merged is compared with `main`, which takes a
    REST request. Raises Stopped when few of those are left this hour.
    """
    new = sorted(set(numbers) - set(known))
    if not new:
        return
    closed = []
    for number, (state, head) in sorted(gh.states(new).items()):
        if state is None:
            known[number] = (MISSING, f"#{number} is not a pull request")
        elif state == "MERGED":
            known[number] = (LANDED, f"#{number} was merged")
        elif state == "OPEN":
            known[number] = (OPEN, f"#{number} is open")
        elif not head:
            known[number] = (UNKNOWN, f"#{number} was closed, and GitHub names no head commit for it")
        else:
            closed.append((number, head))
    for number, head in closed:
        gh.check()
        found = gh.in_main(main, head)
        if found is None:
            known[number] = (UNKNOWN, f"#{number} was closed, and GitHub no longer has its head commit")
        elif found:
            known[number] = (LANDED, f"#{number} was closed, and its head is in `{main}`")
        else:
            known[number] = (DROPPED, f"#{number} was closed without landing")


def plan(pr, repo, known):
    """What to change on an open pull request, given `known` (see `resolve`): (the description with
    every line ticked whose pull requests have all landed, the Declarations ticked, and the pull
    requests named on lines not ticked that were closed without landing)."""
    landed = {number for number, (fate, _) in known.items() if fate == LANDED}
    body, ticked = _dependencies.tick(pr["body"], repo, landed)
    dropped = sorted({number for line in _dependencies.declarations(pr["body"], repo) if not line.ticked
                      for number in line.numbers if known.get(number, (None,))[0] == DROPPED})
    return body, ticked, dropped


def idle(pr, repo, known):
    """Why nothing changes on a pull request, for the log of a run for that pull request alone."""
    lines = _dependencies.declarations(pr["body"], repo)
    if not any(line.numbers for line in lines):
        return "its description declares no dependency"
    why = sorted({known[number][1] for line in lines if not line.ticked for number in line.numbers
                  if number in known and known[number][0] != LANDED})
    if not any(line.tickable for line in lines if line.numbers):
        why.insert(0, "no line that names a pull request has an empty box")
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
    """Tick what can be ticked in one open pull request's description, and tell it about the pull
    requests it depends on that were closed without landing. Returns what was done, as a list of
    phrases for the log, empty if nothing was."""
    number, repo = pr["number"], gh.repo
    resolve(gh, main, wanted(pr, repo), known)
    _, ticked, dropped = plan(pr, repo, known)
    if not (ticked or dropped):
        return []
    # The description may have been edited since it was read, perhaps minutes ago in a sweep. The
    # ticks are made on the copy read now, so that an edit made meanwhile is kept.
    _, fresh = gh.one(number)
    if fresh is None or not fresh["open"]:
        return ["skipped, because it was closed meanwhile"]
    resolve(gh, main, wanted(fresh, repo), known)
    body, ticked, dropped = plan(fresh, repo, known)
    told = gh.told(number) if dropped else set()
    notes = [other for other in dropped if other not in told]
    if not (ticked or notes):
        return []
    gh.check()
    verb, said = "would " if gh.dry_run else "", []
    if ticked:
        where = ", ".join(str(line.index + 1) for line in ticked)
        gh.describe(number, body, f"(tick line {where} of the description)")
        for line in ticked:
            why = ", ".join(known[other][1] for other in line.numbers)
            said.append(f"{verb}tick line {line.index + 1}, because {why}")
    if notes:
        # Asked once a run (see `github-rest.py`).
        if not gh.label_exists(WAITING):
            if not gh.dry_run:
                raise Refused(f"There is no `{WAITING}` label in {repo}. Was it renamed?")
            said.append(f"there is no `{WAITING}` label yet, so a real run would stop here")
        # The label first: if a comment then fails, the next run sends it and finds the label there.
        if WAITING not in fresh["labels"]:
            gh.add_labels(number, [WAITING])
            said.append(f"{verb}add `{WAITING}`")
        for other in notes:
            gh.comment(number, message(other))
            said.append(f"{verb}tell it that {known[other][1]}")
    return said


def sync(gh, number=None, closed=None):
    """Tick and tell on one pull request (`number`), on the open pull requests whose description
    names one that was just closed (`closed`), or on every open pull request. Returns a log."""
    log, known, counts = [], {}, {"ticked": 0, "told": 0}
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
    try:
        # Everything named at once: a hundred pull requests to a query, and each compared once.
        resolve(gh, main, sorted({other for pr in targets for other in wanted(pr, gh.repo)}), known)
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
                counts["ticked"] += sum(phrase.startswith(("tick", "would tick")) for phrase in said)
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
        log.append(f"{len(targets)} of {len(everyone)} open pull requests {which}; {counts['ticked']} lines "
                   f"{would}ticked; {counts['told']} pull requests {would}told about a dependency closed "
                   "without landing")
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


