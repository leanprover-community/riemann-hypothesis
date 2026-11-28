#!/usr/bin/env python3
"""Keep the `batch-building` label on the open pull requests that are in a batch being built.

The batch building workflow runs this from its trusted checkout (see batch-building.yml). Nothing
from a pull request or a batch branch is checked out or run: everything is read from GitHub's API,
and the only things written are labels. Each run works everything out again from GitHub, so it
keeps no record of its own.

A batch is assembled by hand on a branch of this repository named `batch/...`, built from `main`,
with one merge commit for each pull request, which brings in that pull request's head commit. Its
own pull request then lands it on `main` through the merge queue. A `batch/...` branch is a batch
being built when:

- comparing it with `main` finds commits that `main` does not have (GitHub's compare answers
  `ahead` or `diverged`). A branch that shares no history with `main`, such as those from before
  `main` was replaced, is not a batch. One that `main` has all of (`behind` or `identical`) has
  landed.
- and its latest pull request is open. A branch whose latest pull request was merged or closed is
  not being built. A branch with no pull request yet is a batch that is about to be opened, unless
  it has been superseded: a batch is often pushed again under another name, and only the last
  gets a pull request. So it counts only while no batch branch has a pull request opened after its
  tip commit, and while its tip commit is less than UNOPENED old, so that a branch nobody opens a
  pull request for does not keep its labels for good. The time a pull request was opened is what
  counts, not its branch's tip: a batch being built that is pushed again, say with `main` merged
  in, supersedes nothing. The pull requests of branches deleted since count as well, as far as the
  latest RECENT pull requests of this repository go.

Only pull requests from the branch itself count, not those from a branch of the same name in a
fork.

An open pull request is in a batch being built when its head commit is one of the commits that
the batch has and `main` does not. A pull request that holds a batch is never in one (see
`holds_batch` in `batch-labels.py`). Every pull request in one gets the label, and every other
pull request that carries it, open or closed, loses it. This script changes no other label.

Comparing a branch with `main` reads 100 commits a REST request. The workflows share an hourly
allowance of REST requests, so the run stops before it falls below RESERVE, and the next run
carries on. A run that stops before it has compared every batch changes nothing, because it does
not yet know which pull requests are in one. Branches and pull requests are read through GraphQL,
whose allowance is separate.
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
from pathlib import Path
import sys
from urllib.parse import quote

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")

MEMBER = _labels.MEMBER
PREFIX = _labels.PREFIX
MAIN = "main"
# How long a batch branch with no pull request counts as being built, from its tip commit's
# committer date, if no batch is opened after it. A batch branch is pushed some minutes before its
# pull request is opened, between 6 and 25 so far: this is only a backstop.
UNOPENED = datetime.timedelta(hours=1)
# The latest pull requests of this repository read for batches opened from branches deleted since.
RECENT = 50
# The run stops before GitHub says fewer than this many REST requests are left this hour, leaving
# the allowance to the other workflows, and the rest to the next run.
RESERVE = 200
# Commits a request when comparing a branch with `main`: GitHub's most.
PAGE = 100
# Branches whose pull requests one GraphQL query reads.
CHUNK = 50

BRANCHES = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    refs(refPrefix: "refs/heads/%s", first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes { name target { oid ... on Commit { committedDate } } }
    }
  }
}""" % PREFIX
# The latest pull requests from a branch, by its name. A fork's branch of the same name answers
# too, so a few more than one are read.
HEADS = """pullRequests(headRefName: $h%d, first: 10, orderBy: {field: CREATED_AT, direction: DESC}) {
      nodes { number state createdAt headRepository { nameWithOwner } }
    }"""
RECENT_PULLS = """query($owner: String!, $name: String!, $count: Int!) {
  repository(owner: $owner, name: $name) {
    pullRequests(first: $count, orderBy: {field: CREATED_AT, direction: DESC}) {
      nodes { number createdAt headRefName headRepository { nameWithOwner } }
    }
  }
}"""
OPEN = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number headRefOid headRefName headRepository { nameWithOwner }
        labels(first: 100) { nodes { name } }
      }
    }
  }
}"""
LABELLED = """query($q: String!, $after: String) {
  search(query: $q, type: ISSUE, first: 100, after: $after) {
    pageInfo { hasNextPage endCursor }
    nodes { ... on PullRequest { number state } }
  }
}"""

Refused = _rest.Refused


class Short(Exception):
    """Too few REST requests are left this hour. The run stops, and the next one carries on."""


def when(text):
    return datetime.datetime.fromisoformat(text.replace("Z", "+00:00"))


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with what this script reads and writes.
    With `dry_run`, label changes are printed, not sent."""

    def spare(self):
        """Stop the run if GitHub last said that fewer than RESERVE REST requests are left."""
        if self.remaining is not None and self.remaining < RESERVE:
            raise Short(f"only {self.remaining} REST requests are left this hour")

    def branches(self):
        """Every `batch/...` branch, as {"name", "oid", "date"}, with `name` in full."""
        found, after = [], None
        while True:
            page = self.graphql(BRANCHES, owner=self.owner, name=self.name, after=after)
            page = page["repository"]["refs"]
            for node in page["nodes"]:
                target = node.get("target") or {}
                date = target.get("committedDate")
                found.append({"name": PREFIX + node["name"], "oid": target.get("oid"),
                              "date": when(date) if date else None})
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def latest_pulls(self, names):
        """The latest pull request from each branch of this repository named in `names`, as
        {"number", "state", "opened"}, by name. A branch without one is left out."""
        found = {}
        for start in range(0, len(names), CHUNK):
            chunk = names[start:start + CHUNK]
            query = "query($owner: String!, $name: String!, %s) {\n  repository(owner: $owner, name: $name) {\n%s\n  }\n}" % (
                ", ".join(f"$h{i}: String!" for i in range(len(chunk))),
                "\n".join(f"    p{i}: " + HEADS % i for i in range(len(chunk))))
            data = self.graphql(query, owner=self.owner, name=self.name,
                                **{f"h{i}": name for i, name in enumerate(chunk)})["repository"]
            for i, name in enumerate(chunk):
                ours = [node for node in data[f"p{i}"]["nodes"]
                        if _labels.holds_batch(self.repo, (node.get("headRepository") or {}).get("nameWithOwner"), name)]
                if ours:
                    found[name] = {"number": ours[0]["number"], "state": ours[0]["state"],
                                   "opened": when(ours[0]["createdAt"])}
        return found

    def recent_batches(self):
        """The pull requests holding a batch among the latest RECENT of this repository, as
        {"number", "opened"}, whether their branches still exist or not."""
        nodes = self.graphql(RECENT_PULLS, owner=self.owner, name=self.name, count=RECENT)
        return [{"number": node["number"], "opened": when(node["createdAt"])}
                for node in nodes["repository"]["pullRequests"]["nodes"]
                if _labels.holds_batch(self.repo, (node.get("headRepository") or {}).get("nameWithOwner"),
                                       node["headRefName"])]

    def compare(self, branch):
        """How `branch` compares with `main`: (GitHub's status, the commits it has that `main` does
        not), or (None, []) when they share no history or the branch is gone."""
        commits, page, status = [], 1, None
        while True:
            self.spare()
            path = f"compare/{_rest.quoted(MAIN)}...{quote(branch, safe='/')}?per_page={PAGE}&page={page}"
            code, data = self.call("GET", path)
            if code == 404:
                return None, []
            if code != 200:
                raise RuntimeError(f"comparing {branch} with {MAIN} answered {code}")
            status = data["status"]
            batch = [commit["sha"] for commit in data.get("commits") or []]
            commits += batch
            if len(batch) < PAGE or len(commits) >= data.get("total_commits", 0):
                return status, commits
            page += 1

    def open_pulls(self):
        """Every open pull request, as {"number", "head", "batch", "labels"}. `batch` says whether
        it holds a batch."""
        found, after = [], None
        while True:
            page = self.graphql(OPEN, owner=self.owner, name=self.name, after=after)
            page = page["repository"]["pullRequests"]
            for node in page["nodes"]:
                home = (node.get("headRepository") or {}).get("nameWithOwner")
                found.append({"number": node["number"], "head": node["headRefOid"],
                              "batch": _labels.holds_batch(self.repo, home, node["headRefName"]),
                              "labels": {label["name"] for label in node["labels"]["nodes"]}})
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def labelled(self):
        """The pull requests that GitHub's search finds with the label, in any state, as
        {number: state}. The search can be a little behind."""
        found, after = {}, None
        query = f'repo:{self.repo} is:pr label:"{MEMBER}"'
        while True:
            page = self.graphql(LABELLED, q=query, after=after)["search"]
            found.update({node["number"]: node["state"] for node in page["nodes"] if node})
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def label(self, number, add):
        """Put the label on pull request `number` or take it off. Returns whether anything was
        sent."""
        verb = "add" if add else "remove"
        if self.dry_run:
            print(f"would {verb} {MEMBER} on #{number}")
            return False
        self.spare()
        if add:
            status, _ = self.write("POST", f"issues/{number}/labels", {"labels": [MEMBER]})
        else:
            status, _ = self.write("DELETE", f"issues/{number}/labels/{_rest.quoted(MEMBER)}")
        # Taking off a label that someone else has just taken off answers 404.
        if status not in (200, 201) and not (status == 404 and not add):
            raise RuntimeError(f"could not {verb} {MEMBER} on #{number}: {status}")
        return True


def age(delta):
    minutes = max(0, int(delta.total_seconds() // 60))
    return f"{minutes // 60} h {minutes % 60} min" if minutes >= 60 else f"{minutes} min"


def batches(gh, now, log):
    """The batches being built, as {branch: set of the commits it has that `main` does not}."""
    branches = gh.branches()
    pulls = gh.latest_pulls([branch["name"] for branch in branches])
    # The batch opened last, which supersedes every branch without a pull request pushed before it.
    opened = list(pulls.values()) + gh.recent_batches()
    last = max(opened, key=lambda pull: pull["opened"]) if opened else None
    found = {}
    for branch in branches:
        name, pull = branch["name"], pulls.get(branch["name"])
        if pull and pull["state"] != "OPEN":
            log.append(f"{name}: not being built, because its pull request #{pull['number']} is "
                       f"{pull['state'].lower()}")
            continue
        if not pull:
            old = now - branch["date"] if branch["date"] else None
            if old is None or old >= UNOPENED:
                log.append(f"{name}: not being built, because it has no pull request and its tip "
                           f"commit is {age(old) + ' old' if old is not None else 'not dated'}")
                continue
            if last and last["opened"] > branch["date"]:
                log.append(f"{name}: not being built, because it has no pull request and batch pull "
                           f"request #{last['number']} was opened after its tip commit")
                continue
        status, commits = gh.compare(name)
        if status is None:
            log.append(f"{name}: not being built, because it shares no history with `{MAIN}`")
        elif status not in ("ahead", "diverged"):
            log.append(f"{name}: not being built, because `{MAIN}` has all of it")
        else:
            why = (f"pull request #{pull['number']} is open" if pull
                   else f"it has no pull request yet and its tip commit is {age(now - branch['date'])} old")
            log.append(f"{name}: being built, because {why}; {len(commits)} commits that `{MAIN}` "
                       f"does not have")
            found[name] = set(commits)
    return found


def sync(gh, now=None, log=None, changed=None):
    """Bring the label up to date on every pull request. Returns the log, the list `log` if one
    is given: what it holds when the run stops is what was done. The numbers of the open pull
    requests whose label was changed are appended to the list `changed`, if one is given."""
    log = [] if log is None else log
    changed = [] if changed is None else changed
    now = now or datetime.datetime.now(datetime.timezone.utc)

    # The first REST request also says how many are left this hour.
    exists = gh.label_exists(MEMBER)
    if not exists:
        if not gh.dry_run:
            raise Refused(f"There is no `{MEMBER}` label in {gh.repo}. Was it renamed?")
        log.append(f"there is no `{MEMBER}` label yet, so a real run would stop here")
    try:
        gh.spare()
        built = batches(gh, now, log)
    except Short as short:
        log.append(f"stopped before changing anything, because {short}: the next run carries on")
        return log

    pulls = gh.open_pulls()
    labelled = gh.labelled()
    adds, removes = [], []
    for pr in pulls:
        into = [] if pr["batch"] else sorted(name for name, commits in built.items() if pr["head"] in commits)
        has = MEMBER in pr["labels"]
        if into and not has:
            adds.append((pr["number"], f"its head commit is in {' and '.join(into)}"))
        elif has and not into:
            why = "it holds a batch" if pr["batch"] else "its head commit is in no batch being built"
            removes.append((pr["number"], why))
        pr["member"] = bool(into)
    members = sum(pr["member"] for pr in pulls)
    listed = {pr["number"] for pr in pulls}
    for number, state in sorted(labelled.items()):
        # An open pull request the list of open ones does not have was opened or closed while the
        # run read them: the next run looks at it again.
        if state != "OPEN" and number not in listed:
            removes.append((number, f"it is {state.lower()}"))

    left = len(adds) + len(removes)
    try:
        for (number, why), add in [(change, True) for change in adds] + [(change, False) for change in removes]:
            try:
                sent = gh.label(number, add)
            except RuntimeError as error:
                # One pull request that cannot be labelled should not hold up the rest.
                gh.failed = True
                log.append(f"#{number}: skipped, because {error}")
                left -= 1
                continue
            left -= 1
            if sent and number in listed:
                changed.append(number)
            log.append(f"#{number}: {'labelled' if add else 'no longer labelled'} `{MEMBER}`, because {why}")
    except Short as short:
        log.append(f"stopped, because {short}: {left} more pull requests need the label changed, and "
                   f"the next run carries on")
    log.append(f"{members} open pull requests are in a batch being built")
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    parser.add_argument("--changed", type=Path,
                        help="write the numbers of the open pull requests whose label changed to this file, one a line")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure, log, changed = None, [], []
    try:
        sync(gh, log=log, changed=changed)
        failure = 1 if gh.failed else None
    except (Refused, RuntimeError) as error:
        # Keep what was done before the stop.
        log.append(str(error))
        failure = 1
    left = f"; {gh.remaining} REST requests left this hour" if gh.remaining is not None else ""
    log.append(f"{gh.calls + gh.queries} requests to GitHub{left}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    if args.changed:
        args.changed.write_text("".join(f"{number}\n" for number in changed))
    sys.exit(failure)


if __name__ == "__main__":
    main()
