#!/usr/bin/env python3
"""Label the pull requests that conflict with main or with the batch being built.

The conflict-labels workflow runs this from its trusted checkout: for one pull request when it
is opened, reopened, pushed to, marked ready or edited, and for every open pull request when a
batch's pull request changes, when main moves on, and every half hour. Nothing from a pull
request is checked out or run. Pull requests are read through GitHub's GraphQL API, their
commits are fetched as git objects and compared with `git merge-tree`, and the only things
written to GitHub are labels and one kind of comment. The label names are in `batch-labels.py`.

Only an open pull request into main that is not a draft and not a batch can carry either label.
A batch is a pull request from a branch of this repository named `batch/...`.

`main-conflict`: GitHub reports that the pull request conflicts with main. While GitHub has not
yet worked that out, the label stays as it is. A pull request whose description says that it
depends on an open batch does not get the label, and loses it: it is expected to carry the
batch's changes, and so to conflict with main until the batch lands. That is a line such as
`- [ ] depends on: #123`, where #123 is the batch's pull request (`pr-dependencies.py` has the
forms such a line can take). There is no comment: GitHub already shows the conflict on the pull
request.

`batch-conflict`: the pull request conflicts with the head of an open batch labelled `building`.
A pull request labelled `batch-building` is in a batch, and does not get it. The comparison is
the one `batch-queue-conflicts.py` makes: git cannot merge a file that both change since they
left main, or one of the two deletes a Lean file that the other starts to import. Most pull
requests change no file that the batch changes, and need no trial merge. When the comparison
cannot be made, the label stays as it is. The first time a pull request gets the label for a
batch, it is also labelled `awaiting-author` and sent a comment that says what conflicts and
what to do. A hidden marker in the comment names the batch, so it is sent once for each batch.

Both labels come off as soon as their reason has gone, whoever put them on: the pull request was
fixed or closed, it joined the batch, or the batch was merged or closed. `awaiting-author` never
comes off here. Its author takes it off by commenting `ready`, or a maintainer does.

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
import subprocess
import sys
import tempfile
import time
from urllib.parse import quote


def _load(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_labels = _load("rh_batch_labels", "batch-labels.py")
# The trial merge and its helpers, as the batch queue uses them to compare queued pull requests.
_conflicts = _load("rh_batch_queue_conflicts", "batch-queue-conflicts.py")
# The parser for the `depends on` lines of a description, shared with `dependency-ticks.py`.
_dependencies = _load("rh_pr_dependencies", "pr-dependencies.py")
dependencies = _dependencies.dependencies
MAIN_CONFLICT, BATCH_CONFLICT = _labels.MAIN_CONFLICT, _labels.BATCH_CONFLICT
BUILDING, MEMBER, WAITING = _labels.BUILDING, _labels.MEMBER, _labels.WAITING
OURS = (MAIN_CONFLICT, BATCH_CONFLICT)
PREFIX = "batch/"
# How GraphQL names the workflow's own account, which REST calls github-actions[bot].
BOT = "github-actions"
# Stop writing when fewer REST requests than this are left for the hour, so other workflows keep
# working. The batch queue keeps the same reserve.
RESERVE = 150
# Seconds between two requests that change something. GitHub allows no more than 80 requests
# that create content a minute, and asks for a pause of a second between those that change
# anything.
PACE = 1.0
# GitHub works out whether a pull request conflicts with main in the background, after it is
# asked. Pull requests it has not worked out yet are read again this many times, this many
# seconds apart, after the git comparisons.
RETRIES, WAIT = 3, 15.0
# Hidden at the start of the comment sent to a pull request that conflicts with a batch.
MARKER = "<!-- conflict-labels-batch {number} -->"
TOLD = re.compile(r"<!-- conflict-labels-batch (\d+) -->")

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
COMMENTS = """query($owner: String!, $name: String!, $number: Int!, $after: String) {
  rateLimit { cost remaining }
  repository(owner: $owner, name: $name) {
    pullRequest(number: $number) {
      comments(first: 100, after: $after) {
        pageInfo { hasNextPage endCursor }
        nodes { body author { __typename login } }
      }
    }
  }
}"""
CLOSED = """query($main: String!, $batch: String!) {
  rateLimit { cost remaining }
  main: search(query: $main, type: ISSUE, first: 100) { nodes { ... on PullRequest { number } } }
  batch: search(query: $batch, type: ISSUE, first: 100) { nodes { ... on PullRequest { number } } }
}"""


class Refused(Exception):
    """Something is wrong with the repository that this script should not paper over."""


class GitHub:
    """GitHub's API through `gh`. With `dry_run`, writes are printed, not sent."""

    def __init__(self, repo, dry_run=False):
        self.repo, self.dry_run = repo, dry_run
        self.owner, _, self.name = repo.partition("/")
        self.calls, self.queries, self.points, self.writes = 0, 0, 0, 0
        self.remaining, self.changed, self.failed = None, None, False

    def run(self, args, payload=None):
        data = json.dumps(payload).encode() if payload is not None else None
        return subprocess.run(["gh", "api", *args], input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def call(self, method, path, payload=None):
        """One REST request. Returns (HTTP status, decoded body or None). Requests that change
        something are spaced PACE seconds apart."""
        if method != "GET":
            if self.changed is not None:
                time.sleep(max(0.0, self.changed + PACE - time.monotonic()))
            self.changed = time.monotonic()
        args = ["--include", "--method", method, f"repos/{self.repo}/{path}"]
        if payload is not None:
            args += ["--input", "-"]
        done = self.run(args, payload)
        self.calls += 1
        head, _, body = done.stdout.decode("utf-8", "replace").replace("\r\n", "\n").partition("\n\n")
        try:
            status = int(head.split()[1])
        except (IndexError, ValueError):
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"no answer from GitHub for {method} {path}") from None
        for line in head.splitlines()[1:]:
            name, _, value = line.partition(":")
            if name.strip().lower() == "x-ratelimit-remaining" and value.strip().isdigit():
                self.remaining = int(value)
        try:
            return status, (json.loads(body) if body.strip() else None)
        except json.JSONDecodeError:
            return status, None

    def write(self, method, path, payload=None):
        """A request that changes something, or with `dry_run` the line saying what it would be."""
        self.writes += 1
        if self.dry_run:
            print(f"would {method} {path} {json.dumps(payload) if payload else ''}".rstrip())
            return 200, None
        return self.call(method, path, payload)

    def graphql(self, query, **variables):
        done = self.run(["graphql", "--input", "-"], {"query": query, "variables": variables})
        self.queries += 1
        try:
            answer = json.loads(done.stdout)
        except json.JSONDecodeError:
            answer = None
        if not isinstance(answer, dict) or answer.get("errors") or done.returncode != 0:
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            found = (answer or {}).get("errors") if isinstance(answer, dict) else None
            raise RuntimeError(f"GraphQL query failed: {json.dumps(found) if found else 'no answer'}")
        self.points += ((answer["data"] or {}).get("rateLimit") or {}).get("cost", 0)
        return answer["data"]

    def rate_limit(self):
        """How many REST requests are left this hour. Asking does not use one up."""
        done = self.run(["rate_limit", "--jq", ".resources.core.remaining"])
        text = done.stdout.decode().strip()
        if done.returncode == 0 and text.isdigit():
            self.remaining = int(text)

    def short(self):
        """Whether the hour's allowance is nearly used up."""
        return self.remaining is not None and self.remaining < RESERVE

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

    def told(self, number):
        """The batches that pull request `number` has been sent this script's comment about."""
        found, after = set(), None
        while True:
            data = self.graphql(COMMENTS, owner=self.owner, name=self.name, number=number, after=after)
            page = data["repository"]["pullRequest"]["comments"]
            for comment in page["nodes"]:
                author = comment.get("author") or {}
                match = TOLD.match(comment.get("body") or "")
                if match and author.get("__typename") == "Bot" and author.get("login") == BOT:
                    found.add(int(match.group(1)))
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def closed_with_labels(self):
        """Closed pull requests that still carry one of the labels, as {label: [numbers]}."""
        query = f"repo:{self.repo} is:pr is:closed label:"
        data = self.graphql(CLOSED, main=query + MAIN_CONFLICT, batch=query + BATCH_CONFLICT)
        return {MAIN_CONFLICT: sorted(node["number"] for node in data["main"]["nodes"] if node),
                BATCH_CONFLICT: sorted(node["number"] for node in data["batch"]["nodes"] if node)}

    # Writing.

    def label_exists(self, name):
        status, _ = self.call("GET", f"labels/{quote(name, safe='')}")
        if status not in (200, 404):
            raise RuntimeError(f"GET labels/{name} answered {status}")
        return status == 200

    def add_labels(self, number, names):
        status, _ = self.write("POST", f"issues/{number}/labels", {"labels": sorted(names)})
        if status not in (200, 201):
            raise RuntimeError(f"could not label #{number}: {status}")

    def remove_label(self, number, name):
        status, _ = self.write("DELETE", f"issues/{number}/labels/{quote(name, safe='')}")
        # Taking off a label that someone else has just taken off answers 404.
        if status not in (200, 204, 404):
            raise RuntimeError(f"could not take `{name}` off #{number}: {status}")

    def comment(self, number, body):
        status, _ = self.write("POST", f"issues/{number}/comments", {"body": body})
        if status not in (200, 201):
            raise RuntimeError(f"could not comment on #{number}: {status}")


def pull(node, repo):
    """What this script needs to know about a pull request, from GraphQL's answer."""
    home = (node.get("headRepository") or {}).get("nameWithOwner") or ""
    return {
        "number": node["number"], "open": node.get("state", "OPEN") == "OPEN",
        "draft": node.get("isDraft", False), "ref": node.get("headRefName", ""),
        "own": home.lower() == repo.lower(), "sha": node.get("headRefOid", ""),
        "base": node.get("baseRefName", ""), "mergeable": node.get("mergeable", "UNKNOWN"),
        "body": node.get("body") or "", "labels": {label["name"] for label in (node.get("labels") or {}).get("nodes", [])},
    }


# ---------------------------------------------------------------------------------------------
# Deciding, from what is known about a pull request. Nothing here asks GitHub or git.


def is_batch(pr):
    return pr["own"] and pr["ref"].startswith(PREFIX)


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


def found_conflict(result):
    return result is not None and (result.kind == "conflict" or bool(result.stale))


def decide(pr, main, batches, results):
    """What the labels of a pull request should be.

    `pr["depends"]` holds the pull requests its description says it depends on (see
    `pr-dependencies.py`). `batches` is every open batch as {number: pull request}, and `results`
    the pull request's comparison with each one being built, as {batch number: Comparison, or None
    when it could not be made}. Returns {"main": wanted, "batch": wanted, "conflicts": {batch
    number: Comparison}, "why": {label: reason}}, where wanted is True or False, or None to leave
    the label as it is.
    """
    why = {}
    gone = unavailable(pr, main)
    if gone:
        return {"main": False, "batch": False, "conflicts": {}, "why": {MAIN_CONFLICT: gone, BATCH_CONFLICT: gone}}
    on = sorted(pr["depends"] & set(batches))
    if on:
        wanted_main, why[MAIN_CONFLICT] = False, f"it depends on the batch #{on[0]}"
    elif pr["mergeable"] == "CONFLICTING":
        wanted_main, why[MAIN_CONFLICT] = True, f"it conflicts with `{main}`"
    elif pr["mergeable"] == "MERGEABLE":
        wanted_main, why[MAIN_CONFLICT] = False, f"it merges into `{main}`"
    else:
        wanted_main, why[MAIN_CONFLICT] = None, "GitHub has not worked out whether it merges"

    building = sorted(number for number, batch in batches.items() if BUILDING in batch["labels"])
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
    return {"main": wanted_main, "batch": wanted_batch, "conflicts": conflicts, "why": why}


def needs_told(pr, decision, batches):
    """Whether to read a pull request's comments to see which batches it was told about.

    That is only needed when it is about to be told something: it conflicts with a batch, and
    either does not carry the label yet or more than one batch is being built.
    """
    building = [number for number, batch in batches.items() if BUILDING in batch["labels"]]
    return bool(decision["conflicts"]) and (BATCH_CONFLICT not in pr["labels"] or len(building) > 1)


def plan(pr, decision, told, batches):
    """The changes to make: (labels to add, labels to take off, [(batch number, comment)]).

    `told` is the set of batches the pull request was already sent a comment about, or None when
    it was not read because nothing new is to be said (see `needs_told`).
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
        f"1. Merge the batch's branch {branch} into your branch, or rebase onto it, and resolve the conflicts.",
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
        f"Or wait until #{batch['number']} has landed, then merge `main` into your branch and resolve the "
        "conflicts there.",
        "",
        f"This pull request is labelled `{BATCH_CONFLICT}` and `{WAITING}` meanwhile. `{BATCH_CONFLICT}` comes "
        "off by itself once the conflict is gone or the batch has landed or been closed. "
        "This compares text, and new imports against deleted Lean files: a pull request that passes both "
        "can still fail to build with the batch.",
    ]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------------------------
# Comparing pull requests with the batches being built, in a clone without file contents.


def compare_all(repo, main, building, candidates, log, *, origin=None):
    """Compare each of `candidates` with each batch in `building` (both {number: pull request}).

    Returns {pull request number: {batch number: Comparison, or None if it could not be made}}.

    One fetch brings main and every head involved, as commits and trees without file contents.
    What each pull request changes since it left main is compared with what the batch changes
    since it did, and only pull requests that change a file the batch changes too are merged on
    trial. Before that, one more fetch brings the file contents that the check for deleted
    imports reads.
    """
    git, merge_base = _conflicts.git, _conflicts.merge_base
    origin = origin or f"https://github.com/{repo}.git"
    results = {number: {} for number in candidates}
    with tempfile.TemporaryDirectory() as work:
        started = time.monotonic()
        git(work, "init", "--quiet")
        git(work, "remote", "add", "origin", origin)
        trunk = f"refs/remotes/origin/{main}"
        numbers = sorted(set(building) | set(candidates))
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
        pairs = {}
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
                elif git(work, "merge-base", "--is-ancestor", base, trunk, ok=(0, 1))[0] == 0:
                    pairs[number, batch] = (base, (fork, head), sides[batch])
                else:
                    pairs[number, batch] = (base, (base, head), (base, sides[batch][1]))

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


# ---------------------------------------------------------------------------------------------
# Putting it together.


def sync(gh, number=None, compare=compare_all):
    """Bring both labels up to date on one pull request, or on every open one. Returns a log."""
    log, checked = [], {}
    if number is None:
        main, pulls = gh.everything()
        targets = sorted(pulls)
    else:
        main, pulls = gh.one(number)
        targets = [number]
    for pr in pulls.values():
        pr["depends"] = dependencies(pr["body"], gh.repo)
    batches = {key: pr for key, pr in pulls.items() if pr["open"] and is_batch(pr)}
    building = {key: pr for key, pr in batches.items() if BUILDING in pr["labels"]}
    candidates = {key: pulls[key] for key in targets if comparable(pulls[key], main)}
    if building:
        log.append("being built: " + ", ".join(f"#{key} (`{pr['ref']}`)" for key, pr in sorted(building.items())))
    results = {}
    if building and candidates:
        try:
            results = compare(gh.repo, main, building, candidates, log)
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

    decisions = {key: decide(pulls[key], main, batches, results.get(key, {})) for key in targets}
    stopped = False
    for key in targets:
        pr, decision = pulls[key], decisions[key]
        try:
            told = gh.told(key) if needs_told(pr, decision, batches) else None
            add, remove, notes = plan(pr, decision, told, batches)
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
            for label in sorted(add):
                if label not in checked:
                    checked[label] = gh.label_exists(label)
                if not checked[label]:
                    if not gh.dry_run:
                        raise Refused(f"There is no `{label}` label in {gh.repo}. Was it renamed?")
                    log.append(f"there is no `{label}` label yet, so a real run would stop here")
            for batch, text in notes:
                gh.comment(key, text)
            if add:
                gh.add_labels(key, add)
            for label in sorted(remove):
                gh.remove_label(key, label)
            pr["labels"] = (pr["labels"] | add) - remove
            verb = "would " if gh.dry_run else ""
            said = [f"{verb}add `{label}`, because {decision['why'].get(label, 'it is told about a batch')}"
                    for label in sorted(add)]
            said += [f"{verb}take `{label}` off, because {decision['why'][label]}" for label in sorted(remove)]
            said += [f"{verb}tell it about the batch #{batch}" for batch, _ in notes]
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
                    gh.remove_label(key, label)
                    log.append(f"#{key}: {'would take' if gh.dry_run else 'took'} `{label}` off, because it is closed")
        except RuntimeError as error:
            gh.failed = True
            log.append(f"closed pull requests: skipped, because {error}")
    if number is None:
        for label in OURS:
            having = [key for key in targets if label in pulls[key]["labels"]]
            log.append(f"{len(having)} of {len(targets)} open pull requests "
                       f"{'would carry' if gh.dry_run else 'carry'} `{label}`"
                       + (": " + ", ".join(f"#{key}" for key in having) if having else ""))
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", type=int, help="look at this pull request only")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    started, failure = time.monotonic(), None
    try:
        log = sync(gh, args.pr)
        failure = 1 if gh.failed else None
    except (Refused, RuntimeError) as error:
        log, failure = [str(error)], 1
    left = f"; {gh.remaining} left this hour" if gh.remaining is not None else ""
    log.append(f"{time.monotonic() - started:.0f} s; {gh.calls} REST requests{left}; {gh.queries} GraphQL "
               f"queries costing {gh.points} points; {gh.writes} {'writes that a real run would make' if gh.dry_run else 'writes'}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
