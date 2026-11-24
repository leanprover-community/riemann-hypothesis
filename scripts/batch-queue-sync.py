#!/usr/bin/env python3
"""Assemble queued pull requests into a batch pull request and keep the labels in step.

The batch-queue workflow runs this from its trusted checkout. Everything goes through GitHub's
API: GitHub performs the merges, and nothing from a pull request is checked out or run here.

Which commit goes into a batch. A maintainer queues one commit of a pull request by commenting
`batch`: the commit that was its head when the comment was posted, or one named in the comment.
The workflow's label job records that commit in a comment of its own, and it is the only one a
batch takes. The `batch queue` label alone queues nothing, and commits pushed afterwards wait
for another `batch`.

A batch is a branch of this repository that this script started, normally with an open pull
request. Its name is `batch/` and the time it was started, such as `batch/2026-11-23-041230`,
with `-2` and so on after it when that name was taken. Other `batch/...` branches, such as one
a maintainer assembled by hand, are not batches here: nothing is merged into them, their pull
requests' text is left alone, and they are never deleted.

- Without the `building` label it is being assembled. Each queued commit is merged into it, and
  a pull request that GitHub cannot merge is told so in a comment.
- With the `building` label it is frozen. Nothing more is merged in, and the pull requests it
  contains swap `batch queue` for `building`. Later arrivals start a new batch.
- Once it is merged, the pull requests it contained lose `building`.
- If it is closed without being merged, they swap `building` back for `batch queue`.

A frozen batch that was merged or closed is found by its pull request, which keeps `building`
until this script has tidied up after it. Its branch may already have been deleted by then.

Taking a pull request out of the queue never changes a batch. Commits already merged into one
stay there, and the batch's description says so. No batch is ever rebuilt.

A pull request that is closed, whether merged or not, loses `batch queue` and `building`: it is
neither waiting for a build nor in one any more. A batch's own pull request is the exception,
because it keeps `building` until it has been tidied up after. When a pull request is reopened,
`batch queue` comes back if this workflow was the last to take a label off, and the pull request
was not taken out of the queue with `-batch` meanwhile. A label a person took off stays off.

The workflow's token may make 1,000 requests an hour, shared with every other workflow here. A
note in each batch pull request's text therefore remembers what was merged and which pull
requests were already looked at. The note is a cache: it is used only while the batch's head
and each pull request's update time are what they were, and everything in it can be read again
from the branch and the comments.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import re
import subprocess
import sys

QUEUED, BUILDING = "batch queue", "building"
PREFIX = "batch/"
# The name `start` gives a batch branch. Any other `batch/...` branch is not this script's.
OWN_BATCH = re.compile(r"batch/[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{6}(?:-[0-9]+)?")
BOT = "github-actions[bot]"
BUILD_WORKFLOW = "build-pr.yml"
# Stop early when fewer requests than this are left for the hour, so other workflows keep working.
RESERVE = 150
# What was read from a pull request is remembered only once the pull request has been quiet for
# this long. GitHub's update times are whole seconds, so two changes in one second look like one.
SETTLE = datetime.timedelta(seconds=120)

# Comments the workflow's label job leaves when a maintainer queues or unqueues a pull request.
# They count only at the very start of a comment written by the workflow itself.
APPROVED = re.compile(r"<!-- batch-queue-approved ([0-9a-f]{40}) -->")
WITHDRAWN = "<!-- batch-queue-withdrawn -->"
# Comments this script leaves on a pull request, each once.
REFUSAL = "<!-- batch-queue-refused {branch} {sha} -->"
MOVED = "<!-- batch-queue-moved {sha} -->"
STAYS = "<!-- batch-queue-stays {branch} -->"
# In a batch pull request's text: the part this script writes, and its note to itself.
BODY = "<!-- batch-queue -->"
STATE = re.compile(r"<!-- batch-queue-state (\{.*\}) -->")
# The merge commit that adds a pull request to a batch, and the name of a build run.
ADDED = re.compile(r"Add #(\d+) to the batch\n\nMerged at ([0-9a-f]{40})\.")
BUILD_RUN = re.compile(r"(?:Build PR|Proof shard) #(\d+)(?: |$)")


class Refused(Exception):
    """GitHub would not do something this script cannot work around."""


class GitHub:
    """The repository's REST API through `gh`. With `dry_run`, writes are printed, not sent."""

    def __init__(self, repo, dry_run=False):
        self.repo, self.dry_run = repo, dry_run
        self.calls, self.remaining = 0, None

    def call(self, method, path, payload=None):
        """One request. Returns (HTTP status, decoded body or None)."""
        args = ["gh", "api", "--include", "--method", method, f"repos/{self.repo}/{path}".rstrip("/")]
        data = None
        if payload is not None:
            args += ["--input", "-"]
            data = json.dumps(payload).encode()
        done = subprocess.run(args, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        head, _, body = done.stdout.decode("utf-8", "replace").replace("\r\n", "\n").partition("\n\n")
        try:
            status = int(head.split()[1])
        except (IndexError, ValueError):
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"no answer from GitHub for {method} {path}") from None
        self.calls += 1
        for line in head.splitlines()[1:]:
            name, _, value = line.partition(":")
            if name.strip().lower() == "x-ratelimit-remaining" and value.strip().isdigit():
                self.remaining = int(value)
        return status, (json.loads(body) if body.strip() else None)

    def get(self, path):
        status, data = self.call("GET", path)
        if status != 200:
            raise RuntimeError(f"GET {path} answered {status}")
        return data

    def pages(self, path):
        """Every item of a paginated list."""
        items, page = [], 1
        while True:
            batch = self.get(f"{path}{'&' if '?' in path else '?'}per_page=100&page={page}")
            items += batch
            if len(batch) < 100:
                return items
            page += 1

    def write(self, method, path, payload=None):
        if self.dry_run:
            print(f"would {method} {path} {json.dumps(payload) if payload else ''}".rstrip())
            return 0, None
        return self.call(method, path, payload)

    def short(self):
        """Whether the hour's allowance is nearly used up."""
        return self.remaining is not None and self.remaining < RESERVE

    def now(self):
        return datetime.datetime.now(datetime.timezone.utc)


def quoted(label):
    return label.replace(" ", "%20")


def open_pulls(gh):
    """Every open pull request, by number. Two requests cover a couple of hundred of them."""
    found = {}
    for info in gh.pages("pulls?state=open"):
        head = info["head"]
        found[info["number"]] = {
            "number": info["number"], "sha": head["sha"], "ref": head["ref"],
            "own": (head.get("repo") or {}).get("full_name") == gh.repo, "base": info["base"]["ref"],
            "labels": {label["name"] for label in info["labels"]},
            "updated": info["updated_at"], "body": info.get("body") or ""}
    return found


def own_batch(ref):
    """Whether a branch name is one `start` gives a batch."""
    return OWN_BATCH.fullmatch(ref) is not None


def is_batch(pr):
    return pr["own"] and own_batch(pr["ref"])


def relabel(gh, pr_or_number, add=None, remove=None):
    """Change labels on GitHub, and on our own copy of the pull request when we hold one."""
    number = pr_or_number["number"] if isinstance(pr_or_number, dict) else pr_or_number
    if add:
        gh.write("POST", f"issues/{number}/labels", {"labels": [add]})
    if remove:
        gh.write("DELETE", f"issues/{number}/labels/{quoted(remove)}")
    if isinstance(pr_or_number, dict):
        pr_or_number["labels"] = (pr_or_number["labels"] | ({add} if add else set())) - {remove}


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
    if any(marker in (comment.get("body") or "") for comment in comments if by_workflow(comment)):
        return False
    gh.write("POST", f"issues/{number}/comments", {"body": f"{marker}\n{text}\n"})
    return True


# ---------------------------------------------------------------------------------------------
# Batches.


def batches(gh, pulls):
    """The batches that can still be merged, as {ref, sha, number, frozen, body}, and the names of
    batch branches left behind by a pull request that was merged or closed.

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
        batch = {"ref": name, "sha": ref["object"]["sha"], "number": None, "frozen": False, "body": ""}
        if name in live:
            pr = live[name]
            batch.update(number=pr["number"], frozen=BUILDING in pr["labels"], body=pr["body"])
        elif gh.get(f"pulls?state=all&head={owner}:{name}"):
            leftover.append(name)
            continue
        found.append(batch)
    return found, leftover


def finished(gh, closed_building):
    """Frozen batches that were merged or closed and not yet tidied up after, with a `fate`.

    They are found by their pull requests, which keep `building` until `finish` is done with
    them. That works whether or not someone has already deleted the branch. `closed_building`
    is every closed issue or pull request that still carries `building`.
    """
    found = []
    for item in closed_building:
        if "pull_request" not in item or BODY not in (item.get("body") or ""):
            continue
        info = gh.get(f"pulls/{item['number']}")
        head = info["head"]
        if (head.get("repo") or {}).get("full_name") == gh.repo and own_batch(head["ref"]):
            found.append({"ref": head["ref"], "sha": head["sha"], "number": info["number"], "frozen": True,
                          "body": info.get("body") or "", "fate": "merged" if info.get("merged") else "closed"})
    return found


def added(gh, batch, main_sha, limit=400):
    """What this workflow merged into a batch, as {number: commit}, read from the branch itself.

    Follows first parents from the batch's head back to main. Commits a maintainer pushed on top
    are stepped over.
    """
    merged, sha = {}, batch["sha"]
    for _ in range(limit):
        commit = gh.get(f"git/commits/{sha}")
        match = ADDED.match(commit["message"])
        if match and len(commit["parents"]) == 2:
            merged.setdefault(match.group(1), match.group(2))
        elif not commit["parents"] or gh.get(f"compare/{main_sha}...{sha}?per_page=1")["ahead_by"] == 0:
            break
        sha = commit["parents"][0]["sha"]
    return merged


def recall(gh, batch, main_sha):
    """What is known about a batch: {"merged": {number: commit}, "refused": {...}, "seen": {...}}.

    `merged` and `refused` come from the note in the pull request's text when the note was
    written for the batch's present head. Otherwise `merged` is read again from the branch.
    """
    state = {"merged": {}, "refused": {}, "seen": {}}
    match = STATE.search(batch["body"])
    try:
        note = json.loads(match.group(1)) if match else {}
    except ValueError:
        note = {}
    if isinstance(note.get("seen"), dict):
        state["seen"] = note["seen"]
    if note.get("head") == batch["sha"] and isinstance(note.get("merged"), dict):
        state["merged"], state["refused"] = note["merged"], dict(note.get("refused") or {})
    else:
        state["merged"] = added(gh, batch, main_sha)
    return state


def describe(batch, state, members, also=(), refused=(), unapproved=()):
    """The text of a batch pull request."""
    lines = [BODY, "The batch-queue workflow assembles this pull request. When a maintainer comments "
             "`batch` on a pull request, the commit that was its head at that moment is merged in here."]
    if batch["frozen"]:
        lines.append(f"\nThis batch is frozen at `{batch['sha'][:10]}`. Nothing more is added to it, "
                     "and later `batch` comments start a new batch.")
    else:
        lines.append("\nCommenting `freeze` here, or starting a build of this pull request, freezes it: "
                     f"nothing more is added, and what it contains is relabelled `{BUILDING}`. "
                     "To be sure of the commit that gets built, comment `freeze` before starting the build.")
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
    lines += ["", f"<!-- batch-queue-state {json.dumps(note, sort_keys=True)} -->"]
    return "\n".join(lines) + "\n"


def publish(gh, batch, main, text):
    """Open the batch's pull request if it has none, and bring its text up to date."""
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


def start(gh, main, main_sha, now, log):
    """Create the branch for a new batch, under a name no other batch has."""
    stamp = (now or datetime.datetime.now(datetime.timezone.utc)).strftime("%Y-%m-%d-%H%M%S")
    status, data = None, None
    for name in [PREFIX + stamp] + [f"{PREFIX}{stamp}-{count}" for count in range(2, 6)]:
        status, data = gh.write("POST", "git/refs", {"ref": f"refs/heads/{name}", "sha": main_sha})
        if status in (0, 201):
            log.append(f"started `{name}` from `{main}`")
            return {"ref": name, "sha": main_sha, "number": None, "frozen": False, "body": ""}
        if status != 422:
            break
    raise Refused(f"GitHub would not create a batch branch ({status}: {(data or {}).get('message', 'no reason given')}).")


def frozen_now(gh, batch):
    """Whether a batch was frozen since this run began: by a comment, or by a build of it.

    A dispatched build freezes a batch through a job that has to wait for a runner. Looking for
    the build run itself closes most of that gap.
    """
    if not batch["number"]:
        return False
    if BUILDING in {label["name"] for label in gh.get(f"issues/{batch['number']}/labels")}:
        return True
    status, data = gh.call("GET", f"actions/workflows/{BUILD_WORKFLOW}/runs?event=workflow_dispatch&per_page=30")
    for run in (data or {}).get("workflow_runs", []) if status == 200 else []:
        match = BUILD_RUN.match(run.get("display_title") or "")
        if match and int(match.group(1)) == batch["number"]:
            relabel(gh, batch["number"], add=BUILDING)
            return True
    return False


# ---------------------------------------------------------------------------------------------
# One run.


def finish(gh, pulls, found, leftover, main_sha, closed_building, log):
    """Tidy up after batches that were merged or closed.

    Returns whether anything was queued again, and the numbers whose `building` was taken off.
    """
    requeued, cleared = False, set()
    frozen = [batch for batch in found if batch["frozen"]]
    elsewhere = {key for batch in frozen for key in recall(gh, batch, main_sha)["merged"]} if frozen else set()
    for batch in finished(gh, closed_building):
        cleared.add(batch["number"])
        for key in recall(gh, batch, main_sha)["merged"]:
            pr = pulls.get(int(key))
            if batch["fate"] == "merged":
                # A pull request that GitHub marked as merged is no longer in `pulls`.
                if pr is None or BUILDING in pr["labels"]:
                    relabel(gh, pr or int(key), remove=BUILDING)
                    cleared.add(int(key))
                    log.append(f"#{key} landed with batch #{batch['number']}: `{BUILDING}` removed")
            elif pr and BUILDING in pr["labels"] and key not in elsewhere:
                relabel(gh, pr, add=QUEUED, remove=BUILDING)
                requeued = True
                log.append(f"batch #{batch['number']} was closed without merging: #{key} is `{QUEUED}` again")
        # Taking the label off the batch itself marks it as dealt with.
        relabel(gh, batch["number"], remove=BUILDING)
        if batch["ref"] not in leftover:
            log.append(f"tidied up after batch #{batch['number']}; its branch was already gone")
    for name in leftover:
        gh.write("DELETE", f"git/refs/heads/{name}")
        log.append(f"removed the branch `{name}`")
    return requeued, cleared


def unlabel_closed(gh, closed_building, cleared, log):
    """Take `batch queue` and `building` off pull requests that were closed, merged or not.

    A pull request of a batch this script made keeps `building` for `finish`, which tells by it
    that the batch is still to be tidied up after. What `finish` already cleared is skipped.
    """
    closed_queued = gh.pages(f"issues?state=closed&labels={quoted(QUEUED)}")
    for label, items in ((QUEUED, closed_queued), (BUILDING, closed_building)):
        for item in items:
            number = item["number"]
            if "pull_request" not in item or BODY in (item.get("body") or ""):
                continue
            if label == BUILDING and number in cleared:
                continue
            relabel(gh, number, remove=label)
            log.append(f"#{number} is closed: `{label}` removed")


def reopened(gh, number):
    """Put `batch queue` back on a reopened pull request that lost it when it was closed.

    Only if this workflow was the last to take `batch queue` or `building` off, after the pull
    request was last closed, and no maintainer has taken it out of the queue with `-batch` since
    it was last queued. A label a person took off stays off. Whether the pull request then becomes
    `building` again is decided by the next sync, as for any other queued pull request.
    """
    info = gh.get(f"pulls/{number}")
    head = info["head"]
    if info["state"] != "open":
        return [f"#{number} is not open: nothing to put back"]
    if (head.get("repo") or {}).get("full_name") == gh.repo and head["ref"].startswith(PREFIX):
        return [f"#{number} holds a batch: nothing to put back"]
    if {label["name"] for label in info["labels"]} & {QUEUED, BUILDING}:
        return [f"#{number} already carries `{QUEUED}` or `{BUILDING}`"]
    events = gh.pages(f"issues/{number}/events")
    closed = [event["created_at"] for event in events if event.get("event") == "closed"]
    removed = [event for event in events if event.get("event") == "unlabeled"
               and (event.get("label") or {}).get("name") in (QUEUED, BUILDING)]
    if not closed or not removed or removed[-1]["created_at"] < closed[-1]:
        return [f"#{number} had no label taken off when it was closed: nothing to put back"]
    last = removed[-1]
    who = (last.get("actor") or {}).get("login") or "someone"
    if who != BOT:
        return [f"#{number}: `{last['label']['name']}` was taken off by {who}, so it stays off"]
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
    relabel(gh, number, add=QUEUED)
    return [f"#{number} was reopened: `{QUEUED}` put back"]


def sync(gh, now=None):
    """Bring batches and labels up to date. Returns lines saying what was done."""
    log = []
    main = gh.get("")["default_branch"]
    main_sha = gh.get(f"git/ref/heads/{main}")["object"]["sha"]
    pulls = open_pulls(gh)
    found, leftover = batches(gh, pulls)
    closed_building = gh.pages(f"issues?state=closed&labels={quoted(BUILDING)}")
    requeued, cleared = finish(gh, pulls, found, leftover, main_sha, closed_building, log)
    unlabel_closed(gh, closed_building, cleared, log)

    # A frozen batch hands `building` to what it contains.
    for batch in (item for item in found if item["frozen"]):
        state = recall(gh, batch, main_sha)
        members, also = [], []
        for key, sha in sorted(state["merged"].items(), key=lambda item: int(item[0])):
            pr = pulls.get(int(key))
            if pr and QUEUED in pr["labels"]:
                relabel(gh, pr, add=BUILDING, remove=QUEUED)
                log.append(f"#{key} is in the frozen batch #{batch['number']}: now `{BUILDING}`")
            if pr and BUILDING in pr["labels"]:
                members.append((int(key), sha))
            else:
                also.append((int(key), "no longer queued" if pr else "closed since it was merged in"))
        publish(gh, batch, main, describe(batch, state, members, also))

    if requeued:
        # Leave time to take the pull request that broke the build out of the queue first.
        log.append("not starting a new batch in this run: the next `batch` or `-batch` comment does")
        return log

    # The batch being assembled takes each commit a maintainer queued.
    assembling = sorted((item for item in found if not item["frozen"]), key=lambda item: item["ref"])
    batch = assembling[-1] if assembling else None
    state = recall(gh, batch, main_sha) if batch else {"merged": {}, "refused": {}, "seen": {}}
    members, refused, unapproved, stopped, before = [], [], [], False, len(log)
    queued = sorted((pr for pr in pulls.values() if QUEUED in pr["labels"] and not is_batch(pr) and pr["base"] == main),
                    key=lambda pr: pr["number"])
    for pr in queued:
        number, key = pr["number"], str(pr["number"])
        sha, comments = look(gh, pr, state["seen"])
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
            batch = start(gh, main, main_sha, now, log)
        # Look again before every merge: the batch may have been frozen a moment ago.
        if frozen_now(gh, batch):
            log.append(f"batch #{batch['number']} was frozen during this run: stopped adding to it")
            stopped = True
            continue
        message = f"Add #{number} to the batch\n\nMerged at {sha}."
        status, data = gh.write("POST", "merges", {"base": batch["ref"], "head": sha, "commit_message": message})
        if status == 201:
            batch["sha"] = data["sha"]
        if status in (0, 201, 204):
            state["merged"][key] = sha
            members.append((number, sha))
            log.append(f"{'would add' if gh.dry_run else 'added'} #{number} at `{sha[:10]}` to `{batch['ref']}`")
            continue
        reason = ("GitHub could not merge it with what is already there." if status == 409 else
                  f"GitHub refused the merge ({status}: `{(data or {}).get('message', 'no reason given')}`).")
        link = f"#{batch['number']}" if batch["number"] else f"`{batch['ref']}`"
        tell(gh, number, comments, REFUSAL.format(branch=batch["ref"], sha=sha),
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
        return log or ["nothing to do"]

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
        publish(gh, batch, main, describe(batch, state, members, also, refused, unapproved))
        if len(log) > before:
            log.append(f"batch pull request #{batch['number']} lists {len(members)} pull request(s)"
                       if batch["number"] else f"`{batch['ref']}` has no pull request yet")
    return log or ["nothing to do"]


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
    sys.exit(failure)


if __name__ == "__main__":
    main()
