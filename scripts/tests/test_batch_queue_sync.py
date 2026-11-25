#!/usr/bin/env python3
"""Batch assembly checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "batch-queue-sync.py"
WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "batch-queue.yml"
spec = importlib.util.spec_from_file_location("batch_queue_sync", SCRIPT)
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)

REPO = "o/r"
NOW = datetime.datetime(2026, 11, 23, 4, 12, 30, tzinfo=datetime.timezone.utc)
# Where the stand-in's clock starts. Each change to a pull request moves it on by a second.
T0 = datetime.datetime(2026, 11, 23, 3, 0, 0, tzinfo=datetime.timezone.utc)
FIRST = "batch/2026-11-23-041230"
QUEUED, BUILDING, LATEST, BOT = batch.QUEUED, batch.BUILDING, batch.LATEST, batch.BOT
MEMBER, FROZEN, WAITING, CHANGED = batch.MEMBER, batch.FROZEN, batch.WAITING, batch.CHANGED
IN = {MEMBER, FROZEN}
# What the label job puts on a pull request it queues.
QF = {QUEUED, FROZEN}
PRIORITY = batch.PRIORITY


def sha(name):
    """A commit id for a made-up commit."""
    return hashlib.sha1(name.encode()).hexdigest()


def short(name):
    return sha(name)[:10]


MAIN = sha("main")



def setUpModule():
    # These tests are written for the conflict labels switched on, as they are once the
    # description check can say what a batch includes and the repository variable is set.
    # `ConflictLabelsOff` covers them off.
    global _conflicts_were, _variable
    _conflicts_were = batch._labels.CONFLICT_LABELS_ON
    batch._labels.CONFLICT_LABELS_ON = True
    _variable = mock.patch.dict(os.environ, {"CONFLICT_LABELS": "on"})
    _variable.start()


def tearDownModule():
    batch._labels.CONFLICT_LABELS_ON = _conflicts_were
    _variable.stop()


class Fake(batch.GitHub):
    """Just enough of the REST API. `inside` says which commits each commit contains."""

    def __init__(self, dry_run=False):
        super().__init__(REPO, dry_run)
        self.pulls, self.refs, self.comments, self.runs, self.events = {}, {}, {}, [], {}
        self.inside = {MAIN: set()}
        self.commits = {MAIN: {"message": "main", "parents": []}}
        self.conflicting, self.allow_pulls, self.writes, self.after_merge = set(), True, [], None
        # Commits that cannot be merged into a branch that already holds one of the others.
        self.clashes = {}
        self.reads = []
        self.clock, self.left, self.comment_ids = 0, None, 0
        # How long after the latest change a run happens. An hour: everything has settled.
        self.ahead = datetime.timedelta(hours=1)
        # Requests to answer badly: [method, pattern of the path, status or exception, times].
        self.failures = []
        # Labels GitHub does not have.
        self.missing = set()
        # Runs of the conflict-labels workflow started, by branch.
        self.dispatched = []

    def fail(self, method, pattern, answer, times=1):
        """Answer the next `times` requests matching with `answer`: a status, or an exception."""
        self.failures.append([method, pattern, answer, times])

    def now(self):
        return T0 + datetime.timedelta(seconds=self.clock) + self.ahead

    # Setting the scene.
    def add_pull(self, number, name, labels=(), ref=None, own=False, base="main"):
        head = sha(name)
        self.inside.setdefault(head, set())
        self.commits.setdefault(head, {"message": f"Work for {number}", "parents": [{"sha": MAIN}]})
        self.pulls[number] = {"number": number, "state": "open", "merged_at": None, "labels": set(labels),
                              "sha": head, "ref": ref or f"topic-{number}", "own": own, "base": base,
                              "body": "", "title": "", "updated": 0}
        self.touch(number)

    def touch(self, number):
        self.clock += 1
        self.pulls[number]["updated"] = self.clock

    def push(self, number, name):
        """The author pushes a new head."""
        head = sha(name)
        self.inside.setdefault(head, set())
        self.commits.setdefault(head, {"message": f"More work for {number}", "parents": [{"sha": MAIN}]})
        self.pulls[number]["sha"] = head
        self.touch(number)

    def stamp(self):
        return (T0 + datetime.timedelta(seconds=self.clock)).strftime("%Y-%m-%dT%H:%M:%SZ")

    def event(self, number, kind, login=BOT, **extra):
        self.events.setdefault(number, []).append(
            {"event": kind, "actor": {"login": login}, "created_at": self.stamp(), **extra})

    def label(self, number, add=None, remove=None, login=BOT):
        """A label goes on or comes off. The workflow's jobs act as BOT; pass `login` for a person."""
        labels = self.pulls[number]["labels"]
        self.pulls[number]["labels"] = (labels | ({add} if add else set())) - {remove}
        self.touch(number)
        if add and add not in labels:
            self.event(number, "labeled", login, label={"name": add})
        if remove and remove in labels:
            self.event(number, "unlabeled", login, label={"name": remove})

    def say(self, number, body, login=BOT):
        self.comment_ids += 1
        self.comments.setdefault(number, []).append({"id": self.comment_ids, "user": {"login": login}, "body": body})
        self.touch(number)
        return self.comment_ids

    def said(self, number):
        """What this script has said on a pull request, leaving out the label job's records."""
        return [item["body"] for item in self.comments.get(number, [])
                if not item["body"].startswith(("<!-- batch-queue-approved", "<!-- batch-queue-withdrawn"))]

    def close(self, number, merged=False, login="author"):
        self.pulls[number].update(state="closed", merged_at="2026-11-23T05:00:00Z" if merged else None)
        if merged:
            self.inside[MAIN] |= self.inside[self.pulls[number]["sha"]] | {self.pulls[number]["sha"]}
        self.touch(number)
        self.event(number, "closed", login)

    def reopen(self, number, login="author"):
        self.pulls[number].update(state="open", merged_at=None)
        self.touch(number)
        self.event(number, "reopened", login)

    def view(self, pr):
        return {"number": pr["number"], "state": pr["state"], "merged_at": pr["merged_at"],
                "labels": [{"name": name} for name in sorted(pr["labels"])],
                "head": {"sha": pr["sha"], "ref": pr["ref"], "repo": {"full_name": REPO if pr["own"] else "fork/r"}},
                "base": {"ref": pr["base"]}, "body": pr["body"], "title": pr["title"], "merged": bool(pr["merged_at"]),
                "draft": pr.get("draft", False),
                "updated_at": (T0 + datetime.timedelta(seconds=pr["updated"])).strftime("%Y-%m-%dT%H:%M:%SZ")}

    # Answering requests.
    def call(self, method, path, payload=None):
        self.calls += 1
        self.remaining = self.left
        for failure in self.failures:
            if failure[3] > 0 and failure[0] == method and re.fullmatch(failure[1], path):
                failure[3] -= 1
                if isinstance(failure[2], Exception):
                    raise failure[2]
                return failure[2], {"message": "refused"}
        if method != "GET":
            self.writes.append((method, path, payload))
        else:
            self.reads.append(path)
        for pattern, handler in self.routes:
            match = re.fullmatch(pattern, f"{method} {path}")
            if match:
                return handler(self, payload, *match.groups())
        raise AssertionError(f"unexpected request: {method} {path}")

    def _label(self, _, name):
        name = name.replace("%20", " ")
        return (404, {"message": "Not Found"}) if name in self.missing else (200, {"name": name})

    def _repo(self, _):
        return 200, {"default_branch": "main"}

    def _open(self, _):
        return 200, [self.view(pr) for pr in self.pulls.values() if pr["state"] == "open"]

    def _pull(self, _, number):
        if int(number) not in self.pulls:
            return 404, {"message": "Not Found"}
        return 200, self.view(self.pulls[int(number)])

    def _closed_with(self, label):
        return 200, [{"number": pr["number"], "pull_request": {}, "body": pr["body"],
                      "labels": [{"name": name} for name in sorted(pr["labels"])]}
                     for pr in self.pulls.values() if pr["state"] == "closed" and label in pr["labels"]]

    def _closed_building(self, _):
        return self._closed_with(BUILDING)

    def _closed_queued(self, _):
        return self._closed_with(QUEUED)

    def _closed_members(self, _):
        return self._closed_with(MEMBER)

    def _closed_frozen(self, _):
        return self._closed_with(FROZEN)

    def _events(self, _, number):
        return 200, list(self.events.get(int(number), []))

    def _refs(self, _):
        return 200, [{"ref": f"refs/heads/{name}", "object": {"sha": head}} for name, head in sorted(self.refs.items())]

    def _main(self, _):
        return 200, {"object": {"sha": MAIN}}

    def _pulls_for(self, _, name):
        return 200, [self.view(pr) for pr in self.pulls.values() if pr["ref"] == name and pr["own"]]

    def _commit(self, _, commit):
        return 200, self.commits[commit]

    def _compare(self, _, base, head):
        # The merge base: a commit both hold that main does not, if there is one.
        common = ({base} | self.inside[base]) & ({head} | self.inside[head]) - {MAIN} - self.inside[MAIN]
        return 200, {"ahead_by": 0 if head == base or head in self.inside[base] else 1,
                     "merge_base_commit": {"sha": min(common) if common else MAIN}}

    def _branch_commits(self, _, base, head, page):
        """The commits of `head` that the branch `base` does not have, a hundred a page, with the
        message and parents of those the stand-in knows."""
        under = self.refs.get(base, MAIN if base == "main" else base)
        commits = sorted(({head} | self.inside[head]) - ({under} | self.inside[under]))
        start = (int(page) - 1) * 100
        return 200, {"total_commits": len(commits), "commits": [
            {"sha": commit, **({"commit": {"message": self.commits[commit]["message"]},
                                "parents": self.commits[commit]["parents"]} if commit in self.commits else {})}
            for commit in commits[start:start + 100]]}

    def _comments(self, _, number):
        return 200, list(self.comments.get(int(number), []))

    def _labels(self, _, number):
        return 200, [{"name": name} for name in sorted(self.pulls[int(number)]["labels"])]

    def _dispatch(self, payload):
        # A real run: one started without `dry_run` is a dry run.
        assert payload["inputs"] == {"dry_run": "false"}, payload
        self.dispatched.append(payload["ref"])
        return 204, None

    def _runs(self, _):
        return 200, {"workflow_runs": [{"display_title": title} for title in self.runs]}

    def _new_ref(self, payload):
        name = payload["ref"][len("refs/heads/"):]
        if name in self.refs:
            return 422, {"message": "Reference already exists"}
        self.refs[name] = payload["sha"]
        return 201, {}

    def _merge(self, payload):
        base, head = self.refs[payload["base"]], payload["head"]
        if head in self.conflicting or self.clashes.get(head, set()) & (self.inside[base] | {base}):
            return 409, {"message": "Merge conflict"}
        if head == base or head in self.inside[base]:
            return 204, None
        merged = sha(f"merge of {head} into {base}")
        self.inside[merged] = self.inside[base] | self.inside[head] | {base, head}
        self.commits[merged] = {"message": payload["commit_message"], "parents": [{"sha": base}, {"sha": head}]}
        self.refs[payload["base"]] = merged
        for pr in self.pulls.values():
            if pr["own"] and pr["ref"] == payload["base"]:
                pr["sha"] = merged
                self.touch(pr["number"])
        if self.after_merge:
            self.after_merge()
        return 201, {"sha": merged}

    def _new_pull(self, payload):
        if not self.allow_pulls:
            return 403, {"message": "GitHub Actions is not permitted to create or approve pull requests."}
        number = max(self.pulls, default=0) + 100
        self.pulls[number] = {"number": number, "state": "open", "merged_at": None, "labels": set(),
                              "sha": self.refs[payload["head"]], "ref": payload["head"], "own": True, "base": "main",
                              "body": payload["body"], "title": payload["title"], "updated": 0}
        self.touch(number)
        return 201, {"number": number}

    def _edit_pull(self, payload, number):
        self.pulls[int(number)].update(payload)
        self.touch(int(number))
        return 200, {}

    def _add_label(self, payload, number):
        for name in payload["labels"]:
            self.label(int(number), add=name)
        return 200, []

    def _drop_label(self, _, number, name):
        name = name.replace("%20", " ")
        if name not in self.pulls[int(number)]["labels"]:
            return 404, {"message": "Label does not exist"}
        self.label(int(number), remove=name)
        return 200, []

    def _set_labels(self, payload, number):
        for name in sorted(self.pulls[int(number)]["labels"] - set(payload["labels"])):
            self.label(int(number), remove=name)
        for name in payload["labels"]:
            self.label(int(number), add=name)
        return 200, []

    def _comment(self, payload, number):
        return 201, {"id": self.say(int(number), payload["body"])}

    def _edit_comment(self, payload, comment_id):
        for number, comments in self.comments.items():
            for comment in comments:
                if comment["id"] == int(comment_id):
                    comment["body"] = payload["body"]
                    self.touch(number)
                    return 200, {}
        return 404, {"message": "Not Found"}

    def _reset_ref(self, payload, name):
        if name not in self.refs:
            return 422, {"message": "Reference does not exist"}
        self.refs[name] = payload["sha"]
        for pr in self.pulls.values():
            if pr["own"] and pr["ref"] == name:
                pr["sha"] = payload["sha"]
                self.touch(pr["number"])
        return 200, {}

    def _drop_ref(self, _, name):
        return (204, None) if self.refs.pop(name, None) else (422, {"message": "Reference does not exist"})

    routes = [
        (r"GET ", _repo),
        (r"GET labels/(.+)", _label),
        (r"GET pulls\?state=open&per_page=100&page=1", _open),
        (r"GET git/matching-refs/heads/batch/", _refs),
        (r"GET git/ref/heads/main", _main),
        (r"GET git/commits/(.+)", _commit),
        (r"GET pulls\?state=all&head=o:(.+)", _pulls_for),
        (r"GET pulls/(\d+)", _pull),
        (r"GET issues\?state=closed&labels=building&per_page=100&page=1", _closed_building),
        (r"GET issues\?state=closed&labels=batch%20queue&per_page=100&page=1", _closed_queued),
        (r"GET issues\?state=closed&labels=batch-building&per_page=100&page=1", _closed_members),
        (r"GET issues\?state=closed&labels=frozen&per_page=100&page=1", _closed_frozen),
        (r"GET issues/(\d+)/events\?per_page=100&page=1", _events),
        (r"GET compare/([^.]+)\.\.\.([^?]+)\?per_page=1", _compare),
        (r"GET compare/([^.]+)\.\.\.([^?]+)\?per_page=100&page=(\d+)", _branch_commits),
        (r"GET issues/(\d+)/comments\?per_page=100&page=1", _comments),
        (r"GET issues/(\d+)/labels", _labels),
        (r"GET labels/(.+)", _label),
        (r"GET actions/workflows/build-pr.yml/runs\?event=workflow_dispatch&per_page=30", _runs),
        (r"POST git/refs", _new_ref),
        (r"POST actions/workflows/conflict-labels\.yml/dispatches", _dispatch),
        (r"POST merges", _merge),
        (r"POST pulls", _new_pull),
        (r"PATCH pulls/(\d+)", _edit_pull),
        (r"POST issues/(\d+)/labels", _add_label),
        (r"DELETE issues/(\d+)/labels/(.+)", _drop_label),
        (r"PUT issues/(\d+)/labels", _set_labels),
        (r"POST issues/(\d+)/comments", _comment),
        (r"PATCH issues/comments/(\d+)", _edit_comment),
        (r"PATCH git/refs/heads/(.+)", _reset_ref),
        (r"DELETE git/refs/heads/(.+)", _drop_ref),
    ]


def queue(gh, *numbers):
    """A maintainer queues the head commit: the label job records it, then adds the label."""
    for number in numbers:
        if number not in gh.pulls:
            gh.add_pull(number, f"head{number}")
        gh.say(number, f"<!-- batch-queue-approved {gh.pulls[number]['sha']} -->\nApproved for batching at this commit.")
        gh.label(number, add=QUEUED)
        gh.label(number, add=FROZEN)


def clash(gh, *numbers):
    """The heads of these pull requests conflict: none can be merged where another one already is."""
    heads = {gh.pulls[number]["sha"] for number in numbers}
    for head in heads:
        gh.clashes[head] = heads - {head}


def unqueue(gh, number):
    """A maintainer comments `-batch`: the label job withdraws the commit, then removes the label."""
    gh.say(number, "<!-- batch-queue-withdrawn -->\nTaken out of the batch queue.")
    gh.label(number, remove=QUEUED)
    if MEMBER not in gh.pulls[number]["labels"]:
        gh.label(number, remove=FROZEN)


def batch_pull(gh, ref=FIRST):
    return next(pr for pr in gh.pulls.values() if pr["ref"] == ref)


def sync(gh, hours=0):
    return batch.sync(gh, NOW + datetime.timedelta(hours=hours))


def told(gh, number):
    """What this script has said on a pull request, other than that it is frozen."""
    return [body for body in gh.said(number) if not body.startswith("<!-- batch-queue-frozen")]


def note(record):
    """The note in this script's record comment on a batch assembled by hand, as the script reads it."""
    return batch.load_note(batch.BY_HAND.match(record).group(1))


def merges(gh):
    return [payload["head"] for method, path, payload in gh.writes if path == "merges"]


def assembling():
    """The code that assembles a batch of the queue's own, switched on, as it was before
    `ASSEMBLE`."""
    return mock.patch.object(batch, "ASSEMBLE", True)


class WithAssembly(unittest.TestCase):
    """Tests written while the sync assembled a batch of its own. `ASSEMBLE` now switches that
    off, and they run with it on, so that the code stays tested and can be revived."""

    def setUp(self):
        patch = assembling()
        patch.start()
        self.addCleanup(patch.stop)


class QueuedCommits(WithAssembly):
    """A batch takes the commit a maintainer queued, and nothing else."""

    def test_a_push_after_queuing_is_not_merged(self):
        gh = Fake()
        queue(gh, 11)
        gh.push(11, "head11-later")
        log = sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])
        self.assertNotIn(sha("head11-later"), gh.inside[gh.refs[FIRST]])
        self.assertIn(f"- #11 at `{short('head11')}`", batch_pull(gh)["body"])
        self.assertEqual(len(gh.said(11)), 1)
        self.assertIn(f"was queued at `{short('head11')}` and its head is now `{short('head11-later')}`", gh.said(11)[0])
        self.assertIn("told #11 that its head has moved since it was queued", log)
        # Later runs neither merge the new commit nor repeat the comment.
        gh.writes = []
        sync(gh)
        sync(gh)
        self.assertEqual((merges(gh), len(gh.said(11))), ([], 1))

    def test_a_push_after_being_merged_is_not_merged_either(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        gh.push(12, "head12-later")
        gh.writes = []
        sync(gh)
        self.assertEqual(merges(gh), [])
        self.assertIn(f"- #12 at `{short('head12')}`", batch_pull(gh)["body"])
        self.assertIn("Comment `batch` again to queue the new one.", gh.said(12)[0])

    def test_queuing_again_merges_the_new_commit(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        gh.push(11, "head11-later")
        queue(gh, 11)
        sync(gh)
        self.assertIn(sha("head11-later"), gh.inside[gh.refs[FIRST]])
        self.assertIn(f"- #11 at `{short('head11-later')}`", batch_pull(gh)["body"])

    def test_the_label_alone_queues_nothing(self):
        gh = Fake()
        queue(gh, 11)
        gh.add_pull(12, "head12", labels=[QUEUED])  # labelled by hand, for instance with the triage role
        log = sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])
        self.assertIn("Labelled `batch queue` but not queued, because no maintainer has commented `batch` on them: #12.",
                      batch_pull(gh)["body"])
        self.assertEqual(gh.said(12), [])
        self.assertEqual(gh.pulls[12]["labels"], {QUEUED})
        self.assertNotIn("left #12 out", " ".join(log))

    def test_with_nothing_queued_no_batch_is_started(self):
        gh = Fake()
        gh.add_pull(12, "head12", labels=[QUEUED])
        self.assertEqual(sync(gh), ["labelled `batch queue` but no commit of them is queued: #12"])
        self.assertEqual((gh.refs, gh.writes), ({}, []))

    def test_only_the_workflows_own_record_counts(self):
        gh = Fake()
        gh.add_pull(11, "head11", labels=[QUEUED])
        gh.add_pull(12, "head12", labels=[QUEUED])
        gh.add_pull(13, "head13", labels=[QUEUED])
        # Written by the author, not by the workflow.
        gh.say(11, f"<!-- batch-queue-approved {sha('head11')} -->", login="author")
        # Written by the workflow, but not at the start: a file name in a report, say.
        gh.say(12, f"Files in conflict: `<!-- batch-queue-approved {sha('head12')} -->`")
        # Not a full commit id.
        gh.say(13, "<!-- batch-queue-approved abc123 -->")
        sync(gh)
        self.assertEqual((merges(gh), gh.refs), ([], {}))

    def test_taking_it_out_withdraws_the_commit_even_if_the_label_comes_back(self):
        gh = Fake()
        queue(gh, 11, 12)
        unqueue(gh, 12)
        gh.label(12, add=QUEUED)  # put back by hand
        sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])
        self.assertIn("no maintainer has commented `batch` on them: #12.", batch_pull(gh)["body"])

    def test_a_record_that_arrives_within_the_same_second_is_not_missed(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        # The label is on, a run reads the comments, and the record lands without the pull
        # request's update time moving: all inside one second.
        gh.ahead = datetime.timedelta(0)
        gh.add_pull(12, "head12", labels=[QUEUED])
        sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])
        gh.comments.setdefault(12, []).append(
            {"user": {"login": BOT}, "body": f"<!-- batch-queue-approved {sha('head12')} -->"})
        sync(gh)
        self.assertEqual(merges(gh), [sha("head11"), sha("head12")])


class Assembling(WithAssembly):
    def test_first_batch_is_started_opened_and_lists_what_went_in(self):
        gh = Fake()
        queue(gh, 12, 11)
        log = sync(gh)
        self.assertEqual(list(gh.refs), [FIRST])
        opened = batch_pull(gh)
        self.assertEqual((opened["title"], opened["number"]), ("Batch 2026-11-23-041230", 112))
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`", opened["body"])
        self.assertTrue(opened["body"].startswith(batch.BODY))
        self.assertTrue({sha("head11"), sha("head12")} <= gh.inside[gh.refs[FIRST]])
        # Being in a batch that is still open to additions does not change a label.
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, QF))
        self.assertIn(f"added #11 at `{short('head11')}` to `{FIRST}`", log)

    def test_running_again_changes_nothing_more(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        head, gh.writes = gh.refs[FIRST], []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual((gh.refs, gh.writes), ({FIRST: head}, []))

    def test_new_arrival_joins_the_batch_being_assembled(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        queue(gh, 13)
        sync(gh, hours=1)
        self.assertEqual(list(gh.refs), [FIRST])
        self.assertIn(f"- #11 at `{short('head11')}`\n- #13 at `{short('head13')}`", batch_pull(gh)["body"])

    def test_commit_that_cannot_be_merged_is_left_out_and_told_once(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add(sha("head12"))
        log = sync(gh)
        body = batch_pull(gh)["body"]
        self.assertIn(f"- #11 at `{short('head11')}`", body)
        self.assertIn("Left out, because GitHub could not merge them into this branch: #12.", body)
        self.assertEqual(len(gh.said(12)), 1)
        self.assertIn(f"The commit `{short('head12')}` of this pull request was not added to the batch `{FIRST}`", gh.said(12)[0])
        self.assertIn("could not merge it with what is already there", gh.said(12)[0])
        self.assertEqual(gh.pulls[12]["labels"], QF)
        self.assertTrue(any(line.startswith("left #12 out") for line in log))
        # The same commit is not tried, or commented on, a second time.
        gh.writes = []
        sync(gh)
        sync(gh)
        self.assertEqual((len(gh.said(12)), merges(gh)), (1, []))
        self.assertIn("#12", batch_pull(gh)["body"])

    def test_refused_commit_is_not_announced_twice_when_the_note_is_lost(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add(sha("head12"))
        sync(gh)
        batch_pull(gh)["body"] = "A maintainer rewrote this description."
        sync(gh)
        self.assertEqual(len(gh.said(12)), 1)
        self.assertIn(f"- #11 at `{short('head11')}`", batch_pull(gh)["body"])

    def test_new_commit_queued_on_a_refused_pull_request_is_tried(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add(sha("head12"))
        sync(gh)
        gh.push(12, "head12-fixed")
        queue(gh, 12)
        sync(gh)
        self.assertIn(f"- #12 at `{short('head12-fixed')}`", batch_pull(gh)["body"])

    def test_other_bases_and_batch_pull_requests_are_not_queued(self):
        gh = Fake()
        gh.add_pull(11, "head11", base="release")
        queue(gh, 11)
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.refs, {})

    def test_refused_merge_reports_what_github_said(self):
        gh = Fake()
        queue(gh, 11)
        gh.routes = [(pattern, handler if pattern != "POST merges" else
                      (lambda self, payload: (403, {"message": "Resource not accessible by integration"})))
                     for pattern, handler in Fake.routes]
        sync(gh)
        self.assertIn("GitHub refused the merge (403: `Resource not accessible by integration`)", gh.said(11)[0])
        self.assertFalse([pr for pr in gh.pulls.values() if pr["own"]])

    def test_a_commit_merged_in_by_hand_under_the_same_message_counts(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        queue(gh, 13)
        before = gh.refs[FIRST]
        by_hand = sha("by hand")
        gh.commits[by_hand] = {"message": f"Add #13 to the batch\n\nMerged at {sha('head13')}.",
                               "parents": [{"sha": before}, {"sha": sha("head13")}]}
        gh.inside[by_hand] = gh.inside[before] | {before, sha("head13")}
        gh.refs[FIRST] = batch_pull(gh)["sha"] = by_hand
        gh.writes = []
        sync(gh)
        self.assertEqual(merges(gh), [])
        self.assertIn(f"- #11 at `{short('head11')}`\n- #13 at `{short('head13')}`", batch_pull(gh)["body"])


class BranchNames(WithAssembly):
    def test_a_name_already_taken_is_not_reused(self):
        gh = Fake()
        gh.refs[FIRST] = MAIN  # made a moment ago, after the batch branches were listed
        gh.routes = [(pattern, handler if pattern != "GET git/matching-refs/heads/batch/" else
                      (lambda self, _: (200, [])))
                     for pattern, handler in Fake.routes]
        queue(gh, 11)
        sync(gh)
        self.assertEqual(gh.refs[FIRST], MAIN)
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST + "-2"]])
        self.assertEqual(batch_pull(gh, FIRST + "-2")["number"], 111)

    def test_a_branch_that_cannot_be_created_stops_the_run(self):
        gh = Fake()
        queue(gh, 11)
        gh.routes = [(pattern, handler if pattern != "POST git/refs" else
                      (lambda self, payload: (403, {"message": "Resource not accessible by integration"})))
                     for pattern, handler in Fake.routes]
        with self.assertRaises(batch.Refused) as caught:
            sync(gh)
        self.assertIn("would not create a batch branch (403", str(caught.exception))
        self.assertEqual(merges(gh), [])


class Growing(WithAssembly):
    """The batch being assembled takes every queued commit while its pull request is open."""

    def test_a_build_of_it_does_not_stop_it(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        gh.runs = ["Build PR #111 manual", "Proof shard #111 manual"]
        queue(gh, 12)
        sync(gh)
        self.assertLessEqual({sha("head11"), sha("head12")}, gh.inside[gh.refs[FIRST]])
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"], gh.pulls[111]["labels"]),
                         (QF, QF, set()))
        self.assertFalse([path for path in gh.reads if path.startswith("actions/")])
        self.assertNotIn("freeze", gh.pulls[111]["body"])


class FinishedBatches(WithAssembly):
    def assembled(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        return gh

    def test_merged_its_branch_is_removed_and_what_landed_leaves_the_queue(self):
        gh = self.assembled()
        gh.push(12, "head12-later")  # so GitHub does not mark #12 merged along with the batch
        gh.close(11, merged=True)
        gh.close(112, merged=True)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (set(), set()))
        self.assertEqual(gh.pulls[12]["state"], "open")
        self.assertEqual(gh.refs, {})
        self.assertIn("#11 is closed: `batch queue` and `frozen` removed", log)
        self.assertIn("#12 landed with batch #112 at the commit that was queued: `batch queue` and `frozen` removed", log)
        self.assertIn(f"removed the branch `{FIRST}`", log)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_queued_again_at_a_new_commit_it_stays_in_the_queue(self):
        gh = self.assembled()
        gh.push(12, "head12-later")
        queue(gh, 12)
        gh.close(11, merged=True)
        gh.close(112, merged=True)
        sync(gh, hours=1)
        self.assertEqual(gh.pulls[12]["labels"], QF)
        newest = batch_pull(gh, "batch/2026-11-23-051230")
        self.assertIn(f"- #12 at `{short('head12-later')}`", newest["body"])

    def test_merged_after_its_branch_was_deleted_the_labels_still_come_off(self):
        gh = self.assembled()
        for number in (11, 12, 112):
            gh.close(number, merged=True)
        del gh.refs[FIRST]  # someone pressed "Delete branch" before this run
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (set(), set()))
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_closed_without_merging_what_it_held_stays_queued_for_the_next_batch(self):
        gh = self.assembled()
        gh.close(112)
        log = sync(gh, hours=1)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, QF))
        self.assertIn(f"removed the branch `{FIRST}`", log)
        self.assertEqual(list(gh.refs), ["batch/2026-11-23-051230"])
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`",
                      batch_pull(gh, "batch/2026-11-23-051230")["body"])

    def test_closed_after_its_branch_was_deleted_the_next_run_starts_again(self):
        gh = self.assembled()
        gh.close(112)
        del gh.refs[FIRST]
        sync(gh, hours=1)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, QF))
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`",
                      batch_pull(gh, "batch/2026-11-23-051230")["body"])

    def test_closing_a_batch_lets_the_next_run_start_again_without_what_left(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        unqueue(gh, 12)
        gh.close(112)
        sync(gh, hours=1)
        self.assertEqual(list(gh.refs), ["batch/2026-11-23-051230"])
        newest = batch_pull(gh, "batch/2026-11-23-051230")
        self.assertIn(f"- #11 at `{short('head11')}`", newest["body"])
        self.assertNotIn("#12", newest["body"])
        self.assertNotIn(sha("head12"), gh.inside[gh.refs["batch/2026-11-23-051230"]])


class LeavingTheQueue(WithAssembly):
    def test_commits_already_in_the_batch_stay_and_the_batch_says_so(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        head = gh.refs[FIRST]
        unqueue(gh, 12)
        gh.writes = []
        log = sync(gh)
        self.assertEqual(gh.refs, {FIRST: head})
        self.assertFalse([path for method, path, _ in gh.writes if path in ("merges", "git/refs") or method == "DELETE"])
        self.assertIn(f"In this batch:\n\n- #11 at `{short('head11')}`\n\nAlso in this branch:\n\n- #12, no longer queued",
                      gh.pulls[112]["body"])
        self.assertEqual(len(gh.said(12)), 1)
        self.assertIn("its commits were already merged into the batch #112 and are still there", gh.said(12)[0])
        self.assertIn("To build without them, close #112.", gh.said(12)[0])
        self.assertIn("told #12 that its commits stay in batch #112", log)
        # Told once, and nothing more happens on later runs.
        sync(gh)
        gh.writes = []
        sync(gh)
        self.assertEqual((len(gh.said(12)), gh.writes), (1, []))

    def test_left_before_being_merged_is_simply_gone(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.conflicting.add(sha("head12"))
        sync(gh)
        unqueue(gh, 12)
        sync(gh)
        self.assertNotIn("#12", gh.pulls[112]["body"])
        self.assertEqual(len(gh.said(12)), 1)  # only the earlier note that it could not be merged

    def test_commits_a_maintainer_pushed_on_top_do_not_hide_what_was_merged(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        before, fix = gh.refs[FIRST], sha("fix")
        gh.commits[fix] = {"message": "Repair the build after the merges", "parents": [{"sha": before}]}
        gh.inside[fix] = gh.inside[before] | {before}
        gh.refs[FIRST] = gh.pulls[112]["sha"] = fix
        unqueue(gh, 12)
        sync(gh)
        self.assertEqual(gh.refs, {FIRST: fix})
        self.assertIn(f"- #11 at `{short('head11')}`\n\nAlso in this branch:\n\n- #12, no longer queued", gh.pulls[112]["body"])


class OtherBatchBranches(WithAssembly):
    """A `batch/...` branch this script did not start, such as one assembled by hand, is left alone."""

    def by_hand(self, gh):
        gh.refs["batch/removals-2026-11-24"] = sha("removals")
        gh.refs["batch/combined-2026-11-24"] = sha("combined")  # no pull request
        gh.inside[sha("removals")] = gh.inside[sha("combined")] = set()
        gh.pulls[413] = {"number": 413, "state": "open", "merged_at": None, "labels": {"extra large"},
                         "sha": sha("removals"), "ref": "batch/removals-2026-11-24", "own": True, "base": "main",
                         "body": "Written by the maintainer who assembled it.", "title": "", "updated": 0}

    def test_queued_commits_go_to_a_batch_of_its_own(self):
        gh = Fake()
        self.by_hand(gh)
        queue(gh, 11)
        log = sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST]])
        self.assertIn(f"added #11 at `{short('head11')}` to `{FIRST}`", log)
        self.assertEqual(gh.pulls[413]["body"], "Written by the maintainer who assembled it.")
        self.assertEqual((gh.refs["batch/removals-2026-11-24"], gh.refs["batch/combined-2026-11-24"]),
                         (sha("removals"), sha("combined")))
        # No pull request is opened for the branch that has none.
        self.assertEqual([pr["ref"] for pr in gh.pulls.values() if pr["own"]], ["batch/removals-2026-11-24", FIRST])

    def test_with_nothing_queued_its_text_is_left_alone(self):
        gh = Fake()
        self.by_hand(gh)
        gh.add_pull(12, "head12", labels=[QUEUED])  # labelled by hand: queues nothing
        sync(gh)
        self.assertEqual(gh.pulls[413]["body"], "Written by the maintainer who assembled it.")
        self.assertEqual(gh.pulls[413]["labels"], {"extra large"})  # it holds no open pull request
        self.assertEqual([write for write in gh.writes if write[1] != "issues/12/labels"], [])

    def test_labelled_building_it_still_gets_nothing_merged_in_and_keeps_its_text(self):
        gh = Fake()
        self.by_hand(gh)
        gh.label(413, add=BUILDING, login="maintainer")  # though it holds no open pull request
        queue(gh, 11)
        sync(gh)
        self.assertEqual(gh.pulls[413]["body"], "Written by the maintainer who assembled it.")
        self.assertEqual(gh.refs["batch/removals-2026-11-24"], sha("removals"))
        # #11 is not in it, so it stays queued and goes to a batch of the workflow's own.
        self.assertEqual(gh.pulls[11]["labels"], QF)
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST]])
        self.assertIn("In this batch: nothing yet.", gh.said(413)[0])

    def test_its_branch_is_not_deleted_when_its_pull_request_is_closed(self):
        gh = Fake()
        self.by_hand(gh)
        gh.close(413, merged=True)
        sync(gh)
        self.assertIn("batch/removals-2026-11-24", gh.refs)
        self.assertNotIn(("DELETE", "git/refs/heads/batch/removals-2026-11-24", None), gh.writes)

    def test_a_batch_branch_of_a_fork_is_an_ordinary_pull_request(self):
        gh = Fake()
        gh.add_pull(15, "head15", ref="batch/mine")
        queue(gh, 15)
        log = sync(gh)
        self.assertEqual(merges(gh), [sha("head15")])
        self.assertIn(f"added #15 at `{short('head15')}` to `{FIRST}`", log)
        self.assertEqual(gh.pulls[15]["labels"], QF)


HAND = "batch/b4-on-896"


def by_hand(gh, *numbers, number=1018, ref=HAND, name="kim", body="Assembled by hand."):
    """A maintainer merges the heads of these pull requests into a branch and opens a pull request.
    Naming the pull request of another batch merges that batch's branch in."""
    head = sha(name)
    gh.inside[head] = {MAIN}.union(*({gh.pulls[n]["sha"]} | gh.inside[gh.pulls[n]["sha"]] for n in numbers))
    gh.commits[head] = {"message": "Merge the batch", "parents": [{"sha": MAIN}]}
    gh.refs[ref] = head
    if number in gh.pulls:
        gh.pulls[number]["sha"] = head
        gh.touch(number)
    else:
        gh.pulls[number] = {"number": number, "state": "open", "merged_at": None, "labels": {"large"},
                            "sha": head, "ref": ref, "own": True, "base": "main",
                            "body": body, "title": "", "updated": 0}
        gh.touch(number)
    return head


class BuiltByHand(WithAssembly):
    """A batch assembled by hand hands `building` to every open pull request it contains."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        gh.add_pull(14, "head14")  # in the branch, but nobody queued it
        by_hand(gh, 11, 12, 14)
        return gh

    def test_what_it_contains_becomes_building_and_the_rest_is_batched_as_before(self):
        gh = self.built()
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [IN, IN, QF, IN])
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING, LATEST})
        self.assertEqual(merges(gh), [sha("head13")])
        self.assertEqual(gh.pulls[1018]["body"], "Assembled by hand.")
        self.assertEqual(gh.refs[HAND], sha("kim"))
        self.assertIn("#1018 is a batch assembled by hand with open pull requests in it: now `building`", log)
        self.assertIn("#11 is in the batch #1018: now `batch-building` and `frozen`", log)
        self.assertIn("#14 is in the batch #1018: now `batch-building` and `frozen`", log)
        [record] = gh.said(1018)
        self.assertTrue(record.startswith("<!-- batch-queue-by-hand {"))
        self.assertEqual(note(record)["queued"], ["11", "12"])
        self.assertIn("In this batch: #11, #12, #14.", record)
        # Later runs change nothing.
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.writes, [])

    def test_labelled_building_by_hand_beforehand_it_is_looked_through_the_same(self):
        gh = self.built()
        gh.label(1018, add=BUILDING, login="maintainer")
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [IN, IN, QF, IN])
        self.assertIn("In this batch: #11, #12, #14.", gh.said(1018)[0])

    def test_a_pull_request_into_another_branch_is_in_it_too(self):
        gh = Fake()
        gh.add_pull(11, "head11", base="batch/b3-on-644")  # opened against an earlier batch
        by_hand(gh, 11)
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], IN)
        self.assertIn("targets `batch/b3-on-644` rather than `main`", gh.said(11)[0])
        gh.close(1018, merged=True)  # GitHub does not mark #11 merged: its head is not in its base
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[11]["state"]), (set(), "closed"))
        self.assertIn("#11 landed with batch #1018 but targets `batch/b3-on-644`: closed", log)
        self.assertIn("GitHub does not mark this pull request merged because it targets `batch/b3-on-644`",
                      gh.said(11)[-1])

    def test_one_holding_no_open_pull_request_is_left_alone(self):
        gh = Fake()
        queue(gh, 11)
        by_hand(gh, 11)
        gh.push(11, "head11-later")  # the batch holds an older commit of #11 only
        gh.writes = []
        sync(gh)
        # Pushed to after it was queued, so changed after it was frozen.
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[1018]["labels"]), (QF | {CHANGED}, {"large"}))
        self.assertEqual(gh.said(1018), [])
        self.assertEqual([write for write in gh.writes if "1018" in write[1]], [])

    def test_one_that_is_queued_itself_waits_in_the_queue(self):
        gh = Fake()
        gh.add_pull(11, "head11")
        by_hand(gh, 11, number=463, ref="batch/citations", name="citations")
        queue(gh, 463)
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[463]["labels"]), (set(), {"large", *QF}))
        self.assertEqual(merges(gh), [sha("citations")])
        self.assertEqual(gh.said(463), [])

    def test_merged_it_takes_building_off_even_what_was_pushed_to_since(self):
        gh = self.built()
        sync(gh)
        gh.push(12, "head12-later")
        sync(gh)
        # What was assembled is still being built, and the author is told what that means.
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        self.assertIn(f"builds and lands `{short('head12')}` only, not `{short('head12-later')}`", gh.said(12)[-1])
        self.assertEqual(len(gh.said(12)), 2)  # frozen, then pushed to: each once
        sync(gh)
        self.assertEqual(len(gh.said(12)), 2)
        gh.close(11, merged=True)  # GitHub marks it merged along with the batch
        gh.close(1018, merged=True)
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14, 1018)], [set(), {WAITING}, set(), {"large"}])
        self.assertEqual(gh.pulls[12]["state"], "open")
        self.assertIn("#12 landed with batch #1018: `batch-building` and `frozen` removed", log)
        self.assertIn("#12 was pushed to after the batch #1018 took it: told what landed, now `awaiting-author`", log)
        self.assertIn(f"What was pushed here after it, up to `{short('head12-later')}`, has not landed", gh.said(12)[-1])
        self.assertIn("tidied up after batch #1018, which was assembled by hand", log)
        self.assertIn(HAND, gh.refs)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_closed_without_merging_only_what_was_queued_goes_back_to_the_queue(self):
        gh = self.built()
        sync(gh)
        gh.close(1018)
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14, 1018)], [QF, QF, set(), {"large"}])
        self.assertIn("batch #1018 was closed without merging: #11 is `batch queue` again", log)
        self.assertIn("batch #1018 was closed without merging: #14 is no longer `batch-building`", log)
        self.assertIn("not starting a new batch in this run: the next `batch` or `-batch` comment does", log)

    def test_a_label_taken_off_by_hand_stays_off(self):
        gh = self.built()
        sync(gh)
        gh.label(14, remove=MEMBER, login="maintainer")
        gh.label(14, remove=FROZEN, login="maintainer")
        gh.writes = []
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], set())
        self.assertEqual(gh.writes, [])

    def test_queued_while_it_is_being_built_it_goes_back_to_the_queue_later(self):
        gh = self.built()
        sync(gh)
        queue(gh, 14)
        log = sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], IN)
        self.assertIn("#14 is in the batch #1018: now `batch-building` and `frozen`", log)
        self.assertEqual(note(gh.said(1018)[0])["queued"], ["11", "12", "14"])
        gh.close(1018)
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], QF)

    def test_what_the_batch_being_assembled_already_took_is_not_told_to_leave(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        by_hand(gh, 11)
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (IN, QF))
        body = batch_pull(gh)["body"]
        # The batch being assembled was rebuilt on top of #1018, which holds #11 now.
        self.assertIn(f"In this batch:\n\n- #12 at `{short('head12')}`\n\nMerge this", body)
        self.assertEqual(told(gh, 11), [])

    def test_a_new_head_is_looked_through_again(self):
        gh = self.built()
        sync(gh)
        # The branch is rebuilt without #11 and #14, and with #13.
        by_hand(gh, 12, 13, name="kim-again")
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [QF, IN, IN, set()])
        self.assertIn("#11 is no longer in the batch #1018: `batch queue` again", log)
        self.assertIn("#14 is no longer in the batch #1018: no longer `batch-building`", log)
        self.assertIn("In this batch: #12, #13.", gh.said(1018)[0])
        self.assertEqual(len(gh.said(1018)), 1)  # the same comment, brought up to date

    def test_commits_pushed_on_top_are_looked_through_in_one_request(self):
        gh = self.built()
        sync(gh)
        # A fix is pushed onto the branch, and #13 is merged in as well.
        old, new = gh.refs[HAND], sha("kim-fixed")
        gh.inside[new] = gh.inside[old] | {old, sha("head13")}
        gh.refs[HAND] = gh.pulls[1018]["sha"] = new
        gh.touch(1018)
        gh.reads = []
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [IN] * 4)
        self.assertIn("In this batch: #11, #12, #13, #14.", gh.said(1018)[0])
        # The branch's commits, then the batch being assembled on top asks whether the old head
        # is in the new one before it follows.
        self.assertEqual([path for path in gh.reads if path.startswith("compare/")],
                         [f"compare/main...{new}?per_page=100&page=1", f"compare/{new}...{old}?per_page=1"])

    def test_a_long_branch_is_listed_a_hundred_commits_at_a_time(self):
        gh = Fake()
        queue(gh, 11)
        head = by_hand(gh, 11)
        gh.inside[head] |= {sha(f"fix {count}") for count in range(250)}
        gh.reads = []
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], IN)
        self.assertEqual([path for path in gh.reads if path.startswith("compare/main")],
                         [f"compare/main...{head}?per_page=100&page={page}" for page in (1, 2, 3)])

    def test_a_batch_inside_another_one_is_never_one_of_its_members(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, number=463, ref="batch/citations", name="citations")
        queue(gh, 463)  # waiting in the queue, so not being built in its own right
        by_hand(gh, 463, 12)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] - {"large"} for n in (11, 12, 1018)],
                         [IN, IN, {BUILDING, LATEST}])
        self.assertEqual(gh.pulls[463]["labels"], {"large", QUEUED, FROZEN})
        self.assertEqual(note(gh.said(1018)[0])["members"], {"11": sha("head11"), "12": sha("head12")})
        sync(gh)
        self.assertEqual(gh.said(463), [])
        gh.close(1018)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] - {"large"} for n in (11, 12, 463)], [QF] * 3)

    def test_looking_through_it_costs_a_request_for_each_hundred_commits(self):
        gh = Fake()
        queue(gh, *range(1, 34))
        by_hand(gh, *range(1, 34))
        gh.reads = []
        before = gh.calls
        sync(gh)
        self.assertEqual(len([path for path in gh.reads if path.startswith("compare/main")]), 1)
        # Labels, the frozen notes and the comment are writes: three for each queued pull request,
        # the batch's note, saved after every ten told, `latest batch` on the batch, and starting
        # the conflict-labels workflow.
        self.assertLess(gh.calls - before, 33 * 3 + 23)
        # The eight requests of a run with nothing new, and this script's comment on the batch.
        for _ in range(2):
            before = gh.calls
            sync(gh)
            self.assertEqual(gh.calls - before, 9)

    def test_a_record_from_before_queued_was_written_down_puts_back_only_what_was_queued(self):
        gh = self.built()
        sync(gh)
        [comment] = [item for item in gh.comments[1018] if item["body"].startswith("<!-- batch-queue-by-hand")]
        comment["body"] = re.sub(r',"unqueued":\[[^]]*\]', "", comment["body"])
        self.assertNotIn("queued", note(comment["body"]))
        gh.close(1018)
        sync(gh)
        # The note takes all three to have been queued, but nobody commented `batch` on #14.
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [QF, QF, set()])

    def test_looking_through_stops_when_the_hours_allowance_is_nearly_gone(self):
        gh = self.built()
        gh.left = batch.RESERVE - 1
        log = sync(gh)
        self.assertIn(f"only {batch.RESERVE - 1} requests left this hour: did not look through the batch #1018, "
                      "and the next run does", log)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[1018]["labels"]), (QF, {"large"}))
        gh.left = 900
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[14]["labels"]), (IN, IN))


URL = "https://github.com/o/r/pull/"
DESCRIPTION = f"""This PR merges 3 pull requests into one batch.

Included:

- {URL}11 Reuse a lemma (@alice)
- {URL}12 Prune imports (@bob)

These replace `nlinarith` with short hinted `linarith` calls and can be dropped if the maintainers prefer:

- {URL}14 Shorten a proof (@carol)

Left out because they conflict with a PR earlier in the batch:

- {URL}21 refactor: fold modules (@dave): conflicts with #11 (`A.lean`); #12 (`B.lean`).
- #22 chore: remove a lemma (@erin): conflicts with #11 (`C.lean`).
  more about the conflict, on a line of its own

Left out for other reasons:

- {URL}23 Drop imports from the root theorems (@frank): it changes `src/Main.lean`.
- {URL}11 Also listed here by mistake (@alice): a member is never told it is left out.

Open PRs that only change CI, scripts or docs are not included.

- {URL}24 a list after a paragraph is under no heading
"""


class Describing(unittest.TestCase):
    """What the description of a batch assembled by hand says is left out."""

    def test_entries_under_left_out_headings_only(self):
        found = batch.left_out(DESCRIPTION, REPO)
        self.assertEqual(sorted(found), [11, 21, 22, 23])
        self.assertEqual(found[21], ("Left out because they conflict with a PR earlier in the batch:",
                                     f"{URL}21 refactor: fold modules (@dave): conflicts with #11 (`A.lean`); #12 (`B.lean`)."))
        self.assertEqual(found[22][1], "#22 chore: remove a lemma (@erin): conflicts with #11 (`C.lean`).")
        self.assertEqual(found[23][0], "Left out for other reasons:")

    def test_older_headings_count_too(self):
        body = "Two PRs from #262 are not included:\n\n- #31 one\n\nNot included:\n\n- #32 two\n\nLeft out:\n* #33 three\n"
        self.assertEqual(sorted(batch.left_out(body, REPO)), [31, 32, 33])

    def test_links_to_another_repository_do_not_count(self):
        body = "Left out:\n\n- https://github.com/other/r/pull/41 elsewhere\n- https://github.com/O/R/pull/42 here\n"
        self.assertEqual(sorted(batch.left_out(body, REPO)), [42])


class Members(unittest.TestCase):
    """What a batch assembled by hand tells the pull requests it contains or leaves out."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.add_pull(14, "head14")
        for number in (21, 22, 23, 24):
            gh.add_pull(number, f"head{number}")
        queue(gh, 21)
        by_hand(gh, 11, 12, 14)
        gh.pulls[1018]["body"] = DESCRIPTION
        return gh

    def left(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-left-out")]

    def frozen(self, gh, number):
        return [item for item in gh.comments.get(number, []) if item["body"].startswith("<!-- batch-queue-frozen")]

    def test_each_member_is_told_once_that_it_is_frozen(self):
        gh = self.built()
        log = sync(gh)
        for number in (11, 12, 14):
            [note] = gh.said(number)
            self.assertTrue(note.startswith(f"<!-- batch-queue-frozen 1018 {sha(f'head{number}')} -->"))
            self.assertIn("Please don't push to this pull request", note)
            self.assertIn("When the batch lands, GitHub marks this pull request merged.", note)
        self.assertIn("told #11 that it is frozen while the batch #1018 is built", log)
        sync(gh)
        self.assertEqual([len(gh.said(number)) for number in (11, 12, 14)], [1, 1, 1])

    def test_what_is_left_out_is_told_why_and_nothing_more(self):
        gh = self.built()
        log = sync(gh)
        [note] = self.left(gh, 23)
        self.assertIn("Batch #1018 leaves this pull request out. Its description says:\n\n"
                      "> Left out for other reasons:\n>\n"
                      f"> `{URL}23` Drop imports from the root theorems", note)
        self.assertIn("This is for your information: it changes no label of this pull request.", note)
        self.assertNotIn("`ready`", note)
        # Conflicts are left to the conflict-labels workflow, which finds them from git. Nothing is
        # handed back to its author.
        self.assertEqual([gh.pulls[n]["labels"] for n in (21, 22, 23, 24)], [QF, set(), set(), set()])
        self.assertEqual([len(self.left(gh, n)) for n in (11, 21, 22, 23, 24)], [0, 0, 0, 1, 0])
        self.assertIn("told #23 that the batch #1018 leaves it out", log)
        # The record says so too.
        record = gh.said(1018)[0]
        self.assertIn("Those this description lists as left out are told why, unless they are `deferred` or a batch "
                      "being built contains them: the comment only informs.", record)
        self.assertNotIn(WAITING, record)
        # Nothing new: nothing said, nothing read. (#21 is queued, so the queue reads it again.)
        gh.reads = []
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (21, 22, 23)], [0, 0, 1])
        self.assertEqual([path for path in gh.reads if path.startswith(("issues/22/", "issues/23/"))], [])

    def test_a_deferred_pull_request_is_not_told(self):
        gh = self.built()
        gh.label(23, add="deferred", login="maintainer")
        log = sync(gh)
        self.assertEqual(gh.said(23), [])
        self.assertEqual(gh.pulls[23]["labels"], {"deferred"})
        self.assertNotIn("told #23 that the batch #1018 leaves it out", log)
        self.assertNotIn("23", note(gh.said(1018)[0])["left"])
        # Its entry removed, it is not told that either.
        gh.pulls[1018]["body"] = DESCRIPTION.replace(f"- {URL}23 Drop imports", f"- {URL}25 Drop imports")
        gh.touch(1018)
        sync(gh)
        self.assertEqual(gh.said(23), [])

    def test_the_same_kind_of_reason_reworded_updates_the_comment_quietly(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)  # the author commented `ready`
        gh.close(1018)
        sync(gh)
        by_hand(gh, 11, 12, 14, number=1100, ref="batch/b5-on-1018", name="kim-b5")
        gh.pulls[1100]["body"] = DESCRIPTION.replace("it changes `src/Main.lean`", "it still changes `src/Main.lean`")
        log = sync(gh)
        [note] = self.left(gh, 23)
        self.assertIn("Batch #1100 leaves this pull request out", note)
        self.assertIn("it still changes `src/Main.lean`", note)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])
        self.assertIn("brought up to date what #23 was told about being left out, for the batch #1100", log)

    def test_ready_is_not_undone_by_the_next_batch_leaving_it_out_for_the_same_reason(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)  # the author commented `ready`
        gh.close(1018)
        sync(gh)
        by_hand(gh, 11, 12, 14, number=1100, ref="batch/b5-on-1018", name="kim-b5")
        gh.pulls[1100]["body"] = DESCRIPTION
        log = sync(gh)
        self.assertEqual(len(self.left(gh, 23)), 1)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])
        self.assertNotIn("told #23 that the batch #1100 leaves it out: now `awaiting-author`", log)

    def moved(self):
        """The description, with #23 moved under another heading. Not one about conflicts: the
        conflict-labels workflow tells those."""
        moved = DESCRIPTION.replace(f"- {URL}23 Drop imports from the root theorems (@frank): it changes `src/Main.lean`.\n", "")
        return moved + f"\nLeft out under the maintainers' guidance in `AGENTS.md`:\n\n- {URL}23 Drop (@frank): adds an option, see #11.\n"

    def test_a_new_heading_in_the_same_batch_edits_its_comment_in_place(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)  # the author commented `ready`
        gh.pulls[1018]["body"] = self.moved()
        gh.touch(1018)
        log = sync(gh)
        [note] = self.left(gh, 23)
        self.assertIn("adds an option, see `#11`", note)
        self.assertIn("> Left out under the maintainers' guidance in `AGENTS.md`:", note)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])
        self.assertIn("brought up to date what #23 was told about being left out, for the batch #1018", log)

    def test_a_heading_corrected_in_the_same_batch_tells_no_one_again(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)
        gh.pulls[1018]["body"] = DESCRIPTION.replace("Left out for other reasons:", "Left out, for other reasons:")
        gh.touch(1018)
        gh.writes = []
        sync(gh)
        [note] = self.left(gh, 23)
        self.assertIn("> Left out, for other reasons:", note)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])
        self.assertEqual([method for method, path, _ in gh.writes if path.startswith("issues/23/")], [])

    def test_a_new_kind_of_reason_from_another_batch_is_told_again(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)
        gh.close(1018)
        sync(gh)
        by_hand(gh, 11, 12, 14, number=1100, ref="batch/b5-on-1018", name="kim-b5")
        gh.pulls[1100]["body"] = self.moved()
        log = sync(gh)
        first, second = self.left(gh, 23)
        self.assertIn("Batch #1018 leaves this pull request out", first)
        self.assertIn("Batch #1100 leaves this pull request out", second)
        self.assertIn("adds an option, see `#11`", second)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])
        self.assertIn("told #23 that the batch #1100 leaves it out", log)

    def test_an_entry_reworded_in_the_description_is_brought_up_to_date(self):
        gh = self.built()
        sync(gh)
        gh.pulls[1018]["body"] = DESCRIPTION.replace("it changes `src/Main.lean`", "it edits `src/Main.lean`")
        sync(gh)
        [note] = self.left(gh, 23)
        self.assertIn("it edits `src/Main.lean`", note)
        gh.writes = []
        sync(gh)
        self.assertEqual([write for write in gh.writes if "comments" in write[1] and "1018" not in write[1]], [])

    def test_an_entry_removed_from_the_description_is_told_so(self):
        gh = self.built()
        sync(gh)
        gh.pulls[1018]["body"] = DESCRIPTION.replace(f"- {URL}23 Drop imports", f"- {URL}25 Drop imports")
        log = sync(gh)
        self.assertIn("The description of batch #1018 no longer lists this pull request as left out", gh.said(23)[-1])
        self.assertIn("told #23 that the batch #1018 no longer lists it as left out", log)
        sync(gh)
        self.assertEqual(len(gh.said(23)), 2)

    def no_longer(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-no-longer-left-out")]

    def others(self, gh, *numbers):
        """The description, with these pull requests left out for other reasons as well, next to #23.
        That heading is not about conflicts, so they are told whether or not the conflict-labels
        workflow is switched on."""
        for number in numbers:
            gh.add_pull(number, f"head{number}")
        extra = "".join(f"- {URL}{number} Too big (@grace): split it.\n" for number in numbers)
        return DESCRIPTION.replace("Left out for other reasons:\n\n", f"Left out for other reasons:\n\n{extra}")

    def reworded(self, body):
        """The description with the heading for other reasons reworded so that it no longer says
        "left out"."""
        return body.replace("Left out for other reasons:", "Waiting for other reasons:")

    def test_a_reworded_heading_tells_no_one_they_are_no_longer_left_out(self):
        gh = self.built()
        body = gh.pulls[1018]["body"] = self.others(gh, 25, 26)
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (23, 25, 26)], [1, 1, 1])
        gh.pulls[1018]["body"] = self.reworded(body)
        gh.touch(1018)
        gh.writes = []
        log = sync(gh)
        self.assertIn("the description of the batch #1018 no longer lists #23, #25, #26 as left out, but still lists "
                      "them: was a heading reworded? They were not told", log)
        self.assertEqual([self.no_longer(gh, n) for n in (23, 25, 26)], [[], [], []])
        self.assertEqual([path for method, path, _ in gh.writes if path.startswith(("issues/23/", "issues/25/",
                                                                                     "issues/26/"))], [])
        self.assertFalse({"23", "25", "26"} & set(note(gh.said(1018)[0])["left"]))
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        # Worded back, their comments are brought up to date: nobody is told again.
        gh.label(23, remove=WAITING)  # the author commented `ready`
        gh.pulls[1018]["body"] = body
        gh.touch(1018)
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (23, 25, 26)], [1, 1, 1])
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])

    def test_a_few_entries_moved_out_of_the_left_out_lists_are_told(self):
        gh = self.built()
        body = gh.pulls[1018]["body"] = self.others(gh, 25)
        sync(gh)
        gh.pulls[1018]["body"] = self.reworded(body)
        gh.touch(1018)
        log = sync(gh)
        self.assertEqual([len(self.no_longer(gh, n)) for n in (23, 25)], [1, 1])
        self.assertIn("told #25 that the batch #1018 no longer lists it as left out", log)

    def test_an_entry_removed_along_with_a_reworded_heading_is_still_told(self):
        gh = self.built()
        body = gh.pulls[1018]["body"] = self.others(gh, 25, 26, 27)
        sync(gh)
        self.assertEqual(len(self.left(gh, 27)), 1)
        gh.pulls[1018]["body"] = self.reworded(body).replace(f"- {URL}27 Too big (@grace): split it.\n", "")
        gh.touch(1018)
        log = sync(gh)
        self.assertEqual([len(self.no_longer(gh, n)) for n in (23, 25, 26, 27)], [0, 0, 0, 1])
        self.assertIn("told #27 that the batch #1018 no longer lists it as left out", log)

    def test_dropped_from_the_branch_it_is_told_it_can_push_again(self):
        gh = self.built()
        sync(gh)
        by_hand(gh, 12, 14, name="kim-without-11")  # the branch is rebuilt without #11
        log = sync(gh)
        # Out of the branch, it is also told what the description says about it.
        self.assertEqual(gh.pulls[11]["labels"], QF)
        dropped = [note for note in gh.said(11) if note.startswith("<!-- batch-queue-dropped")]
        self.assertEqual(len(dropped), 1)
        self.assertIn("is no longer in batch #1018: its branch was changed without it", dropped[0])
        self.assertIn("It is back in the batch queue, at the commit that was queued, and stays `frozen`", dropped[0])
        self.assertEqual(len(self.left(gh, 11)), 1)
        self.assertIn("#11 is no longer in the batch #1018: `batch queue` again", log)

    def test_closed_without_merging_what_it_held_is_told_it_can_push_again(self):
        gh = self.built()
        sync(gh)
        gh.close(1018)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 14)], [QF, set()])
        self.assertIn("Batch #1018 was closed without being merged.", gh.said(14)[-1])
        self.assertNotIn("batch queue", gh.said(14)[-1])
        self.assertIn("It is back in the batch queue, at the commit that was queued, and stays `frozen`", gh.said(11)[-1])

    def test_a_new_head_merged_into_the_branch_is_what_the_batch_holds(self):
        gh = self.built()
        sync(gh)
        [first] = self.frozen(gh, 12)
        gh.push(12, "head12-later")
        by_hand(gh, 11, 12, 14, name="kim-with-12-later")  # merged in again before the next run
        gh.reads, gh.writes = [], []
        log = sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN)
        # The comment that told it it is frozen names the new head now, marker and all: it is
        # edited, after one read of its comments, and nothing is posted.
        [said] = self.frozen(gh, 12)
        self.assertEqual(len(gh.said(12)), 1)
        self.assertEqual(said["id"], first["id"])
        self.assertTrue(said["body"].startswith(f"<!-- batch-queue-frozen 1018 {sha('head12-later')} -->\n"))
        self.assertIn(f"Commit `{short('head12-later')}` of this pull request is in batch #1018", said["body"])
        self.assertNotIn(short("head12"), said["body"].replace(short("head12-later"), ""))
        self.assertEqual([(method, path) for method, path, _ in gh.writes
                          if path.startswith("issues/12/") or path == f"issues/comments/{first['id']}"],
                         [("PATCH", f"issues/comments/{first['id']}")])
        self.assertEqual(gh.reads.count("issues/12/comments?per_page=100&page=1"), 1)
        self.assertIn(f"#12 is in the batch #1018 at its new head `{short('head12-later')}`: its comments say so now",
                      log)
        record = note(gh.said(1018)[0])
        self.assertEqual((record["members"]["12"], record["told"]["12"]), (sha("head12-later"),) * 2)
        # Nothing more on the next run.
        gh.reads, gh.writes = [], []
        sync(gh)
        self.assertEqual((gh.writes, [path for path in gh.reads if path.startswith("issues/12/")]), ([], []))

    def test_a_member_loses_changed_after_frozen_once_the_batch_merges_in_its_new_head(self):
        gh = self.built()
        sync(gh)
        gh.push(12, "head12-later")
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        by_hand(gh, 11, 12, 14, name="kim-with-12-later")
        log = sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN)
        self.assertIn(f"#12 is at `{short('head12-later')}`, the commit that was taken: `{CHANGED}` removed", log)

    def test_members_labelled_before_the_labels_were_split_are_relabelled(self):
        gh = self.built()
        sync(gh)
        for number in (11, 12, 14):
            gh.pulls[number]["labels"] = {BUILDING}
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [IN] * 3)
        self.assertIn("#14 is in the batch #1018: now `batch-building` and `frozen`", log)

    def test_telling_stops_when_the_hours_allowance_is_nearly_gone_and_carries_on_later(self):
        gh = self.built()
        gh.left = batch.RESERVE - 1
        sync(gh)
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14, 23)], [0, 0, 0, 0])
        gh.left = 900
        sync(gh)
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14, 23)], [1, 1, 1, 1])


class Robustness(unittest.TestCase):
    """Runs cut short, refused writes, and the ways a pull request can leave and come back."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.add_pull(14, "head14")
        by_hand(gh, 11, 12, 14)
        return gh

    def frozen_notes(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-frozen")]

    def test_a_run_cut_short_tells_no_one_twice(self):
        gh = self.built()
        gh.fail("POST", r"issues/14/comments", RuntimeError("no answer from GitHub"))
        with self.assertRaises(RuntimeError):
            sync(gh)
        sync(gh)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [1, 1, 1])

    def test_a_refused_comment_or_label_is_tried_again(self):
        gh = self.built()
        gh.fail("POST", r"issues/12/comments", 403)
        gh.fail("POST", r"issues/14/labels", 403)
        sync(gh)
        self.assertEqual((len(self.frozen_notes(gh, 12)), gh.pulls[14]["labels"]), (0, set()))
        sync(gh)
        self.assertEqual((len(self.frozen_notes(gh, 12)), gh.pulls[14]["labels"]), (1, IN))

    def test_the_rate_limit_stops_the_run_and_the_next_one_carries_on(self):
        gh = self.built()
        gh.fail("POST", r"issues/12/comments", 429)
        with self.assertRaises(batch.Refused):
            sync(gh)
        sync(gh)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [1, 1, 1])

    def test_a_round_whose_note_was_not_saved_tells_no_one_twice(self):
        gh = self.built()
        # The rate limit refuses the comment to #12, and every save of the note after the comment
        # to #11: the note on GitHub does not show that #11 was told.
        said = gh.say

        def say(number, body, login=BOT):
            if number == 11 and body.startswith("<!-- batch-queue-frozen"):
                gh.fail("PATCH", r"issues/comments/\d+", 429)
            return said(number, body, login)

        gh.say = say
        gh.fail("POST", r"issues/12/comments", 429)
        with self.assertRaises(batch.Refused):
            sync(gh)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [1, 0, 0])
        stored = note(gh.said(1018)[0])
        self.assertEqual((stored.get("telling"), stored.get("told")), (True, {}))
        # The next run finds the round unfinished, and looks before it tells.
        gh.say, gh.reads = said, []
        sync(gh)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [1, 1, 1])
        self.assertIn("issues/11/comments?per_page=100&page=1", gh.reads)
        stored = note(gh.said(1018)[0])
        self.assertEqual((stored.get("telling"), sorted(stored["told"])), (None, ["11", "12", "14"]))
        # The round is over: the run after that reads no member's comments.
        gh.reads = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual([path for path in gh.reads if path.startswith(("issues/11/", "issues/12/", "issues/14/"))], [])

    def test_a_round_that_was_finished_leaves_no_mark(self):
        gh = self.built()
        sync(gh)
        self.assertNotIn("telling", note(gh.said(1018)[0]))
        self.assertNotIn('"telling"', gh.said(1018)[0])

    def test_a_record_that_cannot_be_saved_stops_the_run_before_anything_is_said(self):
        gh = self.built()
        gh.fail("POST", r"issues/1018/comments", 403, times=5)
        with self.assertRaises(batch.Refused):
            sync(gh)
        self.assertEqual([gh.said(n) for n in (11, 12, 14)], [[], [], []])

    def test_a_batch_reopened_after_it_was_closed_starts_again(self):
        gh = self.built()
        sync(gh)
        gh.close(1018)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 14)], [QF, set()])
        gh.reopen(1018)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [IN] * 3)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 14)], [2, 2])

    def test_a_batch_closed_without_merging_has_what_it_told_cleared(self):
        gh = self.built()
        gh.add_pull(23, "head23")
        gh.pulls[1018]["body"] = f"Left out for other reasons:\n\n- #23 Too big (@frank): it changes `src/Main.lean`.\n"
        sync(gh)
        gh.label(23, remove=WAITING)  # the author commented `ready`
        gh.close(1018)
        sync(gh)
        stored = note(gh.said(1018)[0])
        self.assertEqual((stored["told"], stored["pushed"], stored["left"], stored["labelled"]), ({}, {}, {}, []))
        gh.reopen(1018)
        sync(gh)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [2, 2, 2])
        # What the description leaves out is brought up to date in place: nobody is told again.
        self.assertEqual(len([body for body in gh.said(23) if body.startswith("<!-- batch-queue-left-out")]), 1)
        self.assertNotIn(WAITING, gh.pulls[23]["labels"])

    def test_a_batch_labelled_building_again_while_open_tells_no_one_again(self):
        gh = self.built()
        sync(gh)
        gh.label(1018, remove=BUILDING, login="maintainer")
        gh.writes = []
        log = sync(gh)
        self.assertIn("#1018 is a batch assembled by hand with open pull requests in it: now `building`", log)
        self.assertEqual([len(self.frozen_notes(gh, n)) for n in (11, 12, 14)], [1, 1, 1])
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [IN] * 3)
        # Labelled `building` again, it starts the conflict-labels workflow, as the first time.
        self.assertEqual([(method, path) for method, path, _ in gh.writes],
                         [("POST", "issues/1018/labels"), ("POST", "actions/workflows/conflict-labels.yml/dispatches")])

    def test_a_member_never_queued_is_not_queued_when_it_is_reopened(self):
        gh = self.built()
        sync(gh)
        gh.close(14)
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], set())
        gh.reopen(14)
        self.assertEqual(batch.reopened(gh, 14), ["#14 was never queued: nothing to put back"])
        sync(gh)  # the batch still holds it
        self.assertEqual(gh.pulls[14]["labels"], IN)

    def test_withdrawn_while_in_a_batch_it_does_not_go_back_to_the_queue(self):
        gh = self.built()
        sync(gh)
        unqueue(gh, 11)
        self.assertEqual(gh.pulls[11]["labels"], IN)  # still in the batch, so still frozen
        gh.close(1018)
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], set())
        self.assertIn("no longer `frozen`", gh.said(11)[-1])

    def test_queued_again_at_a_new_head_it_goes_back_to_the_queue_when_the_batch_lands(self):
        gh = self.built()
        sync(gh)
        gh.push(11, "head11-later")
        queue(gh, 11)
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], IN | {WAITING, CHANGED})
        gh.close(1018, merged=True)
        log = sync(gh)
        self.assertTrue(QF <= gh.pulls[11]["labels"])
        self.assertIn("That commit was queued, so it is back in the batch queue.", told(gh, 11)[-1])
        self.assertIn("#11 was pushed to after the batch #1018 took it: told what landed, now `awaiting-author` "
                      "and `batch queue` again", log)

    def test_nothing_is_said_or_closed_for_a_commit_that_is_not_on_main(self):
        gh = Fake()
        gh.add_pull(15, "head15", base="batch/b3-on-644")
        by_hand(gh, 15)
        sync(gh)
        gh.close(1018, merged=True)
        gh.inside[MAIN] = set()  # merged into something else than main, say
        log = sync(gh)
        self.assertEqual(gh.pulls[15]["state"], "open")
        self.assertIn(f"#15: commit `{short('head15')}`, which batch #1018 took, is not on `main`: left alone", log)

    def test_tidying_up_stops_when_the_allowance_runs_short_and_finishes_later(self):
        gh = self.built()
        sync(gh)
        gh.close(1018)
        gh.left = batch.RESERVE - 1
        sync(gh)
        self.assertIn(BUILDING, gh.pulls[1018]["labels"])
        gh.left = 900
        sync(gh)
        self.assertNotIn(BUILDING, gh.pulls[1018]["labels"])
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [QF, QF, set()])
        for number in (11, 12, 14):
            self.assertEqual(len([body for body in gh.said(number) if body.startswith("<!-- batch-queue-unfrozen")]), 1)


LISTED = f"""This PR merges 3 pull requests into one batch.

Included:

- {URL}11 Reuse a lemma (@alice)
- #12 Prune imports (@bob)

These can be dropped if the maintainers prefer:

- {URL}14 Shorten a proof (@carol)

Left out for other reasons:

- {URL}23 Drop imports from the root theorems (@frank): it changes `src/Main.lean`.
"""
# The same, with #13 listed as included as well.
WITH_13 = LISTED.replace("- #12 Prune", "- #13 Not merged in (@dan)\n- #12 Prune")


def merge_and_revert(gh, number, subject=None, name="kim-revert", ref=HAND, pr=1018):
    """A maintainer merges the head of #`number` into a batch's branch and then reverts that merge
    with git's message. Returns the commit that reverts it."""
    old, head = gh.refs[ref], gh.pulls[number]["sha"]
    subject = subject or f"Merge PR #{number} into batch"
    merge, undo = sha(f"{name} merge"), sha(f"{name} revert")
    gh.commits[merge] = {"message": subject, "parents": [{"sha": old}, {"sha": head}]}
    gh.commits[undo] = {"message": f'Revert "{subject}"\n\nThis reverts commit {merge}, reversing\nchanges made to {old}.',
                        "parents": [{"sha": merge}]}
    gh.inside[merge] = gh.inside[old] | gh.inside[head] | {old, head}
    gh.inside[undo] = gh.inside[merge] | {merge}
    move(gh, undo, ref, pr)
    return undo


def move(gh, head, ref=HAND, pr=1018):
    """The batch's branch moves to `head`."""
    gh.refs[ref] = head
    gh.pulls[pr]["sha"] = head
    gh.touch(pr)


class DescriptionCheck(unittest.TestCase):
    """The comment on a batch assembled by hand that compares its description with its branch."""

    def built(self, body=LISTED):
        gh = Fake()
        queue(gh, 11, 12)
        for number in (13, 14, 23):
            gh.add_pull(number, f"head{number}")
        by_hand(gh, 11, 12, 14)
        gh.pulls[1018]["body"] = body
        return gh

    def checks(self, gh):
        return [body for body in gh.said(1018) if body.startswith(batch.CHECK)]

    def record(self, gh):
        return next(body for body in gh.said(1018) if body.startswith("<!-- batch-queue-by-hand"))

    def reverted(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-reverted")]

    def test_a_description_that_matches_the_branch_gets_no_comment(self):
        gh = self.built()
        sync(gh)
        self.assertEqual(self.checks(gh), [])
        gh.writes = []
        sync(gh)
        self.assertEqual(gh.writes, [])

    def test_a_closed_pull_request_listed_as_included_is_named(self):
        gh = self.built(LISTED.replace("- #12 Prune", "- #15 Gone (@dan)\n- #12 Prune"))
        gh.add_pull(15, "head15")
        gh.close(15)
        log = sync(gh)
        [check] = self.checks(gh)
        self.assertIn("Listed as included, but closed without being merged: #15.", check)
        self.assertNotIn("head commit is not in this branch", check)
        self.assertIn("posted on the batch #1018 what its description and its branch disagree on", log)
        # What became of it is asked once.
        self.assertEqual(note(self.record(gh))["fates"], {"15": "closed"})
        gh.reads = []
        sync(gh)
        self.assertNotIn("pulls/15", gh.reads)

    def test_a_merged_pull_request_listed_as_included_is_said_to_be_merged(self):
        gh = self.built(LISTED.replace("- #12 Prune", "- #15 Landed (@dan)\n- #16 Gone (@eve)\n- #12 Prune"))
        gh.add_pull(15, "head15")
        gh.close(15, merged=True)
        log = sync(gh)
        [check] = self.checks(gh)
        self.assertIn("Listed as included, but merged already: #15. Take them off the list.", check)
        # #16 is no pull request at all.
        self.assertIn("Listed as included, but not an open pull request: #16.", check)
        self.assertNotIn("closed", check.split("\n\n", 1)[1])

    def test_a_member_closed_without_being_merged_is_named_and_said_to_land(self):
        gh = self.built(LISTED.replace("- #12 Prune", "- #15 Gone (@dan)\n- #12 Prune"))
        gh.add_pull(15, "head15")
        gh.close(15)
        sync(gh)
        gh.close(12)  # its commit is still in the branch, and the note still holds it
        sync(gh)
        self.assertIn("12", note(self.record(gh))["members"])
        [check] = self.checks(gh)
        self.assertIn("Listed as included, but closed without being merged: #12, #15. Of these, #12 is still in "
                      "this branch, so their "
                      "changes land with it, although GitHub does not mark a closed pull request merged.", check)
        self.assertNotIn("head commit is not in this branch", check)

    def test_an_open_pull_request_listed_but_not_in_the_branch_is_named(self):
        gh = self.built(WITH_13)
        sync(gh)
        [check] = self.checks(gh)
        self.assertIn("Listed as included, but their head commit is not in this branch: #13. Merge the head commit", check)

    def test_one_pushed_to_before_the_batch_was_first_looked_through_is_named_too(self):
        gh = self.built()
        gh.push(12, "head12-later")  # after it was merged in, before the workflow first looks
        sync(gh)
        # Queued, then pushed to before the batch was looked through: still queued at the old commit,
        # which the sync, too, now says.
        self.assertEqual(gh.pulls[12]["labels"], QF | {CHANGED})
        [check] = self.checks(gh)
        self.assertIn("head commit is not in this branch: #12.", check)
        self.assertIn("pushed to after it was merged in but before the workflow first looked through the batch", check)
        # Taking it off the list would leave its earlier commit in the batch: the advice is to rebuild.
        self.assertIn("To leave such a one out instead, rebuild the branch without it, since its earlier commit would "
                      "still land, and take it off the list.", check)

    def test_a_member_pushed_to_after_it_was_merged_in_is_not_named(self):
        gh = self.built()
        sync(gh)
        gh.push(12, "head12-later")
        sync(gh)
        self.assertEqual(self.checks(gh), [])

    def test_what_the_branch_holds_but_the_description_does_not_list_is_named(self):
        gh = self.built(LISTED.replace(f"- {URL}14 Shorten a proof (@carol)\n", f"- {URL}24 Something else\n"))
        sync(gh)
        [check] = self.checks(gh)
        self.assertIn("In this branch, but not listed in the description: #14.", check)

    def test_without_a_list_of_what_is_included_the_branch_is_not_compared_with_it(self):
        gh = self.built("Assembled by hand.\n\nLeft out:\n\n- #23 reason\n")
        sync(gh)
        self.assertEqual(self.checks(gh), [])

    def test_what_the_branch_holds_but_the_description_leaves_out_is_named(self):
        gh = self.built(DESCRIPTION)  # lists #11 both as included and as left out
        sync(gh)
        [check] = self.checks(gh)
        self.assertIn("In this branch, but listed as left out: #11.", check)
        self.assertNotIn("not listed in the description", check)
        self.assertEqual([body for body in gh.said(11) if body.startswith("<!-- batch-queue-left-out")], [])

    def test_the_comment_is_edited_in_place_and_says_when_all_is_well(self):
        gh = self.built(WITH_13)
        sync(gh)
        [first] = [comment["id"] for comment in gh.comments[1018] if comment["body"].startswith(batch.CHECK)]
        by_hand(gh, 11, 12, 13, 14, name="kim-with-13")
        log = sync(gh)
        [check] = self.checks(gh)
        self.assertIn("Nothing to report: every pull request listed as included is in this branch", check)
        self.assertEqual([comment["id"] for comment in gh.comments[1018] if comment["body"].startswith(batch.CHECK)], [first])
        self.assertIn("brought up to date what the batch #1018 is told about its description: all is well now", log)

    def test_a_run_with_nothing_new_writes_nothing(self):
        gh = self.built(WITH_13)
        sync(gh)
        gh.writes = []
        sync(gh)
        gh.pulls[1018]["body"] += "\nA paragraph that changes nothing.\n"
        gh.touch(1018)
        sync(gh)
        self.assertEqual(gh.writes, [])
        self.assertEqual(len(self.checks(gh)), 1)

    def test_a_revert_is_named_and_the_pull_request_is_told_once(self):
        gh = self.built()
        sync(gh)
        undo = merge_and_revert(gh, 13)
        gh.pulls[1018]["body"] = WITH_13
        log = sync(gh)
        self.assertEqual(gh.pulls[13]["labels"], IN)  # still in the batch: its head commit is
        [check] = self.checks(gh)
        self.assertIn(f"Reverted in this branch: #13 in `{undo[:10]}`.", check)
        [told] = self.reverted(gh, 13)
        self.assertTrue(told.startswith(f"<!-- batch-queue-reverted 1018 {undo} -->"))
        self.assertIn("GitHub marks this pull request merged although its changes did not land", told)
        self.assertIn("told #13 that the batch #1018 reverts it", log)
        gh.writes, gh.reads = [], []
        sync(gh)
        self.assertEqual((gh.writes, len(self.reverted(gh, 13))), ([], 1))
        self.assertEqual([path for path in gh.reads if path.startswith(("compare/", "issues/13/"))], [])

    def test_a_revert_already_told_is_not_told_again_when_the_note_is_lost(self):
        gh = self.built()
        merge_and_revert(gh, 13)
        sync(gh)
        gh.close(1018)
        sync(gh)
        gh.reopen(1018)
        sync(gh)
        self.assertEqual(len(self.reverted(gh, 13)), 1)

    def test_any_revert_of_a_merge_that_brought_the_pull_request_in_counts(self):
        gh = self.built()
        merge_and_revert(gh, 13, subject="Merge pull request #13 from dan/topic-13")
        sync(gh)
        self.assertEqual(len(self.reverted(gh, 13)), 1)
        # Not listed in the description, it is named only as reverted: listing it is not the fix.
        [check] = self.checks(gh)
        self.assertIn("Reverted in this branch: #13", check)
        self.assertNotIn("not listed in the description", check)

    def test_a_revert_naming_a_pull_request_it_did_not_bring_in_does_not_count_it(self):
        gh = self.built()
        merge_and_revert(gh, 13, subject="Merge pull request #13 from dan/topic-13, after #12")
        sync(gh)
        self.assertEqual((len(self.reverted(gh, 12)), len(self.reverted(gh, 13))), (0, 1))

    def test_a_revert_that_names_the_merge_by_a_short_id_counts(self):
        # As the reverts of #1796 into batch 10b were written.
        gh = self.built()
        undo = merge_and_revert(gh, 13)
        merge = gh.commits[undo]["parents"][0]["sha"]
        gh.commits[undo]["message"] = f"Take #13 out of the batch\n\nThis undoes the merge of #13 into the batch ({merge[:12]})."
        sync(gh)
        [told] = self.reverted(gh, 13)
        self.assertTrue(told.startswith(f"<!-- batch-queue-reverted 1018 {undo} -->"))

    def test_a_short_id_counts_only_for_a_merge_that_brought_a_pull_request_in(self):
        gh = self.built()
        undo = merge_and_revert(gh, 13)
        merge = gh.commits[undo]["parents"][0]["sha"]
        # It names the head of #13 itself, and the commit the merge was made on: neither is a merge
        # that brought a pull request in.
        gh.commits[undo]["message"] = (f"Tidy up\n\nSee {gh.pulls[13]['sha'][:10]} and "
                                       f"{gh.commits[merge]['parents'][0]['sha'][:10]}.")
        sync(gh)
        self.assertEqual(self.reverted(gh, 13), [])

    def test_a_deferred_pull_request_is_not_told_it_was_reverted(self):
        gh = self.built(WITH_13)
        gh.label(13, add="deferred", login="maintainer")
        undo = merge_and_revert(gh, 13)
        log = sync(gh)
        self.assertEqual(self.reverted(gh, 13), [])
        self.assertNotIn("told #13 that the batch #1018 reverts it", log)
        # The batch's own comment still names it.
        [check] = self.checks(gh)
        self.assertIn(f"Reverted in this branch: #13 in `{undo[:10]}`.", check)

    def test_one_merged_in_at_another_commit_is_named_for_information_only(self):
        # As #1513 in batch 13: `main` was merged into it for the batch, and that merge was never
        # pushed to its branch.
        gh = self.built()
        sync(gh)
        gh.pulls[1018]["body"] = WITH_13
        old, head = gh.refs[HAND], gh.pulls[13]["sha"]
        with_main, merge = sha("13 with main"), sha("kim merge 13")
        gh.commits[with_main] = {"message": "Merge main into this branch", "parents": [{"sha": head}, {"sha": MAIN}]}
        gh.inside[with_main] = gh.inside[head] | {head, MAIN}
        gh.commits[merge] = {"message": "Merge PR #13 into batch", "parents": [{"sha": old}, {"sha": with_main}]}
        gh.inside[merge] = gh.inside[old] | gh.inside[with_main] | {old, with_main}
        gh.push(13, "head13-later")  # its head moved on, without that merge
        move(gh, merge)
        log = sync(gh)
        self.assertEqual(note(self.record(gh))["absorbed"], {"13": with_main})
        self.assertEqual(self.checks(gh), [])  # nothing is posted for it alone
        self.assertNotIn("posted on the batch #1018 what its description and its branch disagree on", log)
        # A comment that is there already shows it, and says all is well otherwise.
        gh.pulls[1018]["body"] = WITH_13.replace("- #12 Prune", "- #24 Not merged in (@eve)\n- #12 Prune")
        gh.touch(1018)
        sync(gh)
        gh.pulls[1018]["body"] = WITH_13
        gh.touch(1018)
        sync(gh)
        [check] = self.checks(gh)
        self.assertIn(f"In this branch at another commit than their head, merged in by the batch's own merge commit: "
                      f"#13 at `{with_main[:10]}`. This is for information", check)
        self.assertIn("Nothing else to report", check)
        self.assertNotIn("head commit is not in this branch", check)

    def test_a_revert_that_is_reverted_again_puts_it_back(self):
        gh = self.built()
        undo = merge_and_revert(gh, 13)
        again = sha("kim-reapply")
        gh.commits[again] = {"message": f'Reapply "Merge PR #13 into batch"\n\nThis reverts commit {undo}.',
                             "parents": [{"sha": undo}]}
        gh.inside[again] = gh.inside[undo] | {undo}
        move(gh, again)
        sync(gh)
        self.assertEqual(self.reverted(gh, 13), [])

    def test_a_revert_is_known_by_the_commit_it_names_not_by_its_first_line(self):
        gh = self.built()
        undo = merge_and_revert(gh, 13)
        gh.commits[undo]["message"] = "Take #13 out again\n\n" + gh.commits[undo]["message"].split("\n\n", 1)[1]
        sync(gh)
        [told] = self.reverted(gh, 13)
        self.assertTrue(told.startswith(f"<!-- batch-queue-reverted 1018 {undo} -->"))

    def test_merged_in_again_at_a_new_head_under_the_same_name_it_is_not_reverted(self):
        gh = self.built(WITH_13)
        merge_and_revert(gh, 13)
        sync(gh)
        self.assertEqual(len(self.reverted(gh, 13)), 1)
        gh.push(13, "head13-new")
        old, head = gh.refs[HAND], gh.pulls[13]["sha"]
        again = sha("kim merge again")
        gh.commits[again] = {"message": "Merge PR #13 into batch", "parents": [{"sha": old}, {"sha": head}]}
        gh.inside[again] = gh.inside[old] | gh.inside[head] | {old, head}
        move(gh, again)
        log = sync(gh)
        self.assertEqual(note(self.record(gh))["members"]["13"], head)
        self.assertEqual(note(self.record(gh))["reverted"], {})
        self.assertEqual(len(self.reverted(gh, 13)), 1)  # told about the first merge only
        [check] = self.checks(gh)
        self.assertNotIn("Reverted in this branch", check)
        self.assertNotIn("told #13 that the batch #1018 reverts it", log)

    def test_a_revert_of_the_reapplied_revert_is_told_again(self):
        gh = self.built()
        undo = merge_and_revert(gh, 13)
        sync(gh)
        again = sha("kim-reapply")
        gh.commits[again] = {"message": f'Reapply "Merge PR #13 into batch"\n\nThis reverts commit {undo}.',
                             "parents": [{"sha": undo}]}
        gh.inside[again] = gh.inside[undo] | {undo}
        move(gh, again)
        sync(gh)
        third = sha("kim-revert-again")
        gh.commits[third] = {"message": f'Revert "Reapply "Merge PR #13 into batch""\n\nThis reverts commit {again}.',
                             "parents": [{"sha": again}]}
        gh.inside[third] = gh.inside[again] | {again}
        move(gh, third)
        sync(gh)
        first, second = self.reverted(gh, 13)
        self.assertTrue(second.startswith(f"<!-- batch-queue-reverted 1018 {third} -->"))

    def stacked(self, upper):
        """#1018 holds #11 and #12 and lists them, and #1050 is stacked on it, adds #13 and has the
        description `upper`."""
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12, body="Included:\n\n- #11 Reuse\n- #12 Prune\n")
        by_hand(gh, 1018, 13, number=1050, ref="batch/b5-on-1018", name="b5", body=upper)
        sync(gh)
        return [body for body in gh.said(1050) if body.startswith(batch.CHECK)]

    def test_a_stacked_batch_lists_only_its_own(self):
        # Its record lists only its own members, so those of the batch under it are not unlisted.
        self.assertEqual(self.stacked("Stacked on #1018.\n\nIncluded:\n\n- #13 Shorten\n"), [])

    def test_a_stacked_batch_may_list_what_the_batch_under_it_holds(self):
        self.assertEqual(self.stacked("Included:\n\n- #11 Reuse\n- #12 Prune\n- #13 Shorten\n"), [])

    def test_a_stacked_batch_still_names_what_it_lists_and_nobody_holds(self):
        [check] = self.stacked("Included:\n\n- #11 Reuse\n- #13 Shorten\n- #14 Missing\n")
        self.assertIn("Listed as included, but not an open pull request: #14.", check)
        self.assertNotIn("#11", check)

    def test_a_note_from_before_reverts_were_recorded_lists_the_branch_once_more(self):
        gh = self.built()
        merge_and_revert(gh, 13)
        sync(gh)
        record = next(comment for comment in gh.comments[1018] if comment["body"].startswith("<!-- batch-queue-by-hand"))
        note = batch.load_note(batch.BY_HAND.match(record["body"]).group(1))
        for name in ("reverted", "warned", "check"):
            note.pop(name, None)
        record["body"] = batch.describe_by_hand(note)
        gh.reads = []
        sync(gh)
        self.assertEqual(len([path for path in gh.reads if path.startswith("compare/")]), 1)
        self.assertEqual(len(self.reverted(gh, 13)), 1)
        gh.reads = []
        sync(gh)
        self.assertEqual([path for path in gh.reads if path.startswith("compare/")], [])

    def test_the_check_waits_when_the_hours_allowance_is_nearly_gone(self):
        gh = self.built(WITH_13)
        sync(gh)
        gh.pulls[1018]["body"] = LISTED.replace("- #12 Prune", "- #24 Not merged in (@dan)\n- #12 Prune")
        gh.left = batch.RESERVE - 1
        log = sync(gh)
        self.assertIn("#13", self.checks(gh)[0])
        self.assertIn(f"only {batch.RESERVE - 1} requests left this hour: did not compare the description of the "
                      "batch #1018 with its branch, and the next run does", log)
        gh.left = 900
        sync(gh)
        self.assertIn("#24", self.checks(gh)[0])

    def test_a_refused_edit_is_tried_again(self):
        gh = self.built(WITH_13)
        sync(gh)
        gh.pulls[1018]["body"] = LISTED
        gh.fail("PATCH", r"issues/comments/\d+", 403)
        sync(gh)
        self.assertIn("#13", self.checks(gh)[0])
        sync(gh)
        self.assertIn("Nothing to report", self.checks(gh)[0])

class ConflictLabelsOff(unittest.TestCase):
    """While the conflict labels are switched off, the sync neither starts their workflow nor
    leaves anything to it: entries under a heading about conflicts are told like any other."""

    def setUp(self):
        batch._labels.CONFLICT_LABELS_ON = False

    def tearDown(self):
        batch._labels.CONFLICT_LABELS_ON = True

    def test_nothing_is_started_and_conflict_entries_are_told(self):
        self.check()

    def test_switched_on_in_the_code_but_not_by_the_repository_variable(self):
        batch._labels.CONFLICT_LABELS_ON = True
        for value in (None, "off"):
            with self.subTest(value=value), mock.patch.dict(os.environ):
                os.environ.pop("CONFLICT_LABELS", None)
                if value is not None:
                    os.environ["CONFLICT_LABELS"] = value
                self.check()

    def check(self):
        gh = Fake()
        gh.add_pull(11, "head11")
        gh.add_pull(21, "head21")
        by_hand(gh, 11)
        gh.pulls[1018]["body"] = "Left out because they conflict with a PR earlier in the batch:\n\n- #21 a (@x): conflicts with #11.\n"
        log = sync(gh)
        self.assertEqual(gh.dispatched, [])
        self.assertNotIn("started conflict-labels.yml", log)
        self.assertEqual(len([b for b in gh.said(21) if b.startswith("<!-- batch-queue-left-out")]), 1)


class ConflictWorkflow(unittest.TestCase):
    def test_a_batch_first_labelled_building_starts_the_conflict_labels(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        log = sync(gh)
        self.assertEqual(gh.dispatched, ["main"])
        self.assertIn("started conflict-labels.yml", log)
        sync(gh)
        self.assertEqual(gh.dispatched, ["main"])  # only when it is first labelled

    def test_a_batch_that_becomes_the_outermost_of_its_stack_starts_it_too(self):
        # It compares pull requests with the outermost batch of each stack only.
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12)
        by_hand(gh, 1018, 13, number=1050, ref="batch/b5-on-1018", name="b5")
        sync(gh)
        self.assertEqual(gh.dispatched, ["main"])  # once, although two batches got labels
        gh.close(1050)
        log = sync(gh)
        self.assertIn(f"#1018 is the outermost batch of its stack: now `{LATEST}`", log)
        self.assertEqual(gh.dispatched, ["main", "main"])

    def test_a_batch_stacked_on_the_outermost_starts_it_once_it_is_labelled_latest(self):
        gh = Fake()
        queue(gh, 11, 13)
        by_hand(gh, 11)
        sync(gh)
        gh.writes = []
        by_hand(gh, 1018, 13, number=1050, ref="batch/b5-on-1018", name="b5")
        sync(gh)
        self.assertEqual(gh.dispatched, ["main", "main"])
        writes = [(method, path) for method, path, _ in gh.writes]
        dispatch = writes.index(("POST", f"actions/workflows/{batch.CONFLICT_WORKFLOW}/dispatches"))
        self.assertLess(writes.index(("POST", "issues/1050/labels")), dispatch)
        self.assertLess(writes.index(("DELETE", "issues/1018/labels/latest%20batch")), dispatch)
        self.assertEqual(gh.pulls[1050]["labels"], {"large", BUILDING, LATEST})

    def test_only_headings_about_conflicts_with_the_batch_are_left_to_it(self):
        # The headings of batch 14 (#2164).
        headings = {
            "Included:": False,
            "Included, but borderline; these can be dropped if the maintainers prefer:": False,
            "Left out at the request of the author or a maintainer:": False,
            "Left out because they conflict with a PR earlier in this batch:": True,
            "Left out because main cannot simply be merged in:": False,
            "Left out because they conflict with main in a way that is not mechanical, so the author needs to "
            "merge main:": False,
            "Left out under the maintainers' guidance in `AGENTS.md`:": False,
            "Left out because they are labelled `deferred`:": False,
            "Left out for other reasons:": False,
            # Other wordings of the same two kinds.
            "Left out because they conflict with the batch:": True,
            "Left out (conflicts with an earlier PR of the batch):": True,
            "Left out: conflicts with main:": False,
        }
        for heading, about_the_batch in headings.items():
            with self.subTest(heading=heading):
                self.assertEqual(bool(batch.CONFLICT_HEADING.search(heading)), about_the_batch)

    def test_a_conflict_with_main_is_told_from_the_description(self):
        gh = Fake()
        gh.add_pull(11, "head11")
        gh.add_pull(21, "head21")
        by_hand(gh, 11)
        gh.pulls[1018]["body"] = ("Left out because they conflict with main in a way that is not mechanical, so the "
                                  "author needs to merge main:\n\n- #21 a (@x): `A.lean`.\n")
        sync(gh)
        self.assertEqual(len([b for b in gh.said(21) if b.startswith("<!-- batch-queue-left-out")]), 1)

    def test_conflict_entries_are_left_to_it_only_for_pull_requests_it_looks_at(self):
        gh = Fake()
        gh.add_pull(11, "head11")
        for number in (21, 22):
            gh.add_pull(number, f"head{number}")
        gh.pulls[22]["draft"] = True
        by_hand(gh, 11)
        gh.pulls[1018]["body"] = ("Left out because they conflict with a PR earlier in the batch:\n\n"
                                  "- #21 a (@x): conflicts with #11.\n- #22 b (@y): conflicts with #11.\n\n"
                                  "Left out (no conflicts, the build failed):\n\n- #23 c (@z): it fails.\n")
        gh.add_pull(23, "head23")
        sync(gh)
        left = lambda n: [b for b in gh.said(n) if b.startswith("<!-- batch-queue-left-out")]
        self.assertEqual([len(left(n)) for n in (21, 22, 23)], [0, 1, 1])


class MissingLabels(unittest.TestCase):
    def test_a_missing_label_stops_the_run_instead_of_being_created(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        gh.missing.add(MEMBER)
        with self.assertRaises(batch.Refused) as caught:
            sync(gh)
        self.assertIn("There is no `batch-building` label", str(caught.exception))
        self.assertNotIn(MEMBER, gh.pulls[14]["labels"])


class Reconciling(unittest.TestCase):
    """`frozen` follows `batch queue` and the batches being built."""

    def test_a_pull_request_queued_before_frozen_existed_is_frozen(self):
        gh = Fake()
        gh.add_pull(31, "head31")
        gh.say(31, f"<!-- batch-queue-approved {sha('head31')} -->\nApproved for batching at this commit.")
        gh.label(31, add=QUEUED)
        log = sync(gh)
        self.assertEqual(gh.pulls[31]["labels"], QF)
        self.assertIn("#31 is queued: now `frozen`", log)

    def test_every_queued_pull_request_is_looked_at(self):
        # With `ASSEMBLE` off nothing else reads what was queued. This costs a request for each pull
        # request labelled `batch queue`, every run: one pushed to is labelled `changed after
        # frozen` by the sync too, not only by the `pushed` job.
        gh = Fake()
        queue(gh, 33)
        gh.add_pull(31, "head31")
        gh.say(31, f"<!-- batch-queue-approved {sha('head31')} -->\nApproved for batching at this commit.")
        gh.label(31, add=QUEUED)
        gh.add_pull(34, "head34", labels=[QUEUED])  # labelled by hand: no `batch` stands for it
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (31, 33, 34)], [QF, QF, {QUEUED}])
        every = [f"issues/{n}/comments?per_page=100&page=1" for n in (31, 33, 34)]
        self.assertEqual([path for path in gh.reads if path.startswith("issues/") and "/comments" in path], every)
        gh.reads = []
        sync(gh)
        self.assertEqual([path for path in gh.reads if "/comments" in path], every)

    def test_labels_of_a_batch_nothing_holds_come_off(self):
        gh = Fake()
        gh.add_pull(32, "head32", labels=[MEMBER, FROZEN])
        log = sync(gh)
        self.assertEqual(gh.pulls[32]["labels"], set())
        self.assertIn("#32 is neither queued nor in a batch being built: `batch-building` and `frozen` removed", log)
        self.assertEqual(sync(gh), ["nothing to do"])


class Pushed(unittest.TestCase):
    """`--pushed`: what the workflow does for a push to a frozen pull request, without a sync."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        gh.add_pull(14, "head14")
        by_hand(gh, 11, 12, 14)
        sync(gh)
        gh.reads, gh.writes, gh.calls = [], [], 0
        return gh

    def pushes(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-pushed-while-frozen")]

    def test_a_member_pushed_to_is_told_once_and_handed_back(self):
        gh = self.built()
        gh.push(12, "head12-later")
        log = batch.pushed(gh, 12)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        [said] = self.pushes(gh, 12)
        self.assertTrue(said.startswith(f"<!-- batch-queue-pushed-while-frozen 1018 {sha('head12')} -->"))
        self.assertIn(f"builds and lands `{short('head12')}` only, not `{short('head12-later')}`", said)
        self.assertEqual(log, ["told #12 that it was pushed to after the batch #1018 took it: now `awaiting-author`",
                               f"#12 was pushed to after `{short('head12')}` was taken: now `{CHANGED}`"])
        # The label first, then the comment, then `changed after frozen`, and nothing else: the
        # batch's note is left to the sync.
        self.assertEqual([(method, path, payload.get("labels")) for method, path, payload in gh.writes],
                         [("POST", "issues/12/labels", [WAITING]), ("POST", "issues/12/comments", None),
                          ("POST", "issues/12/labels", [CHANGED])])
        self.assertLessEqual(gh.calls, 10)
        # A second push, and then the sync: nobody is told again, and the sync notes it.
        gh.label(12, remove=WAITING)  # the author commented `ready`
        gh.push(12, "head12-again")
        self.assertEqual(batch.pushed(gh, 12), ["#12: nothing to do"])
        sync(gh)
        self.assertEqual(len(self.pushes(gh, 12)), 1)
        self.assertEqual(gh.pulls[12]["labels"], IN | {CHANGED})
        self.assertEqual(note(gh.said(1018)[0])["pushed"], {"12": sha("head12")})

    def test_one_the_sync_told_already_is_not_told_again(self):
        gh = self.built()
        gh.push(12, "head12-later")
        sync(gh)
        gh.writes = []
        self.assertEqual(batch.pushed(gh, 12), ["#12: nothing to do"])
        self.assertEqual((gh.writes, len(self.pushes(gh, 12))), ([], 1))

    def test_a_pull_request_only_queued_is_told_nothing_but_labelled(self):
        gh = self.built()
        gh.push(13, "head13-later")
        self.assertEqual(batch.pushed(gh, 13),
                         [f"#13 was pushed to after `{short('head13')}` was taken: now `{CHANGED}`"])
        self.assertEqual(gh.said(13), [])
        self.assertEqual(gh.pulls[13]["labels"], QF | {CHANGED})
        self.assertLessEqual(gh.calls, 10)

    def test_one_frozen_for_nothing_loses_the_labels(self):
        gh = self.built()
        gh.add_pull(32, "head32", labels=[FROZEN])
        self.assertEqual(batch.pushed(gh, 32), ["#32 is neither queued nor in a batch being built: `frozen` removed"])
        self.assertEqual(gh.pulls[32]["labels"], set())

    def test_in_stacked_batches_its_own_batch_tells_it(self):
        gh = self.built()
        by_hand(gh, 1018, 13, number=1100, ref="batch/b5-on-1018", name="kim-b5")
        sync(gh)
        for number in (12, 13):
            gh.push(number, f"head{number}-later")
            self.assertEqual(batch.pushed(gh, number)[0], f"told #{number} that it was pushed to after the batch "
                             f"#{1018 if number == 12 else 1100} took it: now `{WAITING}`")
        self.assertTrue(self.pushes(gh, 12)[0].startswith(f"<!-- batch-queue-pushed-while-frozen 1018 {sha('head12')}"))
        self.assertTrue(self.pushes(gh, 13)[0].startswith(f"<!-- batch-queue-pushed-while-frozen 1100 {sha('head13')}"))

    def test_in_stacked_batches_the_lowest_record_that_holds_it_counts(self):
        # The upper batch's record was written before batches were stacked, and holds #12 too.
        gh = self.built()
        by_hand(gh, 1018, 13, number=1100, ref="batch/b5-on-1018", name="kim-b5")
        old = {"head": sha("kim-b5"), "members": {"12": sha("head12"), "13": sha("head13"), "1018": sha("kim")},
               "queued": ["12", "13"]}
        gh.say(1100, batch.describe_by_hand(old))
        gh.label(1100, add=BUILDING)
        gh.push(12, "head12-later")
        batch.pushed(gh, 12)
        [said] = self.pushes(gh, 12)
        self.assertTrue(said.startswith(f"<!-- batch-queue-pushed-while-frozen 1018 {sha('head12')} -->"))

    def test_of_two_batches_at_the_same_commit_the_lower_number_tells_it(self):
        gh = self.built()
        by_hand(gh, 11, 12, 14, number=1100, ref="batch/copy", name="kim")
        sync(gh)
        gh.push(12, "head12-later")
        log = batch.pushed(gh, 12)
        self.assertIn("told #12 that it was pushed to after the batch #1018 took it: now `awaiting-author`", log)
        self.assertEqual(len(self.pushes(gh, 12)), 1)

    def held_already(self, gh):
        """#12 is pushed to with a commit that the batch's branch already has, as when the merge of
        `main` that the batch was built from is pushed to the pull request afterwards."""
        merged = sha("head12-merged")
        gh.inside[gh.pulls[1018]["sha"]].add(merged)
        gh.inside[merged] = {sha("head12"), MAIN}
        gh.push(12, "head12-merged")
        return merged

    def test_a_push_of_a_commit_the_batch_has_already_is_not_told(self):
        gh = self.built()
        merged = self.held_already(gh)
        log = batch.pushed(gh, 12)
        self.assertEqual(log, [f"#12 was pushed to with `{merged[:10]}`, which the batch #1018 has already: nothing "
                               "to say"])
        self.assertEqual((gh.writes, self.pushes(gh, 12)), ([], []))
        self.assertEqual(gh.pulls[12]["labels"], IN)
        # The sync records the new commit, says nothing, and asks no more once it has.
        log = sync(gh)
        self.assertIn(f"#12 was pushed to with `{merged[:10]}`, which the batch #1018 has already: recorded at that "
                      "commit", log)
        record = note(gh.said(1018)[0])
        self.assertEqual((record["members"]["12"], record["told"]["12"]), (merged, merged))
        # Its one comment names the new commit now.
        [said] = gh.said(12)
        self.assertTrue(said.startswith(f"<!-- batch-queue-frozen 1018 {merged} -->"))
        gh.reads = []
        sync(gh)
        self.assertFalse([path for path in gh.reads if path.startswith("compare/")])
        # A later push that the batch does not have is told, at the commit now recorded.
        gh.push(12, "head12-later")
        batch.pushed(gh, 12)
        [said] = self.pushes(gh, 12)
        self.assertTrue(said.startswith(f"<!-- batch-queue-pushed-while-frozen 1018 {merged} -->"))

    def test_the_sync_alone_does_not_tell_a_push_the_batch_has_already(self):
        gh = self.built()
        merged = self.held_already(gh)
        gh.reads = []
        sync(gh)
        self.assertEqual(self.pushes(gh, 12), [])
        self.assertEqual(gh.pulls[12]["labels"], IN)
        self.assertEqual(note(gh.said(1018)[0])["members"]["12"], merged)
        # Whether the branch has the new head, and whether that has the commit the batch took.
        self.assertEqual(len([path for path in gh.reads if path.startswith("compare/")]), 2)

    def test_a_push_back_to_an_earlier_commit_the_batch_has_is_told(self):
        # The batch took `head12`. Its author drops that commit by force-pushing its parent, which
        # the branch has too. The batch still lands `head12`, so the push is told, by `pushed` or by
        # the sync, and the record stays at `head12`, even once the branch is listed again.
        for by_sync in (False, True):
            with self.subTest(by_sync=by_sync):
                gh = Fake()
                queue(gh, 11)
                gh.add_pull(12, "head12-first")
                gh.inside[sha("head12")] = {sha("head12-first")}
                gh.push(12, "head12")
                queue(gh, 12)
                by_hand(gh, 11, 12)
                sync(gh)
                self.assertIn(sha("head12-first"), gh.inside[gh.pulls[1018]["sha"]])
                gh.push(12, "head12-first")
                log = sync(gh) if by_sync else batch.pushed(gh, 12)
                self.assertIn("told #12 that it was pushed to after the batch #1018 took it: now `awaiting-author`",
                              log)
                [said] = self.pushes(gh, 12)
                self.assertTrue(said.startswith(f"<!-- batch-queue-pushed-while-frozen 1018 {sha('head12')} -->"))
                self.assertIn(f"builds and lands `{short('head12')}` only, not `{short('head12-first')}`", said)
                sync(gh)
                self.assertEqual(note(gh.said(1018)[0])["members"]["12"], sha("head12"))
                # Another pull request is merged into the branch, which is listed again.
                gh.add_pull(14, "head14")
                old = gh.pulls[1018]["sha"]
                new = sha("kim-with-14")
                gh.inside[new] = gh.inside[old] | {old, sha("head14")}
                gh.commits[new] = {"message": "Merge #14", "parents": [{"sha": old}, {"sha": sha("head14")}]}
                gh.refs[HAND], gh.pulls[1018]["sha"] = new, new
                gh.touch(1018)
                sync(gh)
                record = note(gh.said(1018)[0])
                self.assertEqual((record["members"]["12"], record["members"]["14"]), (sha("head12"), sha("head14")))
                self.assertEqual(len(self.pushes(gh, 12)), 1)
                self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})

    def test_a_push_back_unanswered_is_asked_about_again(self):
        gh = Fake()
        queue(gh, 11)
        gh.add_pull(12, "head12-first")
        gh.inside[sha("head12")] = {sha("head12-first")}
        gh.push(12, "head12")
        queue(gh, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        gh.push(12, "head12-first")
        # Whether the new head has the commit the batch took in it.
        ancestry = rf"compare/{sha('head12-first')}\.\.\.{sha('head12')}\?per_page=1"
        gh.fail("GET", ancestry, 502)
        self.assertEqual(batch.pushed(gh, 12)[0], "GitHub did not say whether the batch #1018 has the new head of #12, "
                         f"with `{short('head12')}` in it: the next sync asks again")
        gh.fail("GET", ancestry, 502)
        self.assertIn("GitHub did not say whether the batch #1018 has the new head of #12, with "
                      f"`{short('head12')}` in it: the next run asks again", sync(gh))
        # Its head is not the commit taken, so it is `changed after frozen` all the same.
        self.assertEqual((self.pushes(gh, 12), gh.pulls[12]["labels"]), ([], IN | {CHANGED}))
        # When the branch is listed again, the question is the other way round.
        old = gh.pulls[1018]["sha"]
        new = sha("kim-moved")
        gh.inside[new], gh.commits[new] = gh.inside[old] | {old}, {"message": "Merge", "parents": [{"sha": old}]}
        gh.refs[HAND], gh.pulls[1018]["sha"] = new, new
        gh.touch(1018)
        gh.fail("GET", rf"compare/{sha('head12')}\.\.\.{sha('head12-first')}\?per_page=1", 502)
        self.assertIn("GitHub did not say whether #12 was pushed back to an earlier commit than the one the batch "
                      "#1018 took: the next run looks again", sync(gh))
        self.assertEqual(note(gh.said(1018)[0])["members"]["12"], sha("head12"))
        sync(gh)
        self.assertEqual(len(self.pushes(gh, 12)), 1)

    def test_a_new_head_merged_on_top_is_taken_though_it_lacks_the_old_commit(self):
        # Rewritten, and merged into the branch on top of the commit the batch took: the batch
        # holds the new head, whichever commit it has besides.
        gh = self.built()
        gh.push(12, "head12-rewritten")
        old, head = gh.pulls[1018]["sha"], sha("head12-rewritten")
        new = sha("kim-with-12-rewritten")
        gh.inside[new] = gh.inside[old] | {old, head}
        gh.commits[new] = {"message": "Merge PR #12 into batch", "parents": [{"sha": old}, {"sha": head}]}
        gh.refs[HAND], gh.pulls[1018]["sha"] = new, new
        gh.touch(1018)
        sync(gh)
        self.assertEqual(note(gh.said(1018)[0])["members"]["12"], head)
        self.assertEqual((self.pushes(gh, 12), gh.pulls[12]["labels"]), ([], IN))

    def test_a_batch_or_a_closed_pull_request_is_not_looked_at(self):
        gh = self.built()
        self.assertEqual(batch.pushed(gh, 1018), ["#1018 holds a batch: the sync looks after it"])
        gh.close(14)
        self.assertEqual(batch.pushed(gh, 14), ["#14 is not open: nothing to do"])
        self.assertEqual(gh.writes, [])


class BackAtItsHead(unittest.TestCase):
    """A member pushed to after its batch took it gets `awaiting-author`. Once the batch holds its
    head again, the label comes off, if the workflow put it on."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        return gh

    def taken(self, gh):
        """The new head of #12 is merged into the batch."""
        by_hand(gh, 11, 12, name="kim-with-12-later")

    def stored(self, gh):
        return note(gh.said(1018)[0])

    def test_when_the_batch_takes_the_new_head_the_label_comes_off(self):
        gh = self.built()
        gh.push(12, "head12-later")
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        self.assertEqual((self.stored(gh)["pushed"], self.stored(gh)["waiting"]), ({"12": sha("head12")}, ["12"]))
        self.taken(gh)
        log = sync(gh)
        self.assertIn("#12 is in the batch #1018 at its head again: `awaiting-author` removed", log)
        self.assertEqual(gh.pulls[12]["labels"], IN)
        self.assertNotIn("waiting", self.stored(gh))
        self.assertNotIn('"waiting"', gh.said(1018)[0])
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_a_label_a_person_put_on_stays(self):
        gh = self.built()
        gh.label(12, add=WAITING, login="maintainer")  # `aa`
        gh.push(12, "head12-later")
        sync(gh)
        [said] = [body for body in gh.said(12) if body.startswith("<!-- batch-queue-pushed-while-frozen")]
        self.assertNotIn(batch.HANDED_BACK, said)
        self.assertNotIn("waiting", self.stored(gh))
        self.taken(gh)
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING})

    def test_a_label_put_back_by_a_person_after_ready_stays(self):
        gh = self.built()
        gh.push(12, "head12-later")
        sync(gh)
        gh.label(12, remove=WAITING, login="author")  # `ready`
        sync(gh)
        self.assertNotIn("waiting", self.stored(gh))
        gh.label(12, add=WAITING, login="maintainer")  # `aa`
        self.taken(gh)
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING})

    def test_told_by_pushed_before_the_sync_noted_it(self):
        gh = self.built()
        gh.push(12, "head12-later")
        batch.pushed(gh, 12)
        [said] = [body for body in gh.said(12) if body.startswith("<!-- batch-queue-pushed-while-frozen")]
        self.assertIn(batch.HANDED_BACK, said)
        # The batch takes the new head before any sync has read that comment.
        self.taken(gh)
        log = sync(gh)
        self.assertIn("#12 is in the batch #1018 at its head again: `awaiting-author` removed", log)
        self.assertEqual(gh.pulls[12]["labels"], IN)

    def test_noted_by_a_sync_after_pushed_told_it(self):
        gh = self.built()
        gh.push(12, "head12-later")
        batch.pushed(gh, 12)
        sync(gh)
        self.assertEqual(self.stored(gh)["waiting"], ["12"])
        self.taken(gh)
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN)

    def test_pushed_back_to_the_commit_the_batch_took(self):
        for noted in (True, False):
            with self.subTest(noted=noted):
                gh = self.built()
                gh.push(12, "head12-later")
                batch.pushed(gh, 12)
                if noted:
                    sync(gh)
                gh.push(12, "head12")  # force-pushed back
                log = batch.pushed(gh, 12)
                self.assertIn("#12 is in the batch #1018 at its head again: `awaiting-author` removed", log)
                self.assertEqual(gh.pulls[12]["labels"], IN)
                sync(gh)
                self.assertEqual(gh.pulls[12]["labels"], IN)
                self.assertNotIn("waiting", self.stored(gh))

    def test_pushed_back_with_a_label_a_person_put_on_it_stays(self):
        gh = self.built()
        gh.label(12, add=WAITING, login="maintainer")
        gh.push(12, "head12-later")
        batch.pushed(gh, 12)
        gh.push(12, "head12")
        self.assertEqual(batch.pushed(gh, 12),
                         [f"#12 is at `{short('head12')}`, the commit that was taken: `{CHANGED}` removed"])
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING})

    def test_taken_at_an_older_head_than_the_latest_push_it_waits_for_that_one(self):
        gh = self.built()
        gh.push(12, "head12-later")
        gh.inside[sha("head12-later")] = {sha("head12")}
        sync(gh)
        self.taken(gh)
        gh.push(12, "head12-latest")
        gh.inside[sha("head12-latest")] = {sha("head12-later"), sha("head12")}
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        self.assertEqual(self.stored(gh)["waiting"], ["12"])
        by_hand(gh, 11, 12, name="kim-with-12-latest")
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN)


class NewHeadTaken(unittest.TestCase):
    """When a batch assembled by hand takes a member's new head, the comments that named the commit
    it took before are edited to name the new one: nothing new is posted."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        return gh

    def taken(self, gh):
        """The new head of #12 is merged into the batch."""
        by_hand(gh, 11, 12, name="kim-with-12-later")

    def held_already(self, gh):
        """#12 is pushed to with a commit that the batch's branch has already, with the commit the
        batch took in it."""
        gh.inside[gh.pulls[1018]["sha"]].add(sha("head12-merged"))
        gh.inside[sha("head12-merged")] = {sha("head12"), MAIN}
        gh.push(12, "head12-merged")

    def ours(self, gh, number):
        """This script's comments on a pull request, as they stand."""
        return [item for item in gh.comments.get(number, [])
                if not item["body"].startswith(("<!-- batch-queue-approved", "<!-- batch-queue-withdrawn"))]

    def pushed_to(self, gh, by_sync):
        """#12 is pushed to with a commit the batch does not have, and told so. Returns the ids of
        its two comments."""
        gh.push(12, "head12-later")
        if by_sync:
            sync(gh)
        else:
            batch.pushed(gh, 12)
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING, CHANGED})
        return [item["id"] for item in self.ours(gh, 12)]

    def check(self, gh, ids, new="head12-later", handed=True):
        frozen, notice = self.ours(gh, 12)
        self.assertEqual([frozen["id"], notice["id"]], ids)
        self.assertTrue(frozen["body"].startswith(f"<!-- batch-queue-frozen 1018 {sha(new)} -->\n"))
        self.assertIn(f"Commit `{short(new)}` of this pull request is in batch #1018", frozen["body"])
        self.assertTrue(notice["body"].startswith(f"<!-- batch-queue-pushed-then-taken 1018 {sha('head12')} -->\n"))
        self.assertIn(f"pushed to after batch #1018 took its commit `{short('head12')}`. The batch has since taken "
                      f"its new head `{short(new)}`, and builds and lands that instead, so nothing more is needed "
                      "here.", notice["body"])
        self.assertEqual(batch.HANDED_BACK in notice["body"], handed)
        # Still `frozen`, and no longer `changed after frozen`.
        self.assertEqual(gh.pulls[12]["labels"], IN if handed else IN | {WAITING})
        record = note(gh.said(1018)[0])
        self.assertEqual((record["members"]["12"], record["told"]["12"]), (sha(new), sha(new)))
        self.assertNotIn("12", record.get("pushed", {}))
        # Nothing more on the next run.
        gh.reads, gh.writes = [], []
        sync(gh)
        self.assertEqual(([(method, path) for method, path, _ in gh.writes if "/12/" in path],
                          [path for path in gh.reads if path.startswith("issues/12/")]), ([], []))

    def test_when_a_sync_told_it_it_was_pushed_to(self):
        gh = self.built()
        ids = self.pushed_to(gh, by_sync=True)
        self.taken(gh)
        gh.reads, gh.writes = [], []
        log = sync(gh)
        self.assertEqual(gh.reads.count("issues/12/comments?per_page=100&page=1"), 1)
        self.assertFalse([path for method, path, _ in gh.writes if method == "POST" and path == "issues/12/comments"])
        self.check(gh, ids)
        self.assertIn(f"#12 is in the batch #1018 at its new head `{short('head12-later')}`: its comments say so now",
                      log)
        self.assertIn("#12 is in the batch #1018 at its head again: `awaiting-author` removed", log)

    def test_when_pushed_told_it_before_a_sync_noted_it(self):
        gh = self.built()
        ids = self.pushed_to(gh, by_sync=False)
        self.taken(gh)
        gh.reads = []
        sync(gh)
        # The comments `retell` read tell `unwait` that the label was the workflow's.
        self.assertEqual(gh.reads.count("issues/12/comments?per_page=100&page=1"), 1)
        self.check(gh, ids)

    def test_a_label_a_person_put_on_stays(self):
        gh = self.built()
        gh.label(12, add=WAITING, login="maintainer")  # `aa`
        ids = self.pushed_to(gh, by_sync=True)
        self.taken(gh)
        sync(gh)
        self.check(gh, ids, handed=False)

    def test_a_push_of_a_commit_the_batch_has_already_after_pushed_told_it(self):
        # `pushed` tells the first push, and says nothing about the second, which the batch has
        # already: the sync records it, edits both comments and takes the label off.
        gh = self.built()
        ids = self.pushed_to(gh, by_sync=False)
        self.held_already(gh)
        gh.writes = []
        self.assertEqual(batch.pushed(gh, 12), [f"#12 was pushed to with `{short('head12-merged')}`, which the batch "
                                                "#1018 has already: nothing to say",
                                                f"#12 is at `{short('head12-merged')}`, the commit that was taken: "
                                                f"`{CHANGED}` removed"])
        # It is frozen at the new head at once, and its comments wait for the sync.
        self.assertEqual([(method, path) for method, path, _ in gh.writes],
                         [("DELETE", "issues/12/labels/changed%20after%20frozen")])
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING})
        gh.reads = []
        log = sync(gh)
        self.assertEqual(gh.reads.count("issues/12/comments?per_page=100&page=1"), 1)
        self.check(gh, ids, new="head12-merged")
        self.assertIn("#12 is in the batch #1018 at its head again: `awaiting-author` removed", log)

    def test_a_comment_that_cannot_be_edited_is_tried_again_by_the_next_run(self):
        for has_head in (False, True):
            with self.subTest(has_head=has_head):
                gh = self.built()
                [frozen] = self.ours(gh, 12)
                if has_head:
                    self.held_already(gh)
                else:
                    gh.push(12, "head12-later")
                    self.taken(gh)
                new = "head12-merged" if has_head else "head12-later"
                gh.fail("PATCH", rf"issues/comments/{frozen['id']}", 403)
                log = sync(gh)
                self.assertEqual([line for line in log if line.startswith("GitHub would not")],
                                 [f"GitHub would not bring up to date what #12 was told about the batch #1018: it "
                                  f"stays at `{short('head12')}` until the next run"])
                record = note(gh.said(1018)[0])
                self.assertEqual((record["members"]["12"], record["told"]["12"]), (sha("head12"),) * 2)
                self.assertTrue(self.ours(gh, 12)[0]["body"].startswith(f"<!-- batch-queue-frozen 1018 {sha('head12')}"))
                sync(gh)
                [said] = self.ours(gh, 12)
                self.assertEqual(said["id"], frozen["id"])
                self.assertTrue(said["body"].startswith(f"<!-- batch-queue-frozen 1018 {sha(new)} -->"))
                self.assertEqual(note(gh.said(1018)[0])["members"]["12"], sha(new))

    def test_with_its_comment_gone_it_is_told_afresh(self):
        gh = self.built()
        gh.comments[12] = [item for item in gh.comments[12] if not item["body"].startswith("<!-- batch-queue-frozen")]
        gh.push(12, "head12-later")
        self.taken(gh)
        log = sync(gh)
        [said] = self.ours(gh, 12)
        self.assertTrue(said["body"].startswith(f"<!-- batch-queue-frozen 1018 {sha('head12-later')} -->"))
        self.assertIn(f"#12 is in the batch #1018 at its new head `{short('head12-later')}`: told that it is frozen "
                      "at that commit", log)


class LeftOutDigests(unittest.TestCase):
    def test_the_kind_of_reason_is_its_heading_up_to_any_parenthesis(self):
        digest = batch.left_out_digest
        self.assertEqual(digest("Left out under the maintainers' guidance in `AGENTS.md` (no instance switching):", "a"),
                         digest("Left out under the maintainers' guidance in `AGENTS.md` (no workarounds):", "b"))
        self.assertNotEqual(digest("Left out for other reasons:", "a"),
                            digest("Left out because they conflict with a PR earlier in the batch:", "a"))


class ChangedAfterFrozen(unittest.TestCase):
    """`changed after frozen` marks a frozen pull request whose head has moved on."""

    def test_a_queued_pull_request_pushed_to_and_queued_again(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        gh.push(11, "head11-later")
        # The push runs `pushed`, which labels it.
        log = batch.pushed(gh, 11)
        self.assertEqual(gh.pulls[11]["labels"], QF | {CHANGED})
        self.assertIn(f"#11 was pushed to after `{short('head11')}` was taken: now `changed after frozen`", log)
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], QF | {CHANGED})
        queue(gh, 11)  # a maintainer queues the new head
        log = sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], QF)
        self.assertIn(f"#11 is at `{short('head11-later')}`, the commit that was taken: `changed after frozen` removed",
                      log)

    def test_a_queued_pull_request_is_labelled_by_a_sync_when_the_pushed_job_failed(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        gh.push(11, "head11-later")
        log = sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], QF | {CHANGED})
        self.assertIn(f"#11 was pushed to after `{short('head11')}` was taken: now `changed after frozen`", log)

    def test_a_member_pushed_to_with_a_commit_its_batch_has_already_is_not_changed_after_frozen(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        sync(gh)
        merged = sha("head14-merged")
        gh.inside[gh.pulls[1018]["sha"]].add(merged)
        gh.inside[merged] = {sha("head14"), MAIN}
        gh.push(14, "head14-merged")
        batch.pushed(gh, 14)
        self.assertEqual(gh.pulls[14]["labels"], IN)
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], IN)
        self.assertEqual(note(gh.said(1018)[0])["members"]["14"], merged)

    def test_a_member_pushed_to_until_its_batch_lands(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        sync(gh)
        gh.push(14, "head14-later")
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], IN | {WAITING, CHANGED})
        gh.close(1018, merged=True)
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], {WAITING})  # no longer frozen, so not changed after it either

    def test_withdrawn_it_loses_the_label_and_closed_too(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        gh.push(11, "head11-later")
        gh.push(12, "head12-later")
        sync(gh)
        unqueue(gh, 11)
        gh.close(12)
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (set(), set()))

    def test_a_member_whose_labels_were_taken_off_by_hand_is_left_alone(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        sync(gh)
        gh.label(14, remove=MEMBER, login="maintainer")
        gh.label(14, remove=FROZEN, login="maintainer")
        gh.push(14, "head14-later")
        sync(gh)
        self.assertEqual(gh.pulls[14]["labels"], {WAITING})

    def test_a_member_whose_frozen_was_taken_off_after_it_changed_loses_the_label(self):
        gh = Fake()
        gh.add_pull(14, "head14")
        by_hand(gh, 14)
        sync(gh)
        gh.push(14, "head14-later")
        sync(gh)
        self.assertIn(CHANGED, gh.pulls[14]["labels"])
        gh.label(14, remove=FROZEN, login="maintainer")
        sync(gh)
        self.assertNotIn(CHANGED, gh.pulls[14]["labels"])

    def test_a_member_loses_the_label_once_pushed_to_a_commit_its_batch_has_already(self):
        # Pushed to with a commit the batch does not have, and then with one it has: the batch
        # takes the new head through `takes`, whether `pushed` runs for the second push or not.
        for job in (True, False):
            with self.subTest(job=job):
                gh = Fake()
                gh.add_pull(14, "head14")
                by_hand(gh, 14)
                sync(gh)
                gh.push(14, "head14-later")
                batch.pushed(gh, 14)
                self.assertEqual(gh.pulls[14]["labels"], IN | {WAITING, CHANGED})
                merged = sha("head14-merged")
                gh.inside[gh.pulls[1018]["sha"]].add(merged)
                gh.inside[merged] = {sha("head14"), MAIN}
                gh.push(14, "head14-merged")
                if job:
                    batch.pushed(gh, 14)
                    self.assertEqual(gh.pulls[14]["labels"], IN | {WAITING})
                log = sync(gh)
                self.assertEqual(gh.pulls[14]["labels"], IN)
                self.assertEqual(note(gh.said(1018)[0])["members"]["14"], merged)
                if not job:
                    self.assertIn(f"#14 is at `{merged[:10]}`, the commit that was taken: `{CHANGED}` removed", log)

class Unlinked(unittest.TestCase):
    """Quoted entries name pull requests without linking to them."""

    def test_references_to_this_repository_go_in_code_spans(self):
        self.assertEqual(batch.unlinked(f"{URL}21 fold: conflicts with #11 (`A.lean`); #12.", REPO),
                         f"`{URL}21` fold: conflicts with `#11` (`A.lean`); `#12`.")
        self.assertEqual(batch.unlinked(f"see [the fix]({URL}30) and https://github.com/o/r/issues/7#issuecomment-1", REPO),
                         f"see the fix (`{URL}30`) and `https://github.com/o/r/issues/7#issuecomment-1`")

    def test_what_is_not_a_reference_here_is_left_alone(self):
        for text in ("already `#11` or `see #12 here`", "other/repo#5 and https://github.com/x/y/pull/5",
                     "issue#5, &#35; and C#", "a heading:"):
            with self.subTest(text=text):
                self.assertEqual(batch.unlinked(text, REPO), text)


class OlderRecords(unittest.TestCase):
    """A batch whose record is older than the notices of what a batch leaves out."""

    def built(self):
        gh = Fake()
        queue(gh, 11, 12)
        for number in (21, 22, 23, 24):
            gh.add_pull(number, f"head{number}")
        by_hand(gh, 11, 12)
        gh.pulls[1018]["body"] = DESCRIPTION
        # Its record, as the workflow before this kept it, labelled `building`.
        gh.label(1018, add=BUILDING)
        gh.say(1018, "<!-- batch-queue-by-hand " + json.dumps(
            {"head": sha("kim"), "members": {"11": sha("head11"), "12": sha("head12")}, "queued": ["11", "12"]})
               + " -->\nWhile this pull request is open, ...")
        for number in (11, 12):
            gh.label(number, remove=QUEUED)
            gh.label(number, add=BUILDING)
        return gh

    def left(self, gh, number):
        return [body for body in gh.said(number) if body.startswith("<!-- batch-queue-left-out")]

    def test_what_the_description_leaves_out_now_is_not_told(self):
        gh = self.built()
        log = sync(gh)
        self.assertEqual([self.left(gh, n) for n in (21, 22, 23)], [[], [], []])
        self.assertEqual([gh.pulls[n]["labels"] for n in (21, 22, 23)], [set(), set(), set()])
        self.assertIn("the record of the batch #1018 is older than the notices of what a batch leaves out: "
                      "what its description leaves out now, 3 pull request(s), is taken as told", log)
        # The members are labelled, but not told that they are frozen: the batch was under way.
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12)], [IN, IN])
        self.assertEqual([[b for b in gh.said(n) if b.startswith("<!-- batch-queue-frozen")] for n in (11, 12)], [[], []])
        self.assertIn("the record of the batch #1018 is older than the notices that a pull request is frozen: "
                      "its 2 pull request(s) are labelled but not told", log)
        # What is listed under the heading about conflicts is left to the conflict-labels workflow.
        self.assertEqual(sorted(note(gh.said(1018)[0])["left"]), ["23"])

    def test_a_pull_request_that_joins_afterwards_is_told_it_is_frozen(self):
        gh = self.built()
        sync(gh)
        gh.add_pull(13, "head13")
        by_hand(gh, 11, 12, 13, name="kim-with-13")
        sync(gh)
        frozen = lambda n: [b for b in gh.said(n) if b.startswith("<!-- batch-queue-frozen")]
        self.assertEqual([len(frozen(n)) for n in (11, 12, 13)], [0, 0, 1])

    def test_only_what_is_added_or_changed_afterwards_is_told(self):
        gh = self.built()
        sync(gh)
        body = DESCRIPTION.replace("it changes `src/Main.lean`", "it edits `src/Main.lean`")
        body = body.replace("Left out for other reasons:\n\n", f"Left out for other reasons:\n\n- {URL}24 New (@gil): too big.\n")
        # #22's entry is removed: it was never told it was left out, so it is not told that it no longer is.
        body = body.replace("- #22 chore: remove a lemma (@erin): conflicts with #11 (`C.lean`).\n", "")
        gh.pulls[1018]["body"] = body
        gh.touch(1018)
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (21, 22, 23, 24)], [0, 0, 1, 1])
        self.assertEqual(gh.said(22), [])
        self.assertIn("it edits `src/Main.lean`", self.left(gh, 23)[0])
        self.assertEqual([gh.pulls[n]["labels"] for n in (22, 23, 24)], [set(), set(), set()])
        self.assertEqual(sorted(note(gh.said(1018)[0])["left"]), ["23", "24"])

    def test_a_record_with_left_out_notices_tells_what_is_new(self):
        # A record of this workflow, which has `left`, even an empty one, is not filled in again.
        gh = self.built()
        record = gh.comments[1018][-1]
        record["body"] = record["body"].replace('"queued"', '"left": {}, "queued"')
        sync(gh)
        # #21 and #22 are listed under the heading about conflicts, left to the conflict-labels workflow.
        self.assertEqual([len(self.left(gh, n)) for n in (21, 22, 23)], [0, 0, 1])


def resets(gh):
    return [(path, payload["sha"]) for method, path, payload in gh.writes if method == "PATCH" and path.startswith("git/refs/")]


class Notes(unittest.TestCase):
    """The note of a batch assembled by hand, as it is kept in the record comment on GitHub."""

    # A note as `hold` leaves it in memory, and as notes were kept on GitHub before `dump_note`.
    OLD = {"head": sha("kim"), "members": {"11": sha("head11"), "12": sha("head12"), "14": sha("head14")},
           "queued": ["11", "12"], "labelled": ["11", "14"],
           "told": {"11": sha("head11"), "12": sha("head12"), "14": sha("head14-before")},
           "pushed": {"12": sha("head12"), "14": sha("head14-before")}, "left": {"21": "0123456789abcdef"}}
    # A note as `dump_note` wrote it before it kept what members were labelled and told.
    QUEUED_ONLY = {"head": sha("kim"), "members": {"11": sha("head11"), "12": sha("head12"), "14": sha("head14")},
                   "queued": ["11", "12"]}

    def test_an_old_note_is_read_as_it_was_written(self):
        self.assertEqual(batch.load_note(json.dumps(self.OLD, sort_keys=True)), self.OLD)

    def test_a_note_keeps_only_the_entries_that_count(self):
        kept = batch.load_note(batch.dump_note(self.OLD))
        # An entry whose commit is not the member's no longer counts.
        wanted = dict(self.OLD, told={"11": sha("head11"), "12": sha("head12")}, pushed={"12": sha("head12")})
        self.assertEqual(kept, wanted)
        self.assertEqual(batch.load_note(batch.dump_note(kept)), kept)
        stored = json.loads(batch.dump_note(self.OLD))
        self.assertEqual((stored["unqueued"], stored["unlabelled"], stored["untold"], stored["pushed"]),
                         ([14], [12], [14], [12]))

    def test_what_the_description_check_remembers_is_kept_and_left_out_when_empty(self):
        full = dict(self.QUEUED_ONLY, reverted={}, absorbed={"13": sha("13 with main")}, fates={"15": "merged"})
        self.assertEqual(batch.load_note(batch.dump_note(full)), full)
        empty = dict(full, absorbed={}, fates={})
        stored = json.loads(batch.dump_note(empty))
        self.assertNotIn("absorbed", stored)
        self.assertNotIn("fates", stored)
        self.assertEqual(batch.load_note(batch.dump_note(empty)), dict(self.QUEUED_ONLY, reverted={}, absorbed={}))

    def test_queued_is_kept_as_the_shorter_list(self):
        stored = json.loads(batch.dump_note(self.QUEUED_ONLY))
        self.assertEqual((stored.get("queued"), stored.get("unqueued")), (None, [14]))
        self.assertEqual(batch.load_note(batch.dump_note(self.QUEUED_ONLY)), self.QUEUED_ONLY)
        few = dict(self.QUEUED_ONLY, queued=["12"])
        stored = json.loads(batch.dump_note(few))
        self.assertEqual((stored.get("queued"), stored.get("unqueued")), ([12], None))
        self.assertEqual(batch.load_note(batch.dump_note(few)), few)
        # A pull request that is not a member is not kept.
        self.assertEqual(batch.load_note(batch.dump_note(dict(self.QUEUED_ONLY, queued=["11", "12", "99"]))),
                         self.QUEUED_ONLY)

    def test_the_batches_below_are_kept(self):
        stacked = dict(batch.load_note(batch.dump_note(self.OLD)), below={"1018": sha("kim")})
        self.assertEqual(json.loads(batch.dump_note(stacked))["below"], {"1018": sha("kim")})
        self.assertEqual(batch.load_note(batch.dump_note(stacked)), stacked)
        self.assertNotIn("below", json.loads(batch.dump_note(dict(self.OLD, below={}))))

    def test_the_labels_the_workflow_handed_back_are_kept(self):
        kept = batch.load_note(batch.dump_note(self.OLD))
        waiting = dict(kept, waiting=["12", "99"])  # #99 is not a member
        self.assertEqual(json.loads(batch.dump_note(waiting))["waiting"], [12])
        self.assertEqual(batch.load_note(batch.dump_note(waiting)), dict(kept, waiting=["12"]))
        self.assertNotIn("waiting", json.loads(batch.dump_note(dict(kept, waiting=[]))))

    def test_a_key_the_note_lacks_stays_missing(self):
        # A note from before `queued` was recorded holds only queued pull requests.
        earliest = {"head": sha("kim"), "members": {"11": sha("head11")}}
        self.assertEqual(batch.load_note(batch.dump_note(earliest)), earliest)
        self.assertEqual(batch.load_note(json.dumps(earliest)), earliest)
        self.assertEqual(batch.queued_before(batch.load_note(json.dumps(earliest))), {"11"})

    def test_what_is_not_a_note_reads_as_an_empty_one(self):
        for text in ("[1, 2]", "{not json", '"text"'):
            with self.subTest(text=text):
                self.assertEqual(batch.load_note(text), {})

    def test_a_thousand_members_fit_in_one_comment(self):
        # Nine in ten queued, nearly all labelled and told, and some of everything else, with pull
        # requests numbered as now and as they will be after #9999.
        for first in (1000, 10000):
            with self.subTest(first=first):
                numbers = [str(number) for number in range(first, first + 1000)]
                found = {key: sha(f"member {key}") for key in numbers}
                kept = {"head": sha("head"), "members": found,
                        "queued": [key for key in numbers if int(key) % 10], "labelled": numbers[1:],
                        "told": {key: found[key] for key in numbers[5:]},
                        "pushed": {key: found[key] for key in numbers[::20]},
                        "left": {str(number): "0123456789abcdef" for number in range(first + 1000, first + 1030)}}
                text = batch.describe_by_hand(kept)
                self.assertLess(len(text), 65536)
                self.assertEqual(note(text), kept)

    def test_a_record_in_the_old_format_is_rewritten_once_and_nothing_is_told_again(self):
        gh = Fake()
        queue(gh, 11, 12)
        gh.add_pull(14, "head14")
        by_hand(gh, 11, 12, 14)
        sync(gh)
        gh.push(12, "head12-later")
        sync(gh)
        record = next(item for item in gh.comments[1018] if item["body"].startswith("<!-- batch-queue-by-hand"))
        kept = note(record["body"])
        self.assertEqual((sorted(kept["told"]), sorted(kept["pushed"])), (["11", "12", "14"], ["12"]))
        record["body"] = record["body"].replace(batch.dump_note(kept), json.dumps(kept, sort_keys=True))
        self.assertIn('"told": {', record["body"])
        gh.writes = []
        sync(gh)
        self.assertEqual(gh.writes, [("PATCH", f"issues/comments/{record['id']}", {"body": batch.describe_by_hand(kept)})])
        self.assertEqual(note(record["body"]), kept)
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.writes, [])

    def test_a_record_written_before_members_were_told_is_carried_on(self):
        # As R0's `dump_note` wrote it: members and `queued` only, so the members are labelled, but
        # not told: the batch was under way before anyone was told.
        gh = Fake()
        queue(gh, 11, 12)
        gh.add_pull(14, "head14")
        by_hand(gh, 11, 12, 14)
        gh.label(1018, add=BUILDING)
        gh.say(1018, batch.describe_by_hand(dict(self.QUEUED_ONLY)))
        for number in (11, 12, 14):
            gh.label(number, add=BUILDING)
        gh.label(11, remove=QUEUED)
        gh.label(12, remove=QUEUED)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 14)], [IN, IN, IN])
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14)], [0, 0, 0])
        self.assertEqual(note(gh.said(1018)[0])["queued"], ["11", "12"])
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])


class StackedOnABatchByHand(WithAssembly):
    """The batch being assembled sits on top of the batch assembled by hand that is being built."""

    def stacked(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12)
        return gh, sync(gh)

    def move_on(self, gh, name="kim-2"):
        """Commits are pushed onto the batch assembled by hand."""
        old, new = gh.refs[HAND], sha(name)
        gh.inside[new] = gh.inside[old] | {old}
        gh.commits[new] = {"message": "Fix the build", "parents": [{"sha": old}]}
        gh.refs[HAND] = gh.pulls[1018]["sha"] = new
        gh.touch(1018)
        return new

    def test_a_new_batch_starts_on_top_of_it(self):
        gh, log = self.stacked()
        self.assertIn(("POST", "git/refs", {"ref": f"refs/heads/{FIRST}", "sha": sha("kim")}), gh.writes)
        self.assertEqual(merges(gh), [sha("head13")])
        self.assertIn(f"started `{FIRST}` on top of #1018", log)
        body = batch_pull(gh)["body"]
        self.assertIn(f"Built on top of #1018 at `{short('kim')}`. Merge it after #1018: merging it first lands "
                      "the pull requests of #1018 too.", body)
        self.assertIn(f"In this batch:\n\n- #13 at `{short('head13')}`\n\nMerge this", body)
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.writes, [])

    def test_a_batch_started_on_main_is_rebuilt_on_top_of_it(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        sync(gh)
        by_hand(gh, 11, 12)
        gh.writes = []
        log = sync(gh)
        self.assertEqual((resets(gh), merges(gh)), ([(f"git/refs/heads/{FIRST}", sha("kim"))], [sha("head13")]))
        self.assertIn(f"rebuilt `{FIRST}` on top of #1018 at `{short('kim')}`", log)
        body = batch_pull(gh)["body"]
        self.assertIn(f"In this batch:\n\n- #13 at `{short('head13')}`\n\nMerge this", body)
        self.assertNotIn("Also in this branch", body)
        self.assertEqual((told(gh, 11), told(gh, 12)), ([], []))

    def test_when_it_moves_on_its_new_head_is_merged_in(self):
        gh, _ = self.stacked()
        new = self.move_on(gh)
        gh.writes = []
        log = sync(gh)
        self.assertEqual((resets(gh), merges(gh)), ([], [new]))
        self.assertIn(new, gh.inside[gh.refs[FIRST]])
        self.assertIn(f"brought `{FIRST}` up to date with #1018 at `{short('kim-2')}`", log)
        self.assertIn(f"Built on top of #1018 at `{short('kim-2')}`.", batch_pull(gh)["body"])
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_the_walk_back_through_the_branch_stops_where_it_was_started(self):
        gh, _ = self.stacked()
        self.move_on(gh)
        sync(gh)
        # A maintainer pushes a fix onto the batch, so its note no longer matches its head.
        tip, fix = gh.refs[FIRST], sha("fix")
        gh.inside[fix] = gh.inside[tip] | {tip}
        gh.commits[fix] = {"message": "Fix by hand", "parents": [{"sha": tip}]}
        gh.refs[FIRST] = batch_pull(gh)["sha"] = fix
        gh.touch(batch_pull(gh)["number"])
        gh.reads, gh.writes = [], []
        sync(gh)
        self.assertIn(f"- #13 at `{short('head13')}`", batch_pull(gh)["body"])
        self.assertEqual((resets(gh), merges(gh)), ([], []))
        self.assertNotIn(f"git/commits/{sha('kim')}", gh.reads)

    def test_when_it_is_rebuilt_so_is_the_batch_on_top(self):
        gh, _ = self.stacked()
        by_hand(gh, 11, 12, name="kim-rebased")
        gh.writes = []
        log = sync(gh)
        self.assertEqual((resets(gh), merges(gh)), ([(f"git/refs/heads/{FIRST}", sha("kim-rebased"))], [sha("head13")]))
        self.assertNotIn(sha("kim"), gh.inside[gh.refs[FIRST]])
        self.assertIn(f"rebuilt `{FIRST}` on top of #1018 at `{short('kim-rebased')}`", log)

    def test_when_it_is_closed_without_merging_the_batch_goes_back_to_main(self):
        gh, _ = self.stacked()
        gh.close(1018)
        gh.writes = []
        sync(gh)  # #11 and #12 are queued again, and nothing is assembled in this run
        self.assertEqual(resets(gh), [])
        log = sync(gh, hours=1)
        self.assertEqual((resets(gh), merges(gh)),
                         ([(f"git/refs/heads/{FIRST}", MAIN)], [sha("head11"), sha("head12"), sha("head13")]))
        self.assertIn(f"rebuilt `{FIRST}` on main", log)
        self.assertNotIn("Built on top", batch_pull(gh)["body"])

    def test_once_it_has_landed_nothing_needs_doing(self):
        gh, _ = self.stacked()
        for number in (11, 12, 1018):
            gh.close(number, merged=True)
        gh.writes = []
        log = sync(gh)
        self.assertEqual((resets(gh), merges(gh)), ([], []))
        self.assertIn(f"#1018, which `{FIRST}` was built on, has landed on main", log)
        self.assertIn(sha("head13"), gh.inside[gh.refs[FIRST]])
        self.assertNotIn("Built on top", batch_pull(gh)["body"])
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_without_a_pull_request_it_is_not_rebuilt_on_every_run(self):
        gh = Fake()
        gh.allow_pulls = False  # so it has no note in a pull request's text
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12)
        sync(gh)
        self.assertTrue(gh.failed)
        for hours in (1, 2):
            gh.reads, gh.writes, gh.failed = [], [], False
            sync(gh, hours=hours)
            self.assertTrue(gh.failed)
            self.assertEqual((resets(gh), merges(gh)), ([], []))
            self.assertNotIn(f"git/commits/{sha('kim')}", gh.reads)
        self.assertIn(sha("head13"), gh.inside[gh.refs[FIRST]])

    def test_with_two_being_built_the_batch_goes_on_main_and_says_why(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11)
        by_hand(gh, 12, number=2000, ref="batch/other", name="other")
        sync(gh)
        self.assertIn(("POST", "git/refs", {"ref": f"refs/heads/{FIRST}", "sha": MAIN}), gh.writes)
        self.assertEqual(merges(gh), [sha("head13")])
        self.assertIn("Built on `main`, because more than one batch assembled by hand into `main` is "
                      "`latest batch`: #1018, #2000.", batch_pull(gh)["body"])

    def test_a_refusal_names_the_batch_underneath_and_is_told_again_after_a_rebuild(self):
        gh = Fake()
        queue(gh, 11, 13)
        gh.conflicting = {sha("head13")}
        sync(gh)
        self.assertEqual(len(gh.said(13)), 1)
        by_hand(gh, 11)
        sync(gh)
        said = gh.said(13)
        self.assertEqual(len(said), 2)
        self.assertTrue(said[1].startswith(f"<!-- batch-queue-refused {FIRST} {sha('head13')} on #1018 -->"))
        self.assertIn("#1018, which this batch is built on, and the pull requests added before it.", said[1])
        sync(gh)
        self.assertEqual(len(gh.said(13)), 2)


UPPER = "batch/b5-on-1018"


class StackedBatches(unittest.TestCase):
    """Batches assembled by hand stacked on one another: an upper batch's branch merges the
    lower one's, and it lands right after it."""

    def stacked(self, ref=UPPER, body="Assembled by hand."):
        """#1018 holds #11 and #12, and #1050 is stacked on it and adds #13."""
        gh = Fake()
        queue(gh, 11, 12, 13, 14)
        by_hand(gh, 11, 12)
        by_hand(gh, 1018, 13, number=1050, ref=ref, name="b5", body=body)
        return gh

    def labels(self, gh, *numbers):
        return [gh.pulls[number]["labels"] - {"large"} for number in numbers]

    def record(self, gh, number):
        return next(body for body in gh.said(number) if body.startswith("<!-- batch-queue-by-hand"))

    def own(self, gh, number):
        return set(note(self.record(gh, number))["members"])

    def frozen(self, gh, number):
        """The batches that told a pull request it is frozen, in order."""
        return [int(body.split()[2]) for body in gh.said(number) if body.startswith("<!-- batch-queue-frozen")]

    def test_the_branch_name_says_which_batch_it_is_stacked_on(self):
        gh = self.stacked()
        log = sync(gh)
        self.assertIn("#1050 is stacked on #1018, as its branch name says", log)
        self.assertEqual(self.labels(gh, 11, 12, 13, 14, 1018, 1050),
                         [IN, IN, IN, QF, {BUILDING}, {BUILDING, LATEST}])
        # Each member is told once, naming its own batch: the lowest that holds it.
        self.assertEqual([self.frozen(gh, number) for number in (11, 12, 13)], [[1018], [1018], [1050]])
        # Each record lists only what its batch adds, and never the pull request of a batch.
        self.assertEqual(self.own(gh, 1018), {"11", "12"})
        upper = note(self.record(gh, 1050))
        self.assertEqual((set(upper["members"]), upper["queued"]), ({"13"}, ["13"]))
        self.assertEqual(upper["below"], {"1018": sha("kim")})
        self.assertIn("This batch is stacked on #1018, as its branch name says.", self.record(gh, 1050))
        self.assertIn("In this batch: #13.", self.record(gh, 1050))
        self.assertFalse([line for line in log if line.startswith("warning")])
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.writes, [])

    def test_a_depends_on_line_says_so_too(self):
        gh = self.stacked(ref="batch/b5", body="Batch 5.\n\n---\n\n- [ ] depends on: #1018\n")
        log = sync(gh)
        self.assertIn("#1050 is stacked on #1018, as a `depends on` line says", log)
        self.assertEqual(self.own(gh, 1050), {"13"})
        self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING}, {BUILDING, LATEST}])

    def test_a_ticked_depends_on_line_counts_while_the_batch_is_open(self):
        gh = self.stacked(ref="batch/b5", body="- [x] depends on: #1018\n")
        self.assertIn("#1050 is stacked on #1018, as a `depends on` line says", sync(gh))

    def test_a_depends_on_line_wins_over_the_branch_name(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11)
        by_hand(gh, 12, number=2000, ref="batch/other", name="other")
        by_hand(gh, 1018, 13, number=1050, ref="batch/b5-on-2000", name="b5", body="- [ ] depends on: #1018\n")
        log = sync(gh)
        self.assertIn("#1050 is stacked on #1018, as a `depends on` line says", log)
        self.assertEqual(self.labels(gh, 1018, 1050, 2000), [{BUILDING}, {BUILDING, LATEST}, {BUILDING, LATEST}])
        self.assertEqual(self.own(gh, 1050), {"13"})

    def test_a_name_or_line_that_names_no_open_batch_stacks_nothing(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11)
        # #12 is an ordinary pull request, and #999 is not open.
        by_hand(gh, 12, number=1050, ref="batch/b5-on-12", name="b5", body="- [ ] depends on: #999\n")
        log = sync(gh)
        self.assertFalse([line for line in log if "stacked on" in line])
        self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING, LATEST}, {BUILDING, LATEST}])

    def test_the_lowest_batch_owns_a_pull_request_both_contain(self):
        gh = self.stacked()
        sync(gh)
        # #12 is pushed to, and the upper batch is rebuilt with its new head as well.
        gh.push(12, "head12-later")
        by_hand(gh, 1018, 13, 12, number=1050, ref=UPPER, name="b5-again")
        log = sync(gh)
        self.assertEqual(note(self.record(gh, 1018))["members"], {"11": sha("head11"), "12": sha("head12")})
        self.assertEqual(self.own(gh, 1050), {"13"})
        # Its own batch, the lower one, tells it that it was pushed to; the upper one says nothing.
        # The lower batch lands `head12` only, so #12 has changed after it was frozen there.
        self.assertEqual(self.labels(gh, 12), [IN | {WAITING, CHANGED}])
        self.assertEqual([line for line in log if "#12" in line],
                         [f"told #12 that it was pushed to after the batch #1018 took it: now `{WAITING}`",
                          f"#12 was pushed to after `{short('head12')}` was taken: now `{CHANGED}`"])
        self.assertEqual(self.frozen(gh, 12), [1018])

    def test_what_moves_down_into_the_lower_batch_keeps_building(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11)
        by_hand(gh, 1018, 12, 13, number=1050, ref=UPPER, name="b5")
        sync(gh)
        self.assertEqual(self.own(gh, 1050), {"12", "13"})
        # #12 is merged into the lower batch, and the upper one takes the new head of it.
        by_hand(gh, 11, 12, name="kim-2")
        by_hand(gh, 1018, 12, 13, number=1050, ref=UPPER, name="b5-2")
        gh.writes = []
        sync(gh)
        self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, {"13"}))
        self.assertEqual(self.labels(gh, 12), [IN])
        self.assertFalse([path for method, path, _ in gh.writes if "labels" in path])
        # It is told which batch it is in now, and not that it left the upper one.
        self.assertEqual(self.frozen(gh, 12), [1050, 1018])
        self.assertFalse([body for body in gh.said(12) if body.startswith("<!-- batch-queue-dropped")])

    def test_latest_batch_moves_up_when_a_batch_is_stacked_on_top_and_back_when_it_closes(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12)
        log = sync(gh)
        self.assertIn("#1018 is the outermost batch of its stack: now `latest batch`", log)
        self.assertEqual(self.labels(gh, 1018), [{BUILDING, LATEST}])
        by_hand(gh, 1018, 13, number=1050, ref=UPPER, name="b5")
        log = sync(gh)
        self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING}, {BUILDING, LATEST}])
        self.assertIn("#1018 is not the outermost batch of a stack: `latest batch` removed", log)
        gh.close(1050)
        log = sync(gh)
        self.assertEqual(self.labels(gh, 1018, 1050, 13), [{BUILDING, LATEST}, set(), QF])
        self.assertEqual(self.labels(gh, 11, 12), [IN, IN])
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_two_separate_stacks_each_have_their_own_latest_batch(self):
        gh = self.stacked()
        queue(gh, 21, 22)
        by_hand(gh, 21, number=2000, ref="batch/other", name="other")
        by_hand(gh, 2000, 22, number=2050, ref="batch/other-2-on-2000", name="other-2")
        sync(gh)
        self.assertEqual(self.labels(gh, 1018, 1050, 2000, 2050),
                         [{BUILDING}, {BUILDING, LATEST}, {BUILDING}, {BUILDING, LATEST}])
        self.assertEqual([self.own(gh, number) for number in (1018, 1050, 2000, 2050)],
                         [{"11", "12"}, {"13"}, {"21"}, {"22"}])

    def test_when_the_lower_batch_merges_the_upper_one_stops_depending_on_it(self):
        gh = self.stacked()
        sync(gh)
        for number in (11, 12, 1018):
            gh.close(number, merged=True)
        gh.writes = []
        log = sync(gh)
        self.assertIn("#1050 is no longer stacked on another batch", log)
        self.assertEqual(self.labels(gh, 1018, 1050, 13), [set(), {BUILDING, LATEST}, IN])
        upper = note(self.record(gh, 1050))
        self.assertEqual((set(upper["members"]), "below" in upper), ({"13"}, False))
        self.assertNotIn("This batch is stacked on", self.record(gh, 1050))
        self.assertFalse([path for method, path, _ in gh.writes if path.startswith("issues/13/")])
        self.assertEqual(gh.said(1050), [self.record(gh, 1050)])
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_when_the_lower_batch_is_closed_unmerged_the_upper_one_is_told_and_takes_over(self):
        gh = self.stacked()
        sync(gh)
        gh.close(1018)
        gh.writes = []
        log = sync(gh)
        self.assertIn("told #1050 that #1018, which it is stacked on, was closed without merging", log)
        [told] = [body for body in gh.said(1050) if body.startswith("<!-- batch-queue-stranded 1018 -->")]
        self.assertIn("#1018, which this batch is stacked on as its branch name says, was closed without being "
                      "merged.", told)
        self.assertIn("still carries the commits of #1018", told)
        self.assertIn("rebuild it on `main` or on another batch, and update its `depends on` line or its branch "
                      "name", told)
        # Its pull requests are in the upper batch's branch, so they are the upper batch's now.
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050), [IN, IN, IN, set(), {BUILDING, LATEST}])
        self.assertFalse([path for method, path, _ in gh.writes
                          if path.startswith(("issues/11/labels", "issues/12/labels"))])
        # They are not told they can push again, but that they are frozen in the upper batch now.
        self.assertEqual([self.frozen(gh, number) for number in (11, 12)], [[1018, 1050], [1018, 1050]])
        self.assertFalse([body for number in (11, 12) for body in gh.said(number)
                          if body.startswith("<!-- batch-queue-unfrozen")])
        # What the closed batch told is forgotten in its own record, in case it is reopened.
        lower = note(self.record(gh, 1018))
        self.assertEqual((lower["labelled"], lower["told"], lower["pushed"], lower["left"]), ([], {}, {}, {}))
        upper = note(self.record(gh, 1050))
        self.assertEqual((set(upper["members"]), upper["queued"]), ({"11", "12", "13"}, ["11", "12", "13"]))
        # Told once.
        sync(gh)
        self.assertEqual(len([body for body in gh.said(1050) if "batch-queue-stranded" in body]), 1)
        # Closed in its turn, what was queued goes back to the queue.
        gh.close(1050)
        sync(gh)
        self.assertEqual(self.labels(gh, 11, 12, 13), [QF] * 3)
        self.assertEqual([len([body for body in gh.said(number) if body.startswith("<!-- batch-queue-unfrozen 1050")])
                          for number in (11, 12, 13)], [1, 1, 1])

    def test_when_the_upper_batch_cannot_be_looked_through_the_closed_lower_one_waits(self):
        gh = self.stacked()
        sync(gh)
        gh.close(1018)
        gh.writes = []
        gh.left = batch.RESERVE - 1
        log = sync(gh)
        self.assertIn("batch #1018 was closed without merging, and a batch stacked on it could not be looked "
                      "through: its pull requests keep their labels, and the next run settles them", log)
        self.assertEqual(self.labels(gh, 11, 12, 1018), [IN, IN, {BUILDING}])
        self.assertFalse([path for method, path, _ in gh.writes if "/labels" in path])
        # The next run, with requests to spare, settles it as if nothing had stood in the way.
        gh.left = 900
        sync(gh)
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050), [IN, IN, IN, set(), {BUILDING, LATEST}])
        self.assertFalse([path for method, path, _ in gh.writes
                          if path.startswith(("issues/11/labels", "issues/12/labels"))])

    def test_a_claim_on_a_batch_whose_branch_it_shares_nothing_with_is_warned_about(self):
        gh = Fake()
        queue(gh, 11, 13)
        by_hand(gh, 11)
        by_hand(gh, 13, number=1050, ref=UPPER, name="b5")  # built on main after all
        log = sync(gh)
        self.assertIn("warning: #1050 says in its branch name that it is stacked on #1018, but its branch shares "
                      "no commit with that of #1018 beyond `main`", log)
        self.assertEqual([self.own(gh, number) for number in (1018, 1050)], [{"11"}, {"13"}])

    def test_an_older_head_of_the_lower_batch_is_shared_enough(self):
        gh = self.stacked()
        sync(gh)
        # The lower batch moves on, and the upper one has not taken its new head yet.
        old, new = gh.refs[HAND], sha("kim-2")
        gh.inside[new] = gh.inside[old] | {old}
        gh.refs[HAND] = gh.pulls[1018]["sha"] = new
        gh.touch(1018)
        log = sync(gh)
        self.assertFalse([line for line in log if line.startswith("warning")])
        self.assertEqual(note(self.record(gh, 1050))["below"], {"1018": new})

    def test_batches_stacked_on_each_other_in_a_circle_are_stacked_on_none(self):
        gh = Fake()
        queue(gh, 11, 13)
        by_hand(gh, 11, body="- [ ] depends on: #1050\n")
        by_hand(gh, 1018, 13, number=1050, ref=UPPER, name="b5")
        log = sync(gh)
        self.assertIn("the batches #1018, #1050 say they are stacked on each other in a circle: none of them is "
                      "taken to be stacked on another batch", log)
        self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING, LATEST}, {BUILDING, LATEST}])

    def twins(self, lower="Assembled by hand.", upper="Assembled by hand.", ref="batch/copy"):
        """#1018 and #1050 are two batches at the same commit, holding #11 and #12."""
        gh = Fake()
        queue(gh, 11, 12, 13)
        by_hand(gh, 11, 12, body=lower)
        by_hand(gh, 11, 12, number=1050, ref=ref, name="kim", body=upper)
        return gh

    TWINS = (f"warning: the batches #1018, #1050 are at the same commit `{short('kim')}`: whatever they say about "
             "each other, each is taken to be stacked on the one with the next lower number (#1050 on #1018)")

    def test_two_batches_at_the_same_commit_are_stacked_in_number_order(self):
        gh = self.twins()
        log = sync(gh)
        self.assertIn(self.TWINS, log)
        # Nothing is held twice: the lower number holds it all, and the higher one is the outermost.
        self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, set()))
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050),
                         [IN, IN, QF, {BUILDING}, {BUILDING, LATEST}])
        # Each member is told once, by the batch that holds it.
        self.assertEqual([self.frozen(gh, number) for number in (11, 12)], [[1018], [1018]])
        self.assertIn("This batch is stacked on #1018, whose branch is at the same commit and whose number is lower.",
                      self.record(gh, 1050))
        self.assertEqual(note(self.record(gh, 1050))["below"], {"1018": sha("kim")})
        # Every run warns again, and changes nothing.
        for _ in range(2):
            gh.writes = []
            self.assertEqual(sync(gh), [self.TWINS])
            self.assertEqual(gh.writes, [])

    def test_what_they_say_about_each_other_does_not_change_the_order(self):
        for lower, upper, ref in (("- [ ] depends on: #1050\n", "- [ ] depends on: #1018\n", "batch/copy"),
                                  ("- [ ] depends on: #1050\n", "Assembled by hand.", "batch/copy"),
                                  ("Assembled by hand.", "Assembled by hand.", UPPER)):
            with self.subTest(lower=lower, upper=upper, ref=ref):
                gh = self.twins(lower, upper, ref)
                log = sync(gh)
                self.assertIn(self.TWINS, log)
                self.assertFalse([line for line in log if "circle" in line])
                self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, set()))
                self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING}, {BUILDING, LATEST}])

    def test_a_batch_that_was_alone_takes_nothing_from_its_twin_and_no_label_changes(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12, number=1050, ref="batch/copy", name="kim")
        sync(gh)
        self.assertEqual(self.own(gh, 1050), {"11", "12"})
        # A second batch with a lower number appears at the same commit: what is held moves down
        # to it, and keeps its labels, as when it moves down a stack.
        by_hand(gh, 11, 12)
        gh.writes = []
        log = sync(gh)
        self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, set()))
        self.assertFalse([path for method, path, _ in gh.writes if "labels" in path
                          and path.startswith(("issues/11/", "issues/12/"))])
        self.assertEqual(self.labels(gh, 11, 12), [IN, IN])
        self.assertFalse([body for body in gh.said(11) if body.startswith("<!-- batch-queue-dropped")])
        # The one that was there first stays the outermost.
        self.assertFalse([line for line in log if LATEST in line])
        self.assertEqual(self.labels(gh, 1018, 1050), [{BUILDING}, {BUILDING, LATEST}])

    def test_once_one_moves_on_what_it_says_counts_again(self):
        gh = self.twins(ref=UPPER)
        sync(gh)
        by_hand(gh, 1018, 13, number=1050, ref=UPPER, name="b5")
        log = sync(gh)
        self.assertFalse([line for line in log if line.startswith("warning")])
        self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, {"13"}))
        self.assertIn("This batch is stacked on #1018, as its branch name says.", self.record(gh, 1050))
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050), [IN, IN, IN, {BUILDING}, {BUILDING, LATEST}])

    def test_what_they_say_about_other_batches_still_counts(self):
        gh = Fake()
        queue(gh, 11, 13)
        by_hand(gh, 11)
        body = "- [ ] depends on: #1018\n"
        by_hand(gh, 1018, 13, number=1050, ref="batch/b5", name="b5", body=body)
        by_hand(gh, 1018, 13, number=1060, ref="batch/b5-copy", name="b5", body=body)
        sync(gh)
        self.assertEqual([self.own(gh, number) for number in (1018, 1050, 1060)], [{"11"}, {"13"}, set()])
        self.assertEqual(self.labels(gh, 1018, 1050, 1060), [{BUILDING}, {BUILDING}, {BUILDING, LATEST}])
        self.assertIn("This batch is stacked on #1018, as a `depends on` line says, and on #1050, whose branch is at "
                      "the same commit and whose number is lower.", self.record(gh, 1060))

    def test_a_circle_through_another_batch_keeps_the_order_of_twins(self):
        gh = Fake()
        queue(gh, 11, 21)
        by_hand(gh, 11, body="- [ ] depends on: #2000\n")
        by_hand(gh, 11, number=1050, ref="batch/copy", name="kim")
        by_hand(gh, 21, number=2000, ref="batch/other", name="other", body="- [ ] depends on: #1050\n")
        log = sync(gh)
        self.assertIn("the batches #1018, #1050, #2000 say they are stacked on each other in a circle: none of them "
                      "is taken to be stacked on another batch, except one at the same commit", log)
        self.assertEqual([self.own(gh, number) for number in (1018, 1050, 2000)], [{"11"}, set(), {"21"}])
        self.assertEqual(self.labels(gh, 1018, 1050, 2000), [{BUILDING}, {BUILDING, LATEST}, {BUILDING, LATEST}])

    def legacy(self):
        """A stack whose records were written before batches were stacked, and before members
        were told anything: the outer batch held the lower one and all it contained, and
        everything is `building`."""
        gh = self.stacked()
        lower = {"head": sha("kim"), "members": {key: gh.pulls[int(key)]["sha"] for key in ("11", "12")},
                 "queued": ["11", "12"]}
        gh.say(1018, "<!-- batch-queue-by-hand " + json.dumps(lower) + " -->\nWhile this pull request is open, ...")
        old = {"head": sha("b5"), "members": {key: gh.pulls[int(key)]["sha"] for key in ("11", "12", "13", "1018")},
               "queued": ["11", "12", "13"]}
        gh.say(1050, "<!-- batch-queue-by-hand " + json.dumps(old) + " -->\nWhile this pull request is open, ...")
        for number in (11, 12, 13):
            gh.label(number, remove=QUEUED)
        for number in (11, 12, 13, 1018, 1050):
            gh.label(number, add=BUILDING)
        return gh

    def test_a_lower_batch_listed_as_a_member_by_an_old_record_keeps_building(self):
        gh = self.legacy()
        gh.writes = []
        log = sync(gh)
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050), [IN, IN, IN, {BUILDING}, {BUILDING, LATEST}])
        self.assertEqual((self.own(gh, 1018), self.own(gh, 1050)), ({"11", "12"}, {"13"}))
        # Only the members lose `building`, for `batch-building` and `frozen`.
        self.assertEqual(sorted(path for method, path, _ in gh.writes if method == "DELETE"),
                         [f"issues/{number}/labels/building" for number in (11, 12, 13)])
        self.assertFalse([line for line in log if "no longer" in line])
        # Both records are old, so nobody is told anything.
        self.assertFalse([body for number in (11, 12, 13) for body in gh.said(number)
                          if not body.startswith("<!-- batch-queue-approved")])

    def test_an_old_record_of_a_batch_closed_on_top_leaves_the_lower_batch_alone(self):
        gh = self.legacy()
        gh.close(1050)
        sync(gh)
        self.assertEqual(self.labels(gh, 11, 12, 13, 1018, 1050), [IN, IN, QF, {BUILDING, LATEST}, set()])

    def test_what_a_closed_lower_batch_held_and_the_upper_one_does_not_is_unfrozen(self):
        gh = self.stacked()
        sync(gh)
        # The lower batch takes #14 after the upper one was built on it, and is then closed.
        by_hand(gh, 11, 12, 14, name="kim-2")
        sync(gh)
        self.assertEqual((self.own(gh, 1018), self.labels(gh, 14)), ({"11", "12", "14"}, [IN]))
        gh.close(1018)
        log = sync(gh)
        self.assertEqual(self.labels(gh, 11, 12, 13, 14), [IN, IN, IN, QF])
        self.assertEqual(self.own(gh, 1050), {"11", "12", "13"})
        self.assertIn("batch #1018 was closed without merging: #14 is `batch queue` again", log)
        [unfrozen] = [body for body in gh.said(14) if body.startswith("<!-- batch-queue-unfrozen 1018 -->")]
        self.assertIn("Batch #1018 was closed without being merged.", unfrozen)
        self.assertFalse([body for number in (11, 12) for body in gh.said(number)
                          if body.startswith("<!-- batch-queue-unfrozen")])

    def test_a_member_of_another_batch_of_the_stack_is_not_told_it_is_left_out(self):
        gh = self.stacked()
        gh.add_pull(21, "head21")
        # The lower batch lists as left out #13, which the upper batch takes, and #21.
        gh.pulls[1018]["body"] = (f"Left out for other reasons:\n\n- {URL}13 Taken by the next batch\n"
                                  f"- {URL}21 Changes `src/Main.lean`\n")
        gh.touch(1018)
        log = sync(gh)
        self.assertEqual(self.labels(gh, 13, 21), [IN, set()])
        self.assertFalse([body for body in gh.said(13) if body.startswith("<!-- batch-queue-left-out")])
        self.assertEqual(len([body for body in gh.said(21) if body.startswith("<!-- batch-queue-left-out")]), 1)
        self.assertIn("told #21 that the batch #1018 leaves it out", log)
        self.assertEqual(note(self.record(gh, 1018))["left"].keys(), {"21"})

    def test_a_lower_batch_an_old_record_lists_is_tidied_up_when_it_lands(self):
        # It lands before this script first runs, while the old record of #1050 still lists it.
        gh = self.legacy()
        for number in (11, 12, 1018):
            gh.close(number, merged=True)
        log = sync(gh)
        self.assertIn("tidied up after batch #1018, which was assembled by hand", log)
        self.assertEqual(self.labels(gh, 11, 12, 1018, 1050), [set(), set(), set(), {BUILDING, LATEST}])
        self.assertNotIn("1018", note(self.record(gh, 1050))["members"])

    def test_without_the_label_on_github_nothing_is_labelled_latest(self):
        gh = self.stacked()
        gh.missing.add(LATEST)
        log = sync(gh)
        self.assertIn("there is no `latest batch` label in this repository: was it renamed?", log)
        self.assertEqual(self.labels(gh, 1050), [{BUILDING}])


class QueueOnAStack(WithAssembly):
    """With `ASSEMBLE` on, the queue's own batch goes on the `latest batch` of the one stack into main."""

    def test_it_starts_on_the_outermost_batch(self):
        gh = Fake()
        queue(gh, 11, 12, 13, 14)
        by_hand(gh, 11, 12)
        by_hand(gh, 1018, 13, number=1050, ref=UPPER, name="b5")
        log = sync(gh)
        self.assertIn(("POST", "git/refs", {"ref": f"refs/heads/{FIRST}", "sha": sha("b5")}), gh.writes)
        self.assertIn(f"started `{FIRST}` on top of #1050", log)
        self.assertEqual(merges(gh), [sha("head14")])
        self.assertIn("Built on top of #1050", batch_pull(gh)["body"])

    def test_with_two_stacks_it_goes_on_main(self):
        gh = Fake()
        queue(gh, 11, 12, 13, 14)
        by_hand(gh, 11)
        by_hand(gh, 1018, 12, number=1050, ref=UPPER, name="b5")
        by_hand(gh, 13, number=2000, ref="batch/other", name="other")
        sync(gh)
        self.assertIn(("POST", "git/refs", {"ref": f"refs/heads/{FIRST}", "sha": MAIN}), gh.writes)
        self.assertIn("is `latest batch`: #1050, #2000.", batch_pull(gh)["body"])

    def test_when_a_batch_is_stacked_on_top_it_is_rebuilt_there(self):
        gh = Fake()
        queue(gh, 11, 12, 14)
        by_hand(gh, 11)
        sync(gh)
        by_hand(gh, 1018, 12, number=1050, ref=UPPER, name="b5")
        gh.writes = []
        log = sync(gh)
        self.assertEqual(resets(gh), [(f"git/refs/heads/{FIRST}", sha("b5"))])
        self.assertIn(f"rebuilt `{FIRST}` on top of #1050 at `{short('b5')}`", log)
        self.assertEqual(merges(gh), [sha("head14")])


class Priority(WithAssembly):
    """Pull requests labelled `priority` go into a batch before the others."""

    def test_it_goes_in_first_and_the_one_it_conflicts_with_is_left_out(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        clash(gh, 11, 12)
        gh.label(12, add=PRIORITY, login="maintainer")
        sync(gh)
        self.assertEqual(merges(gh), [sha("head12"), sha("head11"), sha("head13")])
        body = batch_pull(gh)["body"]
        self.assertIn(f"In this batch:\n\n- #12 at `{short('head12')}`\n- #13 at `{short('head13')}`\n", body)
        self.assertIn("Left out, because GitHub could not merge them into this branch: #11.", body)

    def test_labelled_after_it_was_left_out_it_goes_first_once_the_batch_is_rebuilt(self):
        gh = Fake()
        queue(gh, 11, 12)
        clash(gh, 11, 12)
        sync(gh)
        self.assertIn("Left out, because GitHub could not merge them into this branch: #12.", batch_pull(gh)["body"])
        gh.label(12, add=PRIORITY, login="maintainer")
        gh.writes = []
        sync(gh)
        self.assertEqual(merges(gh), [])
        # A batch assembled by hand is opened, and the batch is rebuilt on top of it.
        gh.add_pull(10, "head10")
        by_hand(gh, 10)
        gh.writes = []
        sync(gh)
        self.assertEqual(merges(gh), [sha("head12"), sha("head11")])
        body = batch_pull(gh)["body"]
        self.assertIn(f"In this batch:\n\n- #12 at `{short('head12')}`\n", body)
        self.assertIn("Left out, because GitHub could not merge them into this branch: #11.", body)


class ClosedPullRequests(WithAssembly):
    """A closed pull request is neither waiting for a build nor in one."""

    def test_closing_takes_the_label_off(self):
        gh = Fake()
        queue(gh, 11)
        gh.add_pull(12, "head12", labels=[QUEUED])  # labelled by hand
        gh.close(12)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, set()))
        self.assertIn("#12 is closed: `batch queue` removed", log)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_merging_by_itself_takes_the_label_off(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        gh.close(12, merged=True)
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], set())
        self.assertIn("#12, closed since it was merged in", batch_pull(gh)["body"])

    def test_closing_a_pull_request_in_a_batch_being_built_takes_building_off(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        gh.close(12)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (IN, set()))
        self.assertIn("#12 is closed: `batch-building` and `frozen` removed", log)
        # The batch's own pull request keeps `building` while it is open, and is not touched.
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING, LATEST})
        # When the batch is closed without merging, only the open one goes back to the queue.
        gh.close(1018)
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, set()))

    def test_a_merged_batch_is_tidied_up_once(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        for number in (11, 12, 1018):
            gh.close(number, merged=True)
        gh.writes = []
        sync(gh)
        # One request each: closed pull requests have their labels set in one go. The batch's own
        # labels come off one by one, `building` last.
        drops = [(method, path) for method, path, _ in gh.writes if method in ("DELETE", "PUT") and "labels" in path]
        self.assertEqual(sorted(drops), [("DELETE", "issues/1018/labels/building"),
                                         ("DELETE", "issues/1018/labels/latest%20batch"),
                                         ("PUT", "issues/11/labels"), ("PUT", "issues/12/labels")])
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12)], [set(), set()])


class Reopening(WithAssembly):
    def closed(self, queued=True):
        gh = Fake()
        if queued:
            queue(gh, 11)
        else:
            gh.add_pull(11, "head11", labels=[QUEUED])  # labelled by hand
        gh.close(11)
        sync(gh)
        self.assertEqual(gh.pulls[11]["labels"], set())
        gh.reopen(11)
        return gh

    def test_the_label_comes_back(self):
        for queued in (True, False):
            gh = self.closed(queued)
            self.assertEqual(batch.reopened(gh, 11), ["#11 was reopened: `batch queue` and `frozen` put back"])
            self.assertEqual(gh.pulls[11]["labels"], QF)

    def test_and_a_queued_commit_is_merged_again_by_the_next_run(self):
        gh = self.closed()
        batch.reopened(gh, 11)
        sync(gh)
        self.assertEqual(merges(gh), [sha("head11")])

    def test_a_label_a_person_took_off_stays_off(self):
        gh = Fake()
        queue(gh, 11)
        gh.close(11)
        gh.label(11, remove=QUEUED, login="maintainer")
        sync(gh)
        gh.reopen(11)
        self.assertEqual(batch.reopened(gh, 11), ["#11: `batch queue` was taken off by maintainer, so it stays off"])
        self.assertEqual(gh.pulls[11]["labels"], set())

    def test_taken_out_of_the_queue_while_closed_stays_out(self):
        gh = Fake()
        queue(gh, 11)
        gh.close(11)
        sync(gh)  # takes the label off
        unqueue(gh, 11)  # `-batch` while closed: the withdrawal is recorded, the label is already off
        gh.reopen(11)
        self.assertIn("taken out of the queue with `-batch`", batch.reopened(gh, 11)[0])
        self.assertEqual(gh.pulls[11]["labels"], set())

    def test_a_label_removed_before_the_close_stays_off(self):
        gh = Fake()
        queue(gh, 11)
        unqueue(gh, 11)  # by the label job, before the close
        gh.close(11)
        gh.reopen(11)
        self.assertIn("had no label taken off when it was closed", batch.reopened(gh, 11)[0])
        self.assertEqual(gh.pulls[11]["labels"], set())

    def test_nothing_happens_to_an_open_labelled_or_batch_pull_request(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        self.assertIn("already carries", batch.reopened(gh, 11)[0])
        self.assertIn("holds a batch", batch.reopened(gh, 111)[0])
        gh.add_pull(12, "head12")
        gh.close(12)
        self.assertIn("is not open", batch.reopened(gh, 12)[0])
        self.assertEqual([write for write in gh.writes if "labels" in write[1] and write[1].startswith("issues/1")
                          and not write[1].startswith("issues/111")], [])


class Requests(WithAssembly):
    """The workflow's token is allowed 1,000 requests an hour, shared with every other workflow."""

    def big(self, count=33):
        gh = Fake()
        queue(gh, *range(1, count + 1))
        return gh

    def spent(self, gh, **options):
        before = gh.calls
        sync(gh, **options)
        return gh.calls - before

    def test_a_run_with_nothing_new_asks_little_however_long_the_queue(self):
        gh = self.big()
        first = self.spent(gh)
        self.assertLess(first, 33 * 5 + 15)
        # The repository, main, open pull requests, batch branches, and the closed pull requests
        # still labelled `building`, `batch-building`, `frozen` or `batch queue`: no more.
        self.assertEqual(self.spent(gh), 8)
        self.assertEqual(self.spent(gh), 8)

    def test_one_more_pull_request_costs_a_handful(self):
        gh = self.big()
        sync(gh)
        sync(gh)
        queue(gh, 50)
        self.assertLessEqual(self.spent(gh), 12)

    def test_merging_stops_when_the_hours_allowance_is_nearly_gone(self):
        gh = self.big(3)
        gh.left = batch.RESERVE - 1
        log = sync(gh)
        self.assertEqual(merges(gh), [])
        self.assertIn(f"only {batch.RESERVE - 1} requests left this hour: stopped merging, and the next run carries on", log)
        gh.left = 900
        sync(gh)
        self.assertEqual(len(merges(gh)), 3)


class OpeningThePullRequest(WithAssembly):
    def test_when_workflows_may_not_open_pull_requests_the_branch_waits_for_a_person(self):
        gh = Fake()
        gh.allow_pulls = False
        queue(gh, 11)
        log = sync(gh)
        [refusal] = [line for line in log if line.startswith("GitHub would not let this workflow open")]
        self.assertIn(f"https://github.com/o/r/compare/main...{FIRST}?expand=1", refusal)
        self.assertIn("not permitted to create", refusal)
        self.assertTrue(gh.failed)
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST]])
        # A maintainer opens it by hand; the next run adopts it instead of starting another branch.
        gh.pulls[50] = {"number": 50, "state": "open", "merged_at": None, "labels": set(), "sha": gh.refs[FIRST],
                        "ref": FIRST, "own": True, "base": "main", "body": "", "title": "", "updated": 0}
        queue(gh, 12)
        sync(gh, hours=1)
        self.assertEqual(list(gh.refs), [FIRST])
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`", gh.pulls[50]["body"])


class RefusedPullRequest(WithAssembly):
    """A refusal to open the batch's pull request does not stop the rest of the run."""

    def test_the_labels_are_still_reconciled_and_the_run_fails(self):
        gh = Fake()
        gh.allow_pulls = False
        queue(gh, 11)
        gh.label(11, remove=FROZEN)  # queued before `frozen` existed
        gh.add_pull(32, "head32", labels=[MEMBER, FROZEN])  # nothing holds it
        log = sync(gh)
        self.assertTrue(gh.failed)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[32]["labels"]), (QF, set()))
        self.assertIn("#11 is queued: now `frozen`", log)
        self.assertIn("#32 is neither queued nor in a batch being built: `batch-building` and `frozen` removed", log)
        refusal = next(index for index, line in enumerate(log) if line.startswith("GitHub would not let"))
        self.assertLess(refusal, log.index("#11 is queued: now `frozen`"))

    def test_main_exits_non_zero(self):
        gh = Fake()
        gh.allow_pulls = False
        queue(gh, 11)
        printed, run = io.StringIO(), batch.sync
        with mock.patch.object(batch, "GitHub", lambda repo, dry_run: gh), \
                mock.patch("sys.argv", ["batch-queue-sync.py", "--repo", REPO]), \
                mock.patch.object(batch, "sync", lambda gh: run(gh, NOW)), \
                contextlib.redirect_stdout(printed), self.assertRaises(SystemExit) as caught:
            batch.main()
        self.assertEqual(caught.exception.code, 1)
        self.assertIn("- GitHub would not let this workflow open a pull request", printed.getvalue())


class DryRun(WithAssembly):
    def test_reads_but_sends_no_change(self):
        gh = Fake(dry_run=True)
        queue(gh, 11, 12)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            log = sync(gh)
        self.assertEqual((gh.writes, gh.refs), ([], {}))
        self.assertEqual((gh.said(11), gh.said(12)), ([], []))
        self.assertIn(f"would add #11 at `{short('head11')}` to `{FIRST}`", log)
        self.assertIn(f'would POST merges {{"base": "{FIRST}", "head": "{sha("head11")}"', printed.getvalue())


class ApprovalList(unittest.TestCase):
    """With `ASSEMBLE` off, as it is: the queue is a list of approvals, and the sync assembles no
    batch of its own. It keeps the labels in step with batches assembled by hand, closed and
    reopened pull requests as before."""

    def test_assembly_is_switched_off(self):
        self.assertIs(batch.ASSEMBLE, False)

    def test_queuing_starts_no_branch_and_merges_nothing(self):
        gh = Fake()
        queue(gh, 11)
        queue(gh, 12)
        gh.label(12, add=PRIORITY)
        writes_before = list(gh.writes)
        log = sync(gh)
        self.assertEqual(log, ["nothing to do"])
        self.assertEqual(gh.writes, writes_before)
        self.assertEqual(gh.refs, {})
        self.assertEqual(merges(gh), [])
        self.assertNotIn("POST pulls", {f"{method} {path}" for method, path, _ in gh.writes})
        # The approvals the label job recorded, and its labels, stay as they are.
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, QF | {PRIORITY}))
        self.assertEqual([batch.APPROVED.match(item["body"]).group(1) for item in gh.comments[12]], [sha("head12")])

    def test_a_dry_run_shows_no_batch_of_its_own(self):
        gh = Fake(dry_run=True)
        queue(gh, 11, 12)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            log = sync(gh)
        self.assertEqual(log, ["nothing to do"])
        self.assertEqual(printed.getvalue(), "")

    def test_a_batch_assembled_by_hand_is_kept_in_step(self):
        gh = Fake()
        queue(gh, 11, 12, 13)
        gh.add_pull(14, "head14")
        by_hand(gh, 11, 12, 14)
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [IN, IN, QF, IN])
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING, LATEST})
        self.assertIn("#1018 is a batch assembled by hand with open pull requests in it: now `building`", log)
        self.assertEqual(note(gh.said(1018)[0])["queued"], ["11", "12"])
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 13, 14)], [1, 1, 0, 1])
        # Nothing is built on top of it.
        self.assertEqual((merges(gh), gh.refs), ([], {HAND: sha("kim")}))
        # Closed without merging, what was queued goes back to the queue, and nothing is started.
        gh.close(1018)
        log = sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12, 13, 14)], [QF, QF, QF, set()])
        self.assertIn("tidied up after batch #1018, which was assembled by hand", log)
        self.assertNotIn("not starting a new batch in this run: the next `batch` or `-batch` comment does", log)
        self.assertEqual((merges(gh), gh.refs), ([], {HAND: sha("kim")}))

    def test_a_merged_batch_assembled_by_hand_takes_its_labels_off(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, 12)
        sync(gh)
        for number in (11, 12, 1018):
            gh.close(number, merged=True)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"], gh.pulls[1018]["labels"]), (set(), set(), {"large"}))
        self.assertIn("#11 landed with batch #1018: `batch-building` and `frozen` removed", log)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_a_closed_pull_request_loses_its_label_and_gets_it_back_when_reopened(self):
        gh = Fake()
        queue(gh, 11)
        gh.close(11)
        self.assertIn("#11 is closed: `batch queue` and `frozen` removed", sync(gh))
        gh.reopen(11)
        self.assertEqual(batch.reopened(gh, 11), ["#11 was reopened: `batch queue` and `frozen` put back"])
        self.assertEqual(gh.pulls[11]["labels"], QF)
        self.assertEqual((sync(gh), gh.refs), (["nothing to do"], {}))

    def test_a_branch_of_its_own_without_a_pull_request_is_left_alone(self):
        # Like `batch/2026-11-24-142233`, which the queue started and could not open a pull
        # request for.
        gh = Fake()
        queue(gh, 11, 12)
        with assembling():
            gh.allow_pulls = False
            sync(gh)
        self.assertTrue(gh.failed)
        left = dict(gh.refs)
        self.assertEqual(list(left), [FIRST])
        queue(gh, 13)
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual((gh.writes, gh.refs), ([], left))

    def test_a_branch_of_its_own_whose_pull_request_was_merged_is_still_removed(self):
        gh = Fake()
        queue(gh, 11, 12)
        with assembling():
            sync(gh)
        gh.push(12, "head12-later")  # so GitHub does not mark #12 merged along with the batch
        gh.close(11, merged=True)
        gh.close(112, merged=True)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (set(), set()))
        self.assertIn("#12 landed with batch #112 at the commit that was queued: `batch queue` and `frozen` removed",
                      log)
        self.assertIn(f"removed the branch `{FIRST}`", log)
        self.assertEqual(gh.refs, {})
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_a_branch_of_its_own_whose_pull_request_was_closed_is_removed_and_not_started_again(self):
        gh = Fake()
        queue(gh, 11, 12)
        with assembling():
            sync(gh)
        gh.close(112)
        log = sync(gh, hours=1)
        self.assertIn(f"removed the branch `{FIRST}`", log)
        self.assertEqual((gh.refs, merges(gh)[2:]), ({}, []))
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (QF, QF))


class Workflow(unittest.TestCase):
    """What the workflow's other jobs do on `batch` and `p`, which the sync's switch leaves alone."""

    def job(self, name):
        """The text of one job of the workflow, up to the next one."""
        return re.search(rf"^  {name}:\n(.*?)(?=^  [a-z]+:\n|\Z)", WORKFLOW.read_text(), re.M | re.S).group(1)

    def test_batch_and_p_record_the_commit_and_label_it(self):
        label = self.job("label")
        self.assertIn("<!-- batch-queue-approved %s -->", label)
        self.assertIn('labels=(-f "labels[]=$LABEL" -f "labels[]=$FROZEN")', label)
        self.assertIn('labels+=(-f "labels[]=$PRIORITY")', label)
        self.assertIn('echo "queued=true" >> "$GITHUB_OUTPUT"', label)

    def test_a_push_to_a_frozen_pull_request_starts_the_cheap_job_not_a_sync(self):
        pushed, sync_job = self.job("pushed"), self.job("sync")
        self.assertIn("github.event.action == 'synchronize'", pushed)
        self.assertIn("contains(github.event.pull_request.labels.*.name, 'frozen')", pushed)
        self.assertIn('--pushed "$PR"', pushed)
        self.assertNotIn("synchronize", sync_job)

    def test_editing_a_batch_runs_the_sync(self):
        # A new `depends on` line changes the order of stacked batches.
        self.assertRegex(WORKFLOW.read_text(), r"pull_request_target:\n    types: \[[^]]*\bedited\b")
        self.assertIn("startsWith(github.event.pull_request.head.ref, 'batch/')", self.job("sync"))

    def test_queuing_still_compares_with_the_rest_of_the_queue(self):
        conflicts = self.job("conflicts")
        self.assertIn("needs.label.outputs.queued == 'true'", conflicts)
        self.assertIn("scripts/batch-queue-conflicts.py", conflicts)
        spec = importlib.util.spec_from_file_location("batch_queue_conflicts", SCRIPT.with_name("batch-queue-conflicts.py"))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertIn(QUEUED, module.LABELS)


class RefusedWrites(unittest.TestCase):
    """A write GitHub refuses, with the run started by `main` as the workflow starts it."""

    def closed(self):
        """Two closed pull requests that kept `batch queue`: the run takes it off #12, then #13."""
        gh = Fake()
        for number in (12, 13):
            gh.add_pull(number, f"head{number}", labels=[QUEUED])
            gh.close(number)
        return gh

    def refuse(self, gh, path, status, message):
        """GitHub answers `status` to every write to `path`."""
        answer = gh.call

        def call(method, to, payload=None):
            if method != "GET" and to == path:
                gh.calls += 1
                return status, {"message": message}
            return answer(method, to, payload)
        gh.call = call

    def run_main(self, gh):
        with tempfile.TemporaryDirectory() as folder:
            summary = Path(folder) / "summary.md"
            argv = ["batch-queue-sync.py", "--repo", REPO, "--summary", str(summary)]
            with mock.patch.object(batch, "GitHub", lambda repo, dry_run=False: gh), \
                    mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()), \
                    self.assertRaises(SystemExit) as stop:
                batch.main()
            return stop.exception.code, summary.read_text()

    def test_a_refusal_for_the_rate_limit_stops_the_run_and_says_so(self):
        gh = self.closed()
        self.refuse(gh, "issues/13/labels/batch%20queue", 429, "API rate limit exceeded")
        code, summary = self.run_main(gh)
        self.assertEqual(code, 1)
        self.assertIn("GitHub's rate limit refused DELETE issues/13/labels/batch%20queue", summary)
        self.assertEqual(gh.pulls[12]["labels"], set())

    def test_another_refusal_is_reported_and_fails_the_run(self):
        gh = self.closed()
        self.refuse(gh, "issues/13/labels/batch%20queue", 500, "Server Error")
        code, summary = self.run_main(gh)
        self.assertEqual(code, 1)
        self.assertIn("- #12 is closed: `batch queue` removed\n", summary)
        self.assertIn("- #13: GitHub answered 500 to removing `batch queue`, so it is still on\n", summary)
        self.assertEqual(gh.pulls[13]["labels"], {QUEUED})

    def test_a_run_without_a_refusal_succeeds(self):
        code, summary = self.run_main(self.closed())
        self.assertIsNone(code)
        self.assertIn("- #13 is closed: `batch queue` removed\n", summary)


if __name__ == "__main__":
    unittest.main()
