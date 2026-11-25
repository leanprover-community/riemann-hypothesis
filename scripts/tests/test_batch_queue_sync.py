#!/usr/bin/env python3
"""Batch assembly checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import re
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
QUEUED, BUILDING, BOT = batch.QUEUED, batch.BUILDING, batch.BOT
MEMBER, FROZEN, WAITING = batch.MEMBER, batch.FROZEN, batch.WAITING
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
        return 200, {"ahead_by": 0 if head == base or head in self.inside[base] else 1}

    def _branch_commits(self, _, base, head, page):
        """The commits of `head` that the branch `base` does not have, a hundred a page."""
        under = self.refs.get(base, MAIN if base == "main" else base)
        commits = sorted(({head} | self.inside[head]) - ({under} | self.inside[under]))
        start = (int(page) - 1) * 100
        return 200, {"total_commits": len(commits), "commits": [{"sha": commit} for commit in commits[start:start + 100]]}

    def _comments(self, _, number):
        return 200, list(self.comments.get(int(number), []))

    def _labels(self, _, number):
        return 200, [{"name": name} for name in sorted(self.pulls[int(number)]["labels"])]

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
        (r"GET actions/workflows/build-pr.yml/runs\?event=workflow_dispatch&per_page=30", _runs),
        (r"POST git/refs", _new_ref),
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
        gh.say(number, f"<!-- batch-queue-approved {gh.pulls[number]['sha']} -->\nQueued at this commit.")
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


def by_hand(gh, *numbers, number=1018, ref=HAND, name="kim"):
    """A maintainer merges the heads of these pull requests into a branch and opens a pull request."""
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
                            "body": "Assembled by hand.", "title": "", "updated": 0}
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
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING})
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
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[1018]["labels"]), (QF, {"large"}))
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
        self.assertEqual(gh.pulls[12]["labels"], IN | {WAITING})
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

    def test_a_batch_inside_another_one_is_built_as_part_of_it(self):
        gh = Fake()
        queue(gh, 11, 12)
        by_hand(gh, 11, number=463, ref="batch/citations", name="citations")
        queue(gh, 463)
        by_hand(gh, 463, 12)
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] - {"large"} for n in (11, 12, 463)], [IN] * 3)
        sync(gh)
        self.assertEqual(gh.said(463), [])  # not being built in its own right
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
        # and the batch's note, saved after every ten told.
        self.assertLess(gh.calls - before, 33 * 3 + 20)
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

    def test_what_is_left_out_is_told_why_and_handed_to_its_author(self):
        gh = self.built()
        log = sync(gh)
        [note] = self.left(gh, 21)
        self.assertIn("Batch #1018 leaves this pull request out. Its description says:\n\n"
                      "> Left out because they conflict with a PR earlier in the batch:\n>\n"
                      f"> `{URL}21` refactor: fold modules", note)
        self.assertIn("comment `ready`", note)
        self.assertEqual(gh.pulls[21]["labels"], QF | {WAITING})  # still queued
        self.assertEqual([gh.pulls[n]["labels"] for n in (22, 23, 24)], [{WAITING}, {WAITING}, set()])
        self.assertEqual([len(self.left(gh, n)) for n in (11, 22, 23, 24)], [0, 1, 1, 0])
        self.assertIn("told #23 that the batch #1018 leaves it out: now `awaiting-author`", log)
        # Nothing new: nothing said, nothing read. (#21 is queued, so the queue reads it again.)
        gh.reads = []
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (21, 22, 23)], [1, 1, 1])
        self.assertEqual([path for path in gh.reads if path.startswith(("issues/22/", "issues/23/"))], [])

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

    def test_a_new_kind_of_reason_is_told_and_hands_it_back_again(self):
        gh = self.built()
        sync(gh)
        gh.label(23, remove=WAITING)
        moved = DESCRIPTION.replace(f"- {URL}23 Drop imports from the root theorems (@frank): it changes `src/Main.lean`.\n", "")
        moved = moved.replace("Left out because they conflict with a PR earlier in the batch:\n\n",
                              f"Left out because they conflict with a PR earlier in the batch:\n\n- {URL}23 Drop (@frank): conflicts with #11.\n")
        gh.pulls[1018]["body"] = moved
        gh.touch(1018)
        sync(gh)
        first, second = self.left(gh, 23)
        self.assertIn("conflicts with `#11`", second)
        self.assertIn(WAITING, gh.pulls[23]["labels"])

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

    def test_dropped_from_the_branch_it_is_told_it_can_push_again(self):
        gh = self.built()
        sync(gh)
        by_hand(gh, 12, 14, name="kim-without-11")  # the branch is rebuilt without #11
        log = sync(gh)
        # Out of the branch, it is also told what the description says about it.
        self.assertEqual(gh.pulls[11]["labels"], QF | {WAITING})
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
        gh.push(12, "head12-later")
        by_hand(gh, 11, 12, 14, name="kim-with-12-later")  # merged in again before the next run
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], IN)
        notes = gh.said(12)
        self.assertEqual([note.split(" -->")[0] for note in notes],
                         [f"<!-- batch-queue-frozen 1018 {sha('head12')}", f"<!-- batch-queue-frozen 1018 {sha('head12-later')}"])

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
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14, 21)], [0, 0, 0, 0])
        gh.left = 900
        sync(gh)
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14, 21)], [1, 1, 1, 1])


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
        self.assertEqual(gh.pulls[11]["labels"], IN | {WAITING})
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
        gh.say(31, f"<!-- batch-queue-approved {sha('head31')} -->\nQueued at this commit.")
        gh.label(31, add=QUEUED)
        log = sync(gh)
        self.assertEqual(gh.pulls[31]["labels"], QF)
        self.assertIn("#31 is queued: now `frozen`", log)

    def test_only_what_is_queued_and_not_yet_frozen_is_looked_at(self):
        # With `ASSEMBLE` off nothing else reads what was queued. This costs a request for each pull
        # request labelled `batch queue` without `frozen`: once for one queued before `frozen`
        # existed, and every run for one labelled by hand, which no `batch` stands for.
        gh = Fake()
        queue(gh, 33)
        gh.add_pull(31, "head31")
        gh.say(31, f"<!-- batch-queue-approved {sha('head31')} -->\nQueued at this commit.")
        gh.label(31, add=QUEUED)
        gh.add_pull(34, "head34", labels=[QUEUED])  # labelled by hand: no `batch` stands for it
        sync(gh)
        self.assertEqual([gh.pulls[n]["labels"] for n in (31, 33, 34)], [QF, QF, {QUEUED}])
        self.assertEqual([path for path in gh.reads if path.startswith("issues/") and "/comments" in path],
                         ["issues/31/comments?per_page=100&page=1", "issues/34/comments?per_page=100&page=1"])
        gh.reads = []
        sync(gh)
        self.assertEqual([path for path in gh.reads if "/comments" in path], ["issues/34/comments?per_page=100&page=1"])

    def test_labels_of_a_batch_nothing_holds_come_off(self):
        gh = Fake()
        gh.add_pull(32, "head32", labels=[MEMBER, FROZEN])
        log = sync(gh)
        self.assertEqual(gh.pulls[32]["labels"], set())
        self.assertIn("#32 is neither queued nor in a batch being built: `batch-building` and `frozen` removed", log)
        self.assertEqual(sync(gh), ["nothing to do"])


class LeftOutDigests(unittest.TestCase):
    def test_the_kind_of_reason_is_its_heading_up_to_any_parenthesis(self):
        digest = batch.left_out_digest
        self.assertEqual(digest("Left out under the maintainers' guidance in `AGENTS.md` (no instance switching):", "a"),
                         digest("Left out under the maintainers' guidance in `AGENTS.md` (no workarounds):", "b"))
        self.assertNotEqual(digest("Left out for other reasons:", "a"),
                            digest("Left out because they conflict with a PR earlier in the batch:", "a"))


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
        # The members are labelled and told that they are frozen as usual.
        self.assertEqual([gh.pulls[n]["labels"] for n in (11, 12)], [IN, IN])
        self.assertEqual(sorted(note(gh.said(1018)[0])["left"]), ["21", "22", "23"])

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
        self.assertEqual([gh.pulls[n]["labels"] for n in (22, 23, 24)], [set(), {WAITING}, {WAITING}])
        self.assertEqual(sorted(note(gh.said(1018)[0])["left"]), ["21", "23", "24"])

    def test_a_record_with_left_out_notices_tells_what_is_new(self):
        # A record of this workflow, which has `left`, even an empty one, is not filled in again.
        gh = self.built()
        record = gh.comments[1018][-1]
        record["body"] = record["body"].replace('"queued"', '"left": {}, "queued"')
        sync(gh)
        self.assertEqual([len(self.left(gh, n)) for n in (21, 22, 23)], [1, 1, 1])


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
        # As R0's `dump_note` wrote it: members and `queued` only, so the members are labelled and
        # told now, once.
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
        self.assertEqual([len(gh.said(n)) for n in (11, 12, 14)], [1, 1, 1])
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
        self.assertIn("Built on `main`, because more than one batch assembled by hand is being built: "
                      "#1018, #2000.", batch_pull(gh)["body"])

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
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING})
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
        # One request each: closed pull requests have their labels set in one go.
        drops = [(method, path) for method, path, _ in gh.writes if method in ("DELETE", "PUT") and "labels" in path]
        self.assertEqual(sorted(drops), [("DELETE", "issues/1018/labels/building"), ("PUT", "issues/11/labels"),
                                         ("PUT", "issues/12/labels")])
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
        self.assertEqual(gh.pulls[1018]["labels"], {"large", BUILDING})
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

    def test_queuing_still_compares_with_the_rest_of_the_queue(self):
        conflicts = self.job("conflicts")
        self.assertIn("needs.label.outputs.queued == 'true'", conflicts)
        self.assertIn("scripts/batch-queue-conflicts.py", conflicts)
        spec = importlib.util.spec_from_file_location("batch_queue_conflicts", SCRIPT.with_name("batch-queue-conflicts.py"))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertIn(QUEUED, module.LABELS)


if __name__ == "__main__":
    unittest.main()
