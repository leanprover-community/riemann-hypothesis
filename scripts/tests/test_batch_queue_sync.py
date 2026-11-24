#!/usr/bin/env python3
"""Batch assembly checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import hashlib
import importlib.util
import io
from pathlib import Path
import re
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "batch-queue-sync.py"
spec = importlib.util.spec_from_file_location("batch_queue_sync", SCRIPT)
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)

REPO = "o/r"
NOW = datetime.datetime(2026, 11, 23, 4, 12, 30, tzinfo=datetime.timezone.utc)
# Where the stand-in's clock starts. Each change to a pull request moves it on by a second.
T0 = datetime.datetime(2026, 11, 23, 3, 0, 0, tzinfo=datetime.timezone.utc)
FIRST = "batch/2026-11-23-041230"
QUEUED, BUILDING, BOT = batch.QUEUED, batch.BUILDING, batch.BOT


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
        self.clock, self.left = 0, None
        # How long after the latest change a run happens. An hour: everything has settled.
        self.ahead = datetime.timedelta(hours=1)

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
        self.comments.setdefault(number, []).append({"user": {"login": login}, "body": body})
        self.touch(number)

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
        if method != "GET":
            self.writes.append((method, path, payload))
        for pattern, handler in self.routes:
            match = re.fullmatch(pattern, f"{method} {path}")
            if match:
                return handler(self, payload, *match.groups())
        raise AssertionError(f"unexpected request: {method} {path}")

    def _repo(self, _):
        return 200, {"default_branch": "main"}

    def _open(self, _):
        return 200, [self.view(pr) for pr in self.pulls.values() if pr["state"] == "open"]

    def _pull(self, _, number):
        return 200, self.view(self.pulls[int(number)])

    def _closed_with(self, label):
        return 200, [{"number": pr["number"], "pull_request": {}, "body": pr["body"]} for pr in self.pulls.values()
                     if pr["state"] == "closed" and label in pr["labels"]]

    def _closed_building(self, _):
        return self._closed_with(BUILDING)

    def _closed_queued(self, _):
        return self._closed_with(QUEUED)

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
        if head in self.conflicting:
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

    def _comment(self, payload, number):
        self.say(int(number), payload["body"])
        return 201, {}

    def _drop_ref(self, _, name):
        return (204, None) if self.refs.pop(name, None) else (422, {"message": "Reference does not exist"})

    routes = [
        (r"GET ", _repo),
        (r"GET pulls\?state=open&per_page=100&page=1", _open),
        (r"GET git/matching-refs/heads/batch/", _refs),
        (r"GET git/ref/heads/main", _main),
        (r"GET git/commits/(.+)", _commit),
        (r"GET pulls\?state=all&head=o:(.+)", _pulls_for),
        (r"GET pulls/(\d+)", _pull),
        (r"GET issues\?state=closed&labels=building&per_page=100&page=1", _closed_building),
        (r"GET issues\?state=closed&labels=batch%20queue&per_page=100&page=1", _closed_queued),
        (r"GET issues/(\d+)/events\?per_page=100&page=1", _events),
        (r"GET compare/([^.]+)\.\.\.([^?]+)\?per_page=1", _compare),
        (r"GET issues/(\d+)/comments\?per_page=100&page=1", _comments),
        (r"GET issues/(\d+)/labels", _labels),
        (r"GET actions/workflows/build-pr.yml/runs\?event=workflow_dispatch&per_page=30", _runs),
        (r"POST git/refs", _new_ref),
        (r"POST merges", _merge),
        (r"POST pulls", _new_pull),
        (r"PATCH pulls/(\d+)", _edit_pull),
        (r"POST issues/(\d+)/labels", _add_label),
        (r"DELETE issues/(\d+)/labels/(.+)", _drop_label),
        (r"POST issues/(\d+)/comments", _comment),
        (r"DELETE git/refs/heads/(.+)", _drop_ref),
    ]


def queue(gh, *numbers):
    """A maintainer queues the head commit: the label job records it, then adds the label."""
    for number in numbers:
        if number not in gh.pulls:
            gh.add_pull(number, f"head{number}")
        gh.say(number, f"<!-- batch-queue-approved {gh.pulls[number]['sha']} -->\nQueued at this commit.")
        gh.label(number, add=QUEUED)


def unqueue(gh, number):
    """A maintainer comments `-batch`: the label job withdraws the commit, then removes the label."""
    gh.say(number, "<!-- batch-queue-withdrawn -->\nTaken out of the batch queue.")
    gh.label(number, remove=QUEUED)


def freeze(gh, number):
    gh.label(number, add=BUILDING)


def batch_pull(gh, ref=FIRST):
    return next(pr for pr in gh.pulls.values() if pr["ref"] == ref)


def sync(gh, hours=0):
    return batch.sync(gh, NOW + datetime.timedelta(hours=hours))


def merges(gh):
    return [payload["head"] for method, path, payload in gh.writes if path == "merges"]


class QueuedCommits(unittest.TestCase):
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


class Assembling(unittest.TestCase):
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
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({QUEUED}, {QUEUED}))
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
        self.assertEqual(gh.pulls[12]["labels"], {QUEUED})
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


class BranchNames(unittest.TestCase):
    def test_a_name_already_taken_is_not_reused(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        freeze(gh, 111)
        sync(gh)
        frozen_head = gh.refs[FIRST]
        queue(gh, 12)
        sync(gh)  # the same second as the first batch
        self.assertEqual(sorted(gh.refs), [FIRST, FIRST + "-2"])
        self.assertEqual(gh.refs[FIRST], frozen_head)
        self.assertNotIn(sha("head12"), gh.inside[frozen_head])
        self.assertIn(sha("head12"), gh.inside[gh.refs[FIRST + "-2"]])

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


class Freezing(unittest.TestCase):
    def frozen(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        freeze(gh, 112)
        return gh

    def test_frozen_batch_hands_its_label_to_what_it_contains(self):
        gh = self.frozen()
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({BUILDING}, {BUILDING}))
        body = gh.pulls[112]["body"]
        self.assertIn("This batch is frozen at", body)
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`", body)
        self.assertIn("#11 is in the frozen batch #112: now `building`", log)
        # And it stays that way on later runs.
        gh.writes = []
        self.assertEqual(sync(gh), ["nothing to do"])
        self.assertEqual(gh.writes, [])

    def test_arrival_after_the_freeze_starts_a_new_batch(self):
        gh = self.frozen()
        sync(gh)
        frozen_head = gh.refs[FIRST]
        queue(gh, 13)
        sync(gh, hours=2)
        self.assertEqual(gh.refs[FIRST], frozen_head)
        newest = batch_pull(gh, "batch/2026-11-23-061230")
        self.assertIn(f"- #13 at `{short('head13')}`", newest["body"])
        self.assertNotIn("#11", newest["body"])
        self.assertEqual(gh.pulls[13]["labels"], {QUEUED})

    def test_freeze_during_a_run_stops_further_merges(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        queue(gh, 12, 13)
        gh.after_merge = lambda: freeze(gh, 111)
        log = sync(gh)
        self.assertIn(sha("head12"), gh.inside[gh.refs[FIRST]])
        self.assertNotIn(sha("head13"), gh.inside[gh.refs[FIRST]])
        self.assertIn("batch #111 was frozen during this run: stopped adding to it", log)

    def test_a_dispatched_build_freezes_before_its_label_arrives(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        queue(gh, 12)
        gh.runs = ["Quick check #111 manual", "Proof shard #111 manual"]  # the freeze job has not run yet
        log = sync(gh)
        self.assertNotIn(sha("head12"), gh.inside[gh.refs[FIRST]])
        self.assertIn(BUILDING, gh.pulls[111]["labels"])
        self.assertIn("batch #111 was frozen during this run: stopped adding to it", log)

    def test_a_quick_check_or_a_build_of_something_else_does_not_freeze(self):
        gh = Fake()
        queue(gh, 11)
        sync(gh)
        queue(gh, 12)
        gh.runs = ["Quick check #111 manual", "Proof shard #1110 manual", "Build PR #11 manual"]
        sync(gh)
        self.assertIn(sha("head12"), gh.inside[gh.refs[FIRST]])
        self.assertNotIn(BUILDING, gh.pulls[111]["labels"])

    def test_frozen_batch_notes_what_left_it(self):
        gh = self.frozen()
        sync(gh)
        gh.label(11, remove=BUILDING)  # taken off by hand
        gh.pulls[12]["state"] = "closed"
        sync(gh)
        body = gh.pulls[112]["body"]
        self.assertIn("- nothing yet\n\nAlso in this branch:\n\n- #11, no longer queued\n- #12, closed since it was merged in", body)
        # A frozen batch is being built: nobody is told to close it.
        self.assertEqual((gh.said(11), gh.said(12)), ([], []))


class FinishedBatches(unittest.TestCase):
    def frozen(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        freeze(gh, 112)
        sync(gh)
        return gh

    def test_merged_batch_clears_building_and_removes_its_branch(self):
        gh = self.frozen()
        gh.add_pull(14, "head14", labels=[BUILDING])  # building in some other batch
        gh.close(11, merged=True)  # GitHub marks it merged along with the batch
        gh.close(112, merged=True)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), (set(), set()))
        self.assertEqual(gh.pulls[14]["labels"], {BUILDING})
        self.assertEqual((gh.refs, gh.pulls[112]["labels"]), ({}, set()))
        self.assertIn("#12 landed with batch #112: `building` removed", log)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_merged_batch_is_tidied_up_even_if_its_branch_was_deleted_first(self):
        gh = self.frozen()
        gh.push(12, "head12-later")
        gh.close(112, merged=True)
        del gh.refs[FIRST]  # someone pressed "Delete branch" before this run
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"], gh.pulls[112]["labels"]), (set(), set(), set()))
        self.assertIn("tidied up after batch #112; its branch was already gone", log)
        self.assertEqual(sync(gh), ["nothing to do"])

    def test_closed_batch_puts_its_pull_requests_back_even_if_its_branch_was_deleted_first(self):
        gh = self.frozen()
        gh.close(112)
        del gh.refs[FIRST]
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({QUEUED}, {QUEUED}))
        self.assertEqual(gh.pulls[112]["labels"], set())
        sync(gh, hours=1)
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`",
                      batch_pull(gh, "batch/2026-11-23-051230")["body"])

    def test_a_push_after_the_freeze_does_not_leave_building_behind(self):
        gh = self.frozen()
        gh.push(12, "head12-later")
        gh.close(112, merged=True)
        sync(gh)
        self.assertEqual(gh.pulls[12]["labels"], set())
        self.assertEqual(gh.pulls[12]["state"], "open")

    def test_frozen_batch_closed_without_merging_puts_its_pull_requests_back(self):
        gh = self.frozen()
        gh.close(112)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({QUEUED}, {QUEUED}))
        self.assertEqual(gh.refs, {})
        self.assertIn("batch #112 was closed without merging: #11 is `batch queue` again", log)
        self.assertIn("not starting a new batch in this run: the next `batch` or `-batch` comment does", log)
        # The pull request that broke the build is taken out, and the next run assembles the rest.
        unqueue(gh, 12)
        sync(gh, hours=1)
        newest = batch_pull(gh, "batch/2026-11-23-051230")
        self.assertIn(f"- #11 at `{short('head11')}`", newest["body"])
        self.assertNotIn("#12", newest["body"])

    def test_closing_a_batch_still_being_assembled_lets_the_next_run_start_again(self):
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


class LeavingTheQueue(unittest.TestCase):
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


class OtherBatchBranches(unittest.TestCase):
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
        self.assertEqual([write for write in gh.writes if write[1] != "issues/12/labels"], [])

    def test_building_does_not_make_it_a_frozen_batch(self):
        gh = Fake()
        self.by_hand(gh)
        gh.label(413, add=BUILDING)  # a build of it was dispatched
        queue(gh, 11)
        sync(gh)
        self.assertEqual(gh.pulls[413]["body"], "Written by the maintainer who assembled it.")
        self.assertEqual(gh.pulls[11]["labels"], {QUEUED})
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST]])

    def test_its_branch_is_not_deleted_when_its_pull_request_is_closed(self):
        gh = Fake()
        self.by_hand(gh)
        gh.close(413, merged=True)
        sync(gh)
        self.assertIn("batch/removals-2026-11-24", gh.refs)
        self.assertNotIn(("DELETE", "git/refs/heads/batch/removals-2026-11-24", None), gh.writes)


class ClosedPullRequests(unittest.TestCase):
    """A closed pull request is neither waiting for a build nor in one."""

    def test_closing_takes_the_label_off(self):
        gh = Fake()
        queue(gh, 11)
        gh.add_pull(12, "head12", labels=[QUEUED])  # labelled by hand
        gh.close(12)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({QUEUED}, set()))
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

    def test_closing_a_pull_request_in_a_frozen_batch_takes_building_off(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        freeze(gh, 112)
        sync(gh)
        gh.close(12)
        log = sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({BUILDING}, set()))
        self.assertIn("#12 is closed: `building` removed", log)
        # The batch's own pull request keeps `building` while it is open, and is not touched.
        self.assertEqual(gh.pulls[112]["labels"], {BUILDING})
        # When the batch is closed without merging, only the open one goes back to the queue.
        gh.close(112)
        sync(gh)
        self.assertEqual((gh.pulls[11]["labels"], gh.pulls[12]["labels"]), ({QUEUED}, set()))

    def test_a_merged_batch_is_tidied_up_once(self):
        gh = Fake()
        queue(gh, 11, 12)
        sync(gh)
        freeze(gh, 112)
        sync(gh)
        gh.close(11, merged=True)
        gh.close(12, merged=True)
        gh.close(112, merged=True)
        gh.writes = []
        sync(gh)
        drops = [path for method, path, _ in gh.writes if method == "DELETE" and "labels" in path]
        self.assertEqual(sorted(drops), ["issues/11/labels/building", "issues/112/labels/building",
                                         "issues/12/labels/building"])


class Reopening(unittest.TestCase):
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
            self.assertEqual(batch.reopened(gh, 11), ["#11 was reopened: `batch queue` put back"])
            self.assertEqual(gh.pulls[11]["labels"], {QUEUED})

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


class Requests(unittest.TestCase):
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
        # still labelled `building` or `batch queue`: no more.
        self.assertEqual(self.spent(gh), 6)
        self.assertEqual(self.spent(gh), 6)

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


class OpeningThePullRequest(unittest.TestCase):
    def test_when_workflows_may_not_open_pull_requests_the_branch_waits_for_a_person(self):
        gh = Fake()
        gh.allow_pulls = False
        queue(gh, 11)
        with self.assertRaises(batch.Refused) as caught:
            sync(gh)
        self.assertIn(f"https://github.com/o/r/compare/main...{FIRST}?expand=1", str(caught.exception))
        self.assertIn("not permitted to create", str(caught.exception))
        self.assertIn(sha("head11"), gh.inside[gh.refs[FIRST]])
        # A maintainer opens it by hand; the next run adopts it instead of starting another branch.
        gh.pulls[50] = {"number": 50, "state": "open", "merged_at": None, "labels": set(), "sha": gh.refs[FIRST],
                        "ref": FIRST, "own": True, "base": "main", "body": "", "title": "", "updated": 0}
        queue(gh, 12)
        sync(gh, hours=1)
        self.assertEqual(list(gh.refs), [FIRST])
        self.assertIn(f"- #11 at `{short('head11')}`\n- #12 at `{short('head12')}`", gh.pulls[50]["body"])


class DryRun(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
