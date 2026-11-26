#!/usr/bin/env python3
"""Batch building label checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import urllib.parse
from unittest import mock

SCRIPT = Path(__file__).resolve().parents[1] / "batch-building.py"
spec = importlib.util.spec_from_file_location("batch_building", SCRIPT)
building = importlib.util.module_from_spec(spec)
spec.loader.exec_module(building)

MEMBER = building.MEMBER
NOW = datetime.datetime(2026, 11, 26, 4, 0, 0, tzinfo=datetime.timezone.utc)


def at(minutes):
    """A GraphQL time stamp, `minutes` before NOW."""
    return (NOW - datetime.timedelta(minutes=minutes)).strftime("%Y-%m-%dT%H:%M:%SZ")


def branch(name, *, status="ahead", commits=(), pulls=(), age=10):
    """A `batch/...` branch. `status` is what comparing it with main answers, None for no common
    ancestor. `commits` are those main does not have. `pulls` holds (number, state), and optionally
    the repository its branch is in and how many minutes ago it was opened, for its pull requests,
    latest first. Its tip commit is `age` minutes old."""
    return {"name": name, "status": status, "commits": list(commits), "age": age,
            "pulls": [p + ("o/r", 1000)[len(p) - 2:] for p in pulls]}


def pull(number, head, *, ref=None, home="o/r", labels=()):
    """An open pull request with head commit `head`."""
    return {"number": number, "head": head, "ref": ref or f"topic-{number}", "home": home,
            "labels": list(labels)}


class Fake(building.GitHub):
    """Just enough of GitHub's REST and GraphQL APIs."""

    def __init__(self, branches=(), pulls=(), closed=None, label=True, dry_run=False, remaining=1000):
        super().__init__("o/r", dry_run)
        self.branches_ = {b["name"]: b for b in branches}
        self.pulls_ = list(pulls)
        # Closed or merged pull requests that carry the label, by number: their state.
        self.closed = closed or {}
        self.has_label, self.writes, self.compared = label, [], []
        # What GitHub says is left after each REST request.
        self.left = remaining
        # Pull requests whose label writes GitHub refuses, with this status.
        self.refuse = {}
        # Batch pull requests whose branches were deleted, as (number, minutes ago it was opened).
        self.deleted = []

    def call(self, method, path, payload=None):
        self.calls += 1
        self.left -= 1
        self.remaining = self.left
        if method == "GET" and path.startswith("labels/"):
            return (200, {"name": urllib.parse.unquote(path.split("/", 1)[1])}) if self.has_label else (404, None)
        if method == "GET" and path.startswith("compare/"):
            where, _, query = path.partition("?")
            base, _, head = urllib.parse.unquote(where[len("compare/"):]).partition("...")
            assert base == "main", base
            page = int(urllib.parse.parse_qs(query)["page"][0])
            per = int(urllib.parse.parse_qs(query)["per_page"][0])
            self.compared.append((head, page))
            found = self.branches_.get(head)
            if found is None or found["status"] is None:
                return 404, {"message": "No common ancestor"}
            commits = found["commits"]
            return 200, {"status": found["status"], "total_commits": len(commits),
                         "commits": [{"sha": sha} for sha in commits[(page - 1) * per:page * per]]}
        if method in ("POST", "DELETE"):
            parts = path.split("/")
            number = int(parts[1])
            if number in self.refuse:
                return self.refuse[number], {"message": "no"}
            name = payload["labels"][0] if method == "POST" else urllib.parse.unquote(parts[3])
            assert name == MEMBER, name
            self.writes.append(("add" if method == "POST" else "remove", number))
            return 200, []
        raise AssertionError(f"unexpected {method} {path}")

    def graphql(self, query, **variables):
        self.queries += 1
        if "refs(" in query:
            return {"repository": {"refs": {"pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": [
                {"name": b["name"][len("batch/"):], "target": {"oid": "tip", "committedDate": at(b["age"])}}
                for b in self.branches_.values()]}}}
        if "headRefName: $h0" in query:
            answer = {}
            for key, name in variables.items():
                if key.startswith("h"):
                    found = self.branches_.get(name, {"pulls": []})["pulls"]
                    answer["p" + key[1:]] = {"nodes": [
                        {"number": n, "state": state, "createdAt": at(opened),
                         "headRepository": {"nameWithOwner": home} if home else None}
                        for n, state, home, opened in found]}
            return {"repository": answer}
        if "$count" in query:
            nodes = [{"number": n, "createdAt": at(opened), "headRefName": b["name"],
                      "headRepository": {"nameWithOwner": home}}
                     for b in self.branches_.values() for n, _, home, opened in b["pulls"]]
            nodes += [{"number": n, "createdAt": at(opened), "headRefName": f"batch/gone-{n}",
                       "headRepository": {"nameWithOwner": "o/r"}} for n, opened in self.deleted]
            nodes.sort(key=lambda node: node["createdAt"], reverse=True)
            return {"repository": {"pullRequests": {"nodes": nodes[:variables["count"]]}}}
        if "search(" in query:
            nodes = [{"number": n, "state": state} for n, state in self.closed.items()]
            nodes += [{"number": p["number"], "state": "OPEN"} for p in self.pulls_ if MEMBER in p["labels"]]
            return {"search": {"pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": nodes}}
        if "states: OPEN" in query:
            # Two to a page, so that the pages are followed.
            start = int(variables["after"] or 0)
            page = self.pulls_[start:start + 2]
            return {"repository": {"pullRequests": {
                "pageInfo": {"hasNextPage": start + 2 < len(self.pulls_), "endCursor": str(start + 2)},
                "nodes": [{"number": p["number"], "headRefOid": p["head"], "headRefName": p["ref"],
                           "headRepository": {"nameWithOwner": p["home"]} if p["home"] else None,
                           "labels": {"nodes": [{"name": name} for name in p["labels"]]}}
                          for p in page]}}}
        raise AssertionError(f"unexpected query {query}")


def sync(gh, changed=None):
    return building.sync(gh, NOW, changed=changed)


class Membership(unittest.TestCase):
    def test_pull_requests_whose_head_commit_is_in_a_batch_are_labelled(self):
        gh = Fake([branch("batch/m1", commits=["m1", "a", "b", "tip"], pulls=[(10, "OPEN")])],
                  [pull(1, "a"), pull(2, "b"), pull(3, "c")])
        changed = []
        log = sync(gh, changed)
        self.assertEqual(gh.writes, [("add", 1), ("add", 2)])
        self.assertEqual(changed, [1, 2])
        self.assertIn("batch/m1: being built, because pull request #10 is open; 4 commits that `main` "
                      "does not have", log)
        self.assertIn("#1: labelled `batch-building`, because its head commit is in batch/m1", log)
        self.assertIn("2 open pull requests are in a batch being built", log)

    def test_a_member_that_has_the_label_is_left_alone(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a", labels=[MEMBER])])
        sync(gh)
        self.assertEqual(gh.writes, [])

    def test_a_pull_request_pushed_to_after_the_batch_took_it_loses_the_label(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a2", labels=[MEMBER])])
        log = sync(gh)
        self.assertEqual(gh.writes, [("remove", 1)])
        self.assertIn("#1: no longer labelled `batch-building`, because its head commit is in no batch "
                      "being built", log)

    def test_every_page_of_the_comparison_is_read(self):
        commits = [f"c{i}" for i in range(250)]
        gh = Fake([branch("batch/big", commits=commits, pulls=[(10, "OPEN")])], [pull(1, "c249")])
        sync(gh)
        self.assertEqual(gh.compared, [("batch/big", 1), ("batch/big", 2), ("batch/big", 3)])
        self.assertEqual(gh.writes, [("add", 1)])

    def test_a_pull_request_that_holds_a_batch_is_never_a_member(self):
        gh = Fake([branch("batch/m1", commits=["a", "tip"], pulls=[(10, "OPEN")])],
                  [pull(1, "a"), pull(10, "tip", ref="batch/m1", labels=[MEMBER])])
        log = sync(gh)
        self.assertEqual(gh.writes, [("add", 1), ("remove", 10)])
        self.assertIn("#10: no longer labelled `batch-building`, because it holds a batch", log)

    def test_a_batch_branch_of_a_fork_is_not_a_batch_pull_request(self):
        # Its head commit is in a batch, so it is a member like any other pull request.
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])],
                  [pull(1, "a", ref="batch/mine", home="fork/r")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])


class Branches(unittest.TestCase):
    def test_a_branch_from_before_main_was_replaced_is_not_a_batch(self):
        gh = Fake([branch("batch/b24-on-main", status=None, pulls=[(5273, "OPEN")])],
                  [pull(1, "a", labels=[MEMBER])])
        log = sync(gh)
        self.assertEqual(gh.writes, [("remove", 1)])
        self.assertIn("batch/b24-on-main: not being built, because it shares no history with `main`", log)

    def test_a_landed_branch_is_not_being_built(self):
        for status in ("behind", "identical"):
            with self.subTest(status=status):
                gh = Fake([branch("batch/m1", status=status, commits=[], pulls=[(10, "OPEN")])],
                          [pull(1, "a", labels=[MEMBER])])
                log = sync(gh)
                self.assertEqual(gh.writes, [("remove", 1)])
                self.assertIn("batch/m1: not being built, because `main` has all of it", log)

    def test_a_diverged_branch_with_an_open_pull_request_is_being_built(self):
        gh = Fake([branch("batch/m1", status="diverged", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])

    def test_a_branch_whose_pull_request_was_closed_or_merged_is_not_being_built(self):
        for state in ("CLOSED", "MERGED"):
            with self.subTest(state=state):
                gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, state)])], [pull(1, "a", labels=[MEMBER])])
                log = sync(gh)
                self.assertEqual(gh.writes, [("remove", 1)])
                self.assertIn(f"batch/m1: not being built, because its pull request #10 is {state.lower()}", log)
                # It is not compared: its pull request settles it.
                self.assertEqual(gh.compared, [])

    def test_only_the_latest_pull_request_of_a_branch_counts(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(11, "OPEN"), (10, "CLOSED")]),
                   branch("batch/m2", commits=["b"], pulls=[(13, "CLOSED"), (12, "OPEN")])],
                  [pull(1, "a"), pull(2, "b")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])

    def test_a_pull_request_from_a_fork_branch_of_the_same_name_does_not_count(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(11, "CLOSED", "fork/r")])], [pull(1, "a")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])

    def test_a_recent_branch_without_a_pull_request_is_being_built(self):
        gh = Fake([branch("batch/m1", commits=["a"], age=20)], [pull(1, "a")])
        log = sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])
        self.assertIn("batch/m1: being built, because it has no pull request yet and its tip commit "
                      "is 20 min old; 1 commits that `main` does not have", log)

    def test_retries_are_superseded_once_the_last_is_opened(self):
        # m11 and m11b were pushed 30 and 20 minutes ago and never opened; m11c, pushed 15 minutes
        # ago, was opened 10 minutes ago. #2 is in m11 and m11b only.
        gh = Fake([branch("batch/m11", commits=["a", "b"], age=30),
                   branch("batch/m11b", commits=["a", "b"], age=20),
                   branch("batch/m11c", commits=["a"], age=15, pulls=[(30, "OPEN", "o/r", 10)])],
                  [pull(1, "a"), pull(2, "b", labels=[MEMBER])])
        log = sync(gh)
        self.assertEqual(gh.writes, [("add", 1), ("remove", 2)])
        self.assertIn("batch/m11: not being built, because it has no pull request and batch pull request "
                      "#30 was opened after its tip commit", log)
        self.assertIn("#1: labelled `batch-building`, because its head commit is in batch/m11c", log)
        self.assertEqual([name for name, _ in gh.compared], ["batch/m11c"])

    def test_retries_count_until_the_last_is_opened(self):
        gh = Fake([branch("batch/m11", commits=["a", "b"], age=30),
                   branch("batch/m11b", commits=["a"], age=20),
                   branch("batch/m10", status="behind", age=200, pulls=[(20, "MERGED", "o/r", 190)])],
                  [pull(1, "a"), pull(2, "b")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1), ("add", 2)])

    def test_an_unopened_branch_newer_than_every_opened_batch_counts(self):
        gh = Fake([branch("batch/m12", commits=["b"], age=5),
                   branch("batch/m11c", commits=["a"], age=15, pulls=[(30, "OPEN", "o/r", 10)])],
                  [pull(1, "a"), pull(2, "b")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1), ("add", 2)])

    def test_pushing_to_an_open_batch_supersedes_nothing(self):
        # m11c was opened before m12 was pushed, and pushed to again since, say with main merged in.
        gh = Fake([branch("batch/m12", commits=["b"], age=5),
                   branch("batch/m11c", commits=["a"], age=1, pulls=[(30, "OPEN", "o/r", 10)])],
                  [pull(2, "b")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 2)])

    def test_a_batch_opened_from_a_branch_deleted_since_supersedes_too(self):
        gh = Fake([branch("batch/m6", commits=["a"], age=30)], [pull(1, "a", labels=[MEMBER])])
        gh.deleted = [(40, 20)]
        log = sync(gh)
        self.assertEqual(gh.writes, [("remove", 1)])
        self.assertIn("batch/m6: not being built, because it has no pull request and batch pull request "
                      "#40 was opened after its tip commit", log)

    def test_pull_requests_from_forks_supersede_nothing(self):
        gh = Fake([branch("batch/m12", commits=["b"], age=30),
                   branch("batch/m13", status=None, age=500, pulls=[(50, "OPEN", "fork/r", 5)])],
                  [pull(2, "b")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 2)])

    def test_the_backstop_is_an_hour(self):
        self.assertEqual(building.UNOPENED, datetime.timedelta(hours=1))
        gh = Fake([branch("batch/m1", commits=["a"], age=59)], [pull(1, "a")])
        sync(gh)
        self.assertEqual(gh.writes, [("add", 1)])

    def test_a_stale_branch_without_a_pull_request_is_not(self):
        old = int(building.UNOPENED.total_seconds() // 60)
        gh = Fake([branch("batch/m1", commits=["a"], age=old)], [pull(1, "a", labels=[MEMBER])])
        log = sync(gh)
        self.assertEqual(gh.writes, [("remove", 1)])
        self.assertIn("batch/m1: not being built, because it has no pull request and its tip commit "
                      "is 1 h 0 min old", log)
        self.assertEqual(gh.compared, [])


class Removal(unittest.TestCase):
    def test_merged_and_closed_pull_requests_lose_the_label(self):
        gh = Fake([branch("batch/m1", status="behind", pulls=[(10, "MERGED")])], [],
                  closed={1: "MERGED", 2: "CLOSED"})
        changed = []
        log = sync(gh, changed)
        self.assertEqual(gh.writes, [("remove", 1), ("remove", 2)])
        self.assertIn("#1: no longer labelled `batch-building`, because it is merged", log)
        self.assertIn("#2: no longer labelled `batch-building`, because it is closed", log)
        # The inbox has nothing to do for closed pull requests.
        self.assertEqual(changed, [])

    def test_an_open_pull_request_the_list_missed_is_left_to_the_next_run(self):
        gh = Fake([], [])
        gh.closed = {3: "OPEN"}
        sync(gh)
        self.assertEqual(gh.writes, [])

    def test_a_label_someone_took_off_meanwhile_is_not_an_error(self):
        gh = Fake([], [pull(1, "a", labels=[MEMBER])])
        gh.refuse[1] = 404
        log = sync(gh)
        self.assertFalse(gh.failed)
        self.assertIn("#1: no longer labelled `batch-building`, because its head commit is in no batch "
                      "being built", log)


class DryRun(unittest.TestCase):
    def test_a_dry_run_writes_nothing(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])],
                  [pull(1, "a"), pull(2, "b", labels=[MEMBER])], closed={3: "MERGED"}, dry_run=True)
        changed = []
        with contextlib.redirect_stdout(io.StringIO()) as out:
            sync(gh, changed)
        self.assertEqual(gh.writes, [])
        self.assertEqual(changed, [])
        self.assertEqual(out.getvalue().splitlines(), [
            f"would add {MEMBER} on #1", f"would remove {MEMBER} on #2", f"would remove {MEMBER} on #3"])

    def test_a_missing_label_stops_a_real_run_but_not_a_dry_run(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")], label=False)
        with self.assertRaises(building.Refused):
            sync(gh)
        self.assertEqual(gh.writes, [])
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")], label=False,
                  dry_run=True)
        with contextlib.redirect_stdout(io.StringIO()):
            log = sync(gh)
        self.assertIn("there is no `batch-building` label yet, so a real run would stop here", log)


class Allowance(unittest.TestCase):
    def test_too_few_requests_left_at_the_start_changes_nothing(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")],
                  remaining=building.RESERVE)
        log = sync(gh)
        self.assertEqual((gh.writes, gh.compared), ([], []))
        self.assertIn(f"stopped before changing anything, because only {building.RESERVE - 1} REST "
                      f"requests are left this hour: the next run carries on", log)

    def test_running_short_while_comparing_changes_nothing(self):
        # Enough for the label and one page, not for the second.
        commits = [f"c{i}" for i in range(150)]
        gh = Fake([branch("batch/m1", commits=commits, pulls=[(10, "OPEN")])],
                  [pull(1, "c0"), pull(2, "x", labels=[MEMBER])], remaining=building.RESERVE + 1)
        log = sync(gh)
        self.assertEqual(gh.compared, [("batch/m1", 1)])
        self.assertEqual(gh.writes, [])
        self.assertTrue(any(line.startswith("stopped before changing anything") for line in log))

    def test_running_short_while_labelling_leaves_the_rest_to_the_next_run(self):
        gh = Fake([branch("batch/m1", commits=["a", "b", "c"], pulls=[(10, "OPEN")])],
                  [pull(1, "a"), pull(2, "b"), pull(3, "c")], remaining=building.RESERVE + 3)
        log = sync(gh)
        # The label and the comparison leave RESERVE + 1, and two writes leave fewer than RESERVE.
        self.assertEqual(gh.writes, [("add", 1), ("add", 2)])
        self.assertIn(f"stopped, because only {building.RESERVE - 1} REST requests are left this hour: 1 more "
                      f"pull requests need the label changed, and the next run carries on", log)


class Main(unittest.TestCase):
    """The run as the workflow starts it."""

    def run_main(self, gh, *more):
        with tempfile.TemporaryDirectory() as folder:
            summary, changed = Path(folder) / "summary.md", Path(folder) / "changed"
            argv = ["batch-building.py", "--repo", "o/r", "--summary", str(summary), "--changed", str(changed),
                    *more]
            # The branches' ages count back from NOW.
            run = building.sync
            with mock.patch.object(building, "GitHub", lambda repo, dry_run=False: gh), \
                    mock.patch.object(building, "sync", lambda gh, log=None, changed=None: run(gh, NOW, log, changed)), \
                    mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(io.StringIO()), \
                    self.assertRaises(SystemExit) as stop:
                building.main()
            return stop.exception.code, summary.read_text(), changed.read_text()

    def test_the_summary_and_the_changed_pull_requests_are_written(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")], closed={2: "MERGED"})
        code, summary, changed = self.run_main(gh)
        self.assertIsNone(code)
        self.assertIn("- #1: labelled `batch-building`, because its head commit is in batch/m1\n", summary)
        self.assertIn("REST requests left this hour", summary.splitlines()[-1])
        self.assertEqual(changed, "1\n")

    def test_a_refusal_for_the_rate_limit_stops_the_run_and_keeps_what_was_done(self):
        gh = Fake([branch("batch/m1", commits=["a", "b"], pulls=[(10, "OPEN")])], [pull(1, "a"), pull(2, "b")])
        gh.refuse[2] = 429
        code, summary, changed = self.run_main(gh)
        self.assertEqual(code, 1)
        self.assertEqual(gh.writes, [("add", 1)])
        self.assertIn("GitHub's rate limit refused POST issues/2/labels", summary)
        self.assertEqual(changed, "1\n")

    def test_another_refusal_skips_that_pull_request_and_fails_the_run(self):
        gh = Fake([branch("batch/m1", commits=["a", "b"], pulls=[(10, "OPEN")])], [pull(1, "a"), pull(2, "b")])
        gh.refuse[1] = 422
        code, summary, changed = self.run_main(gh)
        self.assertEqual(code, 1)
        self.assertEqual(gh.writes, [("add", 2)])
        self.assertIn("- #1: skipped, because could not add batch-building on #1: 422\n", summary)
        self.assertEqual(changed, "2\n")

    def test_running_short_is_not_a_failure(self):
        gh = Fake([branch("batch/m1", commits=["a"], pulls=[(10, "OPEN")])], [pull(1, "a")], remaining=1)
        code, summary, changed = self.run_main(gh)
        self.assertIsNone(code)
        self.assertIn("stopped before changing anything", summary)
        self.assertEqual(changed, "")

    def test_the_script_starts_and_answers_help(self):
        done = subprocess.run([sys.executable, str(SCRIPT), "--help"], capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertIn("--dry-run", done.stdout)


if __name__ == "__main__":
    unittest.main()
