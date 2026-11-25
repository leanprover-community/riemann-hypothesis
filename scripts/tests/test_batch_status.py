#!/usr/bin/env python3
"""Batch status issue checks against an in-memory stand-in for GitHub; no network calls."""
import datetime
import importlib.util
import json
from pathlib import Path
import re
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


status = load("batch_status", "batch-status.py")
labels = load("batch_labels_for_status", "batch-labels.py")

REPO = "o/r"
NOW = datetime.datetime(2026, 11, 24, 10, 3, tzinfo=datetime.timezone.utc)
QUEUED, PRIORITY, BUILDING, WAITING = status.QUEUED, status.PRIORITY, status.BUILDING, status.WAITING
CHANGED, MAIN_CONFLICT, BATCH_CONFLICT, LATEST = (
    status.CHANGED, status.MAIN_CONFLICT, status.BATCH_CONFLICT, status.LATEST)
BOT = {"__typename": "Bot", "login": "github-actions"}
COLOURS = {QUEUED: "c5def5", PRIORITY: "d93f0b", BUILDING: "fbca04", WAITING: "fbca04",
           CHANGED: "f9d0c4", MAIN_CONFLICT: "e99695", BATCH_CONFLICT: "d62929", LATEST: "e600e6"}


def sha(number):
    return f"{number:040x}"


def node(number, labels=(), ref=None, home=REPO, title=None, author="alice", draft=False):
    """A pull request as GraphQL lists it."""
    return {"number": number, "title": title or f"Change {number}", "isDraft": draft,
            "headRefName": ref or f"topic-{number}", "headRefOid": sha(number),
            "headRepository": {"nameWithOwner": home}, "author": {"login": author},
            "labels": {"nodes": [{"name": name} for name in labels]}}


def record(members, head):
    """The sync's record comment on a batch that contains `members`."""
    note = {"head": head, "members": {str(number): sha(number) for number in members}}
    return {"author": BOT, "body": f"<!-- batch-queue-by-hand {json.dumps(note)} -->\nBatch record"}


class Fake(status.GitHub):
    """Just enough of GitHub's GraphQL and REST APIs."""

    def __init__(self, nodes=(), batches=None, issues=(), pinned=(), found=(), ours=(), colours=None, dry_run=False):
        super().__init__(REPO, dry_run)
        self.nodes = list(nodes)
        # {number: (description, [comments])}
        self.batches = batches or {}
        # `found` is what the search by title finds, and `ours` what the search for the workflow's
        # issues that mention `batch-status` does.
        self.issues, self.pinned, self.found, self.ours = list(issues), list(pinned), list(found), list(ours)
        self.colours_ = COLOURS if colours is None else colours
        self.writes = []

    def now(self):
        return NOW

    def graphql(self, query, **variables):
        self.queries += 1
        if query is status.PULLS:
            # Two to a page, so that the pages are followed.
            start = int(variables["after"] or 0)
            return {"repository": {"pullRequests": {
                "nodes": self.nodes[start:start + 2],
                "pageInfo": {"hasNextPage": start + 2 < len(self.nodes), "endCursor": str(start + 2)}}}}
        if query is status.BATCH:
            body, comments = self.batches.get(variables["number"], ("", []))
            # One to a page.
            start = int(variables["after"] or 0)
            return {"repository": {"pullRequest": {"body": body, "comments": {
                "nodes": comments[start:start + 1],
                "pageInfo": {"hasNextPage": start + 1 < len(comments), "endCursor": str(start + 1)}}}}}
        if query is status.ISSUES:
            self.searched = (variables["q"], variables["ours"])
            return {"repository": {"pinnedIssues": {"nodes": [{"issue": issue} for issue in self.pinned]},
                                   "issues": {"nodes": self.issues}},
                    "search": {"nodes": self.found}, "ours": {"nodes": self.ours}}
        raise AssertionError(f"unexpected query {query[:40]}")

    def call(self, method, path, payload=None):
        self.calls += 1
        if method == "GET" and path.startswith("labels?"):
            return 200, [{"name": name, "color": colour.upper()} for name, colour in self.colours_.items()]
        if method in ("POST", "PATCH"):
            self.writes.append((method, path, payload))
            number = 99 if method == "POST" else int(path.split("/")[1])
            return (201 if method == "POST" else 200), {"number": number}
        raise AssertionError(f"unexpected {method} {path}")


def issue(number, body, state="OPEN", author=BOT):
    return {"number": number, "state": state, "body": body, "author": author}


def scene():
    """Two stacked batches, a queue with every group, and a description that leaves some out."""
    description = ("Batch 12.\n\nIncluded:\n\n- #11\n\nLeft out because they conflict with main:\n\n"
                   "- #30 needs main merged in\n- #31 also\n- #11 is in the branch after all\n"
                   "- #77 is closed\n\nLeft out at the author's request:\n\n- #32 asked\n")
    nodes = [
        node(200, [BUILDING], ref="batch/b12-on-100", title="batch 12"),
        node(100, [BUILDING, LATEST], ref="batch/b11-on-90", title="batch 11"),
        # A `batch/...` branch of a fork is not a batch, and neither is a pull request with
        # `building` left over from before.
        node(300, [BUILDING], ref="batch/sneaky", home="fork/r"),
        node(301, [BUILDING]),
        node(10, [WAITING]), node(11, [CHANGED]), node(12, []),
        node(20, [QUEUED]), node(21, [QUEUED, PRIORITY]), node(22, [QUEUED, MAIN_CONFLICT]),
        node(23, [QUEUED, CHANGED, BATCH_CONFLICT, PRIORITY]), node(24, [QUEUED, BATCH_CONFLICT, WAITING]),
        node(25, [QUEUED, CHANGED]), node(26, [QUEUED, WAITING, PRIORITY]),
        node(27, [QUEUED, MAIN_CONFLICT, PRIORITY]), node(12_000, [QUEUED], draft=True),
        node(30, [WAITING]), node(31, []), node(32, [QUEUED]),
    ]
    batches = {
        100: ("", [{"author": {"__typename": "User", "login": "maint"}, "body": "hello"},
                   record([10, 12], sha(100))]),
        # Batch 12 holds batch 11 and its members; its record is for an older head.
        200: (description, [record([100, 10, 12, 11], sha(1))]),
    }
    return nodes, batches


def full(fake):
    return status.status(REPO, fake.pulls(), fake.batch)


class Grouping(unittest.TestCase):
    def setUp(self):
        self.fake = Fake(*scene())
        self.found = full(self.fake)

    def test_batches_are_open_batch_branches_labelled_building_latest_first(self):
        self.assertEqual([batch["number"] for batch in self.found["batches"]], [100, 200])
        self.assertTrue(self.found["batches"][0]["latest"])

    def test_without_latest_the_newest_comes_first(self):
        nodes, batches = scene()
        nodes[1] = node(100, [BUILDING], ref="batch/b11-on-90")
        found = full(Fake(nodes, batches))
        self.assertEqual([batch["number"] for batch in found["batches"]], [200, 100])

    def test_a_stacked_batch_lists_only_its_own_members(self):
        outer = self.found["batches"][1]
        self.assertEqual(outer["members"], [10, 11, 12, 100])
        self.assertEqual(outer["contains"], [100])
        self.assertEqual(outer["own"], [11])

    def test_a_stacked_batch_read_from_the_sync_that_records_what_it_is_on(self):
        # Since stacked batches, the sync lists only a batch's own members and records the batches
        # it is stacked on under `below`.
        nodes, batches = scene()
        note = {"head": sha(1), "members": {"11": sha(11)}, "below": {"100": sha(100)}}
        batches[200] = (batches[200][0], [{"author": BOT, "body": f"<!-- batch-queue-by-hand {json.dumps(note)} -->"}])
        outer = full(Fake(nodes, batches))["batches"][1]
        self.assertEqual((outer["contains"], outer["own"], outer["members"]), ([100], [11], [10, 11, 12, 100]))

    def test_ready_is_queued_without_change_or_conflict(self):
        ready = [entry["number"] for entry in self.found["queue"] if entry["group"] == "ready"]
        self.assertEqual(ready, [21, 26, 20, 32, 12_000])

    def test_first_group_wins_and_priority_comes_first(self):
        groups = {entry["number"]: entry["group"] for entry in self.found["queue"]}
        # Changed after frozen and in conflict: pushed to since approval.
        self.assertEqual(groups[23], "changed")
        self.assertEqual(groups[25], "changed")
        self.assertEqual(groups[22], "conflict")
        self.assertEqual(groups[24], "conflict")
        order = [entry["number"] for entry in self.found["queue"]]
        self.assertEqual(order, [21, 26, 20, 32, 12_000, 23, 25, 27, 22, 24])

    def test_awaiting_author_does_not_change_the_group(self):
        groups = {entry["number"]: entry["group"] for entry in self.found["queue"]}
        self.assertEqual(groups[26], "ready")

    def test_what_a_batch_holds_is_not_queued(self):
        nodes, batches = scene()
        nodes.append(node(13, [QUEUED]))
        batches[100] = ("", [record([10, 12, 13], sha(100))])
        found = full(Fake(nodes, batches))
        self.assertNotIn(13, [entry["number"] for entry in found["queue"]])

    def test_left_out_by_heading_without_members_or_closed_ones(self):
        self.assertEqual(self.found["left"], {200: [
            ("Left out because they conflict with main:", [30, 31]),
            ("Left out at the author's request:", [32])]})
        self.assertEqual(self.found["gone"], {200: 1})


class Badges(unittest.TestCase):
    def test_escaping(self):
        self.assertEqual(status.shields("awaiting-author"), "awaiting--author")
        self.assertEqual(status.shields("batch queue"), "batch%20queue")
        self.assertEqual(status.shields("snake_case-x y"), "snake__case--x%20y")

    def test_a_badge(self):
        self.assertEqual(
            status.badge("changed after frozen", "f9d0c4", REPO),
            "[![changed after frozen](https://img.shields.io/badge/changed%20after%20frozen-f9d0c4"
            "?style=flat-square)](https://github.com/o/r/labels/changed%20after%20frozen)")
        self.assertEqual(status.badge("main-conflict", None, REPO, plain=True), "`main-conflict`")

    def test_live_colours_are_used(self):
        nodes, batches = scene()
        fake = Fake(nodes, batches, colours={**COLOURS, PRIORITY: "123ABC"})
        status.run(fake)
        body = fake.writes[0][2]["body"]
        self.assertIn(f"/badge/{PRIORITY}-123abc?style=flat-square", body)
        # A label GitHub does not have is grey.
        fake = Fake(nodes, batches, colours={})
        status.run(fake)
        self.assertIn(f"-{status.GREY}?style=flat-square", fake.writes[0][2]["body"])

    def test_titles_mention_nobody(self):
        self.assertEqual(status.escaped("Fix #12 for @bob | a_b"), "Fix #​12 for @​bob \\| a\\_b")


class Issue(unittest.TestCase):
    def test_opens_the_issue_when_there_is_none(self):
        fake = Fake(*scene())
        log = status.run(fake)
        self.assertEqual(len(fake.writes), 1)
        method, path, payload = fake.writes[0]
        self.assertEqual((method, path, payload["title"]), ("POST", "issues", "Batch status"))
        self.assertTrue(payload["body"].startswith(status.MARKER + "\n<!-- batch-status {"))
        self.assertIn("opened #99", log[-1])

    def test_finds_it_by_its_marker_and_author(self):
        body = status.MARKER + "\nold"
        someone = {"__typename": "User", "login": "x"}
        fake = Fake(*scene(),
                    issues=[issue(5, "something else"), issue(6, body, author=someone),
                            issue(7, "quoting " + status.MARKER, author=someone)],
                    found=[issue(9, body)], pinned=[issue(8, body, state="CLOSED")])
        status.run(fake)
        self.assertEqual([(method, path) for method, path, _ in fake.writes], [("PATCH", "issues/9")])

    def test_a_line_added_above_the_marker_does_not_lose_it(self):
        body = "Pinned: read this first.\n\n" + status.MARKER + "\nold"
        fake = Fake(*scene(), ours=[issue(9, body)])
        status.run(fake)
        self.assertEqual([(method, path) for method, path, _ in fake.writes], [("PATCH", "issues/9")])
        self.assertIn("author:app/github-actions", fake.searched[1])

    def test_a_closed_one_is_updated_not_duplicated(self):
        fake = Fake(*scene(), found=[issue(8, status.MARKER + "\nold", state="CLOSED")])
        log = status.run(fake)
        self.assertEqual([(method, path) for method, path, _ in fake.writes], [("PATCH", "issues/8")])
        self.assertIn("closed", log[-1])

    def test_no_write_when_nothing_changed(self):
        fake = Fake(*scene())
        status.run(fake)
        body = fake.writes[0][2]["body"]
        # Later, with only the time different.
        later = body.replace("2026-11-24 10:03", "2026-11-24 09:48")
        fake = Fake(*scene(), issues=[issue(99, later)])
        log = status.run(fake)
        self.assertEqual(fake.writes, [])
        self.assertIn("up to date", log[-1])

    def test_a_change_is_written_with_a_new_time(self):
        fake = Fake(*scene())
        status.run(fake)
        old = fake.writes[0][2]["body"].replace("2026-11-24 10:03", "2026-11-24 09:48")
        nodes, batches = scene()
        nodes.append(node(40, [QUEUED]))
        fake = Fake(nodes, batches, issues=[issue(99, old)])
        status.run(fake)
        self.assertEqual(fake.writes[0][:2], ("PATCH", "issues/99"))
        self.assertIn("Last changed 2026-11-24 10:03 UTC; last checked 2026-11-24 10:03 UTC.", fake.writes[0][2]["body"])

    def written(self):
        fake = Fake(*scene())
        status.run(fake)
        return fake.writes[0][2]["body"]

    def test_last_checked_is_written_again_only_once_it_is_six_hours_old(self):
        body = self.written()
        # Five hours ago: nothing to write.
        recent = body.replace("last checked 2026-11-24 10:03", "last checked 2026-11-24 05:04")
        fake = Fake(*scene(), issues=[issue(99, recent)])
        status.run(fake)
        self.assertEqual(fake.writes, [])
        # Six hours ago: written again, with only that time new.
        old = body.replace("Last changed 2026-11-24 10:03 UTC; last checked 2026-11-24 10:03",
                           "Last changed 2026-11-23 18:00 UTC; last checked 2026-11-24 04:03")
        fake = Fake(*scene(), issues=[issue(99, old)])
        log = status.run(fake)
        [(method, path, payload)] = fake.writes
        self.assertEqual((method, path), ("PATCH", "issues/99"))
        self.assertIn("Last changed 2026-11-23 18:00 UTC; last checked 2026-11-24 10:03 UTC.", payload["body"])
        self.assertEqual(payload["body"], body.replace("Last changed 2026-11-24 10:03", "Last changed 2026-11-23 18:00"))
        self.assertIn('updated #99: only its "last checked" time', log[-1])

    def test_a_footer_from_before_last_checked_is_written_again(self):
        body = self.written()
        before = body.replace("Last changed 2026-11-24 10:03 UTC; last checked 2026-11-24 10:03 UTC.",
                              "Last changed 2026-11-24 09:00 UTC.")
        fake = Fake(*scene(), issues=[issue(99, before)])
        status.run(fake)
        self.assertIn("Last changed 2026-11-24 09:00 UTC; last checked 2026-11-24 10:03 UTC.",
                      fake.writes[0][2]["body"])

    def test_dry_run_and_short_write_nothing(self):
        with tempfile.TemporaryDirectory() as folder:
            preview = Path(folder) / "preview.md"
            fake = Fake(*scene(), dry_run=True)
            log = status.run(fake, preview)
            self.assertEqual(fake.writes, [])
            self.assertIn("would open", log[-1])
            self.assertTrue(preview.read_text().startswith(status.MARKER))
        fake = Fake(*scene())
        fake.remaining = 3
        log = status.run(fake)
        self.assertEqual(fake.writes, [])
        self.assertIn("left this hour", log[-1])


class Body(unittest.TestCase):
    def body(self, nodes=None, batches=None):
        default = scene()
        fake = Fake(nodes or default[0], batches or default[1])
        status.run(fake)
        return fake.writes[0][2]["body"]

    def test_the_json_block(self):
        body = self.body()
        line = body.splitlines()[1]
        match = re.fullmatch(r"<!-- batch-status (\{.*\}) -->", line)
        block = json.loads(match.group(1))
        self.assertEqual(block["batches"][0], {"number": 100, "branch": "batch/b11-on-90", "head": sha(100),
                                               "latest": True, "members": [10, 12], "contains": []})
        self.assertEqual(block["batches"][1]["contains"], [100])
        self.assertEqual(block["queue"][0], {"number": 21, "group": "ready", "priority": True})
        self.assertEqual(block["left_out"], {"200": [30, 31, 32]})

    def test_nothing_in_the_json_ends_the_comment(self):
        nodes, batches = scene()
        nodes[0] = node(200, [BUILDING], ref="batch/a-->b")
        line = self.body(nodes, batches).splitlines()[1]
        self.assertEqual(line.count("-->"), 1)
        block = json.loads(re.fullmatch(r"<!-- batch-status (\{.*\}) -->", line).group(1))
        self.assertIn("batch/a-->b", [batch["branch"] for batch in block["batches"]])

    def test_sections_searches_and_footer(self):
        body = self.body()
        for heading in ("## Batches being built", "### #100 batch 11", "## Batch queue", "### Ready (5)",
                        "### Pushed to since approval (2)", "### Conflicts (3)", "## Left out", "### From #200",
                        "**Left out because they conflict with main:**"):
            self.assertIn(heading, body)
        self.assertIn("is%3Apr%20is%3Aopen%20label%3A%22batch%20queue%22%20-label%3A%22changed%20after%20frozen"
                      "%22%20-label%3Abatch-conflict%20-label%3Amain-conflict", body)
        self.assertIn("It contains the batch #100", body)
        self.assertIn("as of", body.replace("This is what it contained at", "as of"))
        self.assertIn("It also lists 1 pull request that is no longer open.", body)
        self.assertIn("`batch status` workflow", body)
        self.assertIn("Last changed 2026-11-24 10:03 UTC; last checked 2026-11-24 10:03 UTC.", body)
        self.assertIn("verification/BATCHES.md#the-status-issue", body)
        self.assertNotIn("Shortened", body)


class Size(unittest.TestCase):
    def crowd(self, count):
        nodes = [node(number, [QUEUED, WAITING, PRIORITY], title="A rather long title " * 6)
                 for number in range(1, count + 1)]
        return Fake(nodes)

    def test_shortened_step_by_step_and_said_so(self):
        seen = set()
        for count, level in ((100, 0), (200, 1), (400, 2), (600, 3), (12_000, 4)):
            fake = self.crowd(count)
            status.run(fake)
            body = fake.writes[0][2]["body"]
            self.assertLessEqual(len(body), status.LIMIT)
            self.assertEqual(sum(step in body for step in status.SHORTENED), level, count)
            seen.add(level)
            if level:
                self.assertIn("> Shortened to fit GitHub's limit", body)
            # The block, whole or not, and the footer survive any shortening.
            line = body.splitlines()[1]
            block = json.loads(re.fullmatch(r"<!-- batch-status (\{.*\}) -->", line).group(1))
            if level < 4:
                self.assertEqual(len(block["queue"]), count)
            else:
                self.assertEqual(block, {"truncated": True})
                self.assertIn("\n…\n", body)
            self.assertIn("Last changed", body)
        self.assertEqual(seen, {0, 1, 2, 3, 4})


class Names(unittest.TestCase):
    def test_the_label_names_are_those_of_batch_labels(self):
        for key in ("QUEUED", "PRIORITY", "BUILDING", "MEMBER", "WAITING", "CHANGED", "MAIN_CONFLICT",
                    "BATCH_CONFLICT", "LATEST"):
            with self.subTest(key=key):
                self.assertEqual(getattr(status, key), getattr(labels, key))


class Workflows(unittest.TestCase):
    WORKFLOWS = SCRIPTS.parent / ".github" / "workflows"

    def test_the_batch_queue_starts_it_after_its_sync_or_pushed_job(self):
        text = (self.WORKFLOWS / "batch-queue.yml").read_text()
        job = text.split("\n  status:\n", 1)[1]
        self.assertIn("needs: [pushed, sync]", job)
        self.assertIn("actions/workflows/batch-status.yml/dispatches", job)

    def test_it_follows_no_workflow_run(self):
        # Following every batch queue run would show most of them as skipped runs here.
        self.assertNotIn("workflow_run", (self.WORKFLOWS / "batch-status.yml").read_text().split("\non:", 1)[1])


if __name__ == "__main__":
    unittest.main()
