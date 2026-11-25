#!/usr/bin/env python3
"""Checks of the ticking of `depends on` boxes against an in-memory stand-in for GitHub; no network
calls."""
import contextlib
import importlib.util
import io
from pathlib import Path
import re
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
WORKFLOWS = SCRIPTS.parent / ".github" / "workflows"


def load(name, filename):
    # Registered before it runs, as `load` in `github-rest.py` does: its dataclass needs that up to
    # Python 3.14.
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


ticks = load("dependency_ticks", "dependency-ticks.py")

REPO = "o/r"
WAITING, BUILDING, LATEST = ticks.WAITING, ticks.BUILDING, ticks.LATEST


class Fake(ticks.GitHub):
    """Just enough of GitHub's GraphQL and REST APIs."""

    def __init__(self, dry_run=False, missing=()):
        super().__init__(REPO, dry_run)
        self.pulls, self.comments, self.sent, self.missing = {}, {}, [], set(missing)
        # Head commits that are in main, head commits GitHub no longer has, and the issues, which
        # are not pull requests. `holds` says which head commits each batch's head holds.
        self.in_main_heads, self.gone, self.issues = set(), set(), set()
        self.holds = {}
        # The compares made, as (base, head), and the pull requests read on their own.
        self.compared, self.reads = [], []
        # Called with the pull request's number each time it is read on its own, as an author's
        # edit made meanwhile.
        self.meanwhile = None
        self.left = 5000

    def add(self, number, body="", *, state="OPEN", labels_=(), head=None, base="main", ref=None, own=False):
        self.pulls[number] = {"number": number, "state": state, "body": body, "labels": set(labels_),
                              "head": head if head is not None else f"{number:040x}", "base": base,
                              "ref": ref or f"topic-{number}", "home": REPO if own else "fork/r"}

    def batch(self, number, *members, latest=False, body=""):
        """An open batch being built, holding the heads of `members`."""
        self.add(number, body, ref=f"batch/b{number}", own=True,
                 labels_=[BUILDING, LATEST] if latest else [BUILDING])
        self.holds[self.pulls[number]["head"]] = {self.pulls[member]["head"] for member in members}

    def head(self, number):
        found = self.pulls[number]
        return {"headRefOid": found["head"], "headRefName": found["ref"],
                "headRepository": {"nameWithOwner": found["home"]}}

    def node(self, number):
        found = self.pulls[number]
        return {"number": number, "state": found["state"], "body": found["body"], **self.head(number),
                "labels": {"nodes": [{"name": name} for name in sorted(found["labels"])]}}

    def graphql(self, query, missing=False, **variables):
        self.queries += 1
        self.points += 1
        if query == ticks.EVERY:
            nodes = [self.node(n) for n in sorted(self.pulls) if self.pulls[n]["state"] == "OPEN"]
            return {"repository": {"defaultBranchRef": {"name": "main"}, "pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": nodes}}}
        if query == ticks.ONE:
            number = variables["number"]
            self.reads.append(number)
            if self.meanwhile:
                self.meanwhile(number)
            return {"repository": {"defaultBranchRef": {"name": "main"},
                                   "pullRequest": self.node(number) if number in self.pulls else None}}
        if query == ticks.BUILT:
            nodes = [self.node(n) for n in sorted(self.pulls)
                     if self.pulls[n]["state"] == "OPEN" and BUILDING in self.pulls[n]["labels"]]
            return {"repository": {"pullRequests": {"nodes": nodes}}}
        if query == ticks.COMMENTS:
            nodes = [{"body": body, "author": author} for body, author in self.comments.get(variables["number"], [])]
            return {"repository": {"pullRequest": {"comments": {
                "pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": nodes}}}}
        found = {}
        for number in map(int, re.findall(r"p(\d+): issueOrPullRequest", query)):
            if number in self.pulls:
                pr = self.pulls[number]
                found[f"p{number}"] = {"__typename": "PullRequest", "number": number, "state": pr["state"],
                                       "baseRefName": pr["base"], **self.head(number)}
            elif number in self.issues:
                found[f"p{number}"] = {"__typename": "Issue"}
            else:
                found[f"p{number}"] = None
        return {"repository": found}

    def rate_limit(self):
        self.remaining = self.left

    def call(self, method, path, payload=None):
        self.calls += 1
        self.remaining = self.left
        if method != "GET":
            self.sent.append((method, path, payload))
        match = re.fullmatch(r"compare/(\w+)\.\.\.(\w+)\?per_page=1", path)
        if match and method == "GET":
            base, head = match.groups()
            self.compared.append((base, head))
            if head in self.gone:
                return 404, {"message": "Not Found"}
            inside = head in (self.in_main_heads if base == "main" else self.holds.get(base, set()))
            return 200, {"ahead_by": 0 if inside else 3, "behind_by": 7}
        match = re.fullmatch(r"labels/(.+)", path)
        if match and method == "GET":
            return (404 if match.group(1) in self.missing else 200), {}
        match = re.fullmatch(r"pulls/(\d+)", path)
        if match and method == "PATCH":
            self.pulls[int(match.group(1))]["body"] = payload["body"]
            return 200, {}
        match = re.fullmatch(r"issues/(\d+)/labels", path)
        if match and method == "POST":
            self.pulls[int(match.group(1))]["labels"] |= set(payload["labels"])
            return 200, []
        match = re.fullmatch(r"issues/(\d+)/comments", path)
        if match and method == "POST":
            self.comments.setdefault(int(match.group(1)), []).append(
                (payload["body"], {"__typename": "Bot", "login": ticks.BOT}))
            return 201, {"id": 1}
        raise AssertionError(f"unexpected request {method} {path}")

    def told_about(self, number):
        return [int(ticks.TOLD.match(body).group(1)) for body, _ in self.comments.get(number, [])
                if ticks.TOLD.match(body)]

    def edits(self):
        return [path for method, path, _ in self.sent if method == "PATCH"]


def run(gh, number=None, closed=None):
    with contextlib.redirect_stdout(io.StringIO()):
        return ticks.sync(gh, number, closed)


class Ticking(unittest.TestCase):
    def test_a_line_is_ticked_once_its_pull_request_is_merged(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2, "Text.\n\n---\n\n- [ ] depends on: #1\n")
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "Text.\n\n---\n\n- [x] depends on: (main) #1\n")
        self.assertIn("#2: tick line 5 as `(main)`, because #1 was merged into `main`", log)
        self.assertEqual(gh.compared, [])

    def test_only_when_every_pull_request_on_the_line_has_landed(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2)
        gh.add(3, "- [ ] depends on: #1, #2\n- [ ] depends on: #1\n")
        run(gh)
        self.assertEqual(gh.pulls[3]["body"], "- [ ] depends on: #1, #2\n- [x] depends on: (main) #1\n")
        gh.pulls[2]["state"] = "MERGED"
        run(gh)
        self.assertEqual(gh.pulls[3]["body"], "- [x] depends on: (main) #1, #2\n- [x] depends on: (main) #1\n")

    def test_the_description_is_kept_byte_for_byte(self):
        body = ("Moves `foo`.\r\n\r\n<!-- - [ ] depends on: #1 -->\r\n```\r\n- [ ] depends on: #1\r\n```\r\n"
                "Ünïcode 🤖  \r\n---\r\n\r\n- [ ] depends on: #1\r\n- [ ] depends on: other/r#1\r\n- depends on: #1")
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2, body)
        run(gh)
        (_, path, payload), = gh.sent
        at = body.rindex("- [ ] depends on: #1\r\n") + 3
        note = at + 1 + len("] depends on: ")
        self.assertEqual((path, payload), ("pulls/2", {"body": body[:at] + "x" + body[at + 1:note] + "(main) "
                                                               + body[note:]}))

    def test_nothing_is_written_when_nothing_changes(self):
        gh = Fake()
        gh.add(1)
        gh.add(4, state="MERGED")
        gh.add(2, "- [ ] depends on: #1\n- [x] depends on: #4\n- depends on: #4\n[] depends on: #4\n"
                  "- [x] depends on: (main) #1\n")
        gh.issues.add(5)
        gh.add(3, "- [ ] depends on: #5\n- [ ] depends on: #6\n")
        run(gh)
        self.assertEqual((gh.sent, gh.reads), ([], []))

    def test_the_description_is_read_again_and_an_edit_made_meanwhile_kept(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2, "- [ ] depends on: #1\n")

        def edit(number):
            gh.pulls[number]["body"] = "Now with a summary.\n\n- [ ] depends on: #1\n"
        gh.meanwhile = edit
        run(gh)
        self.assertEqual(gh.reads, [2])
        self.assertEqual(gh.sent, [("PATCH", "pulls/2", {"body": "Now with a summary.\n\n- [x] depends on: (main) #1\n"})])

    def test_no_write_when_the_fresh_copy_needs_none(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2, "- [ ] depends on: #1\n")

        def tick_by_hand(number):
            gh.pulls[number]["body"] = "- [x] depends on: #1\n"
        gh.meanwhile = tick_by_hand
        log = run(gh)
        self.assertEqual(gh.sent, [])
        self.assertFalse(any(line.startswith("#2") for line in log), log)

    def test_a_pull_request_closed_meanwhile_is_skipped(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(2, "- [ ] depends on: #1\n")
        gh.meanwhile = lambda number: gh.pulls[number].update(state="CLOSED")
        log = run(gh)
        self.assertEqual(gh.sent, [])
        self.assertIn("#2: skipped, because it was closed meanwhile", log)

    def test_landed_when_closed_with_its_head_in_main(self):
        gh = Fake()
        gh.add(1, state="CLOSED")
        gh.in_main_heads.add(gh.pulls[1]["head"])
        gh.add(2, "- [ ] depends on: #1\n")
        gh.add(3, "- [ ] blocked by https://github.com/o/r/pull/1\n")
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (main) #1\n")
        self.assertEqual(gh.pulls[3]["body"], "- [x] blocked by (main) https://github.com/o/r/pull/1\n")
        self.assertIn("#2: tick line 1 as `(main)`, because #1 was closed, and its head is in `main`", log)
        # Compared once for both pull requests that name it, and nobody told anything.
        self.assertEqual(gh.compared, [("main", gh.pulls[1]["head"])])
        self.assertEqual(gh.comments, {})

    def test_a_head_github_no_longer_has_decides_nothing(self):
        gh = Fake()
        gh.add(1, state="CLOSED", head="")
        gh.add(7, state="CLOSED")
        gh.gone.add(gh.pulls[7]["head"])
        gh.add(2, "- [ ] depends on: #1\n- [ ] depends on: #7\n")
        log = run(gh, 2)
        self.assertEqual(gh.sent, [])
        self.assertIn("#2: nothing to change, because #1 was closed, and GitHub names no head commit for it; "
                      "#7 was closed, and GitHub no longer has its head commit", log)


class ClosedWithoutLanding(unittest.TestCase):
    def scene(self, **options):
        gh = Fake(**options)
        gh.add(1, state="CLOSED")
        gh.add(2, "- [ ] depends on: #1\n")
        return gh

    def test_the_author_is_told_once_and_handed_the_pull_request(self):
        gh = self.scene()
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\n")
        self.assertEqual((gh.told_about(2), gh.pulls[2]["labels"]), ([1], {WAITING}))
        self.assertIn(f"#2: add `{WAITING}`; tell it that #1 was closed without landing", log)
        self.assertEqual([method for method, _, _ in gh.sent], ["POST", "POST"])
        # The author comments `ready`, which takes the label off, and the line stays. Nothing is
        # said again, and the label stays off.
        gh.pulls[2]["labels"].clear()
        gh.sent.clear()
        run(gh)
        run(gh, 2)
        run(gh, closed=1)
        self.assertEqual((gh.sent, gh.told_about(2), gh.pulls[2]["labels"]), ([], [1], set()))

    def test_one_comment_for_each_closed_pull_request(self):
        gh = self.scene()
        gh.add(3, state="CLOSED")
        gh.pulls[2]["body"] += "- [ ] depends on: #3, #1\n"
        run(gh)
        self.assertEqual(gh.told_about(2), [1, 3])
        run(gh)
        self.assertEqual(gh.told_about(2), [1, 3])

    def test_what_the_author_is_told(self):
        text = ticks.message(12)
        self.assertTrue(text.startswith("<!-- dependency-ticks-closed 12 -->\n"))
        for needed in ("#12 was closed without its changes landing in `main`", "probably still carries",
                       "merge `main` into your branch", "take over the work of #12", "edit the description",
                       "comment `ready`", f"`{WAITING}`"):
            self.assertIn(needed, text)

    def test_a_dependency_that_is_still_open_is_not_mentioned(self):
        gh = self.scene()
        gh.pulls[1]["state"] = "OPEN"
        run(gh)
        self.assertEqual((gh.sent, gh.comments), ([], {}))

    def test_a_line_ticked_by_hand_is_settled(self):
        gh = self.scene()
        gh.pulls[2]["body"] = "- [x] depends on: #1\n"
        run(gh)
        self.assertEqual(gh.sent, [])

    def test_a_line_without_a_box_still_counts(self):
        gh = self.scene()
        gh.pulls[2]["body"] = "Depends on #1.\n"
        run(gh)
        self.assertEqual(gh.told_about(2), [1])

    def test_a_marker_from_someone_else_does_not_count(self):
        gh = self.scene()
        gh.comments[2] = [("<!-- dependency-ticks-closed 1 -->\nfake", {"__typename": "User", "login": "someone"})]
        run(gh)
        self.assertEqual(gh.told_about(2), [1, 1])

    def test_already_labelled_is_only_told(self):
        gh = self.scene()
        gh.pulls[2]["labels"].add(WAITING)
        run(gh)
        self.assertEqual([path for _, path, _ in gh.sent], ["issues/2/comments"])

    def test_a_missing_label_stops_a_real_run(self):
        gh = self.scene(missing=[WAITING])
        with self.assertRaises(ticks.Refused):
            run(gh)
        self.assertEqual(gh.comments, {})

    def test_ticks_and_tells_together(self):
        gh = self.scene()
        gh.add(3, state="MERGED")
        gh.pulls[2]["body"] = "- [ ] depends on: #3\r\n- [ ] depends on: #1\r\n"
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (main) #3\r\n- [ ] depends on: #1\r\n")
        self.assertEqual(gh.told_about(2), [1])


class OnMainOrInABatch(unittest.TestCase):
    """When a line counts as done: its pull requests are on main, or in a batch being built."""

    def test_merged_into_a_batch_branch_is_not_on_main(self):
        gh = Fake()
        gh.add(1, state="MERGED", base="batch/b9")
        gh.add(2, "- [ ] depends on: #1\n")
        log = run(gh, 2)
        self.assertEqual(gh.sent, [])
        self.assertIn("#2: nothing to change, because #1 was merged into `batch/b9`, which is neither in `main` "
                      "nor in a batch being built", log)
        # Nor is it closed without landing: nobody is told anything.
        self.assertEqual(gh.comments, {})
        # Once its head reaches main, it is on main.
        gh.in_main_heads.add(gh.pulls[1]["head"])
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (main) #1\n")

    def test_in_a_batch_being_built_it_is_ticked_as_batched_and_then_marked_main(self):
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1, latest=True)
        gh.add(2, "Text.\r\n\r\n---\r\n\r\n- [ ] depends on: #1\r\n")
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "Text.\r\n\r\n---\r\n\r\n- [x] depends on: (batched) #1\r\n")
        self.assertIn("#2: tick line 5 as `(batched)`, because #1 is in the batch #900, which is being built", log)
        # An open pull request is not compared with main.
        self.assertEqual(gh.compared, [(gh.pulls[900]["head"], gh.pulls[1]["head"])])
        # Nothing to do while it stays there.
        gh.sent.clear()
        run(gh)
        self.assertEqual(gh.sent, [])
        # The batch lands.
        gh.pulls[1]["state"] = gh.pulls[900]["state"] = "MERGED"
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "Text.\r\n\r\n---\r\n\r\n- [x] depends on: (main) #1\r\n")
        self.assertIn("#2: mark line 5 `(main)`, because #1 was merged into `main`", log)
        gh.sent.clear()
        run(gh)
        self.assertEqual(gh.sent, [])

    def test_a_lower_batch_counts_too(self):
        # #901 is stacked on #900, which was repaired with a new head of #1 that #901 has not merged.
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1)
        gh.batch(901, latest=True)
        gh.add(2, "- [ ] depends on: #1\n")
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (batched) #1\n")
        self.assertIn("#2: tick line 1 as `(batched)`, because #1 is in the batch #900, which is being built", log)
        # The outermost batch is asked first, and each batch once.
        self.assertEqual(gh.compared, [(gh.pulls[901]["head"], gh.pulls[1]["head"]),
                                       (gh.pulls[900]["head"], gh.pulls[1]["head"])])

    def test_only_batches_being_built_count(self):
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1)
        gh.pulls[900]["labels"].discard(BUILDING)
        gh.add(901, ref="batch/b901", labels_=[BUILDING])  # from a fork: not a batch
        gh.holds[gh.pulls[901]["head"]] = {gh.pulls[1]["head"]}
        gh.add(2, "- [ ] depends on: #1\n")
        run(gh)
        self.assertEqual((gh.sent, gh.compared), ([], []))

    def test_every_pull_request_on_the_line_must_be_on_main_or_in_a_batch(self):
        gh = Fake()
        gh.add(1, state="MERGED")
        gh.add(3)
        gh.add(4)
        gh.batch(900, 3, latest=True)
        gh.add(2, "- [ ] depends on: #1, #3\n- [ ] depends on: #3, #4\n")
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (batched) #1, #3\n- [ ] depends on: #3, #4\n")

    def test_a_line_that_leaves_every_batch_is_unticked(self):
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1, latest=True)
        gh.add(2, "- [ ] depends on: #1\r\n- [x] depends on: #1\r\n")
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: (batched) #1\r\n- [x] depends on: #1\r\n")
        # The batch is rebuilt without #1. The line ticked by hand stays as it is.
        gh.holds[gh.pulls[900]["head"]] = set()
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\r\n- [x] depends on: #1\r\n")
        self.assertIn("#2: untick line 1, because #1 is open", log)
        self.assertEqual(gh.comments, {})
        # The batch is closed with #1 still in it.
        gh.holds[gh.pulls[900]["head"]] = {gh.pulls[1]["head"]}
        run(gh)
        gh.pulls[900]["state"] = "CLOSED"
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\r\n- [x] depends on: #1\r\n")

    def test_closed_in_a_batch_and_then_dropped_from_it_is_unticked_and_told(self):
        gh = Fake()
        gh.add(1, state="CLOSED")
        gh.batch(900, 1, latest=True)
        gh.add(2, "- [ ] depends on: #1\n")
        run(gh)
        self.assertEqual((gh.pulls[2]["body"], gh.comments), ("- [x] depends on: (batched) #1\n", {}))
        gh.holds[gh.pulls[900]["head"]] = set()
        log = run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\n")
        self.assertIn(f"#2: untick line 1, because #1 was closed without landing; add `{WAITING}`; tell it that #1 "
                      "was closed without landing", log)
        self.assertEqual(gh.told_about(2), [1])

    def test_marked_main_or_ticked_by_hand_is_never_looked_at_again(self):
        gh = Fake()
        gh.add(1)
        gh.add(2, "- [x] depends on: (main) #1\n- [x] depends on: #1\n- [X] depends on: #1\n")
        run(gh)
        self.assertEqual((gh.sent, gh.compared, gh.queries), ([], [], 1))


class Batches(unittest.TestCase):
    """Lines about batches get no annotation, and are ticked once the batches are on main."""

    def test_the_line_stacking_one_batch_on_another(self):
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1)
        gh.batch(901, 1, latest=True, body="Batch 10.\n\n- [ ] depends on: #900\n")
        run(gh)
        self.assertEqual((gh.sent, gh.compared), ([], []))
        # The lower batch lands.
        gh.pulls[900]["state"] = "MERGED"
        gh.pulls[900]["labels"].discard(BUILDING)
        log = run(gh)
        self.assertEqual(gh.pulls[901]["body"], "Batch 10.\n\n- [x] depends on: #900\n")
        self.assertIn("#901: tick line 3, because #900 was merged into `main`", log)

    def test_any_line_of_a_batch_is_ticked_plainly_and_only_once_on_main(self):
        gh = Fake()
        gh.add(1)
        gh.add(3, state="MERGED")
        gh.batch(900, 1, latest=True, body="- [ ] depends on: #1\n- [ ] depends on: #3\n")
        run(gh)
        self.assertEqual(gh.pulls[900]["body"], "- [ ] depends on: #1\n- [x] depends on: #3\n")

    def test_a_pull_request_depending_on_a_batch(self):
        gh = Fake()
        gh.add(1)
        gh.batch(900, 1)
        gh.batch(901, latest=True)
        gh.holds[gh.pulls[901]["head"]] = {gh.pulls[1]["head"], gh.pulls[900]["head"]}
        gh.add(2, "- [ ] depends on: #900\n- [ ] depends on: #1, #900\n")
        run(gh)
        # In a batch being built, but a batch counts only once it is on main.
        self.assertEqual(gh.sent, [])
        self.assertNotIn(gh.pulls[900]["head"], [head for _, head in gh.compared])
        gh.pulls[900]["state"] = gh.pulls[1]["state"] = "MERGED"
        run(gh)
        self.assertEqual(gh.pulls[2]["body"], "- [x] depends on: #900\n- [x] depends on: #1, #900\n")

    def test_a_batch_closed_without_landing_unticks_nothing(self):
        gh = Fake()
        gh.add(900, state="MERGED", ref="batch/b9", own=True)
        gh.add(2, "- [x] depends on: #900\n")
        run(gh)
        gh.pulls[900]["state"] = "CLOSED"
        run(gh)
        self.assertEqual(gh.sent, [])

    def test_the_parser_still_reads_annotated_lines(self):
        body = "- [x] depends on: (batched) #1, #2\n- [x] depends on (main) o/r#3\n- [ ] needs: (main)\n"
        self.assertEqual(ticks._dependencies.dependencies(body, REPO), {1, 2, 3})


class Runs(unittest.TestCase):
    def scene(self, **options):
        gh = Fake(**options)
        gh.add(1, state="MERGED")
        gh.add(5)
        gh.add(2, "- [ ] depends on: #1\n")
        gh.add(3, "- [ ] needs #1\n")
        gh.add(4, "- [ ] depends on: #5\n")
        return gh

    def test_the_sweep_looks_at_every_open_pull_request(self):
        gh = self.scene()
        log = run(gh)
        self.assertEqual(sorted(gh.edits()), ["pulls/2", "pulls/3"])
        self.assertIn("3 of 4 open pull requests declare dependencies; 2 lines ticked, marked or unticked; "
                      "0 pull requests told about a dependency closed without landing", log)

    def test_one_pull_request_alone(self):
        gh = self.scene()
        log = run(gh, 3)
        self.assertEqual(gh.edits(), ["pulls/3"])
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\n")
        log = run(gh, 4)
        self.assertIn("#4: nothing to change, because #5 is open", log)

    def test_one_pull_request_that_is_closed_or_missing(self):
        gh = self.scene()
        self.assertEqual(run(gh, 1), ["#1: nothing to change, because it is closed"])
        with self.assertRaises(ticks.Refused):
            run(gh, 99)

    def test_the_dependents_of_a_closed_pull_request(self):
        gh = self.scene()
        gh.add(6, state="MERGED")
        gh.add(7, "- [ ] depends on: #6\n")
        log = run(gh, closed=1)
        self.assertEqual(sorted(gh.edits()), ["pulls/2", "pulls/3"])
        self.assertIn("open pull requests that depend on #1: #2, #3", log)
        self.assertEqual(gh.pulls[7]["body"], "- [ ] depends on: #6\n")

    def test_a_dry_run_reads_everything_and_writes_nothing(self):
        gh = self.scene(dry_run=True)
        gh.add(8, state="CLOSED")
        gh.add(9, "- [ ] depends on: #8\n")
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            log = ticks.sync(gh)
        self.assertEqual(gh.sent, [])
        self.assertEqual(gh.pulls[2]["body"], "- [ ] depends on: #1\n")
        self.assertEqual(sorted(gh.reads), [2, 3, 9])
        self.assertIn("would PATCH pulls/2 (change line 1 of the description)", printed.getvalue())
        self.assertIn("would POST issues/9/comments", printed.getvalue())
        self.assertIn("#2: would tick line 1 as `(main)`, because #1 was merged into `main`", log)
        self.assertIn(f"#9: would add `{WAITING}`; would tell it that #8 was closed without landing", log)
        self.assertEqual(gh.wrote, 4)

    def test_writes_stop_when_the_hour_is_nearly_used_up(self):
        gh = self.scene()
        gh.left = ticks.RESERVE - 1
        log = run(gh)
        self.assertEqual(gh.sent, [])
        self.assertIn(f"only {ticks.RESERVE - 1} REST requests left this hour: stopped, and the next run carries on",
                      log)

    def test_compares_stop_too(self):
        gh = self.scene()
        gh.add(8, state="CLOSED")
        gh.add(9, "- [ ] depends on: #8\n")
        gh.left = ticks.RESERVE - 1
        run(gh)
        self.assertEqual((gh.compared, gh.sent), ([], []))

    def test_the_stop_comes_between_pull_requests(self):
        gh = self.scene()
        calls = []
        original = gh.call

        def call(method, path, payload=None):
            found = original(method, path, payload)
            calls.append(path)
            gh.remaining = gh.left = ticks.RESERVE - 1
            return found
        gh.call = call
        log = run(gh)
        self.assertEqual(gh.edits(), ["pulls/2"])
        self.assertTrue(any("stopped" in line for line in log), log)

    def test_a_failed_write_does_not_hold_up_the_rest(self):
        gh = self.scene()
        original = gh.call

        def call(method, path, payload=None):
            if path == "pulls/2":
                gh.sent.append((method, path, payload))
                return 422, {"message": "Validation Failed"}
            return original(method, path, payload)
        gh.call = call
        log = run(gh)
        self.assertTrue(gh.failed)
        self.assertIn("#2: skipped, because could not edit the description of #2: 422", log)
        self.assertEqual(gh.pulls[3]["body"], "- [x] needs (main) #1\n")


class Workflow(unittest.TestCase):
    def test_the_sweep_runs_at_minutes_no_other_workflow_uses(self):
        minutes = {}
        for path in sorted(WORKFLOWS.glob("*.yml")):
            for cron in re.findall(r"cron:\s*'([^']+)'", path.read_text()):
                for minute in cron.split()[0].split(","):
                    minutes.setdefault(minute, []).append(path.name)
        self.assertIn("dependencies.yml", {name for names in minutes.values() for name in names})
        self.assertEqual({minute: names for minute, names in minutes.items() if len(names) > 1}, {})


if __name__ == "__main__":
    unittest.main()
