#!/usr/bin/env python3
"""Conflict label checks against an in-memory stand-in for GitHub and a small local repository;
no network calls."""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import re
import subprocess
import tempfile
import sys
import unittest
from unittest import mock
from unittest.mock import patch
from urllib.parse import unquote

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


labels = load("conflict_labels", "conflict-labels.py")
inbox = load("inbox_sync_for_conflicts", "inbox-sync.py")
Comparison = labels._conflicts.Comparison

REPO = "o/r"
MAIN_CONFLICT, BATCH_CONFLICT = labels.MAIN_CONFLICT, labels.BATCH_CONFLICT
BUILDING, LATEST, MEMBER, WAITING = labels.BUILDING, labels.LATEST, labels.MEMBER, labels.WAITING


# ---------------------------------------------------------------------------------------------
# The dependency lines. `test_pr_dependencies.py` checks the parser itself.


class Dependencies(unittest.TestCase):
    def test_the_shared_parser_is_used(self):
        self.assertEqual(labels.dependencies.__module__, "rh_pr_dependencies")
        self.assertEqual(labels.dependencies("Some text.\n\n---\n\n- [ ] depends on: #123\n", REPO), {123})


# ---------------------------------------------------------------------------------------------
# Deciding, from facts alone.


def pr(number, *, labels_=(), mergeable="MERGEABLE", draft=False, open_=True, ref=None, own=False,
       base="main", depends=()):
    ref = ref or f"topic-{number}"
    return {"number": number, "open": open_, "draft": draft, "ref": ref,
            "batch": labels._labels.holds_batch(REPO, REPO if own else "fork/r", ref),
            "sha": f"{number:040x}", "base": base, "mergeable": mergeable, "body": "",
            "labels": set(labels_), "depends": set(depends)}


def batch(number, *, building=True, ref=None):
    return pr(number, labels_=[BUILDING] if building else [], ref=ref or f"batch/b{number}", own=True)


B = batch(900)
BATCHES = {900: B}
CONFLICT = Comparison("conflict", [b"src/A.lean"], [b"src/A.lean"])


def stale():
    result = Comparison("apart")
    result.stale = [("theirs", b"src/Gone.lean", b"src/New.lean")]
    return result


class Decide(unittest.TestCase):
    def test_pull_requests_that_can_carry_neither_label(self):
        cases = {"it is closed": pr(1, open_=False), "it is a draft": pr(1, draft=True),
                 "it is a batch": batch(1), "it targets `other`": pr(1, base="other")}
        for why, case in cases.items():
            with self.subTest(why=why):
                case["mergeable"] = "CONFLICTING"
                found = labels.decide(case, "main", BATCHES, {900: CONFLICT})
                self.assertEqual((found["main"], found["batch"], found["why"][MAIN_CONFLICT]), (False, False, why))

    def test_a_branch_named_batch_in_a_fork_is_not_a_batch(self):
        found = labels.decide(pr(1, ref="batch/mine", mergeable="CONFLICTING"), "main", BATCHES, {900: CONFLICT})
        self.assertEqual((found["main"], found["batch"]), (True, True))

    def test_main_conflict_follows_github(self):
        for state, wanted in (("CONFLICTING", True), ("MERGEABLE", False), ("UNKNOWN", None)):
            with self.subTest(state=state):
                self.assertEqual(labels.decide(pr(1, mergeable=state), "main", {}, {})["main"], wanted)

    def test_main_conflict_is_ignored_when_depending_on_an_open_batch(self):
        found = labels.decide(pr(1, mergeable="CONFLICTING", depends=[900]), "main", BATCHES, {900: Comparison("clean")})
        self.assertEqual((found["main"], found["why"][MAIN_CONFLICT]), (False, "it depends on the batch #900"))

    def test_a_batch_that_is_not_being_built_counts_for_the_dependency(self):
        waiting = {901: batch(901, building=False)}
        self.assertIs(labels.decide(pr(1, mergeable="CONFLICTING", depends=[901]), "main", waiting, {})["main"], False)

    def test_depending_on_something_else_does_not_count(self):
        # #5 is not a batch, and #901 is not open, so neither is in `batches`.
        found = labels.decide(pr(1, mergeable="CONFLICTING", depends=[5, 901]), "main", BATCHES, {900: Comparison("clean")})
        self.assertIs(found["main"], True)

    def test_batch_conflict_follows_the_comparison(self):
        cases = ((CONFLICT, True), (stale(), True), (Comparison("clean", [b"a"]), False), (Comparison("apart"), False),
                 (Comparison("too many"), None), (Comparison("unknown"), None), (None, None))
        for result, wanted in cases:
            with self.subTest(kind=getattr(result, "kind", None)):
                self.assertEqual(labels.decide(pr(1), "main", BATCHES, {900: result})["batch"], wanted)

    def test_not_compared_at_all_leaves_the_label(self):
        self.assertIsNone(labels.decide(pr(1), "main", BATCHES, {})["batch"])

    def test_members_of_the_batch_never_get_it(self):
        found = labels.decide(pr(1, labels_=[MEMBER, BATCH_CONFLICT]), "main", BATCHES, {})
        self.assertIs(found["batch"], False)

    def test_nothing_being_built_means_no_batch_conflict(self):
        self.assertIs(labels.decide(pr(1), "main", {901: batch(901, building=False)}, {})["batch"], False)
        self.assertIs(labels.decide(pr(1), "main", {}, {})["batch"], False)

    def test_only_the_outermost_batch_of_a_stack_counts(self):
        # #901 is stacked on #900 and holds its changes, so a conflict with #900 alone is not one.
        stack = {900: batch(900), 901: pr(901, labels_=[BUILDING, LATEST], ref="batch/b10-on-900", own=True)}
        self.assertEqual(labels.compared(stack), [901])
        found = labels.decide(pr(1), "main", stack, {900: CONFLICT, 901: Comparison("apart")})
        self.assertEqual((found["batch"], found["why"][BATCH_CONFLICT]), (False, "it merges with #901"))
        found = labels.decide(pr(1), "main", stack, {901: CONFLICT})
        self.assertEqual((found["batch"], sorted(found["conflicts"])), (True, [901]))

    def test_without_latest_batch_every_batch_being_built_counts(self):
        self.assertEqual(labels.compared({900: batch(900), 901: batch(901), 902: batch(902, building=False)}),
                         [900, 901])

    def test_each_stack_counts_once(self):
        stacks = {900: batch(900), 901: pr(901, labels_=[BUILDING, LATEST], ref="batch/b10-on-900", own=True),
                  910: pr(910, labels_=[BUILDING, LATEST], ref="batch/c1", own=True)}
        self.assertEqual(labels.compared(stacks), [901, 910])

    def test_one_conflict_is_enough_when_another_batch_is_unknown(self):
        batches = {900: B, 901: batch(901)}
        found = labels.decide(pr(1), "main", batches, {900: None, 901: CONFLICT})
        self.assertEqual((found["batch"], sorted(found["conflicts"])), (True, [901]))


class Plan(unittest.TestCase):
    def test_newly_conflicting_is_labelled_handed_back_and_told_without_reading_comments(self):
        case = pr(1)
        decision = labels.decide(case, "main", BATCHES, {900: CONFLICT})
        self.assertFalse(labels.needs_told(case, decision))
        add, remove, notes = labels.plan(case, decision, None, BATCHES)
        self.assertEqual((add, remove, [number for number, _ in notes]), ({BATCH_CONFLICT, WAITING}, set(), [900]))
        self.assertTrue(notes[0][1].startswith("<!-- conflict-labels-batch 900 -->\n"))

    def test_conflicting_again_without_the_label_is_told_again(self):
        case = pr(1)
        decision = labels.decide(case, "main", BATCHES, {900: CONFLICT})
        add, remove, notes = labels.plan(case, decision, {900}, BATCHES)
        self.assertEqual((add, remove, [number for number, _ in notes]), ({BATCH_CONFLICT, WAITING}, set(), [900]))

    def test_labelled_and_told_before_about_this_batch_is_left_alone(self):
        case = pr(1, labels_=[BATCH_CONFLICT])
        decision = labels.decide(case, "main", BATCHES, {900: CONFLICT})
        self.assertEqual(labels.plan(case, decision, {900}, BATCHES), (set(), set(), []))

    def test_labelled_and_conflicting_reads_the_comments_unless_known(self):
        case = pr(1, labels_=[BATCH_CONFLICT])
        decision = labels.decide(case, "main", BATCHES, {900: CONFLICT})
        self.assertTrue(labels.needs_told(case, decision))
        self.assertFalse(labels.needs_told(case, decision, {"told": {900}, "stale": set()}))
        self.assertEqual(labels.plan(case, decision, None, BATCHES), (set(), set(), []))

    def test_a_second_batch_is_told_about_too(self):
        batches = {900: B, 901: batch(901)}
        case = pr(1, labels_=[BATCH_CONFLICT, WAITING])
        decision = labels.decide(case, "main", batches, {900: CONFLICT, 901: CONFLICT})
        self.assertTrue(labels.needs_told(case, decision))
        add, remove, notes = labels.plan(case, decision, {900}, batches)
        self.assertEqual((add, remove, [number for number, _ in notes]), (set(), set(), [901]))

    def test_labels_come_off_but_awaiting_author_stays(self):
        case = pr(1, labels_=[MAIN_CONFLICT, BATCH_CONFLICT, WAITING])
        decision = labels.decide(case, "main", BATCHES, {900: Comparison("apart")})
        self.assertEqual(labels.plan(case, decision, None, BATCHES), (set(), {MAIN_CONFLICT, BATCH_CONFLICT}, []))

    def test_unknown_leaves_both_labels(self):
        case = pr(1, labels_=[MAIN_CONFLICT, BATCH_CONFLICT], mergeable="UNKNOWN")
        decision = labels.decide(case, "main", BATCHES, {900: None})
        self.assertEqual(labels.plan(case, decision, None, BATCHES), (set(), set(), []))


class Message(unittest.TestCase):
    def test_what_the_author_is_told(self):
        result = Comparison("conflict", [b"src/A.lean", b"src/B.lean"], [b"src/A.lean", b"src/B.lean"])
        result.stale = [("theirs", b"src/Gone.lean", b"src/New.lean"), ("ours", b"src/Old.lean", b"src/X.lean")]
        text = labels.message(batch(900, ref="batch/b9-on-1313"), result)
        self.assertTrue(text.startswith("<!-- conflict-labels-batch 900 -->\n"))
        for needed in ("#900", "`batch/b9-on-1313`", "git cannot merge 2 files", "`src/A.lean`, `src/B.lean`",
                       "#900 deletes `src/Gone.lean`, which this pull request starts to import in `src/New.lean`",
                       "this pull request deletes `src/Old.lean`, which #900 starts to import in `src/X.lean`",
                       "Merge the batch's branch `batch/b9-on-1313` into your branch and resolve the conflicts",
                       "at the end of the pull request's description, under a line `---`", "- [ ] depends on: #900",
                       "Comment `ready`", "wait until #900 has landed, then merge `main`",
                       f"`{BATCH_CONFLICT}` and `{WAITING}`"):
            self.assertIn(needed, text)
        # The line to copy is one the parser reads.
        line = next(line for line in text.splitlines() if "depends on" in line and "#900" in line)
        self.assertEqual(labels.dependencies(line.strip(), REPO), {900})

    def test_branch_names_cannot_break_out_of_code_formatting(self):
        text = labels.message(batch(900, ref="batch/`x`\n@y"), CONFLICT)
        self.assertIn("`batch/?x??@y`", text)


class Stale(unittest.TestCase):
    """A pull request whose branch carries commits that the batch it builds on no longer has."""

    def decided(self, labels_=()):
        case = pr(5, labels_=labels_, depends=[900])
        return case, labels.decide(case, "main", BATCHES, {900: Comparison("clean")}, {"on": [900], "prs": [11]})

    def test_it_is_told_once_for_each_set_of_pull_requests_and_handed_back(self):
        case, decision = self.decided()
        self.assertEqual(decision["stale"], {900: {"head": B["sha"], "prs": [11]}})
        self.assertTrue(labels.needs_told(case, decision))
        add, remove, notes = labels.plan(case, decision, set(), BATCHES, set())
        self.assertEqual((add, remove, [number for number, _ in notes]), ({WAITING}, set(), [900]))
        self.assertTrue(notes[0][1].startswith("<!-- conflict-labels-stale 900 11 -->\n"))
        # Told about #11 already, by this batch at any head or by another: nothing to read, nothing
        # to say, and `awaiting-author` is not put back.
        known = {"told": set(), "stale": {"11"}}
        self.assertFalse(labels.needs_told(case, decision, known))
        self.assertEqual(labels.plan(case, decision, None, BATCHES, None), (set(), set(), []))
        self.assertEqual(labels.plan(case, decision, set(), BATCHES, known["stale"]), (set(), set(), []))
        # Another set of pull requests is told again.
        self.assertTrue(labels.needs_told(case, decision, {"told": set(), "stale": {"11,12"}}))

    def test_a_batch_rebuilt_under_a_new_number_tells_nothing_new(self):
        batches = {**BATCHES, 901: batch(901)}
        case = pr(5, depends=[900, 901])
        decision = labels.decide(case, "main", batches, {}, {"on": [900, 901], "prs": [11]})
        # Said once, for the lowest of them.
        self.assertEqual(list(decision["stale"]), [900])
        self.assertEqual(labels.plan(case, decision, set(), batches, {"11"}), (set(), set(), []))

    def test_what_the_author_is_told(self):
        text = labels.stale_message(batch(900, ref="batch/b9-on-1313"), [11, 12])
        for needed in ("carries commits of #11, #12 that #900", "`batch/b9-on-1313` was rebuilt without them",
                       "GitHub marks #11, #12 merged", "new branch from the batch's current branch",
                       "`git cherry-pick`", "comment `ready`", "never by rebasing", f"`{WAITING}`"):
            self.assertIn(needed, text)

    def test_nothing_carried_is_nothing_to_say(self):
        case = pr(5, depends=[900])
        decision = labels.decide(case, "main", BATCHES, {900: Comparison("clean")}, {"on": [900], "prs": []})
        self.assertEqual(decision["stale"], {})
        self.assertFalse(labels.needs_told(case, decision))


# ---------------------------------------------------------------------------------------------
# Whole runs against a stand-in for GitHub.


class Fake(labels.GitHub):
    """Just enough of GitHub's GraphQL and REST APIs."""

    def __init__(self, dry_run=False, missing=()):
        super().__init__(REPO, dry_run)
        self.pulls, self.comments, self.sent, self.missing = {}, {}, [], set(missing)
        # What a later read finds for whether a pull request merges, as {number: [states]}.
        self.later = {}
        self.left = 5000
        # The pull requests whose comments were read, in order.
        self.comment_reads = []

    def add(self, number, *, ref=None, own=False, base="main", labels_=(), mergeable="MERGEABLE", body="",
            draft=False):
        self.pulls[number] = {"number": number, "state": "OPEN", "isDraft": draft, "headRefName": ref or f"topic-{number}",
                              "headRefOid": f"{number:040x}", "baseRefName": base, "mergeable": mergeable,
                              "body": body, "headRepository": {"nameWithOwner": REPO if own else "fork/r"},
                              "labels": set(labels_)}

    def node(self, number, fields=None):
        found = dict(self.pulls[number])
        found["labels"] = {"nodes": [{"name": name} for name in sorted(found["labels"])]}
        return found

    def graphql(self, query, **variables):
        self.queries += 1
        self.points += 1
        if query == labels.EVERY:
            nodes = [self.node(n) for n in sorted(self.pulls) if self.pulls[n]["state"] == "OPEN"]
            return {"repository": {"defaultBranchRef": {"name": "main"}, "pullRequests": {
                "pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": nodes}}}
        if query == labels.ONE:
            number = variables["number"]
            nodes = [self.node(n) for n in sorted(self.pulls)
                     if self.pulls[n]["state"] == "OPEN" and BUILDING in self.pulls[n]["labels"]]
            return {"repository": {"defaultBranchRef": {"name": "main"},
                                   "pullRequest": self.node(number) if number in self.pulls else None,
                                   "pullRequests": {"nodes": nodes}}}
        if query == labels.COMMENTS:
            self.comment_reads.append(variables["number"])
            nodes = [{"body": body, "author": author} for body, author in self.comments.get(variables["number"], [])]
            return {"repository": {"pullRequest": {"comments": {
                "pageInfo": {"hasNextPage": False, "endCursor": None}, "nodes": nodes}}}}
        if query == labels.CLOSED:
            def closed(label):
                return [{"number": n} for n in sorted(self.pulls)
                        if self.pulls[n]["state"] != "OPEN" and label in self.pulls[n]["labels"]]
            return {"main": {"nodes": closed(MAIN_CONFLICT)}, "batch": {"nodes": closed(BATCH_CONFLICT)}}
        found = {}
        for number in map(int, re.findall(r"p(\d+): pullRequest", query)):
            if number in self.pulls:
                node = self.node(number)
                if self.later.get(number):
                    node["mergeable"] = self.pulls[number]["mergeable"] = self.later[number].pop(0)
                found[f"p{number}"] = node
        return {"repository": found}

    def rate_limit(self):
        self.remaining = self.left

    def call(self, method, path, payload=None):
        self.calls += 1
        self.remaining = self.left
        if method != "GET":
            self.sent.append((method, path, payload))
        match = re.fullmatch(r"labels/(.+)", path)
        if match and method == "GET":
            return (404 if match.group(1) in self.missing else 200), {}
        match = re.fullmatch(r"issues/(\d+)/labels", path)
        if match:
            self.pulls[int(match.group(1))]["labels"] |= set(payload["labels"])
            return 200, []
        match = re.fullmatch(r"issues/(\d+)/labels/(.+)", path)
        if match:
            have = self.pulls[int(match.group(1))]["labels"]
            name = unquote(match.group(2))
            if name not in have:
                return 404, None
            have.discard(name)
            return 200, []
        match = re.fullmatch(r"issues/(\d+)/comments", path)
        if match:
            self.comments.setdefault(int(match.group(1)), []).append(
                (payload["body"], {"__typename": "Bot", "login": labels.BOT}))
            return 201, {"id": 1}
        raise AssertionError(f"unexpected request {method} {path}")

    def told_about(self, number):
        return [labels.TOLD.match(body).group(1) for body, _ in self.comments.get(number, []) if labels.TOLD.match(body)]


def comparing(table, stale=None):
    """A stand-in for `compare_all` that answers from {(pull request, batch): Comparison}, and
    finds what `stale` says each pull request carries, as {number: {"on": [...], "prs": [...]}}."""
    seen = []

    def compare(repo, main, building, candidates, log, *, watch=None, carried=None):
        seen.append((sorted(building), sorted(candidates)))
        compare.watch = watch
        if carried is not None:
            carried.update({number: found for number, found in (stale or {}).items() if number in candidates})
        return {number: {other: table.get((number, other), Comparison("apart")) for other in building}
                for number in candidates}
    compare.seen = seen
    return compare


def run(gh, number=None, table=None, stale=None, known=None):
    with contextlib.redirect_stdout(io.StringIO()):
        return labels.sync(gh, number, compare=comparing(table or {}, stale), known=known)


class Included(unittest.TestCase):
    def test_only_headings_that_include_count(self):
        # As batches 13 to 17 headed them. "Held by the maintainers:" says neither, so #6 is
        # compared like any other pull request.
        batches = {900: dict(batch(900), body="Included:\n\n- #1 a\n\n"
                                              "Included, but borderline; these can be dropped if the maintainers prefer:\n\n"
                                              "- #2 b\n\nLeft out:\n\n- #3 c\n\nA paragraph.\n- #4 d\n\n"
                                              "Borderline and not included, for a maintainer to decide:\n\n- #7 g\n\n"
                                              "Held by the maintainers:\n\n- #6 f\n"),
                   901: dict(batch(901, building=False), body="Included:\n\n- #5 e\n")}
        self.assertEqual(labels.included_in(batches, REPO), {1: {900}, 2: {900}})

    def test_included_gets_neither_label(self):
        found = labels.decide(dict(pr(1, mergeable="CONFLICTING"), included={900}), "main", {900: batch(900)}, {900: CONFLICT})
        self.assertEqual((found["main"], found["batch"]), (False, False))

class SwitchedOff(unittest.TestCase):
    def test_a_real_run_does_nothing_while_the_labels_are_off(self):
        was = labels._labels.CONFLICT_LABELS_ON
        labels._labels.CONFLICT_LABELS_ON = False
        try:
            with mock.patch.object(sys, "argv", ["conflict-labels.py", "--repo", REPO]), \
                    mock.patch.object(labels, "sync", side_effect=AssertionError("ran")), \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                labels.main()
        finally:
            labels._labels.CONFLICT_LABELS_ON = was
        self.assertIn("switched off", out.getvalue())

    def test_a_dry_run_runs_while_the_labels_are_off(self):
        # A maintainer looks at a dry run before switching the labels on.
        was = labels._labels.CONFLICT_LABELS_ON
        labels._labels.CONFLICT_LABELS_ON = False
        try:
            with mock.patch.object(sys, "argv", ["conflict-labels.py", "--repo", REPO, "--dry-run"]), \
                    mock.patch.object(labels, "sync", return_value=["looked"]) as sync, \
                    contextlib.redirect_stdout(io.StringIO()) as out, self.assertRaises(SystemExit) as done:
                labels.main()
        finally:
            labels._labels.CONFLICT_LABELS_ON = was
        self.assertTrue(sync.call_args.args[0].dry_run)
        self.assertEqual((done.exception.code, out.getvalue().splitlines()[0]), (None, "- looked"))


class Runs(unittest.TestCase):
    def scene(self, **options):
        gh = Fake(**options)
        gh.add(900, ref="batch/b9", own=True, labels_=[BUILDING])
        gh.add(1)
        gh.add(2, mergeable="CONFLICTING")
        gh.add(3, labels_=[MEMBER])
        return gh

    def test_a_pull_request_the_batch_lists_as_included_is_not_compared_or_labelled(self):
        # Its changes are in the batch, merged with `main` for it, though its own head is not.
        gh = Fake()
        gh.add(900, ref="batch/b9", own=True, labels_=[BUILDING],
               body="Included:\n\n- #1 a (@x): main merged into the branch for this batch\n\n"
                    "Left out for other reasons:\n\n- #2 b (@y): too big\n")
        gh.add(1, mergeable="CONFLICTING", labels_=[MAIN_CONFLICT, BATCH_CONFLICT])
        gh.add(2, mergeable="CONFLICTING")
        compare = comparing({(1, 900): CONFLICT, (2, 900): CONFLICT})
        with contextlib.redirect_stdout(io.StringIO()):
            log = labels.sync(gh, None, compare=compare)
        self.assertEqual(compare.seen, [([900], [2])])
        self.assertEqual(gh.pulls[1]["labels"], set())
        self.assertEqual(gh.told_about(1), [])
        self.assertIn("the description of #900 lists it as included", " ".join(log))
        # One the description leaves out is compared as before.
        self.assertEqual(gh.pulls[2]["labels"], {MAIN_CONFLICT, BATCH_CONFLICT, WAITING})

    def test_stacked_batches_are_compared_through_the_outermost_one(self):
        gh = self.scene()
        gh.add(901, ref="batch/b10-on-900", own=True, labels_=[BUILDING, LATEST])
        compare = comparing({(1, 900): CONFLICT, (1, 901): CONFLICT})
        with contextlib.redirect_stdout(io.StringIO()):
            log = labels.sync(gh, None, compare=compare)
        self.assertEqual(compare.seen, [([901], [1, 2])])
        self.assertIn("compared with the batches being built: #901 (`batch/b10-on-900`); not with #900 on its own: "
                      "a batch stacked on it holds its changes", log)
        # Told about the batch on top only, which it has to merge and depend on.
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT, WAITING}, ["901"]))

    def test_a_pull_request_pushed_to_during_a_sweep_is_left_to_its_own_run(self):
        gh = self.scene()
        inner = comparing({(1, 900): CONFLICT})

        def compare(*args, **options):
            gh.pulls[1]["headRefOid"] = "f" * 40  # its author pushes while the sweep compares
            return inner(*args, **options)
        with contextlib.redirect_stdout(io.StringIO()):
            log = labels.sync(gh, None, compare=compare)
        self.assertEqual(gh.pulls[1]["labels"], set())
        self.assertIn("#1: changed during this sweep, so left to the run for it", log)

    def test_a_rate_limit_refusal_stops_the_run(self):
        gh = self.scene()
        gh.add(4)
        original = gh.call

        def call(method, path, payload=None):
            if method == "POST" and path.startswith("issues/1/"):
                gh.calls += 1
                return 403, {"message": "You have exceeded a secondary rate limit."}
            return original(method, path, payload)
        gh.call = call
        with self.assertRaises(labels.Refused):
            run(gh, table={(1, 900): CONFLICT, (4, 900): CONFLICT})
        self.assertEqual(gh.pulls[4]["labels"], set())

    def test_a_refused_label_is_not_lost(self):
        # The labels go on first. Had the comment gone first, the next run would find it, and
        # `awaiting-author` would never be added.
        gh = self.scene()
        original = gh.call

        def call(method, path, payload=None):
            if method == "POST" and path == "issues/1/labels":
                gh.calls += 1
                return 403, {"message": "You have exceeded a secondary rate limit."}
            return original(method, path, payload)
        gh.call = call
        with self.assertRaises(labels.Refused):
            run(gh, table={(1, 900): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), (set(), []))
        gh.call = original
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT, WAITING}, ["900"]))
        self.assertEqual([(method, path) for method, path, _ in gh.sent if path.startswith("issues/1/")],
                         [("POST", "issues/1/labels"), ("POST", "issues/1/comments")])

    def test_a_conflict_with_the_batch_is_told_once(self):
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual(gh.pulls[1]["labels"], {BATCH_CONFLICT, WAITING})
        self.assertEqual(gh.told_about(1), ["900"])
        # The author comments `ready`, which takes `awaiting-author` off. Nothing is said again.
        gh.pulls[1]["labels"].discard(WAITING)
        gh.sent.clear()
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual((gh.sent, gh.pulls[1]["labels"]), ([], {BATCH_CONFLICT}))
        # Fixed, then broken again by a later push to the batch: told again, and handed back.
        run(gh, table={(1, 900): Comparison("clean", [b"a"])})
        self.assertEqual(gh.pulls[1]["labels"], set())
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT, WAITING}, ["900", "900"]))
        # And once only while the label stays on.
        gh.pulls[1]["labels"].discard(WAITING)
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT}, ["900", "900"]))

    def test_a_label_left_from_an_older_batch_does_not_keep_the_new_one_from_being_told(self):
        # #900 is closed and #901 is built before a sweep has taken the label off.
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[1]["labels"].discard(WAITING)  # `ready`
        gh.pulls[900]["labels"].discard(BUILDING)
        gh.pulls[900]["state"] = "CLOSED"
        gh.add(901, ref="batch/b10", own=True, labels_=[BUILDING])
        gh.comment_reads.clear()
        run(gh, table={(1, 901): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT, WAITING}, ["900", "901"]))
        self.assertEqual(gh.comment_reads, [1])

    def test_a_new_batch_is_told_about_again(self):
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[900]["state"] = "CLOSED"
        run(gh)
        self.assertEqual(gh.pulls[1]["labels"], {WAITING})
        gh.add(901, ref="batch/b10", own=True, labels_=[BUILDING])
        run(gh, table={(1, 901): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.told_about(1)), ({BATCH_CONFLICT, WAITING}, ["900", "901"]))

    def test_the_label_comes_off_when_the_batch_closes_and_awaiting_author_stays(self):
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[900]["state"] = "CLOSED"
        log = run(gh)
        self.assertEqual(gh.pulls[1]["labels"], {WAITING})
        self.assertIn("#1: take `batch-conflict` off, because no batch is being built", log)
        self.assertNotIn(("DELETE", f"issues/1/labels/{WAITING}", None), gh.sent)

    def test_the_label_comes_off_when_the_batch_stops_being_built(self):
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[900]["labels"].discard(BUILDING)
        run(gh)
        self.assertEqual(gh.pulls[1]["labels"], {WAITING})

    def test_the_label_comes_off_when_the_pull_request_joins_the_batch(self):
        gh = self.scene()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[1]["labels"] |= {MEMBER}
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual(gh.pulls[1]["labels"], {MEMBER, WAITING})

    def test_whoever_added_it_it_comes_off(self):
        gh = self.scene()
        gh.pulls[1]["labels"] |= {MAIN_CONFLICT, BATCH_CONFLICT}
        run(gh)
        self.assertEqual(gh.pulls[1]["labels"], set())

    def test_members_and_batches_are_not_compared(self):
        gh = self.scene()
        compare = comparing({})
        with contextlib.redirect_stdout(io.StringIO()):
            labels.sync(gh, compare=compare)
        self.assertEqual(compare.seen, [([900], [1, 2])])

    def test_nothing_is_fetched_without_a_batch_being_built(self):
        gh = self.scene()
        gh.pulls[900]["labels"].clear()
        compare = comparing({})
        with contextlib.redirect_stdout(io.StringIO()):
            labels.sync(gh, compare=compare)
        self.assertEqual(compare.seen, [])

    def test_main_conflict_is_labelled_without_a_comment(self):
        gh = self.scene()
        run(gh)
        self.assertEqual(gh.pulls[2]["labels"], {MAIN_CONFLICT})
        self.assertNotIn(2, gh.comments)
        gh.pulls[2]["mergeable"] = "MERGEABLE"
        run(gh)
        self.assertEqual(gh.pulls[2]["labels"], set())

    def test_main_conflict_is_ignored_and_removed_when_depending_on_the_batch(self):
        gh = self.scene()
        run(gh)
        self.assertIn(MAIN_CONFLICT, gh.pulls[2]["labels"])
        gh.pulls[2]["body"] = "Uses the batch.\n\n- [ ] depends on: #900\n"
        log = run(gh)
        self.assertEqual(gh.pulls[2]["labels"], set())
        self.assertIn("#2: take `main-conflict` off, because it depends on the batch #900", log)

    def test_depending_on_a_batch_that_was_closed_does_not_count(self):
        gh = self.scene()
        gh.pulls[2]["body"] = "- [ ] depends on: #900\n"
        gh.pulls[900]["state"] = "CLOSED"
        run(gh)
        self.assertEqual(gh.pulls[2]["labels"], {MAIN_CONFLICT})

    def test_unknown_mergeability_is_asked_again_and_then_left(self):
        gh = self.scene()
        gh.pulls[1]["labels"].add(MAIN_CONFLICT)
        gh.pulls[1]["mergeable"] = gh.pulls[2]["mergeable"] = "UNKNOWN"
        gh.later = {1: ["UNKNOWN", "UNKNOWN", "UNKNOWN"], 2: ["UNKNOWN", "CONFLICTING"]}
        with patch.object(labels, "WAIT", 0):
            run(gh)
        self.assertEqual((gh.pulls[1]["labels"], gh.pulls[2]["labels"]), ({MAIN_CONFLICT}, {MAIN_CONFLICT}))

    def test_closed_pull_requests_lose_the_labels(self):
        gh = self.scene()
        gh.add(4, labels_=[MAIN_CONFLICT, BATCH_CONFLICT, WAITING])
        gh.pulls[4]["state"] = "CLOSED"
        run(gh)
        self.assertEqual(gh.pulls[4]["labels"], {WAITING})

    def test_drafts_lose_the_labels(self):
        gh = self.scene()
        gh.add(4, labels_=[MAIN_CONFLICT, BATCH_CONFLICT], mergeable="CONFLICTING", draft=True)
        run(gh, table={(4, 900): CONFLICT})
        self.assertEqual(gh.pulls[4]["labels"], set())

    def test_one_pull_request(self):
        gh = self.scene()
        gh.pulls[2]["labels"].add(BATCH_CONFLICT)
        run(gh, 1, table={(1, 900): CONFLICT})
        self.assertEqual((gh.pulls[1]["labels"], gh.pulls[2]["labels"]), ({BATCH_CONFLICT, WAITING}, {BATCH_CONFLICT}))

    def test_one_pull_request_finds_the_batch_it_depends_on(self):
        gh = self.scene()
        gh.add(901, ref="batch/waiting", own=True)
        gh.pulls[2]["body"] = "- [ ] depends on: #901\n"
        gh.pulls[2]["labels"].add(MAIN_CONFLICT)
        run(gh, 2)
        self.assertEqual(gh.pulls[2]["labels"], set())

    def test_one_batch_pull_request_loses_the_labels(self):
        gh = self.scene()
        gh.pulls[900]["labels"].add(MAIN_CONFLICT)
        run(gh, 900)
        self.assertEqual(gh.pulls[900]["labels"], {BUILDING})

    def test_a_dry_run_writes_nothing(self):
        gh = self.scene(dry_run=True)
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            log = labels.sync(gh, compare=comparing({(1, 900): CONFLICT}))
        self.assertEqual(gh.sent, [])
        self.assertEqual(gh.pulls[1]["labels"], set())
        self.assertIn("would POST issues/1/comments", printed.getvalue())
        self.assertIn("1 of 4 open pull requests would carry `batch-conflict`: #1", log)

    def test_writes_stop_when_the_hour_is_nearly_used_up(self):
        gh = self.scene()
        gh.left = labels.RESERVE - 1
        log = run(gh, table={(1, 900): CONFLICT})
        self.assertEqual(gh.sent, [])
        self.assertTrue(any("REST requests left this hour" in line for line in log))

    def test_a_missing_label_stops_a_real_run(self):
        gh = self.scene(missing=[BATCH_CONFLICT])
        with self.assertRaises(labels.Refused):
            run(gh, table={(1, 900): CONFLICT})
        self.assertNotIn(1, gh.comments)

    def test_a_failed_comparison_leaves_batch_conflict_and_still_keeps_main_conflict(self):
        gh = self.scene()
        gh.pulls[1]["labels"].add(BATCH_CONFLICT)

        def broken(*args, **options):
            raise RuntimeError("git failed")
        with contextlib.redirect_stdout(io.StringIO()):
            labels.sync(gh, compare=broken)
        self.assertTrue(gh.failed)
        self.assertEqual((gh.pulls[1]["labels"], gh.pulls[2]["labels"]), ({BATCH_CONFLICT}, {MAIN_CONFLICT}))

    def test_a_comment_by_someone_else_with_the_marker_does_not_count(self):
        gh = self.scene()
        gh.pulls[1]["labels"].add(BATCH_CONFLICT)  # so that its comments are read
        gh.comments[1] = [("<!-- conflict-labels-batch 900 -->\nfake", {"__typename": "User", "login": "someone"})]
        run(gh, table={(1, 900): CONFLICT})
        self.assertEqual(gh.told_about(1), ["900", "900"])

    # Two separate stacks: every sweep compares with both.

    def stacks(self):
        gh = self.scene()
        gh.pulls[900]["labels"].add(LATEST)
        gh.add(910, ref="batch/c1", own=True, labels_=[BUILDING, LATEST])
        return gh

    def test_with_two_stacks_each_sweep_reads_once_and_tells_no_one_twice(self):
        gh = self.stacks()
        table = {(1, 900): CONFLICT, (1, 910): CONFLICT}
        run(gh, table=table)
        run(gh, table=table)
        # The first run tells it without reading, and the second reads once.
        self.assertEqual((gh.comment_reads, gh.told_about(1)), ([1], ["900", "910"]))

    def test_with_two_stacks_a_new_conflict_is_still_told(self):
        gh = self.stacks()
        run(gh, table={(1, 900): CONFLICT})
        gh.pulls[1]["labels"].discard(WAITING)  # `ready`
        # The other stack's batch moves on, and now conflicts too.
        run(gh, table={(1, 900): CONFLICT, (1, 910): CONFLICT})
        self.assertEqual(gh.told_about(1), ["900", "910"])
        self.assertEqual(gh.pulls[1]["labels"], {BATCH_CONFLICT, WAITING})

    # A pull request that builds on a batch rebuilt without one of its pull requests.

    def dependent(self):
        gh = self.scene()
        gh.add(5, body="Builds on the batch.\n\n- [ ] depends on: #900\n", mergeable="CONFLICTING")
        gh.add(11)  # taken out of the batch, and still carried by #5
        return gh

    def test_a_dependent_carrying_what_the_batch_dropped_is_told_once(self):
        gh, known = self.dependent(), {}
        stale = {5: {"on": [900], "prs": [11]}}
        compare = comparing({}, stale)
        with contextlib.redirect_stdout(io.StringIO()):
            log = labels.sync(gh, None, compare=compare, known=known)
        self.assertEqual(compare.watch[5], {"on": [900], "exclude": [900]})
        self.assertEqual(compare.watch[1], {"on": [], "exclude": [900]})
        self.assertIn("#5: add `awaiting-author`, because it is told about a batch; tell it that its branch carries "
                      "commits #900 no longer has", log)
        [said] = [body for body, _ in gh.comments[5]]
        self.assertTrue(said.startswith("<!-- conflict-labels-stale 900 11 -->\n"))
        self.assertEqual(gh.pulls[5]["labels"], {WAITING})  # and no `main-conflict`: it depends on the batch
        # Told once, whether or not the next run knows it already.
        gh.pulls[5]["labels"].discard(WAITING)
        run(gh, stale=stale, known=known)
        run(gh, stale=stale)
        self.assertEqual((len(gh.comments[5]), gh.pulls[5]["labels"]), (1, set()))
        # The batch is rebuilt again, and #5 still carries #11: nothing new, and the label it had
        # taken off stays off.
        gh.pulls[900]["headRefOid"] = "e" * 40
        run(gh, stale=stale, known=known)
        run(gh, stale=stale)
        self.assertEqual((len(gh.comments[5]), gh.pulls[5]["labels"]), (1, set()))
        # It also carries #12 now: that is told.
        gh.add(12)
        stale[5]["prs"] = [11, 12]
        run(gh, stale=stale, known=known)
        self.assertEqual(len(gh.comments[5]), 2)
        self.assertTrue(gh.comments[5][1][0].startswith("<!-- conflict-labels-stale 900 11,12 -->\n"))
        self.assertEqual(gh.pulls[5]["labels"], {WAITING})

    def test_one_pull_request_alone_is_not_looked_at_for_this(self):
        gh = self.dependent()
        compare = comparing({}, {5: {"on": [900], "prs": [11]}})
        with contextlib.redirect_stdout(io.StringIO()):
            labels.sync(gh, 5, compare=compare)
        self.assertEqual((compare.watch, gh.comments.get(5)), ({}, None))

    def test_a_conflict_and_a_stale_branch_read_the_comments_once(self):
        gh = self.dependent()
        run(gh, table={(5, 900): CONFLICT}, stale={5: {"on": [900], "prs": [11]}})
        self.assertEqual(gh.comment_reads, [5])
        self.assertEqual(sorted(body.split(" ")[1] for body, _ in gh.comments[5]),
                         ["conflict-labels-batch", "conflict-labels-stale"])


# ---------------------------------------------------------------------------------------------
# The comparison itself, fetched from a local repository standing in for GitHub.

IDENTITY = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
            "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid"}
LINES = "".join(f"line {number}\n" for number in range(1, 21))


class Origin:
    """A repository with a main branch, and pull request heads under refs/pull/<n>/head."""

    def __init__(self, root):
        self.root = Path(root)
        self.git("init", "--quiet", "--initial-branch=main")
        self.git("config", "uploadpack.allowFilter", "true")
        self.git("config", "uploadpack.allowAnySHA1InWant", "true")
        for name in ("a.txt", "b.txt", "c.txt"):
            (self.root / name).write_text("".join(f"{name} {line}\n" for line in LINES.splitlines()))
        (self.root / "src").mkdir()
        (self.root / "src" / "Gone.lean").write_text("theorem gone : True := trivial\n")
        (self.root / "src" / "Kept.lean").write_text("theorem kept : True := trivial\n")
        self.main = self.commit("base")

    def git(self, *args):
        done = subprocess.run(["git", "-C", str(self.root), "-c", "commit.gpgsign=false", *args],
                              check=True, capture_output=True, env={**os.environ, **IDENTITY})
        return done.stdout.decode().strip()

    def commit(self, message):
        self.git("add", "--all")
        self.git("commit", "--quiet", "--allow-empty", "--message", message)
        return self.git("rev-parse", "HEAD")

    def edit(self, name, line, text):
        lines = (self.root / name).read_text().splitlines(keepends=True)
        lines[line - 1] = text + "\n"
        (self.root / name).write_text("".join(lines))

    def pull(self, number, start, change, *, merge=None):
        """A pull request's head: `change` on top of `start`, then `merge` merged in if given."""
        self.git("checkout", "--quiet", "--detach", start)
        change()
        head = self.commit(f"pr {number}")
        if merge:
            self.git("merge", "--quiet", "--no-edit", merge)
            head = self.git("rev-parse", "HEAD")
        self.git("update-ref", f"refs/pull/{number}/head", head)
        self.git("checkout", "--quiet", "main")
        return head


class CompareAll(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory()
        o = cls.origin = Origin(cls.directory.name)
        # In the batch, though not labelled so yet. It starts to import what the batch deletes,
        # but that is the batch's own problem.
        member = o.pull(7, o.main, lambda: (o.edit("a.txt", 10, "seven"),
                                            (o.root / "src" / "Uses.lean").write_text("import Gone\n")))
        # The batch edits line 2 of a.txt and deletes src/Gone.lean.
        cls.early = o.pull(900, o.main, lambda: o.edit("c.txt", 9, "batch early"))
        o.pull(900, cls.early, lambda: (o.edit("a.txt", 2, "batch"), (o.root / "src" / "Gone.lean").unlink()),
               merge=member)
        o.pull(1, o.main, lambda: o.edit("a.txt", 2, "one"))                 # conflicts
        o.pull(2, o.main, lambda: o.edit("b.txt", 2, "two"))                 # apart
        o.pull(3, o.main, lambda: o.edit("a.txt", 18, "three"))              # same file, merges
        # Starts to import the file the batch deletes: git merges it, the build would fail.
        o.pull(4, o.main, lambda: (o.root / "src" / "New.lean").write_text("import Gone\n"))
        # Merged the batch's head and resolved: nothing left to merge.
        o.pull(5, o.main, lambda: o.edit("b.txt", 5, "five"), merge="refs/pull/900/head")
        # Merged an earlier head of the batch, then changed what the batch changed after.
        o.pull(6, o.main, lambda: o.edit("a.txt", 2, "six"), merge=cls.early)
        # Main moves on after everything forked, changing c.txt line 2.
        o.edit("c.txt", 2, "main later")
        o.commit("main later")

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_each_kind_of_pull_request(self):
        building = {900: batch(900)}
        candidates = {number: pr(number) for number in range(1, 8)}
        log = []
        results = labels.compare_all(REPO, "main", building, candidates, log,
                                     origin=f"file://{self.origin.root}")
        found = {number: (results[number][900].kind, results[number][900].conflicts, results[number][900].stale)
                 for number in candidates}
        self.assertEqual(found[1], ("conflict", [b"a.txt"], []))
        self.assertEqual(found[2], ("apart", [], []))
        self.assertEqual(found[3], ("clean", [], []))
        self.assertEqual(found[4], ("apart", [], [("theirs", b"src/Gone.lean", b"src/New.lean")]))
        self.assertEqual(found[5][0], "clean")
        self.assertEqual(found[6], ("conflict", [b"a.txt"], []))
        self.assertEqual(found[7], ("clean", [], []))
        for number in candidates:
            decided = labels.decide(pr(number), "main", building, results[number])["batch"]
            self.assertEqual(decided, number in (1, 4, 6), number)
        self.assertTrue(any(line.startswith("fetched 8 heads") for line in log), log)


class Rebuilt(unittest.TestCase):
    """`stale_in`, on a batch rebuilt without one of its pull requests."""

    def test_a_dependent_still_carrying_a_pull_request_taken_out_is_found(self):
        with tempfile.TemporaryDirectory() as root:
            o = Origin(root)
            ten = o.pull(10, o.main, lambda: o.edit("a.txt", 3, "ten"))
            eleven = o.pull(11, o.main, lambda: o.edit("b.txt", 3, "eleven"))

            def assemble(*heads):
                # Each pull request's head merged in as batches are, with the message that names it.
                o.git("checkout", "--quiet", "--detach", o.main)
                for number, head in heads:
                    o.git("merge", "--quiet", "--no-ff", "-m", f"Merge PR #{number} into batch", head)
                head = o.git("rev-parse", "HEAD")
                o.git("checkout", "--quiet", "main")
                return head
            old = assemble((10, ten), (11, eleven))
            # Started from the batch's branch, and merged it in: both carry #11.
            o.pull(12, old, lambda: o.edit("c.txt", 3, "twelve"))
            o.pull(14, o.main, lambda: o.edit("c.txt", 7, "fourteen"), merge=old)
            # The batch is rebuilt without #11, by force-push.
            new = assemble((10, ten))
            o.git("update-ref", "refs/pull/900/head", new)
            # Merged the batch as it is now, and is stacked on #16, another open pull request, without
            # saying so: it carries #16's commits, but no batch ever held #16.
            side = o.pull(16, o.main, lambda: o.edit("c.txt", 12, "sixteen, first"))
            o.pull(13, new, lambda: o.edit("c.txt", 5, "thirteen"), merge=side)
            # Merged #11 itself, and says it depends on it.
            o.pull(15, o.main, lambda: o.edit("c.txt", 9, "fifteen"), merge=eleven)
            candidates = {number: pr(number) for number in (11, 12, 13, 14, 15, 16)}
            watch = {number: {"on": [900] if number in (12, 13) else [], "exclude": [900]} for number in candidates}
            watch[15]["exclude"] = [11, 900]
            carried, log = {}, []
            labels.compare_all(REPO, "main", {900: batch(900)}, candidates, log, origin=f"file://{root}",
                               watch=watch, carried=carried)
            # #11 is pushed to after it was taken out: what #12 and #14 carry is still its own.
            o.pull(11, eleven, lambda: o.edit("b.txt", 4, "eleven, again"))
            again = {}
            labels.compare_all(REPO, "main", {900: batch(900)}, candidates, [], origin=f"file://{root}",
                               watch=watch, carried=again)
        # #14 says nothing, but shares commits with the batch's branch. #13 carries its own work
        # and #16's, which no batch held, and #15 a pull request it depends on.
        self.assertEqual(carried, {12: {"on": [900], "prs": [11]}, 14: {"on": [900], "prs": [11]}})
        self.assertIn("#12 carries commits of #11 that #900 no longer has", log)
        self.assertEqual(again, carried)

    def test_a_dependent_with_several_merge_bases_is_found(self):
        # Main moves on after #10 and #11 branch off, and the batch is built on it. A pull request
        # that merges the batch, rebuilt since without #11, has two best common ancestors with it:
        # main's commit and #10's head. `git merge-base` alone prints main's, so the two would not
        # be taken to share commits beyond main.
        with tempfile.TemporaryDirectory() as root:
            o = Origin(root)
            ten = o.pull(10, o.main, lambda: o.edit("a.txt", 3, "ten"))
            eleven = o.pull(11, o.main, lambda: o.edit("b.txt", 3, "eleven"))
            o.edit("c.txt", 20, "main later")
            later = o.commit("main later")

            def assemble(*heads):
                o.git("checkout", "--quiet", "--detach", later)
                for number, head in heads:
                    o.git("merge", "--quiet", "--no-ff", "-m", f"Merge PR #{number} into batch", head)
                head = o.git("rev-parse", "HEAD")
                o.git("checkout", "--quiet", "main")
                return head
            old = assemble((11, eleven), (10, ten))
            dependent = o.pull(14, later, lambda: o.edit("c.txt", 7, "fourteen"), merge=old)
            new = assemble((10, ten))
            o.git("update-ref", "refs/pull/900/head", new)
            self.assertEqual(set(o.git("merge-base", "--all", dependent, new).split()), {later, ten})
            candidates = {number: pr(number) for number in (10, 11, 14)}
            watch = {number: {"on": [], "exclude": [900]} for number in candidates}
            carried, log = {}, []
            labels.compare_all(REPO, "main", {900: batch(900)}, candidates, log, origin=f"file://{root}",
                               watch=watch, carried=carried)
        self.assertEqual(carried, {14: {"on": [900], "prs": [11]}})


# ---------------------------------------------------------------------------------------------


class Inbox(unittest.TestCase):
    def test_batch_conflict_keeps_a_pull_request_out_of_the_inbox_and_main_conflict_does_not(self):
        self.assertIn(BATCH_CONFLICT, inbox.DECIDED)
        self.assertNotIn(MAIN_CONFLICT, inbox.DECIDED)
        base = {"draft": False, "ref": "topic", "batch": False}
        self.assertEqual(inbox.unavailable({**base, "labels": {BATCH_CONFLICT}}), f"it is labelled `{BATCH_CONFLICT}`")
        self.assertIsNone(inbox.unavailable({**base, "labels": {MAIN_CONFLICT}}))

    def test_the_names(self):
        self.assertEqual((MAIN_CONFLICT, BATCH_CONFLICT), ("main-conflict", "batch-conflict"))


if __name__ == "__main__":
    unittest.main()
