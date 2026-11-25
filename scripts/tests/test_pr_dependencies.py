#!/usr/bin/env python3
"""Checks of the parser for the `depends on` lines of a description; no network calls."""
import importlib.util
from pathlib import Path
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


deps = load("pr_dependencies", "pr-dependencies.py")

REPO = "o/r"


class Dependencies(unittest.TestCase):
    def read(self, body):
        return deps.dependencies(body, REPO)

    def test_the_line_agents_md_asks_for(self):
        self.assertEqual(self.read("Some text.\n\n---\n\n- [ ] depends on: #123\n"), {123})

    def test_every_wording_and_task_box(self):
        for line in ("- [ ] depends on: #7", "- [x] depends on: #7", "- [X] Depends on #7", "depends on #7",
                     "Depend on: #7", "* [ ] depends upon #7", "  - depends on: #7", "DEPENDS ON #7",
                     "depend upon #7", "+ depends on #7"):
            with self.subTest(line=line):
                self.assertEqual(self.read(line), {7})

    def test_other_common_wordings(self):
        for line in ("blocked by #7", "- [ ] Blocked by: #7", "requires #7", "Requires: #7", "needs #7",
                     "- [x] needs: #7", "> depends on #7", "> - [ ] blocked by #7", "-depends on #7",
                     "[ ] depends on #7", "[] depends on #7", "**Depends on** #7", "depends\ton\t#7",
                     "- [ ]depends on #7"):
            with self.subTest(line=line):
                self.assertEqual(self.read(line), {7})

    def test_several_on_one_line_and_several_lines(self):
        self.assertEqual(self.read("- [ ] depends on: #1, #2\n- [x] depends on: #3\n"), {1, 2, 3})

    def test_addresses_and_references_to_this_repository_only(self):
        body = ("depends on https://github.com/o/r/pull/11\n"
                "depends on https://github.com/other/r/pull/12\n"
                "depends on o/r#13 and other/r#14\n"
                "depends on http://github.com/O/R/pull/15/files\n")
        self.assertEqual(self.read(body), {11, 13, 15})

    def test_only_at_the_start_of_a_line(self):
        self.assertEqual(self.read("This depends on #5.\n- see #6, which depends on #7\n"), set())

    def test_other_words_are_not_dependencies(self):
        self.assertEqual(self.read("dependson #1\ndepends #2\ndepends-on #3\n- [ ] closes #4\n"
                                   "needed by #5\nrequired #6\nblocked #7\n"), set())

    def test_a_sentence_after_a_number_is_not_read(self):
        self.assertEqual(self.read("depends on #12. See also #99 for context.\n"), {12})
        self.assertEqual(self.read("depends on #12; #13 is related\n"), {12})
        self.assertEqual(self.read("depends on #1, #2.\n"), {1, 2})

    def test_comments_and_code_blocks_are_not_read(self):
        body = ("<!-- - [ ] depends on: #1 -->\n<!--\ndepends on #2\n-->\n"
                "```\n- [ ] depends on: #3\n```\n~~~md\ndepends on #4\n~~~\ndepends on #5\n")
        self.assertEqual(self.read(body), {5})

    def test_a_fence_closes_only_with_its_own_kind(self):
        body = "````\n```\ndepends on #1\n```\ndepends on #2\n````\n~~~\n```\ndepends on #3\n~~~\ndepends on #4\n"
        self.assertEqual(self.read(body), {4})

    def test_an_unclosed_fence_or_comment_runs_to_the_end(self):
        self.assertEqual(self.read("depends on #1\n```\ndepends on #2\n"), {1})
        self.assertEqual(self.read("depends on #1\n<!-- draft\ndepends on #2\n"), {1})

    def test_code_spans_are_not_read(self):
        self.assertEqual(self.read("depends on `#5`\n"), set())
        self.assertEqual(self.read("`depends on #5`\n"), set())
        self.assertEqual(self.read("depends on ``#5`` and #6\n"), {6})
        self.assertEqual(self.read("depends on ```#5``` and #6\n"), {6})
        # A lone backtick opens nothing.
        self.assertEqual(self.read("depends on #5 ` and #6\n"), {5, 6})

    def test_a_comment_before_the_line_is_not_in_the_way(self):
        self.assertEqual(self.read("<!-- note --> - [ ] depends on #5\n<!-- a\nlonger note --> needs #6\n"), {5, 6})

    def test_windows_line_ends(self):
        self.assertEqual(self.read("text\r\n- [ ] depends on: #9\r\n```\r\ndepends on #10\r\n```\r\n"), {9})

    def test_a_number_must_stand_alone(self):
        self.assertEqual(self.read("depends on #14 and #12abc and &#13;\n"), {14})


class Declarations(unittest.TestCase):
    def test_what_each_line_says(self):
        body = "Text.\n- [ ] depends on: #3, #1, #3\n- [x] needs #2\n* blocked by #4\nrequires Lean\n[] needs #5\n"
        found = deps.declarations(body, REPO)
        self.assertEqual([(line.index, line.box, line.numbers) for line in found],
                         [(1, " ", (3, 1)), (2, "x", (2,)), (3, None, (4,)), (4, None, ()), (5, "", (5,))])
        first = found[0]
        self.assertEqual(body[first.start:first.end], "- [ ] depends on: #3, #1, #3")
        self.assertEqual(body[first.box_at], " ")
        self.assertEqual(body[first.box_at - 1:first.box_at + 2], "[ ]")
        self.assertEqual([(line.tickable, line.ticked) for line in found[:3]], [(True, False), (False, True), (False, False)])
        self.assertIsNone(found[2].box_at)

    def test_lines_end_before_a_carriage_return(self):
        body = "a\r\n- [ ] depends on #1\r\nb"
        line, = deps.declarations(body, REPO)
        self.assertEqual((line.index, body[line.start:line.end]), (1, "- [ ] depends on #1"))

    def test_the_box_after_a_comment_is_found_where_it_is(self):
        body = "<!-- x --> - [ ] depends on #5\n"
        line, = deps.declarations(body, REPO)
        self.assertEqual(body[line.box_at - 1:line.box_at + 2], "[ ]")


class Annotations(unittest.TestCase):
    def test_an_annotation_is_read_and_names_no_pull_request(self):
        body = "- [x] depends on: (batched) #1, #2\n- [x] Depends on (main) #3\n- [ ] needs: (main)\n- [ ] needs #4 (main)\n"
        found = deps.declarations(body, REPO)
        self.assertEqual([(line.note, line.numbers) for line in found],
                         [("batched", (1, 2)), ("main", (3,)), ("main", ()), (None, (4,))])
        self.assertEqual([body[line.note_at:line.note_end] for line in found], ["(batched) ", "(main) ", "(main)", ""])
        self.assertEqual(body[found[3].note_at:found[3].note_at + 2], "#4")

    def test_in_code_it_is_not_an_annotation(self):
        line, = deps.declarations("- [x] depends on: `(main)` #1\n", REPO)
        self.assertEqual((line.note, line.numbers), (None, (1,)))


class Mark(unittest.TestCase):
    def test_ticking_and_annotating_change_nothing_else(self):
        body = ("Intro with é and 🤖 and trailing spaces   \r\n\r\n---\r\n\r\n- [ ] depends on: #12\r\n"
                "- [ ] depends on #13\r\n<!-- - [ ] depends on: #12 -->\r\n```\r\n- [ ] depends on: #12\r\n```\r\nend")
        first, second = deps.declarations(body, REPO)
        new = deps.mark(body, [(first, "x", "batched"), (second, "x", None)])
        self.assertEqual(new, body.replace("- [ ] depends on: #12\r\n- [ ] depends on #13",
                                           "- [x] depends on: (batched) #12\r\n- [x] depends on #13"))
        self.assertEqual(new.encode().count(b"\r\n"), body.encode().count(b"\r\n"))

    def test_an_annotation_is_replaced_or_taken_off_exactly(self):
        body = "- [x] depends on: (batched) #1\n- [X] depends on: (batched) #2\n"
        first, second = deps.declarations(body, REPO)
        self.assertEqual(deps.mark(body, [(first, "x", "main")]),
                         "- [x] depends on: (main) #1\n- [X] depends on: (batched) #2\n")
        self.assertEqual(deps.mark(body, [(first, " ", None), (second, " ", None)]),
                         "- [ ] depends on: #1\n- [ ] depends on: #2\n")

    def test_nothing_to_change_is_nothing_changed(self):
        body = "- [ ] depends on: #1\n"
        self.assertEqual(deps.mark(body, []), body)


if __name__ == "__main__":
    unittest.main()
