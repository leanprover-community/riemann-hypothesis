"""Read the lines of a pull request's description that say which pull requests it depends on.

`conflict-labels.py` and `dependency-ticks.py` load this file. A line declares dependencies when
it starts with `depends on`, `depend on`, `depends upon`, `depend upon`, `blocked by`, `requires`
or `needs`, in any letter case, optionally after any of `-`, `*`, `+` and `>` and a task box such
as `[ ]` or `[x]`, with or without a `:` after the words. It declares every pull request of the
repository that the rest of the line names: `#123`, `owner/name#123` or the pull request's
address. A full stop or semicolon straight after a number ends the line, so that a sentence after
it is not read. For example:

    - [ ] depends on: #123, #124
    > blocked by https://github.com/owner/name/pull/125

These are the lines that `prdag`, the tool a maintainer uses to keep chains of dependent pull
requests up to date, reads as dependencies, so that both agree on what a description declares.
Text that GitHub does not show as text is not read: HTML comments, fenced code blocks, and code
spans such as `#123` in backticks. Pull requests of other repositories are left out.
"""
from __future__ import annotations

from dataclasses import dataclass
import re

# The start of a declaring line, after code and comments have been blanked out (see `_visible`).
# Group 1 is the character in the task box, if there is a box: ` `, `x`, `X` or nothing.
DECLARES = re.compile(r"[ \t>*+-]*(?:\[([ xX]?)\][ \t]*)?"
                      r"(?:depends?[ \t]+(?:up)?on|blocked[ \t]+by|requires|needs)\b[ \t]*:?", re.IGNORECASE)
# A full stop or semicolon straight after a number, followed by a space or the end of the line.
SENTENCE = re.compile(r"(?<=\d)[.;](?:\s|$)")
# A pull request named on such a line: `owner/name#123`, `#123` or the pull request's address.
# `&#123;` is a character reference, which GitHub shows as a character, not a link.
REFERENCE = re.compile(r"(?<![\w/&.-])([\w.-]+/[\w.-]+)#(\d+)\b"
                       r"|(?<![\w/&])#(\d+)\b"
                       r"|https?://github\.com/([\w.-]+/[\w.-]+)/pull/(\d+)", re.IGNORECASE)
# The opening line of a fenced code block, and the backtick runs that open and close code spans.
FENCE = re.compile(r"[ \t]*(`{3,}|~{3,})(.*)")
TICKS = re.compile(r"`+")


@dataclass(frozen=True)
class Declaration:
    """One line of a description that declares dependencies.

    `index` counts lines from 0, and `start` and `end` are where the line's text starts and ends
    in the description, without its line ending. `box` is the character in the line's task box
    (` `, `x`, `X`, or `""` for `[]`), or None when the line has no box, and `box_at` where that
    character is, or would be for `[]`. `numbers` are the pull requests of the repository that
    the line names, in order and once each.
    """

    index: int
    start: int
    end: int
    box: str | None
    box_at: int | None
    numbers: tuple[int, ...]

    @property
    def ticked(self):
        return self.box in ("x", "X")

    @property
    def tickable(self):
        """Whether the line has an empty task box, `[ ]`, that ticking turns into `[x]`."""
        return self.box == " "


def _lines(text):
    """Each line of `text` as (start, end), without its line ending, which is `\\n` or `\\r\\n`."""
    start = 0
    while True:
        end = text.find("\n", start)
        stop = len(text) if end < 0 else end
        yield start, (stop - 1 if stop > start and text[stop - 1] == "\r" else stop)
        if end < 0:
            return
        start = end + 1


def _visible(body):
    """`body` with everything GitHub does not show as plain text blanked out: HTML comments, fenced
    code blocks and code spans. Each blanked character becomes a space, apart from line endings,
    so every position in the result is the same as in `body`.

    A comment or code block that is never closed runs to the end, as on GitHub. Code spans are read
    within one line.
    """
    out = list(body)

    def blank(start, end):
        for at in range(start, end):
            if out[at] not in "\r\n":
                out[at] = " "

    fence, comment = None, False
    for start, end in _lines(body):
        line = body[start:end]
        if fence:
            blank(start, end)
            close = re.fullmatch(r"[ \t]*(%s{%d,})[ \t]*" % (re.escape(fence[0]), len(fence)), line)
            if close:
                fence = None
            continue
        at = 0
        if comment:
            stop = line.find("-->")
            if stop < 0:
                blank(start, end)
                continue
            blank(start, start + stop + 3)
            at, comment = stop + 3, False
        else:
            opening = FENCE.fullmatch(line)
            # A backtick fence's info string cannot hold a backtick: such a line is a code span.
            if opening and not (opening.group(1)[0] == "`" and "`" in opening.group(2)):
                fence = opening.group(1)
                blank(start, end)
                continue
        while at < len(line):
            tick, open_ = line.find("`", at), line.find("<!--", at)
            if open_ >= 0 and (tick < 0 or open_ < tick):
                stop = line.find("-->", open_ + 4)
                if stop < 0:
                    blank(start + open_, end)
                    comment = True
                    break
                blank(start + open_, start + stop + 3)
                at = stop + 3
            elif tick >= 0:
                run = TICKS.match(line, tick).group()
                close = next((found for found in TICKS.finditer(line, tick + len(run)) if found.group() == run), None)
                if close:
                    blank(start + tick, start + close.end())
                    at = close.end()
                else:
                    at = tick + len(run)
            else:
                break
    return "".join(out)


def declarations(body, repo):
    """The lines of `body` that declare dependencies, as a list of Declaration.

    `repo` is `owner/name`: pull requests of any other repository are left out of `numbers`. A
    line that names none is still a Declaration, with no numbers.
    """
    shown = _visible(body)
    found = []
    for index, (start, end) in enumerate(_lines(shown)):
        match = DECLARES.match(shown, start, end)
        if not match:
            continue
        rest = shown[match.end():end]
        stop = SENTENCE.search(rest)
        if stop:
            rest = rest[:stop.start()]
        numbers = []
        for named, number, bare, url_repo, url_number in REFERENCE.findall(rest):
            where = named or url_repo
            if not where or where.lower() == repo.lower():
                value = int(number or bare or url_number)
                if value not in numbers:
                    numbers.append(value)
        box = match.group(1)
        found.append(Declaration(index, start, end, box, match.start(1) if box is not None else None,
                                 tuple(numbers)))
    return found


def dependencies(body, repo):
    """The pull requests that a description says this one depends on, as a set of numbers.
    Ticked lines count as much as unticked ones."""
    return {number for line in declarations(body, repo) for number in line.numbers}


def tick(body, repo, landed):
    """Tick each `[ ]` line all of whose pull requests are in `landed`, a set of numbers.

    Returns the new description and the Declarations that were ticked. Only the space in each such
    box changes, to `x`; every other character stays as it was, line endings included. A line that
    names no pull request, has no box or is ticked already is left alone, and nothing is unticked.
    """
    out, ticked = list(body), []
    for line in declarations(body, repo):
        if line.tickable and line.numbers and all(number in landed for number in line.numbers):
            out[line.box_at] = "x"
            ticked.append(line)
    return "".join(out), ticked
