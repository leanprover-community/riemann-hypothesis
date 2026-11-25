#!/usr/bin/env python3
"""Keep the batch status issue up to date: which batches are being built, what each contains and
leaves out, and which pull requests are in the batch queue.

The batch status workflow (`.github/workflows/batch-status.yml`) runs this from its trusted
checkout, every fifteen minutes and after each run of the batch queue and conflict labels
workflows. Nothing from a pull request is checked out or run. Everything is read from GitHub's API,
and the only thing written is the issue.

The issue is the one in this repository that the workflow opened and whose description starts
with `<!-- batch-status -->`. This script opens it, titled "Batch status", when there is none. A
maintainer pins it by hand. Its description is rewritten only when what it says changes, so the
time in its footer is when that last happened. A closed status issue is still kept up to date. It
is not reopened, and no second one is opened.

What it says:

- The batches being built: open pull requests that hold a batch (see `holds_batch` in
  `batch-labels.py`) and are labelled `building`. Both are needed: `building` is also left on
  pull requests from before the members of a batch were labelled `batch-building`. The batch
  labelled `latest batch` comes first, then the others by pull request number, newest first. That
  order is approximate: it is the order of a stack of batches only when the newest batch is the
  outermost one. What a batch contains is read from the note in the batch queue sync's record
  comment on the batch's pull request (see `read_record` in `batch-queue-sync.py`), not from its
  description. A batch that contains another batch being built lists only the pull requests it
  adds, and says which batch it contains.
- The batch queue: open pull requests labelled `batch queue` that no batch being built contains,
  in three groups. A pull request goes in the first that applies: "Pushed to since approval" when
  it is labelled `changed after frozen`, "Conflicts" when it is labelled `batch-conflict` or
  `main-conflict`, and "Ready" otherwise. `priority` and `awaiting-author` show as badges and do
  not change the group. Within a group, `priority` pull requests come first, then the rest by
  number.
- What each batch leaves out: the pull requests its description lists under a heading that says
  "left out" or "not included" (`left_out` in the sync), by heading, without the reasons. What the
  batch contains is never listed as left out, as in the sync.
- Links to the same searches on GitHub, which are live where the issue is a snapshot.

The top of the description holds a hidden block for agents and scripts to read instead of the
tables: `<!-- batch-status {...} -->`, with compact JSON (see `data`, and
`verification/BATCHES.md`).

Label badges are shields.io images in each label's colour on GitHub, read once a run. A
description holds at most 65,536 characters. When the full one would not fit, it is shortened step
by step, and says so at the top: badges become plain label names, then titles are cut shorter,
then each table becomes a list of numbers, and as a last resort the end is cut off.

Pull requests, and the batches' descriptions and notes, are read through GraphQL, in a few
requests, and the label colours through REST, in one. The issue is found through GraphQL too:
among the pinned issues, the latest twenty, and those titled "Batch status". Only an issue the
workflow opened counts, so that nobody can make the workflow write into an issue of theirs. The
pinned and latest issues find it before GitHub's search index does.
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
from pathlib import Path
import re
import sys
from urllib.parse import quote

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")
# The sync, for how it reads a batch's note (`BY_HAND`, `load_note`, `members`) and what a batch's
# description leaves out (`left_out`). Loading it only defines things.
_sync = _rest.load("batch-queue-sync.py")


def names(labels):
    """The label names this script uses, from `labels`, the module `batch-labels.py`.

    `CHANGED`, `MAIN_CONFLICT`, `BATCH_CONFLICT` and `LATEST` come from other pull requests, which
    may land before or after this one: `changed after frozen` from #1697, the two conflict labels
    from #1700, and `latest batch` from the one that orders stacked batches. Until they land, the
    names are the ones those labels already have on GitHub.
    """
    return {
        "QUEUED": labels.QUEUED, "PRIORITY": labels.PRIORITY, "BUILDING": labels.BUILDING,
        "MEMBER": labels.MEMBER, "WAITING": labels.WAITING,
        "CHANGED": getattr(labels, "CHANGED", "changed after frozen"),
        "MAIN_CONFLICT": getattr(labels, "MAIN_CONFLICT", "main-conflict"),
        "BATCH_CONFLICT": getattr(labels, "BATCH_CONFLICT", "batch-conflict"),
        "LATEST": getattr(labels, "LATEST", "latest batch"),
    }


_names = names(_labels)
QUEUED, PRIORITY, BUILDING, MEMBER, WAITING = (
    _names[key] for key in ("QUEUED", "PRIORITY", "BUILDING", "MEMBER", "WAITING"))
CHANGED, MAIN_CONFLICT, BATCH_CONFLICT, LATEST = (
    _names[key] for key in ("CHANGED", "MAIN_CONFLICT", "BATCH_CONFLICT", "LATEST"))
# The labels shown as badges, in this order. `building` is not one: see above.
BADGES = (PRIORITY, CHANGED, BATCH_CONFLICT, MAIN_CONFLICT, WAITING, LATEST)

TITLE = "Batch status"
MARKER = "<!-- batch-status -->"
WORKFLOW = "batch status"
# The workflow's token, as GraphQL names the author of what it writes.
BOT = "github-actions"
# GitHub refuses a description longer than 65,536 characters. This leaves a margin for how it
# counts them.
LIMIT = 65_000
# The colour of a badge for a label GitHub does not have.
GREY = "ededed"
# The time in the footer, which alone is not a change.
STAMP = "Last changed {} UTC."
STAMPED = re.compile(r"Last changed \d{4}-\d\d-\d\d \d\d:\d\d UTC\.")
# The ways a description is shortened to fit, each on top of those before it.
SHORTENED = (
    "label badges are shown as plain label names",
    "titles are cut shorter",
    "each table is a list of numbers",
    "the end is cut off",
)
# How many characters of a title a table shows, in full and once shortened.
WIDE, NARROW = 72, 32

PULLS = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes {
        number title isDraft headRefName headRefOid
        headRepository { nameWithOwner }
        author { login }
        labels(first: 100) { nodes { name } }
      }
    }
  }
}"""
BATCH = """query($owner: String!, $name: String!, $number: Int!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $number) {
      body
      comments(first: 100, after: $after) {
        pageInfo { hasNextPage endCursor }
        nodes { author { __typename login } body }
      }
    }
  }
}"""
ISSUE = "number state body author { __typename login }"
ISSUES = """query($owner: String!, $name: String!, $q: String!) {
  repository(owner: $owner, name: $name) {
    pinnedIssues(first: 3) { nodes { issue { %s } } }
    issues(first: 20, orderBy: {field: CREATED_AT, direction: DESC}) { nodes { %s } }
  }
  search(query: $q, type: ISSUE, first: 20) { nodes { ... on Issue { %s } } }
}""" % (ISSUE, ISSUE, ISSUE)

Refused = _rest.Refused


def by_workflow(node):
    """Whether GraphQL says the workflow wrote this comment or issue."""
    author = (node or {}).get("author") or {}
    return author.get("__typename") == "Bot" and author.get("login") == BOT


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with the queries this script reads with,
    and a clock that the tests can set."""

    def now(self):
        return datetime.datetime.now(datetime.timezone.utc)

    def pulls(self):
        """Every open pull request, by number."""
        found, after = {}, None
        while True:
            page = self.graphql(PULLS, owner=self.owner, name=self.name, after=after)
            page = page["repository"]["pullRequests"]
            for node in page["nodes"]:
                found[node["number"]] = pull(node, self.repo)
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def batch(self, number):
        """A batch's description and the note in the sync's record comment on it, as
        (description, note). The note is empty while there is no record."""
        after = None
        while True:
            node = self.graphql(BATCH, owner=self.owner, name=self.name, number=number, after=after)
            node = node["repository"]["pullRequest"] or {}
            comments = node.get("comments") or {"nodes": [], "pageInfo": {"hasNextPage": False}}
            for comment in comments["nodes"]:
                match = _sync.BY_HAND.match(comment.get("body") or "")
                if match and by_workflow(comment):
                    return node.get("body") or "", _sync.load_note(match.group(1))
            if not comments["pageInfo"]["hasNextPage"]:
                return node.get("body") or "", {}
            after = comments["pageInfo"]["endCursor"]

    def colours(self):
        """Each label's colour, by name, as six hex digits."""
        return {label["name"]: label["color"].lower() for label in self.pages("labels")}

    def issue(self):
        """The status issue as GraphQL gives it ({number, state, body, author}), or None when
        there is none yet. Of several, the open one with the lowest number."""
        found = self.graphql(ISSUES, owner=self.owner, name=self.name,
                             q=f'repo:{self.repo} is:issue in:title "{TITLE}"')
        repository = found["repository"]
        nodes = [pinned.get("issue") for pinned in repository["pinnedIssues"]["nodes"]]
        nodes += repository["issues"]["nodes"] + found["search"]["nodes"]
        ours = {node["number"]: node for node in nodes
                if node and (node.get("body") or "").startswith(MARKER) and by_workflow(node)}
        if not ours:
            return None
        return min(ours.values(), key=lambda node: (node["state"] != "OPEN", node["number"]))


def pull(node, repo):
    """What this script needs to know about a pull request, from GraphQL's answer. `repo` is this
    repository, as `owner/name`."""
    return {
        "number": node["number"], "title": node.get("title") or "", "draft": bool(node.get("isDraft")),
        "ref": node["headRefName"], "sha": node["headRefOid"],
        "author": (node.get("author") or {}).get("login"),
        "labels": {label["name"] for label in node["labels"]["nodes"]},
        "batch": _labels.holds_batch(repo, (node.get("headRepository") or {}).get("nameWithOwner"),
                                     node["headRefName"]),
    }


# What the issue says, worked out before it is written down.


def group(labels):
    """The group of the queue a pull request with these labels goes in: the first that applies."""
    if CHANGED in labels:
        return "changed"
    if BATCH_CONFLICT in labels or MAIN_CONFLICT in labels:
        return "conflict"
    return "ready"


def status(repo, pulls, read):
    """What the issue says, from the open pull requests by number and `read`, which gives a batch's
    (description, note) by its number. Returns {batches, queue, left}:

    batches  the batches being built, outermost first as far as is known, each as {number, title,
             ref, sha, latest, record, members, contains, own}: `record` is the head the note was
             written for, `members` every pull request the note says the batch contains,
             `contains` the batches being built among them, and `own` what it adds to those.
    queue    the queued pull requests no batch being built contains, in order, as {number, group,
             priority}.
    left     {batch number: [(heading, [numbers])]}: the open pull requests each batch's description
             leaves out, apart from what the batch contains, in the description's order.
    gone     {batch number: how many more it leaves out that are no longer open}.
    """
    found = [pr for pr in pulls.values() if pr["batch"] and BUILDING in pr["labels"]]
    found.sort(key=lambda pr: (LATEST not in pr["labels"], -pr["number"]))
    batches, texts = [], {}
    for pr in found:
        texts[pr["number"]], note = read(pr["number"])
        batches.append({"number": pr["number"], "title": pr["title"], "ref": pr["ref"], "sha": pr["sha"],
                        "latest": LATEST in pr["labels"], "record": note.get("head"),
                        "members": sorted(int(key) for key in _sync.members(note))})
    building = {batch["number"]: batch for batch in batches}
    for batch in batches:
        inner = [number for number in batch["members"] if number in building and number != batch["number"]]
        covered = set(inner)
        for number in inner:
            covered |= set(building[number]["members"])
        batch["contains"] = inner
        batch["own"] = [number for number in batch["members"] if number not in covered]
    held = {number for batch in batches for number in batch["members"]}
    queued = sorted((pr for pr in pulls.values() if QUEUED in pr["labels"] and pr["number"] not in held),
                    key=lambda pr: (PRIORITY not in pr["labels"], pr["number"]))
    queue = [{"number": pr["number"], "group": group(pr["labels"]), "priority": PRIORITY in pr["labels"]}
             for pr in queued]
    queue.sort(key=lambda entry: ("ready", "changed", "conflict").index(entry["group"]))
    left, gone = {}, {}
    for batch in batches:
        headings = {}
        for number, (heading, _) in _sync.left_out(texts[batch["number"]], repo).items():
            if number in batch["members"]:
                continue
            if number in pulls:
                headings.setdefault(heading, []).append(number)
            else:
                gone[batch["number"]] = gone.get(batch["number"], 0) + 1
        if headings:
            left[batch["number"]] = list(headings.items())
    return {"batches": batches, "queue": queue, "left": left, "gone": gone}


def data(found, whole=True):
    """The hidden block for agents and scripts: `<!-- batch-status {...} -->` with compact JSON.
    Without `whole`, for when the block alone would not fit, it is `{"truncated":true}`.

    batches   outermost first, as far as is known: {number, branch, head (the full commit id),
              latest (whether it is labelled `latest batch`), members (every pull request it
              contains, by the sync's record), contains (the batches being built among them)}
    queue     in the order shown: {number, group ("ready", "changed" or "conflict"), priority}
    left_out  {batch number as a string: [the open pull requests its description leaves out]}

    `--` in the JSON is written `-\\u002d`, so that nothing in it ends the comment early.
    """
    if not whole:
        return '<!-- batch-status {"truncated":true} -->'
    block = {
        "batches": [{"number": batch["number"], "branch": batch["ref"], "head": batch["sha"],
                     "latest": batch["latest"], "members": batch["members"], "contains": batch["contains"]}
                    for batch in found["batches"]],
        "queue": found["queue"],
        "left_out": {str(number): [pr for _, listed in headings for pr in listed]
                     for number, headings in found["left"].items()},
    }
    text = json.dumps(block, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return f"<!-- batch-status {text.replace('--', '-' + chr(92) + 'u002d')} -->"


# Writing it down.


def escaped(text):
    """Text from a pull request, such as its title, as plain text in a table cell or a line:
    Markdown's special characters escaped, and `@name` and `#123` broken by a zero-width space so
    that they mention nobody and link nothing."""
    text = re.sub(r"([\\`*_\[\]<>|~])", r"\\\1", " ".join(text.split()))
    return re.sub(r"([@#])(?=\w)", "\\1\u200b", text)


def heading(text, repo):
    """A heading from a batch's description, as Markdown: its references to pull requests in code
    spans, as the sync quotes them (`unlinked`), and `@name` outside code spans broken as in
    `escaped`."""
    parts = re.split(r"(`+[^`]*`+)", _sync.unlinked(" ".join(text.split()), repo))
    for index in range(0, len(parts), 2):
        parts[index] = re.sub(r"@(?=\w)", "@\u200b", parts[index])
    return "".join(parts)


def cut(text, width):
    return text if len(text) <= width else text[:width - 1].rstrip() + "…"


def shields(name):
    """A label's name as the text of a shields.io static badge's path: `-` is written `--`, `_`
    `__`, and the rest is escaped for a URL, a space as `%20`."""
    return quote(name.replace("-", "--").replace("_", "__"), safe="")


def badge(name, colour, repo, plain=False):
    """A label as a badge in its colour that links to the label, or with `plain`, its name in a
    code span. The badge's alt text is the label's name."""
    if plain:
        return f"`{name}`"
    alt = re.sub(r"([\\\[\]])", r"\\\1", name)
    image = f"https://img.shields.io/badge/{shields(name)}-{colour or GREY}?style=flat-square"
    return f"[![{alt}]({image})](https://github.com/{repo}/labels/{quote(name, safe='')})"


def label(name, sign=""):
    """A search term for a label, or for any of several."""
    given = [name] if isinstance(name, str) else list(name)
    return sign + "label:" + ",".join(f'"{n}"' if " " in n or "," in n else n for n in given)


def search(repo, *terms):
    """A link to GitHub's search of the repository's open pull requests."""
    query = " ".join(("is:pr", "is:open") + terms)
    return f"https://github.com/{repo}/pulls?q={quote(query, safe='')}"


class Writer:
    """Writes the description, shortened by the first `level` steps of `SHORTENED`."""

    def __init__(self, repo, pulls, colours, level=0):
        self.repo, self.pulls, self.colours, self.level = repo, pulls, colours, level

    def badge(self, name):
        return badge(name, self.colours.get(name), self.repo, plain=self.level >= 1)

    def table(self, numbers):
        """The pull requests `numbers` as a table of number, title, author and badges."""
        if not numbers:
            return ["None."]
        if self.level >= 3:
            return [", ".join(f"#{number}" for number in numbers)]
        width = NARROW if self.level >= 2 else WIDE
        rows = ["| PR | Title | Author | Labels |", "|---|---|---|---|"]
        for number in numbers:
            pr = self.pulls.get(number)
            if pr is None:
                rows.append(f"| #{number} | *not open* | | |")
                continue
            title = escaped(cut(pr["title"], width))
            if pr["batch"]:
                title = "**batch:** " + title
            elif pr["draft"]:
                title = "*draft:* " + title
            badges = " ".join(self.badge(name) for name in BADGES if name in pr["labels"])
            rows.append(f"| #{number} | {title} | {pr['author'] or 'ghost'} | {badges} |")
        return rows

    def batches(self, found):
        lines = ["## Batches being built", "",
                 f"Live: [batches being built]({search(self.repo, 'head:' + _labels.PREFIX, label(BUILDING))})"
                 f" · [the pull requests in them]({search(self.repo, label(MEMBER))})"
                 f" · [`{LATEST}`]({search(self.repo, label(LATEST))})", ""]
        if not found["batches"]:
            return lines + ["No batch is being built.", ""]
        lines += [f"The outermost batch comes first, as far as is known: the one labelled `{LATEST}`, then the "
                  "others by number, newest first. This order is approximate.", ""]
        for batch in found["batches"]:
            latest = " " + self.badge(LATEST) if batch["latest"] else ""
            lines += [f"### #{batch['number']} {escaped(cut(batch['title'], WIDE))}{latest}", ""]
            count = len(batch["members"])
            about = f"`{batch['ref']}` at `{batch['sha'][:7]}` · {count} pull request{'s' * (count != 1)}"
            inner = batch["contains"]
            if inner:
                about += (f", {len(batch['own'])} of them its own. It contains the "
                          f"batch{'es' * (len(inner) > 1)} {', '.join(f'#{n}' for n in inner)}, and "
                          f"what {'they contain' if len(inner) > 1 else 'that contains'} is listed there")
            about += "."
            if batch["record"] is None:
                about += " The batch queue sync has not recorded what it contains yet."
            elif batch["record"] != batch["sha"]:
                about += (f" This is what it contained at `{batch['record'][:7]}`: the batch queue sync has "
                          "not looked at its new head yet.")
            lines += [about, ""] + self.table(batch["own"]) + [""]
        return lines

    def queue(self, found):
        groups = {"ready": [], "changed": [], "conflict": []}
        for entry in found["queue"]:
            groups[entry["group"]].append(entry["number"])
        total = len(found["queue"])
        lines = ["## Batch queue", "",
                 f"Live: [`{QUEUED}`]({search(self.repo, label(QUEUED))})", "",
                 f"{total} pull request{'s' * (total != 1)} labelled `{QUEUED}` that no batch being built "
                 f"contains. Each is in the first group that applies. `{PRIORITY}` pull requests come first in "
                 f"each group, and neither `{PRIORITY}` nor `{WAITING}` changes the group.", ""]
        sections = (
            ("ready", "Ready", f"Labelled none of `{CHANGED}`, `{BATCH_CONFLICT}` and `{MAIN_CONFLICT}`",
             (label(QUEUED), label(CHANGED, "-"), label(BATCH_CONFLICT, "-"), label(MAIN_CONFLICT, "-"))),
            ("changed", "Pushed to since approval", f"Labelled `{CHANGED}`", (label(QUEUED), label(CHANGED))),
            ("conflict", "Conflicts", f"Labelled `{BATCH_CONFLICT}` or `{MAIN_CONFLICT}`, and not `{CHANGED}`",
             (label(QUEUED), label((BATCH_CONFLICT, MAIN_CONFLICT)), label(CHANGED, "-"))),
        )
        for key, heading, rule, terms in sections:
            lines += [f"### {heading} ({len(groups[key])})", "",
                      f"{rule}. Live: [search]({search(self.repo, *terms)})", ""]
            lines += self.table(groups[key]) + [""]
        return lines

    def left(self, found):
        lines = ["## Left out", "",
                 f"Live: [`{WAITING}`]({search(self.repo, label(WAITING))}), which also holds the pull requests "
                 "handed back for other reasons", ""]
        if not found["left"] and not found["gone"]:
            return lines + ["No batch being built leaves anything out.", ""]
        lines += ["What each batch's description lists as left out, by heading. The full reason is in the "
                  "batch's description and in the comment on the pull request.", ""]
        for number in (batch["number"] for batch in found["batches"]):
            if number not in found["left"] and number not in found["gone"]:
                continue
            lines += [f"### From #{number}", ""]
            for title, numbers in found["left"].get(number, ()):
                lines += [f"**{heading(title, self.repo)}**", ""] + self.table(numbers) + [""]
            gone = found["gone"].get(number)
            if gone:
                lines += [f"It also lists {gone} pull request{'s' * (gone != 1)} that {'are' if gone != 1 else 'is'} "
                          "no longer open.", ""]
        return lines

    def footer(self, stamp):
        guide = f"https://github.com/{self.repo}/blob/main/verification/BATCHES.md#the-status-issue"
        return ["---", "",
                "<sub>This issue shows the batches being built, the batch queue and what each batch leaves out. "
                f"The `{WORKFLOW}` workflow (`.github/workflows/batch-status.yml`) keeps it up to date: it looks "
                "every 15 minutes and after each run of the batch queue and conflict labels workflows, and "
                f"rewrites this only when something in it changes. {STAMP.format(stamp)} Agents and scripts: "
                "read the `batch-status` JSON block at the top of this description's source, not the tables. "
                f"See [`verification/BATCHES.md`]({guide}).</sub>", ""]

    def body(self, found, stamp):
        head = [MARKER, data(found), ""]
        if self.level >= len(SHORTENED) and len(head[1]) > LIMIT // 2:
            head[1] = data(found, whole=False)
        if self.level:
            head += ["> [!NOTE]", "> Shortened to fit GitHub's limit on the length of an issue: "
                     f"{', '.join(SHORTENED[:self.level])}.", ""]
        main = "\n".join(self.batches(found) + self.queue(found) + self.left(found))
        top, foot = "\n".join(head), "\n".join(self.footer(stamp))
        if self.level >= len(SHORTENED):
            room = LIMIT - len(top) - len(foot) - len("\n\n…\n\n")
            if len(main) + 1 > room:
                # At the end of a line, or of a number in a list when its line is long.
                kept = main[:max(0, room)]
                line = kept.rsplit("\n", 1)[0]
                main = (line if len(line) > len(kept) - 1000 else kept.rsplit(" ", 1)[0]) + "\n\n…\n"
        return f"{top}\n{main}\n{foot}"


def describe(repo, pulls, colours, found, stamp):
    """The description, shortened as little as it can be to fit `LIMIT`, and how much it was."""
    for level in range(len(SHORTENED) + 1):
        text = Writer(repo, pulls, colours, level).body(found, stamp)
        if len(text) <= LIMIT:
            break
    return text, level


def same(old, new):
    """Whether two descriptions say the same, the time in the footer apart."""
    def plain(text):
        return STAMPED.sub("", (text or "").replace("\r\n", "\n")).strip()
    return plain(old) == plain(new)


def run(gh, preview=None):
    """Bring the status issue up to date. Returns a log. With `preview`, the description it
    should have is written to that file as well."""
    pulls = gh.pulls()
    colours = gh.colours()
    found = status(gh.repo, pulls, gh.batch)
    issue = gh.issue()
    text, level = describe(gh.repo, pulls, colours, found, gh.now().strftime("%Y-%m-%d %H:%M"))
    unchanged = issue is not None and same(issue["body"], text)
    if unchanged:
        text = issue["body"]
    if preview:
        Path(preview).write_text(text)
    left = sum(len(numbers) for headings in found["left"].values() for _, numbers in headings)
    log = [f"{len(found['batches'])} batches being built, {len(found['queue'])} pull requests queued, "
           f"{left} left out; {len(text)} characters"
           + (f", shortened: {', '.join(SHORTENED[:level])}" if level else "")]
    if unchanged:
        log.append(f"#{issue['number']} is up to date")
        return log
    where = f"#{issue['number']}" if issue else "the status issue"
    if gh.short():
        log.append(f"only {gh.remaining} requests left this hour: did not write {where}, and the next run does")
        return log
    if gh.dry_run:
        log.append(f"would {'update' if issue else 'open'} {where}")
        return log
    if issue:
        answer, _ = gh.write("PATCH", f"issues/{issue['number']}", {"body": text})
        if answer != 200:
            raise RuntimeError(f"could not update #{issue['number']}: {answer}")
        log.append(f"updated #{issue['number']}" + (" (it is closed)" if issue["state"] != "OPEN" else ""))
    else:
        answer, made = gh.write("POST", "issues", {"title": TITLE, "body": text})
        if answer != 201:
            raise RuntimeError(f"could not open the status issue: {answer}")
        log.append(f"opened #{(made or {}).get('number')}: a maintainer can pin it")
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--preview", type=Path, help="write the description to this file as well")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        log = run(gh, args.preview)
    except (Refused, RuntimeError) as error:
        log, failure = [str(error)], 1
    left = f"; {gh.remaining} REST requests left this hour" if gh.remaining is not None else ""
    log.append(f"{gh.calls + gh.queries} requests to GitHub{left}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
