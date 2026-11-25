"""Read a batch's description and branch the way the batch-queue workflow does, without asking GitHub.

`batch-queue-sync.py` loads this file. Everything here works on text the sync has already read: a
batch's description, the messages of its branch's commits, and the note in which the sync records
what the batch contains. `verification/BATCHES.md` describes the format of a description for the
people who write one.
"""
from __future__ import annotations

import hashlib
import re

# The comment on a batch assembled by hand that compares its description with its branch.
CHECK = "<!-- batch-queue-description-check -->"
# A heading in a batch's description under which the pull requests listed are left out.
LEFT_OUT_HEADING = re.compile(r"\b(?:left out|not included)\b", re.IGNORECASE)
# The merge commit that adds a pull request to a batch assembled by hand, and the first line git
# gives a commit that reverts another one, or that reverts such a revert.
MERGED_BY_HAND = re.compile(r"Merge PR #(\d+) into batch")
UNDONE = re.compile(r'(Revert|Reapply) "(.*)"')
# A left-out heading for conflicts. `conflict-labels.py` finds those itself, from git, and tells
# the pull request with `batch-conflict`, so they are not told again from the description.
CONFLICT_HEADING = re.compile(r"\bconflicts?\s+with\b", re.IGNORECASE)


def list_entries(body, repo):
    """Every pull request a batch's description lists, as (number, heading, entry), in order.

    A heading is a line of its own, not part of a list, that ends with a colon. The pull
    requests under it are the list entries that start with a link to one, `#123` or its full
    URL, up to the next heading or paragraph. The heading is None for a list that follows a
    paragraph instead.
    """
    link = re.compile(rf"[-*]\s+(?:https://github\.com/{re.escape(repo)}/pull/|#)(\d+)\b", re.IGNORECASE)
    found, heading = [], None
    for line in body.splitlines():
        text = line.strip()
        if not text or line[0].isspace():
            continue
        if line.startswith(("- ", "* ")):
            match = link.match(line)
            if match:
                found.append((int(match.group(1)), heading, text[1:].strip()))
            continue
        heading = text if text.endswith(":") else None
    return found


def leaves_out(heading):
    """Whether the pull requests listed under a heading are left out."""
    return bool(heading and LEFT_OUT_HEADING.search(heading))


def left_out(body, repo):
    """The pull requests a batch's description lists as left out, as {number: (heading, entry)}:
    those listed under a heading that says "left out" or "not included". A pull request listed
    twice keeps its first entry."""
    found = {}
    for number, heading, entry in list_entries(body, repo):
        if leaves_out(heading):
            found.setdefault(number, (heading, entry))
    return found


def entry_digest(entry):
    """A short digest of a pull request's (heading, entry) in a batch's description, which the
    note's `left` keeps."""
    return hashlib.sha256("\n".join(entry).encode()).hexdigest()[:16]


def left_out_digest(heading, entry):
    """What kind of reason a pull request is left out for, as a short digest: its heading, up to
    any parenthesis, in lower case. The entry itself is left out of it. The descriptions of
    batches are written afresh each time, so the same reason seldom comes back in the same
    words, while the headings stay put."""
    kind = re.split(r"[(:]", heading, maxsplit=1)[0]
    return hashlib.sha256(" ".join(kind.lower().split()).encode()).hexdigest()[:16]


def reverts(commits, found):
    """Which pull requests in a batch assembled by hand its branch reverts, as {number: the commit
    that reverts it}. `commits` is what `branch_commits` lists, oldest first, and `found` what the
    batch contains, as {number: commit}.

    A commit whose first line is `Revert "Merge PR #123 into batch"` reverts #123: that is the
    message git gives a commit that reverts the merge commit adding #123. So does one whose first
    line is `Revert "..."` around any other line naming #123, if a merge commit of the branch with
    that first line brought in the commit of #123 the batch holds. A revert of such a revert, which
    git calls `Revert "Revert "..."` or `Reapply "..."`, puts the pull request back.
    """
    brought = {}
    for message, parents in commits.values():
        for parent in parents[1:]:
            brought.setdefault(message.split("\n", 1)[0].strip(), set()).add(parent)
    count, last = {}, {}
    for commit, (message, _) in commits.items():
        subject, depth = message.split("\n", 1)[0].strip(), 0
        match = UNDONE.fullmatch(subject)
        while match:
            subject, depth = match.group(2), depth + (1 if match.group(1) == "Revert" else 2)
            match = UNDONE.fullmatch(subject)
        if not depth:
            continue
        ours = MERGED_BY_HAND.fullmatch(subject)
        for key in {ours.group(1)} if ours else set(re.findall(r"#(\d+)\b", subject)):
            if key in found and (ours or found[key] in brought.get(subject, ())):
                count[key] = count.get(key, 0) + (1 if depth % 2 else -1)
                if depth % 2:
                    last[key] = commit
    return {key: last[key] for key in sorted(count, key=int) if count[key] > 0}


def description_check(number, body, repo, note, pulls):
    """What the comment comparing the description of the batch #`number` with its branch says, and
    whether all is well. `note` is the batch's note, and `pulls` the open pull requests, as
    `batch-queue-sync.py` reads them.

    It names what the description lists as included, under any heading but one that leaves pull
    requests out, that is not in the branch: closed pull requests, and open ones whose head commit
    is not there. It names what is in the branch that the description does not list at all, unless
    the description lists nothing as included or it holds a batch itself; what is in the branch that
    it lists as left out; and what the branch reverts, which is named for that alone. What is in
    the branch is what the note records, at the commit it was found at, so a pull request pushed
    to since it was merged in is still in it.
    """
    entries = list_entries(body, repo)
    found = {int(key) for key in note["members"]}
    included = {entry for entry, heading, _ in entries if heading and not leaves_out(heading)} - {number}
    anywhere = {entry for entry, _, _ in entries}
    out = {entry for entry, heading, _ in entries if leaves_out(heading)}
    closed = sorted(entry for entry in included - found if entry not in pulls)
    missing = sorted(entry for entry in included - found if entry in pulls)
    undone = sorted((int(key), undo) for key, undo in note["reverted"].items() if int(key) in pulls)
    found -= {entry for entry, _ in undone}
    unlisted = sorted(entry for entry in found - anywhere if included and entry in pulls and not pulls[entry]["batch"])
    against = sorted(entry for entry in found & out if entry in pulls)

    def links(numbers):
        return ", ".join(f"#{entry}" for entry in numbers)

    lines = [CHECK, "The batch-queue workflow compares this description with the branch. It reads what the batch "
             "contains from the branch: each open pull request whose head commit is in it. This comment is brought up "
             "to date when either of them changes. See `verification/BATCHES.md`."]
    if closed:
        lines += ["", f"Listed as included, but closed: {links(closed)}."]
    if missing:
        lines += ["", f"Listed as included, but their head commit is not in this branch: {links(missing)}. Merge the head "
                  "commit of each into the branch, or take it off the list. One whose earlier commit is in the branch, "
                  "for example because it was pushed to before the workflow first looked through the batch, does not "
                  "count either: GitHub marks a pull request merged only when its head commit lands."]
    if unlisted:
        lines += ["", f"In this branch, but not listed in the description: {links(unlisted)}."]
    if against:
        lines += ["", f"In this branch, but listed as left out: {links(against)}. They are in the batch and will land "
                  "with it, whatever the description says. Take them off that list, or rebuild the branch without them."]
    if undone:
        lines += ["", "Reverted in this branch: " + ", ".join(f"#{entry} in `{undo[:10]}`" for entry, undo in undone)
                  + ". Their head commits are still in the branch, so GitHub marks them merged when this lands, although "
                  "their changes did not land. Rebuild the branch without them and force-push instead of reverting. "
                  "Each one whose head has not moved since is told so."]
    clear = not (closed or missing or unlisted or against or undone)
    if clear and included:
        lines += ["", "Nothing to report: every pull request listed as included is in this branch, everything in it is "
                  "listed, and nothing in it is reverted."]
    elif clear:
        lines += ["", "Nothing to report: nothing in this branch is listed as left out or reverted."]
    return "\n".join(lines) + "\n", clear
