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
# The line git writes in the message of a commit that reverts another one, naming that commit.
REVERTS = re.compile(r"^This reverts commit ([0-9a-f]{7,40})\b", re.MULTILINE)
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
    that reverts it}. `commits` is what `branch_commits` lists, as {commit: (message, parents)},
    and `found` what the batch contains, as {number: commit}.

    A pull request is reverted when a commit of the branch reverts the merge commit that brought in
    the commit of it the batch holds, as one of its parents after the first. A commit reverts
    another when its message says `This reverts commit <commit>`, as git writes it, whatever its
    first line says. A revert of that revert, which git calls `Revert "Revert "..."` or `Reapply
    "..."`, puts the pull request back, and so on. The commit named for a pull request is the
    revert in effect that comes last in that chain. A merge brings in a pull request only at the
    commit the batch holds, so one merged in again at a new head is not taken for reverted by a
    revert of its earlier merge, whatever the two merges are called.
    """
    def named(text):
        found_ = [commit for commit in commits if commit.startswith(text)]
        return found_[0] if len(found_) == 1 else None

    target = {}
    for commit, (message, _) in commits.items():
        match = REVERTS.search(message)
        undone = named(match.group(1)) if match else None
        if undone is not None and undone != commit:
            target[commit] = undone
    by = {}
    for commit, undone in target.items():
        by.setdefault(undone, set()).add(commit)
    brought = {}
    for commit, (_, parents) in commits.items():
        for key, held in found.items():
            if held in parents[1:]:
                brought.setdefault(key, set()).add(commit)

    undone_, depth_ = {}, {}

    def is_undone(commit, seen=()):
        # Undone when a commit reverts it that is not undone itself.
        if commit not in undone_:
            undone_[commit] = any(not is_undone(other, (*seen, commit))
                                  for other in sorted(by.get(commit, ())) if other not in seen)
        return undone_[commit]

    def chain(commit):
        """Every commit that reverts `commit`, directly or not, with how many reverts deep it is."""
        found_, todo = {}, [(other, 1) for other in by.get(commit, ())]
        while todo:
            other, depth = todo.pop()
            if other not in found_:
                found_[other] = depth
                todo += [(next_, depth + 1) for next_ in by.get(other, ())]
        return found_

    result = {}
    for key in sorted(brought, key=int):
        for merge in sorted(brought[key]):
            if not is_undone(merge):
                continue
            # The revert in effect, of an odd depth, deepest in the chain.
            live = [(depth, other) for other, depth in chain(merge).items() if depth % 2 and not is_undone(other)]
            if live:
                result[key] = max(live)[1]
                break
    return result


def description_check(number, body, repo, note, pulls, below=()):
    """What the comment comparing the description of the batch #`number` with its branch says, and
    whether all is well. `note` is the batch's note, and `pulls` the open pull requests, as
    `batch-queue-sync.py` reads them. `below` is what the batches this one is stacked on contain,
    as numbers: the branch holds them too, but the note records only what the batch contains of
    its own.

    It names what the description lists as included, under any heading but one that leaves pull
    requests out, that is closed, saying which of those are still in the branch and so land with it
    although GitHub will not mark them merged; and what it lists as included that is open but whose
    head commit is not in the branch. It names what is in the branch that the description does not
    list at all, unless the description lists nothing as included or it holds a batch itself; what
    is in the branch that it lists as left out; and what the branch reverts, which is named for that
    alone. What is in the branch is what the note records, at the commit it was found at, so a pull
    request pushed to since it was merged in is still in it. A pull request that a batch under this
    one contains is in the branch when the description lists it as included, and is not named when
    it does not list it: the description of a stacked batch need list only its own.
    """
    entries = list_entries(body, repo)
    found = {int(key) for key in note["members"]}
    included = {entry for entry, heading, _ in entries if heading and not leaves_out(heading)} - {number}
    anywhere = {entry for entry, _, _ in entries}
    out = {entry for entry, heading, _ in entries if leaves_out(heading)}
    # A closed pull request stays in the note while its commit is in the branch.
    closed = sorted(entry for entry in included if entry not in pulls)
    landing = [entry for entry in closed if entry in found | set(below)]
    missing = sorted(entry for entry in included - found - set(below) if entry in pulls)
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
        if landing:
            lines[-1] += (f" Of these, {links(landing)} {'is' if len(landing) == 1 else 'are'} still in this branch, "
                          "so their changes land with it, although GitHub does not mark a closed pull request merged. "
                          "Rebuild the branch without any that should not land.")
    if missing:
        lines += ["", f"Listed as included, but their head commit is not in this branch: {links(missing)}. Merge the head "
                  "commit of each into the branch. One whose earlier commit is in the branch, for example because it "
                  "was pushed to after it was merged in but before the workflow first looked through the batch, does "
                  "not count: GitHub marks a pull request merged only when its head commit lands. To leave such a one "
                  "out instead, rebuild the branch without it, since its earlier commit would still land, and take it "
                  "off the list. One that is not in the branch at all only needs to come off the list."]
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
