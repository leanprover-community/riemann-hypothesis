#!/usr/bin/env python3
"""Keep the `inbox` label on the pull requests that are waiting for a maintainer's first response.

The inbox workflow runs this from its trusted checkout: for one pull request when it is opened,
reopened, marked ready, turned back into a draft, commented on, reviewed, relabelled or closed,
and for every open pull request every fifteen minutes. Nothing from a pull request is checked out or run.
Everything is read from GitHub's API, and the only things written are labels.

Each branch that pull requests are based on has an inbox label of its own (`INBOXES`): `inbox` for
`main`, and `alpoge-inbox` for `alpoge` (see below). A pull request based on another branch is in
no inbox. A pull request can be in its branch's inbox when it is open, is not a draft, is not a
batch, and carries none of `batch queue`, `building`, `batch-building` and `awaiting-author` (named
in `batch-labels.py`). A batch is a pull request from a branch of this repository named
`batch/...`. One from a `batch/...` branch of a fork is not a batch, and can be in the inbox like
any other pull request (see `holds_batch` in `batch-labels.py`). When `batch-building`
comes off an open pull request, it goes back in the inbox unless someone has responded since it
entered review: that label's changes, and the inbox taking it out meanwhile, are a bot's and do
not count.

A pull request enters review when it is opened, reopened or marked ready, and again when
`awaiting-author` comes off it: its author commented `ready` (see review-commands.yml), or a
maintainer took the label off by hand. It belongs in the inbox until someone with triage access or
more responds to it after that: a comment, such as `aa`, a review or a review comment, or a
change to its labels other than the ones label-pr.yml keeps up to date. Responses by the pull
request's author or by a bot do not count.

A maintainer who takes `inbox` off by hand is not overruled until the pull request enters review
again. One who puts it back asks for another look: it then stays until the next response, not
counting their own in the ten minutes after, which usually just say why.

The branch `alpoge` holds the work done before `main` was replaced, and about 1,200 open pull
requests are based on it. Whether it will be kept up is undecided, and it may be phased out. Until
then its pull requests have an inbox of their own, `alpoge-inbox`, so that they do not crowd the
pull requests on `main`, and every open pull request based on it is labelled `alpoge`. GitHub
runs the default branch's copy of the inbox workflow for their events too, except reviews, which
run the copy of `inbox review` on `alpoge`: the sweep catches those. Everything about `alpoge` here is in `INBOXES` and `ALPOGE`, and goes
when the branch does.

Reviews on pull requests from forks only get a read-only token, so the workflow hears about them
through a second workflow, `inbox review`, that does nothing but run. The sweep catches anything
the events missed, including closed pull requests that kept the label. It reads every open pull
request through GraphQL, a few requests in all, whose allowance is separate from the REST one that
the other workflows use. Before it changes the label on a pull request it reads that pull
request again, so that a response, a label put back or a change of state that came in meanwhile
is not missed. Access is looked up
through REST, once a run for each responder.
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
from pathlib import Path
import sys

_REST_SPEC = importlib.util.spec_from_file_location("rh_github_rest", Path(__file__).with_name("github-rest.py"))
_rest = importlib.util.module_from_spec(_REST_SPEC)
_REST_SPEC.loader.exec_module(_rest)
_labels = _rest.load("batch-labels.py")

INBOX = "inbox"
# The inbox label of each branch that pull requests are based on. A pull request based on any
# other branch is in no inbox.
MAIN = "main"
INBOXES = {MAIN: INBOX, "alpoge": "alpoge-inbox"}
# On every open pull request based on `alpoge`, whose future is undecided (see above).
ALPOGE = "alpoge"
# Labels that this script keeps up to date. Someone adding or removing one has not responded.
OWN = set(INBOXES.values()) | {ALPOGE}
# A sweep changes the labels of at most about this many pull requests, those based on `main` first,
# and leaves the rest to the next sweep. The workflows share an allowance of REST requests an hour,
# and one sweep could otherwise spend it, such as the first, which labels some 1,200 pull requests
# `alpoge`.
CHANGES = 100
# Handed back to the author. Taking it off hands the pull request back to the maintainers.
WAITING = _labels.WAITING
# Labels that mean a maintainer has already decided what happens next.
DECIDED = (_labels.QUEUED, _labels.BUILDING, _labels.MEMBER, WAITING)
# Labels that label-pr.yml keeps up to date from the files a pull request changes and its size.
# Someone adding or removing one of these by hand has not responded to the pull request: they were
# all put on by hand once, before that workflow existed.
AUTOMATIC = ("CI", "changes-challenge", "changes-lake", "changes-solution", "documentation",
             "extra small", "small", "medium", "large", "extra large")
# Repository roles whose response takes a pull request out of the inbox. The REST API reports
# maintain as write and triage as read under `permission`, so `role_name` is the one to read.
ROLES = ("admin", "maintain", "write", "triage")
# How long after putting the label back a maintainer's own responses are taken to be about that.
GRACE = datetime.timedelta(minutes=10)

# The latest 50 comments and reviews and 100 timeline events are enough for any pull request here.
ACTOR = "{ __typename login }"
FIELDS = f"""
  number state isDraft baseRefName headRefName createdAt
  headRepository {{ nameWithOwner }}
  author {{ login }}
  labels(first: 100) {{ nodes {{ name }} }}
  comments(last: 50) {{ nodes {{ createdAt author {ACTOR} }} }}
  reviews(last: 50) {{ nodes {{ state submittedAt author {ACTOR} }} }}
  timelineItems(last: 100, itemTypes: [LABELED_EVENT, UNLABELED_EVENT, READY_FOR_REVIEW_EVENT,
                                       REOPENED_EVENT]) {{
    nodes {{
      __typename
      ... on LabeledEvent {{ createdAt label {{ name }} actor {ACTOR} }}
      ... on UnlabeledEvent {{ createdAt label {{ name }} actor {ACTOR} }}
      ... on ReadyForReviewEvent {{ createdAt }}
      ... on ReopenedEvent {{ createdAt }}
    }}
  }}
"""
EVERY = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes { %s }
    }
  }
}""" % FIELDS
CLOSED = """query($q: String!) {
  search(query: $q, type: ISSUE, first: 100) { nodes { ... on PullRequest { number } } }
}"""
ONE = """query($owner: String!, $name: String!, $number: Int!) {
  repository(owner: $owner, name: $name) { pullRequest(number: $number) { %s } }
}""" % FIELDS


Refused = _rest.Refused


class GitHub(_rest.GitHub):
    """GitHub's API through `gh` (see `github-rest.py`), with the queries this script reads pull
    requests with. With `dry_run`, label changes are printed, not sent."""

    def __init__(self, repo, dry_run=False):
        super().__init__(repo, dry_run)
        # Whether each responder has triage access or more, by login.
        self.access = {}

    def pulls(self):
        """Every open pull request."""
        found, after = [], None
        while True:
            page = self.graphql(EVERY, owner=self.owner, name=self.name, after=after)
            page = page["repository"]["pullRequests"]
            found += [pull(node, self.repo) for node in page["nodes"]]
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def closed_in_inbox(self, name=INBOX):
        """The numbers of closed pull requests that still carry the inbox label `name`."""
        found = self.graphql(CLOSED, q=f'repo:{self.repo} is:pr is:closed label:"{name}"')
        return [node["number"] for node in found["search"]["nodes"] if node]

    def pull(self, number):
        """One pull request, open or not, or None if there is no such pull request."""
        node = self.graphql(ONE, owner=self.owner, name=self.name, number=number)
        node = node["repository"]["pullRequest"]
        return pull(node, self.repo) if node else None

    def can_triage(self, login):
        """Whether `login` has triage access or more to this repository."""
        if login not in self.access:
            status, found = self.call("GET", f"collaborators/{login}/permission")
            if status == 404:
                self.access[login] = False
            elif status != 200:
                raise RuntimeError(f"could not read the access {login} has to {self.repo}: {status}")
            else:
                self.access[login] = (found.get("role_name") in ROLES
                                      or found.get("permission") in ("admin", "write"))
        return self.access[login]

    def label_exists(self, name=INBOX):
        """Whether the label `name` exists. `sync` decides what a missing one means."""
        return super().label_exists(name)

    def label(self, number, add, name=INBOX):
        verb = "add" if add else "remove"
        if self.dry_run:
            print(f"would {verb} {name} on #{number}")
            return
        if add:
            status, _ = self.write("POST", f"issues/{number}/labels", {"labels": [name]})
        else:
            status, _ = self.write("DELETE", f"issues/{number}/labels/{_rest.quoted(name)}")
        # Taking off a label that someone else has just taken off answers 404.
        if status not in (200, 201) and not (status == 404 and not add):
            raise RuntimeError(f"could not {verb} {name} on #{number}: {status}")


def when(text):
    return datetime.datetime.fromisoformat(text.replace("Z", "+00:00"))


def person(actor):
    """The login of a person, or None for a bot or a deleted account."""
    if not actor or actor.get("__typename") == "Bot":
        return None
    return actor.get("login")


def pull(node, repo):
    """What this script needs to know about a pull request, from GraphQL's answer. `repo` is this
    repository, as `owner/name`."""
    entered = when(node["createdAt"])
    inbox = INBOXES.get(node["baseRefName"])
    added = added_by = removed = removed_by = None
    responses = []
    # Timeline events come oldest first, so the last of each kind is the latest.
    for item in node["timelineItems"]["nodes"]:
        kind, at = item["__typename"], when(item["createdAt"])
        if kind in ("ReadyForReviewEvent", "ReopenedEvent"):
            entered = max(entered, at)
            continue
        actor = person(item.get("actor"))
        name = (item.get("label") or {}).get("name")
        if kind == "UnlabeledEvent" and name == WAITING:
            # Whoever took the label off, the pull request needs another look. Counting this as a
            # response too would take it straight back out.
            entered = max(entered, at)
            continue
        if name == inbox:
            if kind == "LabeledEvent":
                added, added_by = at, actor
            else:
                removed, removed_by = at, actor
        elif actor and name not in AUTOMATIC and name not in OWN:
            responses.append({"login": actor, "at": at, "did": "changed its labels"})
    for comment in node["comments"]["nodes"]:
        login = person(comment.get("author"))
        if login:
            responses.append({"login": login, "at": when(comment["createdAt"]), "did": "commented"})
    for review in node["reviews"]["nodes"]:
        login = person(review.get("author"))
        if login and review.get("submittedAt") and review.get("state") != "PENDING":
            responses.append({"login": login, "at": when(review["submittedAt"]), "did": "reviewed it"})
    responses.sort(key=lambda response: response["at"])
    return {
        "number": node["number"], "open": node["state"] == "OPEN", "draft": node["isDraft"],
        "base": node["baseRefName"], "inbox": inbox,
        "batch": _labels.holds_batch(repo, (node.get("headRepository") or {}).get("nameWithOwner"),
                                     node["headRefName"]),
        "ref": node["headRefName"], "author": (node.get("author") or {}).get("login"),
        "labels": {label["name"] for label in node["labels"]["nodes"]},
        "entered": entered, "responses": responses,
        "added": added, "added_by": added_by, "removed": removed, "removed_by": removed_by,
    }


def unavailable(pr):
    """Why the pull request cannot be in the inbox at all, or None if it can."""
    if pr["inbox"] is None:
        return f"it is based on `{pr['base']}`, which has no inbox"
    if pr["draft"]:
        return "it is a draft"
    if pr["batch"]:
        return "it is a batch"
    decided = [label for label in DECIDED if label in pr["labels"]]
    if decided:
        return "it is labelled " + " and ".join(f"`{label}`" for label in decided)
    return None


def responder(gh, pr, since, grace=None):
    """The first response after `since` by someone with triage access, or None.

    `grace` is a login and a time: that person's responses up to then do not count.

    Every responder's access is looked up. Their `authorAssociation` would be cheaper, but GitHub
    reports a private member of the organisation as a mere contributor to a token that cannot see
    the membership, and the workflow's token is one of those.
    """
    for response in pr["responses"]:
        if response["login"] == pr["author"] or response["at"] <= since:
            continue
        if grace and response["login"] == grace[0] and response["at"] <= grace[1]:
            continue
        if gh.can_triage(response["login"]):
            return response
    return None


def decide(gh, pr):
    """What to do with the inbox label of the pull request's branch: ("add" or "remove" or None,
    and why)."""
    has = pr["inbox"] in pr["labels"]
    if not pr["open"]:
        return ("remove" if has else None), "it is closed"
    why = unavailable(pr)
    if why:
        return ("remove" if has else None), why
    # Responses count from when the pull request last entered review, or from when a person put
    # the label back to ask for another look.
    since, grace = pr["entered"], None
    if has and pr["added_by"] and pr["added"] > since:
        since, grace = pr["added"], (pr["added_by"], pr["added"] + GRACE)
    found = responder(gh, pr, since, grace)
    said = f"{found['login']} {found['did']}" if found else None
    if has:
        return ("remove", said) if found else (None, "it is waiting for a response")
    if found:
        return None, said
    if pr["removed_by"] and pr["removed"] > pr["entered"]:
        return None, f"{pr['removed_by']} took it out of the inbox"
    return "add", "it is waiting for a response"


def tidy(pr):
    """The other labels this script keeps, as ("add" or "remove", label, why) for each change: the
    inbox labels of other branches come off, and `alpoge` is on the open pull requests based on
    `alpoge` and on no other open pull request."""
    changes = [("remove", name, f"it is based on `{pr['base']}`") for name in sorted(INBOXES.values())
               if name != pr["inbox"] and name in pr["labels"]]
    if pr["open"]:
        on = pr["base"] == ALPOGE
        if on != (ALPOGE in pr["labels"]):
            changes.append(("add" if on else "remove", ALPOGE, f"it is based on `{pr['base']}`"))
    return changes


def where(name):
    return "the inbox" if name == INBOX else f"the `{name}` inbox"


def sync(gh, number=None, log=None):
    """Bring the label up to date on one pull request, or on all open ones. Returns the log, the
    list `log` if one is given: what it holds when an error stops the sweep is what was done."""
    log = [] if log is None else log
    checked = set()

    def check_label(name):
        # Only adding needs the label to exist: GitHub would make a new one. Removing never does.
        if name in checked:
            return
        checked.add(name)
        if not gh.label_exists(name):
            if not gh.dry_run:
                raise Refused(f"There is no `{name}` label in {gh.repo}. Was it renamed?")
            log.append(f"there is no `{name}` label yet, so a real run would stop here")

    def change(pr, action, name):
        nonlocal budget
        if budget is not None:
            budget -= 1
        if action == "add":
            check_label(name)
        gh.label(pr["number"], action == "add", name)
        pr["labels"] = (pr["labels"] | {name}) if action == "add" else (pr["labels"] - {name})

    if number is None:
        pulls = gh.pulls()
    else:
        found = gh.pull(number)
        if found is None:
            raise Refused(f"There is no pull request #{number} in {gh.repo}.")
        pulls = [found]
    budget = CHANGES if number is None else None
    deferred = 0
    pulls.sort(key=lambda pr: pr["base"] != MAIN)
    for i, pr in enumerate(pulls):
        try:
            action, why = decide(gh, pr) if pr["inbox"] else (None, unavailable(pr))
            if budget is not None and budget <= 0:
                deferred += bool(action or tidy(pr))
                continue
            if (action or tidy(pr)) and number is None:
                # The sweep read this pull request a while ago. A response, a close, a label put
                # back or a pull request marked ready since then would otherwise be missed.
                pr = pulls[i] = gh.pull(pr["number"]) or pr
                action, why = decide(gh, pr) if pr["inbox"] else (None, unavailable(pr))
            if action:
                change(pr, action, pr["inbox"])
                log.append(f"#{pr['number']}: {'put in' if action == 'add' else 'taken out of'} "
                           f"{where(pr['inbox'])}, because {why}")
            elif number is not None:
                log.append(f"#{pr['number']}: left as it was, because {why}")
            for action, name, because in tidy(pr):
                change(pr, action, name)
                log.append(f"#{pr['number']}: {'labelled' if action == 'add' else 'no longer labelled'} "
                           f"`{name}`, because {because}")
        except RuntimeError as error:
            # One pull request that cannot be read or labelled should not hold up the rest.
            gh.failed = True
            log.append(f"#{pr['number']}: skipped, because {error}")
    if deferred:
        log.append(f"{deferred} more pull requests need their labels changed: the next sweep carries on")
    if number is None:
        # A closed pull request whose `closed` run failed would keep the label for good otherwise.
        for name in INBOXES.values():
            try:
                for closed in gh.closed_in_inbox(name):
                    gh.label(closed, False, name)
                    log.append(f"#{closed}: taken out of {where(name)}, because it is closed")
            except RuntimeError as error:
                gh.failed = True
                log.append(f"closed pull requests in {where(name)}: skipped, because {error}")
        for branch, name in INBOXES.items():
            # The pull requests the sweep read as open, some of which may have closed since.
            based = [pr for pr in pulls if pr["base"] == branch]
            waiting = sum(name in pr["labels"] and pr["open"] for pr in based)
            log.append(f"{waiting} of the {len(based)} open pull requests based on `{branch}` are in "
                       f"{where(name)}")
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", type=int, help="look at this pull request only")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure, log = None, []
    try:
        sync(gh, args.pr, log)
        failure = 1 if gh.failed else None
    except (Refused, RuntimeError) as error:
        # Keep what was done before the stop.
        log.append(str(error))
        failure = 1
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
