"""The labels the batch-queue, conflict-labels and inbox workflows give pull requests, and which
pull requests hold a batch, in one place.

`batch-queue-sync.py`, `batch-queue-conflicts.py`, `conflict-labels.py` and `inbox-sync.py` read
the names from here, and use `holds_batch`.
A workflow's `if:` cannot read this file, so the workflows in `.github/workflows` name some of them
too, in `if:` and `env:`: rename a label there as well, and on GitHub before either change lands.
`tests/test_label_names.py` checks that every label name a workflow writes is one of these or
another label the workflows know, and that `verification/BATCHES.md` lists these.
"""

# Wanted in an upcoming batch: a maintainer commented `batch` on the pull request.
QUEUED = "batch queue"
# A queued pull request that goes into a batch before the others.
PRIORITY = "priority"
# On the pull request of a batch assembled by hand that is being built.
BUILDING = "building"
# On the pull request of a batch assembled by hand that is being built and that no other such
# batch is stacked on: the outermost batch of its stack.
LATEST = "latest batch"
# On each open pull request whose commit is in that batch and in no batch it is stacked on.
MEMBER = "batch-building"
# On the same pull requests: the batch builds the commit it took, so their authors should not
# push until it has landed or been closed.
FROZEN = "frozen"
# On a frozen pull request whose head has moved on from the commit a batch or the queue took:
# the commits after it are not part of what is built.
CHANGED = "changed after frozen"
# Handed back to the pull request's author.
WAITING = "awaiting-author"
# Conflicts with main, as GitHub sees it. `conflict-labels.py` keeps it up to date.
MAIN_CONFLICT = "main-conflict"
# Conflicts with a batch that is being built. `conflict-labels.py` keeps it up to date.
BATCH_CONFLICT = "batch-conflict"
# Whether `conflict-labels.py` keeps those two labels up to date, and so whether the batch queue
# leaves to it the pull requests a batch's description lists under a heading about conflicts.
# It is off until the description check can tell it which pull requests a batch says it
# includes: without that, it would tell the author of a pull request whose changes a batch
# carries, merged with `main`, to merge that batch's branch.
CONFLICT_LABELS_ON = False

# What a pull request in a batch assembled by hand carries, `building` from before the batch's
# pull request and its members were labelled differently included.
IN_BATCH = (MEMBER, FROZEN, BUILDING)

# The start of the name of a branch that holds a batch.
PREFIX = "batch/"


def holds_batch(repo, home, ref):
    """Whether a pull request holds a batch: its head branch `ref` is in `repo`, this repository,
    and its name starts with `batch/`. `home` is the repository the branch is in, as `owner/name`,
    or None when GitHub no longer knows it. A `batch/...` branch of a fork is not a batch: only
    those who can push to this repository can make one. Repository names are compared ignoring
    letter case, as GitHub does."""
    return bool(home) and home.lower() == repo.lower() and ref.startswith(PREFIX)
