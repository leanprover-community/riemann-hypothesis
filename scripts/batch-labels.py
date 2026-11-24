"""The labels the batch-queue and inbox workflows give pull requests, in one place.

`batch-queue-sync.py`, `batch-queue-conflicts.py` and `inbox-sync.py` read the names from here.
A workflow's `if:` cannot read this file, so `.github/workflows/batch-queue.yml` names some of
them too: rename a label there as well, and on GitHub before either change lands.
"""

# Wanted in an upcoming batch: a maintainer commented `batch` on the pull request.
QUEUED = "batch queue"
# A queued pull request that goes into a batch before the others.
PRIORITY = "priority"
# On the pull request of a batch assembled by hand that is being built.
BUILDING = "building"
# On each open pull request whose commit is in that batch.
MEMBER = "batch-building"
# On the same pull requests: the batch builds the commit it took, so their authors should not
# push until it has landed or been closed.
FROZEN = "frozen"
# On a frozen pull request whose head has moved on from the commit a batch or the queue took:
# the commits after it are not part of what is built.
CHANGED = "changed after frozen"
# Handed back to the pull request's author.
WAITING = "awaiting-author"
