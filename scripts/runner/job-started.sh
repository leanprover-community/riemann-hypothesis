#!/bin/bash
# The runner's job-started hook (ACTIONS_RUNNER_HOOK_JOB_STARTED), run before any step of a job.
# A non-zero exit fails the job before any of its code runs.
#
# Pull requests can change the workflow they run, so a pull request could ask for any runner.
# Only build.yml of this repository runs here, and only the jobs build.yml sends to this runner's
# label, which loop.sh passes in RH_RUNNER_LABEL (unset means rh-big):
# - rh-big: the merge queue (merge_group on main's queue), pushes to main, manual runs
#   (workflow_dispatch, which needs write access), and pull requests from a branch of this
#   repository whose name starts with batch/ (the batcher's batch pull requests);
# - rh-pr-trusted: pull requests from any branch of this repository (pushing one needs write
#   access).
# A pull request from a fork is refused by both. Its head repository and branch are read from
# the event payload at $GITHUB_EVENT_PATH, which GitHub writes and the pull request cannot change.
set -u
repository=leanprover-community/riemann-hypothesis
label=${RH_RUNNER_LABEL:-rh-big}
reject() {
  case "$label" in
    rh-big) echo "::error::The $label runner only runs build.yml for the merge queue, pushes to main, manual runs and pull requests from batch/ branches of $repository ($1)." ;;
    *) echo "::error::The $label runner only runs build.yml for pull requests from branches of $repository ($1)." ;;
  esac
  exit 1
}
case "$label" in
  rh-big | rh-pr-trusted) ;;
  *) reject "unknown runner label $label" ;;
esac
[ "${GITHUB_REPOSITORY:-}" = "$repository" ] || reject "repository ${GITHUB_REPOSITORY:-unset}"
case "${GITHUB_WORKFLOW_REF:-}" in
  "$repository/.github/workflows/build.yml@"*) ;;
  *) reject "workflow ${GITHUB_WORKFLOW_REF:-unset}" ;;
esac
event=${GITHUB_EVENT_NAME:-}
if [ "$label" = rh-pr-trusted ] && [ "$event" != pull_request ]; then
  reject "event ${event:-unset}"
fi
case "$event" in
  merge_group)
    case "${GITHUB_REF:-}" in
      refs/heads/gh-readonly-queue/main/*) ;;
      *) reject "merge group ref ${GITHUB_REF:-unset}" ;;
    esac ;;
  push)
    [ "${GITHUB_REF:-}" = refs/heads/main ] || reject "push to ${GITHUB_REF:-unset}" ;;
  workflow_dispatch) ;;
  pull_request)
    # Prints the head repository's full name and the head branch on two lines, each empty if it
    # is missing or not a string.
    head=$(python3 -I -c '
import json, sys
with open(sys.argv[1]) as stream:
    head = (json.load(stream).get("pull_request") or {}).get("head") or {}
name = (head.get("repo") or {}).get("full_name")
ref = head.get("ref")
print(name if isinstance(name, str) else "")
print(ref if isinstance(ref, str) else "")
' "${GITHUB_EVENT_PATH:-/nonexistent}" 2>/dev/null) || reject "pull request event payload ${GITHUB_EVENT_PATH:-unset} unreadable"
    { read -r head_repo; read -r head_ref; } <<<"$head"
    [ -n "$head_repo" ] || reject "pull request without a head repository"
    [ "$head_repo" = "$repository" ] || reject "pull request from $head_repo"
    if [ "$label" = rh-big ]; then
      case "$head_ref" in
        batch/*) ;;
        *) reject "pull request from branch ${head_ref:-unset}, which build.yml sends to rh-pr-trusted" ;;
      esac
    fi ;;
  *) reject "event ${event:-unset}" ;;
esac
echo "Self-hosted runner $(hostname) ($label): ${event} of ${GITHUB_REF} at ${GITHUB_SHA:-?}"
