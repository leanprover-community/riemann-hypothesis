#!/bin/bash
# The runner's job-started hook (ACTIONS_RUNNER_HOOK_JOB_STARTED), run before any step of a job.
# A non-zero exit fails the job before any of its code runs.
#
# Pull requests can change the workflow they run, so a pull request could ask for this runner.
# Only these jobs may run here: the merge queue (merge_group on main's queue), pushes to main,
# manual runs (workflow_dispatch, which needs write access), and pull requests whose head branch
# is in this repository (pushing one needs write access too), all of build.yml in this
# repository. A pull request from a fork is refused. Its head repository is read from the event
# payload at $GITHUB_EVENT_PATH, which GitHub writes and the pull request cannot change.
set -u
repository=leanprover-community/riemann-hypothesis
reject() {
  echo "::error::This self-hosted runner only runs build.yml for the merge queue, pushes to main, manual runs and pull requests from branches of $repository ($1)."
  exit 1
}
[ "${GITHUB_REPOSITORY:-}" = "$repository" ] || reject "repository ${GITHUB_REPOSITORY:-unset}"
case "${GITHUB_WORKFLOW_REF:-}" in
  "$repository/.github/workflows/build.yml@"*) ;;
  *) reject "workflow ${GITHUB_WORKFLOW_REF:-unset}" ;;
esac
case "${GITHUB_EVENT_NAME:-}" in
  merge_group)
    case "${GITHUB_REF:-}" in
      refs/heads/gh-readonly-queue/main/*) ;;
      *) reject "merge group ref ${GITHUB_REF:-unset}" ;;
    esac ;;
  push)
    [ "${GITHUB_REF:-}" = refs/heads/main ] || reject "push to ${GITHUB_REF:-unset}" ;;
  workflow_dispatch) ;;
  pull_request)
    # Prints the head repository's full name, or nothing if it is missing or null.
    head=$(python3 -I -c '
import json, sys
with open(sys.argv[1]) as stream:
    repo = ((json.load(stream).get("pull_request") or {}).get("head") or {}).get("repo") or {}
name = repo.get("full_name")
print(name if isinstance(name, str) else "")
' "${GITHUB_EVENT_PATH:-/nonexistent}" 2>/dev/null) || reject "pull request event payload ${GITHUB_EVENT_PATH:-unset} unreadable"
    [ -n "$head" ] || reject "pull request without a head repository"
    [ "$head" = "$repository" ] || reject "pull request from $head" ;;
  *) reject "event ${GITHUB_EVENT_NAME:-unset}" ;;
esac
echo "Self-hosted runner $(hostname): ${GITHUB_EVENT_NAME} of ${GITHUB_REF} at ${GITHUB_SHA:-?}"
