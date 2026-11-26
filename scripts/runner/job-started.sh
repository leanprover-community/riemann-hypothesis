#!/bin/bash
# The runner's job-started hook (ACTIONS_RUNNER_HOOK_JOB_STARTED), run before any step of a job.
# A non-zero exit fails the job before any of its code runs.
#
# Pull requests can change the workflow they run, so a pull request could ask for this runner.
# Only these jobs may run here: the merge queue (merge_group on main's queue), pushes to main,
# and manual runs (workflow_dispatch, which needs write access), all of build.yml in this
# repository.
set -u
repository=leanprover-community/riemann-hypothesis
reject() {
  echo "::error::This self-hosted runner only runs build.yml for the merge queue, pushes to main and manual runs ($1)."
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
  *) reject "event ${GITHUB_EVENT_NAME:-unset}" ;;
esac
echo "Self-hosted runner $(hostname): ${GITHUB_EVENT_NAME} of ${GITHUB_REF} at ${GITHUB_SHA:-?}"
