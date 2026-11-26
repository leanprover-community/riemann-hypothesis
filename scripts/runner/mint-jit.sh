#!/usr/bin/env bash
# Keep the runner host's spool of one-time runner configurations full. Run on a trusted
# workstation whose `gh` is logged in as a repository admin, every minute or so (a systemd user
# timer): `mint-jit.sh <ssh-host> [depth] [instance] [label]`. Without an instance it fills the
# rh-big runner's spool /var/lib/rh-runner/spool; with one, /var/lib/rh-runner/<instance>/spool
# (see loop.sh). The label defaults to rh-big.
#
# Each configuration comes from POST /repos/{owner}/{repo}/actions/runners/generate-jitconfig.
# It registers one ephemeral runner (labels self-hosted, linux and the label) that can run
# exactly one job; it is not a token for anything else. The host keeps no GitHub token.
# Configurations older than 20 hours are deleted, with their runner registrations, before GitHub
# expires them.
set -euo pipefail
host=${1:?usage: mint-jit.sh <ssh-host> [depth] [instance] [label]}
depth=${2:-4}
instance=${3:-}
label=${4:-rh-big}
[[ $instance =~ ^[a-z0-9]*$ && $label =~ ^[a-z0-9-]+$ ]] || { echo "bad instance or label" >&2; exit 1; }
repo=leanprover-community/riemann-hypothesis
spool=/var/lib/rh-runner${instance:+/$instance}/spool
max_age=$((20 * 3600))

listing=$(ssh -o ConnectTimeout=15 -o BatchMode=yes "$host" "ls -1 $spool" 2>/dev/null) || {
  echo "$(date -u +%FT%TZ) $host $spool unreachable; nothing minted"; exit 0; }
now=$(date +%s)
count=0
for f in $listing; do
  [[ $f =~ ^([0-9]+)-([0-9]+)\.jit$ ]] || continue
  if (( now - BASH_REMATCH[1] >= max_age )); then
    ssh -o BatchMode=yes "$host" "rm -f $spool/$f"
    gh api -X DELETE "repos/$repo/actions/runners/${BASH_REMATCH[2]}" >/dev/null 2>&1 || true
    echo "$(date -u +%FT%TZ) expired $f"
  else
    count=$((count + 1))
  fi
done
while (( count < depth )); do
  name="$label-${instance:+$instance-}$(date +%Y%m%d%H%M%S)-$RANDOM"
  response=$(gh api -X POST "repos/$repo/actions/runners/generate-jitconfig" \
    -f name="$name" -F runner_group_id=1 -f work_folder=_work \
    -f 'labels[]=self-hosted' -f 'labels[]=linux' -f "labels[]=$label")
  id=$(jq -r '.runner.id' <<<"$response")
  file="$(date +%s)-$id.jit"
  jq -r '.encoded_jit_config' <<<"$response" |
    ssh -o BatchMode=yes "$host" "umask 077; cat > $spool/.$file && mv $spool/.$file $spool/$file"
  echo "$(date -u +%FT%TZ) minted $name ($file)"
  count=$((count + 1))
done
