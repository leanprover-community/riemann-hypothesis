#!/bin/bash
# Run one ephemeral just-in-time GitHub Actions runner per job, forever (root).
#
# For each job: take the oldest one-time runner configuration from the spool (filled by
# mint-jit.sh on a trusted workstation), give the runner user a fresh home directory with a fresh
# copy of the runner, run the runner as that user in a transient systemd unit until it has run its
# one job, then kill whatever the job left running and delete the home directory again.
#
# `loop.sh` (rh-runner.service) is the rh-big runner: user ghrunner, spool
# /var/lib/rh-runner/spool, all CPUs. `loop.sh <instance>` (rh-runner@<instance>.service) is one
# of several runners on a shared host: user ghrunner-<instance>, spool
# /var/lib/rh-runner/<instance>/spool, and the label, CPUs and memory limit in
# /etc/rh-runner/<instance>.env (written by setup-host.sh). Each instance has its own user, so
# wiping one instance's processes and files never touches another's.
set -uo pipefail
instance=${1:-}
if [ -z "$instance" ]; then
  U=ghrunner
  SPOOL=/var/lib/rh-runner/spool
  RUN=/run/rh-runner
  JOB_UNIT=rh-runner-job
  LABEL=rh-big
  CPUS=""
  MEMORY_MAX=470G
else
  [[ $instance =~ ^[a-z0-9]+$ ]] || { echo "bad instance name $instance" >&2; exit 1; }
  U=ghrunner-$instance
  SPOOL=/var/lib/rh-runner/$instance/spool
  RUN=/run/rh-runner-$instance
  JOB_UNIT=rh-runner-job-$instance
  # LABEL, CPUS (a cpuset list such as 0-37) and MEMORY_MAX.
  # shellcheck disable=SC1090
  . "/etc/rh-runner/$instance.env"
fi
H=/home/$U
MAX_AGE=$((20 * 3600))  # GitHub deletes a just-in-time runner that has not connected for a day.

log() { echo "$(date -u +%FT%TZ) $*"; }

# The number of CPUs in a cpuset list such as 0-37,64.
cpu_count() {
  local n=0 part
  for part in ${1//,/ }; do
    if [[ $part == *-* ]]; then n=$((n + ${part#*-} - ${part%-*} + 1)); else n=$((n + 1)); fi
  done
  echo "$n"
}

wipe() {
  local pids
  pids=$(pgrep -u "$U" || true)
  if [ -n "$pids" ]; then
    # shellcheck disable=SC2086
    kill -KILL $pids 2>/dev/null || true
    sleep 1
  fi
  rm -rf --one-file-system "$H"
  install -d -m 0700 -o "$U" -g "$U" "$H"
  find /dev/shm /tmp /var/tmp -xdev -user "$U" -delete 2>/dev/null || true
}

install -d -m 0700 -o root -g root "$RUN"
wipe
while true; do
  config=""
  for f in $(ls -1 "$SPOOL" 2>/dev/null | grep -E '^[0-9]+-[0-9]+\.jit$' | sort -n); do
    created=${f%%-*}
    if [ $(( $(date +%s) - created )) -lt "$MAX_AGE" ]; then
      config=$SPOOL/$f
      break
    fi
  done
  if [ -z "$config" ]; then
    sleep 5
    continue
  fi
  name=$(basename "$config" .jit)
  # Use each configuration once, even if the runner fails to start.
  umask 077
  printf 'ACTIONS_RUNNER_INPUT_JITCONFIG=%s\n' "$(cat "$config")" > "$RUN/job.env"
  printf 'ACTIONS_RUNNER_HOOK_JOB_STARTED=/opt/rh-runner/job-started.sh\n' >> "$RUN/job.env"
  # Tells the hook which jobs this runner may run.
  printf 'RH_RUNNER_LABEL=%s\n' "$LABEL" >> "$RUN/job.env"
  rm -f "$config"
  umask 022
  cp -a /opt/rh-runner/actions-runner "$H/runner"
  chown -R "$U:$U" "$H/runner"
  # Confines the job to the instance's CPUs (a cgroup cpuset, which the job cannot widen), and
  # sizes Lean's thread pool to them.
  cpus=()
  if [ -n "$CPUS" ]; then
    cpus=(-p AllowedCPUs="$CPUS" -p Environment="LEAN_NUM_THREADS=$(cpu_count "$CPUS")")
  fi
  log "starting runner $name"
  systemd-run --unit="$JOB_UNIT" --quiet --wait --collect --uid="$U" --gid="$U" "${cpus[@]}" \
    -p WorkingDirectory="$H/runner" -p EnvironmentFile="$RUN/job.env" \
    -p Environment="HOME=$H" -p Environment="USER=$U" -p Environment="LANG=C.UTF-8" \
    -p Environment="PATH=/usr/local/bin:/usr/bin:/bin" \
    -p PrivateTmp=yes -p NoNewPrivileges=yes -p ProtectSystem=strict -p ProtectHome=tmpfs \
    -p BindPaths="$H" -p InaccessiblePaths=/srv -p InaccessiblePaths=-/etc/rh-buildq \
    -p PrivateDevices=yes -p ProtectKernelTunables=yes -p ProtectKernelModules=yes \
    -p ProtectKernelLogs=yes -p ProtectControlGroups=yes -p ProtectClock=yes -p RestrictSUIDSGID=yes \
    -p IPAddressDeny="169.254.0.0/16 10.0.0.0/8 172.16.0.0/12 192.168.0.0/16 100.64.0.0/10 fd00::/8 fe80::/10" \
    -p LimitNOFILE=1048576 -p LimitSTACK=infinity -p TasksMax=infinity -p MemoryMax="$MEMORY_MAX" \
    -p KillMode=control-group -p RuntimeMaxSec=8h \
    -p StandardOutput=journal -p StandardError=journal \
    "$H/runner/run.sh"
  log "runner $name exited $?"
  rm -f "$RUN/job.env"
  wipe
done
