#!/bin/bash
# Set up (or update) a host for a self-hosted GitHub Actions runner. Run as root, from a copy of
# this directory. It is idempotent, and restarts the runner it sets up (killing a running job).
#
#   bash setup-host.sh
#       the rh-big runner of the merge queue: user ghrunner, rh-runner.service, all CPUs;
#   bash setup-host.sh <instance> <label> <cpus> <memory-max>
#       one of several runners on a shared host, for example
#       `bash setup-host.sh pr1 rh-pr-trusted 0-37 150G`: user ghrunner-<instance>,
#       rh-runner@<instance>.service, confined to the cpuset <cpus> and to <memory-max> of memory.
#
# The host holds no credential of the project. Each runner runs one ephemeral just-in-time runner
# at a time as its own unprivileged user, which gets a fresh home directory for every job (see
# loop.sh). It gets each job's one-time runner configuration from its spool directory, which a
# trusted workstation fills (mint-jit.sh). See CACHE.md, "Self-hosted runners".
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
VERSION=2.338.2
SHA256=baebf204307bac6193480852732f0aba2ae97b6c5597c244f4d5558390147c40

[ "$(id -u)" = 0 ] || { echo "run as root" >&2; exit 1; }
instance=${1:-}
if [ -z "$instance" ]; then
  U=ghrunner
  spool=/var/lib/rh-runner/spool
  firewall=ghrunner-firewall
  service=rh-runner.service
else
  [ $# = 4 ] || { echo "usage: setup-host.sh [<instance> <label> <cpus> <memory-max>]" >&2; exit 1; }
  label=$2 cpus=$3 memory_max=$4
  [[ $instance =~ ^[a-z0-9]+$ ]] || { echo "bad instance name $instance" >&2; exit 1; }
  case "$label" in rh-big | rh-pr-trusted) ;; *) echo "unknown label $label" >&2; exit 1 ;; esac
  [[ $cpus =~ ^[0-9]+(-[0-9]+)?(,[0-9]+(-[0-9]+)?)*$ ]] || { echo "bad cpuset $cpus" >&2; exit 1; }
  [[ $memory_max =~ ^[0-9]+[KMGT]$ ]] || { echo "bad memory limit $memory_max" >&2; exit 1; }
  U=ghrunner-$instance
  spool=/var/lib/rh-runner/$instance/spool
  firewall=ghrunner-firewall-$instance
  service=rh-runner@$instance.service
fi

# The user: no sudo, no password, no other groups.
if ! id "$U" >/dev/null 2>&1; then
  useradd --create-home --home-dir /home/$U --shell /bin/bash --user-group "$U"
fi
passwd -l "$U" >/dev/null
chmod 0700 /home/$U
if id -nG "$U" | tr ' ' '\n' | grep -qvx "$U"; then
  echo "$U must not be in any group but its own" >&2; exit 1
fi
uid=$(id -u "$U")

# The pristine runner, owned by root. loop.sh copies it into the fresh home for each job.
install -d -m 0755 /opt/rh-runner
if [ "$(cat /opt/rh-runner/actions-runner/.version 2>/dev/null)" != "$VERSION" ]; then
  tmp=$(mktemp -d)
  curl -fsSL -o "$tmp/runner.tar.gz" \
    "https://github.com/actions/runner/releases/download/v$VERSION/actions-runner-linux-x64-$VERSION.tar.gz"
  echo "$SHA256  $tmp/runner.tar.gz" | sha256sum --check --quiet
  rm -rf /opt/rh-runner/actions-runner.new
  mkdir /opt/rh-runner/actions-runner.new
  tar -xzf "$tmp/runner.tar.gz" -C /opt/rh-runner/actions-runner.new
  rm -rf "$tmp"
  /opt/rh-runner/actions-runner.new/bin/installdependencies.sh >/dev/null
  echo "$VERSION" > /opt/rh-runner/actions-runner.new/.version
  chown -R root:root /opt/rh-runner/actions-runner.new
  chmod -R go-w /opt/rh-runner/actions-runner.new
  rm -rf /opt/rh-runner/actions-runner
  mv /opt/rh-runner/actions-runner.new /opt/rh-runner/actions-runner
fi
install -m 0755 -o root -g root "$here/loop.sh" /opt/rh-runner/loop.sh
install -m 0755 -o root -g root "$here/job-started.sh" /opt/rh-runner/job-started.sh

# The spool of one-time runner configurations: root only.
install -d -m 0700 -o root -g root /var/lib/rh-runner "$(dirname "$spool")" "$spool"
if [ -n "$instance" ]; then
  install -d -m 0755 -o root -g root /etc/rh-runner
  printf 'LABEL=%s\nCPUS=%s\nMEMORY_MAX=%s\n' "$label" "$cpus" "$memory_max" > "/etc/rh-runner/$instance.env"
  chmod 0644 "/etc/rh-runner/$instance.env"
fi

# No metadata service (IMDS, IPv4 and IPv6) and no private addresses for the runner user.
# loop.sh also denies these addresses to the job's cgroup (IPAddressDeny).
cat > /usr/local/sbin/$firewall <<EOF
#!/bin/bash
set -e
for d in 169.254.0.0/16 10.0.0.0/8 172.16.0.0/12 192.168.0.0/16 100.64.0.0/10; do
  iptables -C OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT 2>/dev/null || iptables -A OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT
done
for d in fd00::/8 fe80::/10; do
  ip6tables -C OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT 2>/dev/null || ip6tables -A OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT
done
EOF
chmod 0755 /usr/local/sbin/$firewall
cat > /etc/systemd/system/$firewall.service <<EOF
[Unit]
Description=Block the metadata service and private ranges for uid $U
Before=network-pre.target $service
Wants=network-pre.target
[Service]
Type=oneshot
RemainAfterExit=yes
ExecStart=/usr/local/sbin/$firewall
[Install]
WantedBy=multi-user.target
EOF

# A process may only ptrace its own descendants.
echo 'kernel.yama.ptrace_scope = 1' > /etc/sysctl.d/60-ptrace-scope.conf
sysctl -q -p /etc/sysctl.d/60-ptrace-scope.conf

# No cron or at jobs for the runner user, so nothing outlives a job.
for f in /etc/cron.deny /etc/at.deny; do
  grep -qx "$U" "$f" 2>/dev/null || echo "$U" >> "$f"
done

if [ -z "$instance" ]; then
  cat > /etc/systemd/system/rh-runner.service <<'EOF'
[Unit]
Description=Ephemeral GitHub Actions runner for the merge queue (one job per runner)
After=network-online.target ghrunner-firewall.service
Wants=network-online.target
Requires=ghrunner-firewall.service
[Service]
ExecStart=/opt/rh-runner/loop.sh
Restart=always
RestartSec=10
[Install]
WantedBy=multi-user.target
EOF
else
  cat > /etc/systemd/system/rh-runner@.service <<'EOF'
[Unit]
Description=Ephemeral GitHub Actions runner %i (one job per runner)
After=network-online.target ghrunner-firewall-%i.service
Wants=network-online.target
Requires=ghrunner-firewall-%i.service
[Service]
ExecStart=/opt/rh-runner/loop.sh %i
Restart=always
RestartSec=10
[Install]
WantedBy=multi-user.target
EOF
fi

systemctl daemon-reload
systemctl enable --now "$firewall.service"
systemctl enable "$service"
systemctl restart "$service"
echo "set up $service: $(cat /opt/rh-runner/actions-runner/.version), user $U, uid $uid"
