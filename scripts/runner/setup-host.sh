#!/bin/bash
# Set up (or update) a host for the self-hosted GitHub Actions runner of the merge queue.
# Run as root, from a copy of this directory: `bash setup-host.sh`. It is idempotent.
#
# The host holds no credential of the project. It runs one ephemeral just-in-time runner at a
# time as the unprivileged user ghrunner, which gets a fresh home directory for every job (see
# loop.sh). It gets each job's one-time runner configuration from the spool directory, which a
# trusted workstation fills (mint-jit.sh). See CACHE.md, "Self-hosted merge queue runner".
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
VERSION=2.338.2
SHA256=baebf204307bac6193480852732f0aba2ae97b6c5597c244f4d5558390147c40
U=ghrunner

[ "$(id -u)" = 0 ] || { echo "run as root" >&2; exit 1; }

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
install -d -m 0700 -o root -g root /var/lib/rh-runner /var/lib/rh-runner/spool

# No metadata service (IMDS, IPv4 and IPv6) and no private addresses for ghrunner. loop.sh
# also denies these addresses to the job's cgroup (IPAddressDeny).
cat > /usr/local/sbin/ghrunner-firewall <<EOF
#!/bin/bash
set -e
for d in 169.254.0.0/16 10.0.0.0/8 172.16.0.0/12 192.168.0.0/16 100.64.0.0/10; do
  iptables -C OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT 2>/dev/null || iptables -A OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT
done
for d in fd00::/8 fe80::/10; do
  ip6tables -C OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT 2>/dev/null || ip6tables -A OUTPUT -d \$d -m owner --uid-owner $uid -j REJECT
done
EOF
chmod 0755 /usr/local/sbin/ghrunner-firewall
cat > /etc/systemd/system/ghrunner-firewall.service <<'EOF'
[Unit]
Description=Block the metadata service and private ranges for uid ghrunner
Before=network-pre.target rh-runner.service
Wants=network-pre.target
[Service]
Type=oneshot
RemainAfterExit=yes
ExecStart=/usr/local/sbin/ghrunner-firewall
[Install]
WantedBy=multi-user.target
EOF

# A process may only ptrace its own descendants.
echo 'kernel.yama.ptrace_scope = 1' > /etc/sysctl.d/60-ptrace-scope.conf
sysctl -q -p /etc/sysctl.d/60-ptrace-scope.conf

# No cron or at jobs for ghrunner, so nothing outlives a job.
for f in /etc/cron.deny /etc/at.deny; do
  grep -qx "$U" "$f" 2>/dev/null || echo "$U" >> "$f"
done

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

systemctl daemon-reload
systemctl enable --now ghrunner-firewall.service
systemctl enable rh-runner.service
systemctl restart rh-runner.service
echo "set up: $(cat /opt/rh-runner/actions-runner/.version), uid $uid"
