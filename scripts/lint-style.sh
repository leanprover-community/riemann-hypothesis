#!/usr/bin/env bash
# Runs Mathlib's text-based style linters (`lake exe mathlib/lint-style`) on every Lean file under
# src/, as .github/workflows/lint-style.yml does. Other arguments go to lint-style, so
# `scripts/lint-style.sh --fix` applies the fixes it knows. Known errors are listed in
# scripts/nolints-style.txt; `scripts/lint-style.sh --update` rewrites that list to the errors
# there are now, for example after files have been renamed.
#
# lint-style reads module A.B from A/B.lean under the working directory, and it lints the
# modules that the root module it is given imports, if their names start like the root's. Our
# modules are under src/ and have no common root, so this makes one for the run: Src is a link
# to src/, and src/Src.lean imports every module as Src.<module>. In the output, Src/ is src/.
set -euo pipefail
cd "$(dirname "$0")/.."

nolints=scripts/nolints-style.txt
tmp=$(mktemp -d)
made_link=
cleanup() {
  if [ -n "$made_link" ]; then rm -f Src; fi
  rm -f src/Src.lean
  if [ -e "$tmp/old" ]; then cp "$tmp/old" "$nolints"; fi   # an --update that did not finish
  rm -rf "$tmp"
}
trap cleanup EXIT

if [ -L Src ] || [ ! -e Src ]; then
  ln -sfn src Src   # this also replaces a link that a killed run left behind
  made_link=1
elif ! [ Src -ef src ]; then
  echo "lint-style.sh: Src is in the way: it should be missing, a link to src, or src itself" >&2
  exit 1
fi   # otherwise the file system ignores case and Src already is src
find src -name '*.lean' ! -path src/Src.lean | LC_ALL=C sort \
  | sed -e 's|^src/|import Src.|' -e 's|\.lean$||' -e 's|/|.|g' > src/Src.lean

if [ "${1-}" != --update ]; then
  lake exe mathlib/lint-style "$@" Src && exit 0 || status=$?
  echo "Src/ in these errors is src/. To apply the fixes lint-style knows, run" \
    "scripts/lint-style.sh --fix (lake exe lint-style --fix does not work here)." >&2
  exit "$status"
fi

# --update: lint-style runs with only the comment lines of the list, so that it reports every
# text error. Each is then listed once per file and message, which is how Mathlib matches them
# (it ignores the line number), keeping the first line it was seen on. Module names cannot be
# listed, so they stay errors.
cp "$nolints" "$tmp/old"
grep '^--' "$tmp/old" > "$nolints" || true
status=0
lake exe mathlib/lint-style --github Src > "$tmp/out" 2> "$tmp/err" || status=$?
sed -n 's/^::ERR file=\([^,]*\),line=\([0-9]*\),code=\([A-Z_]*\)::[^ ]* [A-Z_]*: \(.*\)$/\1 : line \2 : \3 : \4/p' \
    "$tmp/out" > "$tmp/entries"
# lint-style returns at most 125 for findings. A failed Lake invocation can also return
# nonzero, so require recognizable findings before accepting that status.
if grep -q '^uncaught exception' "$tmp/err" || [ "$status" -gt 125 ] ||
    { [ "$status" -ne 0 ] && [ ! -s "$tmp/entries" ] && ! grep -q '^error: module name ' "$tmp/err"; }; then
  cat "$tmp/out" "$tmp/err" >&2
  echo "lint-style.sh: lint-style stopped early; $nolints is unchanged" >&2
  exit 1
fi
LC_ALL=C sort -k1,1 -k4,4n "$tmp/entries" \
  | awk -F ' : ' '{ key = $1; for (i = 3; i <= NF; i++) key = key FS $i } !seen[key]++' \
  >> "$nolints"
rm "$tmp/old"
echo "$nolints now lists $(grep -vc '^--' "$nolints") known errors. Check that its diff adds none" \
  "that should be fixed instead."
grep '^error: module name' "$tmp/err" >&2 || true
