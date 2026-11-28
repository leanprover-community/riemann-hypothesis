#!/usr/bin/env python3
"""Report new Mathlib text-style diagnostics in Lean files between BASE and HEAD."""
import argparse
from collections import Counter
from pathlib import Path
import subprocess
import tempfile


def git(*args):
    return subprocess.check_output(["git", *args])


def changes(base):
    fields = git("diff", "--name-status", "-z", "--find-renames", "--diff-filter=AMRT",
                 base, "HEAD", "--", "src/").decode().split("\0")
    entries = iter(fields[:-1])
    for status in entries:
        path = next(entries)
        target = next(entries) if status.startswith("R") else path
        if target.endswith(".lean"):
            old = path if status != "A" and path.endswith(".lean") else None
            yield old, target


def lean(mode, *args):
    return ["lake", "env", "lean", "--run", "scripts/LintStyle.lean", mode, *args]


def lint(root, paths):
    if not paths:
        return []
    result = subprocess.run(lean("text", root, *paths), capture_output=True)
    stdout = result.stdout.decode("utf-8")
    if result.returncode:
        raise SystemExit(stdout + result.stderr.decode("utf-8") or "Mathlib's text linter failed.")
    # The diagnostics include literal offending characters, including line separators.
    records = (line.removesuffix("\r") for line in stdout.split("\n"))
    return [line.split(" : ", 3) for line in records if line]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", metavar="BASE")
    args = parser.parse_args()
    base = git("rev-parse", "--verify", "--end-of-options", args.base + "^{commit}").decode().strip()
    changed = list(changes(base))
    if not changed:
        return 0

    old_paths = {}
    new_paths = []
    checked_names = []
    with tempfile.TemporaryDirectory(prefix="grh-lint-style-") as temporary:
        for old, new in changed:
            name = new.removeprefix("src/")
            path = Path(new)
            if path.is_symlink() or not path.is_file():
                raise SystemExit(f"Expected a regular Lean source file: {new}")
            new_paths.append(name)
            if old != new:
                checked_names.append(name)
            if old is not None:
                old_name = old.removeprefix("src/")
                old_paths[old_name] = name
                snapshot = Path(temporary) / old_name
                snapshot.parent.mkdir(parents=True, exist_ok=True)
                snapshot.write_bytes(git("show", f"{base}:{old}"))
        inherited = Counter((old_paths[path], code, message)
                            for path, _, code, message in lint(temporary, list(old_paths)))

    if checked_names and subprocess.run(lean("names", *checked_names)).returncode:
        return 1
    failures = 0
    for path, location, code, message in lint("src", new_paths):
        diagnostic = path, code, message
        if inherited[diagnostic]:
            inherited[diagnostic] -= 1
        else:
            print(f"src/{path}:{location.removeprefix('line ')}: {message}")
            failures += 1
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
