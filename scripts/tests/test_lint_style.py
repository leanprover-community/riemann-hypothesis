#!/usr/bin/env python3
"""Exercise the style gate with Git snapshots and Mathlib-shaped diagnostics."""

from contextlib import chdir, redirect_stdout
import importlib.util
from io import StringIO
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "lint-style.py"
spec = importlib.util.spec_from_file_location("lint_style", SCRIPT)
style = importlib.util.module_from_spec(spec)
spec.loader.exec_module(style)

# Mathlib's exceptions-file format carries the offending character as literal text.
TEXT_LINTER = r"""
from pathlib import Path
import sys
root, *names = sys.argv[1:]
for name in names:
    lines = (Path(root) / name).read_bytes().decode("utf-8").split("\n")
    for number, line in enumerate(lines, 1):
        for character in "\u2028\u2029\r":
            if character in line:
                print(f"{name} : line {number} : ERR_UNICODE : Unwanted character '{character}'")
"""


class TestLintStyle(unittest.TestCase):
    def git(self, *args):
        return subprocess.check_output(["git", *args], text=True).strip()

    def commit(self, content, message):
        path = Path("src/New/Example.lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content.encode("utf-8"))
        self.git("add", str(path))
        self.git("-c", "user.name=Linter Test", "-c", "user.email=lint@example.invalid",
                 "commit", "-qm", message)
        return self.git("rev-parse", "HEAD")

    def linter_command(self, mode, *args):
        self.assertEqual(mode, "text")
        return [sys.executable, "-I", "-c", TEXT_LINTER, *args]

    def run_check(self, before, after):
        with tempfile.TemporaryDirectory() as directory, chdir(directory):
            self.git("init", "-q")
            base = self.commit(before, "base")
            self.commit(after, "head")
            with (patch.object(style, "lean", side_effect=self.linter_command),
                  patch.object(sys, "argv", [str(SCRIPT), base]),
                  redirect_stdout(StringIO()) as output):
                return style.main(), output.getvalue()

    def test_accepts_removing_or_moving_an_existing_diagnostic(self):
        source = "-- Existing line separator: \u2028.\n"
        for edited in ("-- Clean.\n", f"-- Inserted line.\n{source}"):
            with self.subTest(edited=edited):
                self.assertEqual(self.run_check(source, edited), (0, ""))

    def test_reports_new_diagnostics_containing_newline_like_characters(self):
        for character in ("\u2028", "\u2029", "\r"):
            with self.subTest(character=repr(character)):
                status, output = self.run_check("-- Clean.\n", f"-- New separator: {character}.\n")
                self.assertEqual(status, 1)
                self.assertIn(f"src/New/Example.lean:1: Unwanted character '{character}'", output)


if __name__ == "__main__":
    unittest.main()
