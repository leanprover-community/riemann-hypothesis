#!/usr/bin/env python3
"""Test the build-log check with Lake's source diagnostic and replay formats."""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check-build-log.py"
KNOWN_SUGGESTION = (
    "info: src/New/Spanning/MainTerm/GlobalSieve.lean:294:25: Try this:\n"
    "  [apply] ring_nf\n"
)


class CheckBuildLog(unittest.TestCase):
    def run_check(self, log):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "build.log"
            path.write_text(log, encoding="utf-8")
            return subprocess.run(
                [sys.executable, "-I", str(SCRIPT), str(path)], capture_output=True, text=True
            )

    def test_allows_warnings_build_status_and_known_suggestion(self):
        result = self.run_check(
            "info: GRH: downloading build outputs\n"
            "warning: src/New/Example.lean:3:0: unused variable `h`\n"
            "info: .lake/packages/mathlib/Mathlib/Example.lean:3:0: Nat : Type\n"
            "ℹ [51/52] Replayed New.Spanning.MainTerm.GlobalSieve\n"
            + KNOWN_SUGGESTION
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_allows_known_suggestion_with_dot_slash_prefix(self):
        result = self.run_check(KNOWN_SUGGESTION.replace("info: src/", "info: ./src/"))
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_allows_known_suggestion_after_the_tactic_moves(self):
        result = self.run_check(KNOWN_SUGGESTION.replace(":294:25:", ":305:17:"))
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_does_not_exempt_the_same_suggestion_in_another_file(self):
        diagnostic = KNOWN_SUGGESTION.replace("GlobalSieve.lean", "Other.lean")
        result = self.run_check(KNOWN_SUGGESTION + diagnostic)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("Other.lean", result.stderr)

    def test_does_not_exempt_an_additional_matching_suggestion(self):
        diagnostic = KNOWN_SUGGESTION.replace(":294:25:", ":305:17:")
        result = self.run_check(KNOWN_SUGGESTION + diagnostic)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(":305:17:", result.stderr)

    def test_rejects_new_source_info_alongside_known_suggestion(self):
        diagnostic = "info: src/New/Example.lean:5:0: Nat : Type"
        result = self.run_check(KNOWN_SUGGESTION + diagnostic)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(diagnostic, result.stderr)
        self.assertNotIn("GlobalSieve", result.stderr)

    def test_does_not_exempt_a_different_suggestion_at_the_same_position(self):
        diagnostic = KNOWN_SUGGESTION.replace("ring_nf", "exact h")
        result = self.run_check(diagnostic)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("GlobalSieve", result.stderr)


if __name__ == "__main__":
    unittest.main()
