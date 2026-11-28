"""Check which pull request changes can reuse a merge-queue build."""
import argparse
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch


spec = importlib.util.spec_from_file_location("ci_github", Path(__file__).resolve().parents[1] / "ci-github.py")
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)


class PullRequestChecks(unittest.TestCase):
    def test_scope(self):
        for paths, expected in [
            (["README.md"], (True, "full")),
            (["scripts/inbox-sync.py", "scripts/tests/test_inbox_sync.py"], (True, "affected")),
            ([".github/workflows/inbox.yml"], (True, "affected")),
            (["GUIDE.md", "src/New/Lemma.lean"], (False, "full")),
            (["src/Lib/A.lean", "scripts/batch-labels.py"], (False, "affected")),
            (["scripts/ci-cache-get.py"], (False, "affected")),
            (["scripts/tests/.gv-dependencies.yaml", "README.md"], (False, "policy")),
            (["scripts/tests/selective.json"], (False, "policy")),
            (["scripts/PrintAxioms.lean", "INDEX.md"], (False, "full")),
        ]:
            with self.subTest(paths=paths):
                self.assertEqual(ci.pr_scope(set(paths)), expected)
        for path in ["Challenge.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
                     ".github/workflows/build.yml", "scripts/ci-github.py", "unrecognized"]:
            with self.subTest(path=path):
                self.assertEqual(ci.pr_scope({path}), (False, "full"))

    def test_base_evidence(self):
        base = "1" * 40
        for parent, changed, runs, problem, expected in [
            (base, b"README.md\0", [{"event": "merge_group"}], None, ("true", "full")),
            (base, b"scripts/github-rest.py\0", [{"event": "merge_group"}], None, ("true", "affected")),
            (base, b"README.md\0", [{"event": "merge_group"}], "wrong job", ("false", "full")),
            (base, b"README.md\0", [{"event": "pull_request"}], None, ("false", "full")),
            (base, b"README.md\0", [], None, ("false", "full")),
            (base, b"README.md\0", OSError("offline"), None, ("false", "full")),
            ("2" * 40, b"README.md\0", [], None, ("false", "full")),
            (base, b"src/A.lean\0README.md\0", [], None, ("false", "full")),
            (base, b"odd\nname\0README.md\0", [], None, ("false", "full")),
        ]:
            with (self.subTest(parent=parent, changed=changed, runs=runs, problem=problem),
                  patch.object(ci.subprocess, "check_output", side_effect=[parent, changed]) as git,
                  patch.object(ci, "runs") as lookup,
                  patch.object(ci, "problem", return_value=problem) as check,
                  patch.object(ci, "outputs") as outputs):
                if isinstance(runs, Exception):
                    lookup.side_effect = runs
                else:
                    lookup.return_value = runs
                ci.pr_checks(argparse.Namespace(sha=base))
                outputs.assert_called_once_with(tested=expected[0], tests=expected[1])
                if parent == base:
                    self.assertIn("--no-renames", git.call_args.args[0])
                if check.called:
                    self.assertEqual(check.call_args.args[1], base)
                if changed.startswith((b"src/", b"odd")) or parent != base:
                    lookup.assert_not_called()


if __name__ == "__main__":
    unittest.main()
