#!/usr/bin/env python3
"""Tests for the clean-input check of scripts/ci-cache-get.py."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("ci-cache-get.py")
spec = importlib.util.spec_from_file_location("ci_cache_get", SCRIPT)
cache_get = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache_get)


class CurrentIdentity(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        (self.root / "src/Dir").mkdir(parents=True)
        (self.root / "src/Dir/A.lean").write_text("theorem a : True := trivial\n")
        (self.root / "lakefile.toml").write_text('name = "fixture"\nsrcDir = "src"\n')
        (self.root / "lake-manifest.json").write_text("{}\n")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.37.0-rc1\n")
        self.git("init", "-q")
        self.git("add", ".")
        self.git("-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-q", "-m", "fixture")
        self.clean = cache_get.current_identity(self.root)

    def git(self, *args):
        subprocess.run(["git", "-C", str(self.root), *args], check=True)

    def test_untracked_non_lean_files_do_not_block_the_cache(self):
        (self.root / "src/.DS_Store").write_bytes(b"\0")
        (self.root / "src/Dir/.DS_Store").write_bytes(b"\0")
        (self.root / "src/Dir/A.lean~").write_text("backup\n")
        self.assertEqual(cache_get.current_identity(self.root), self.clean)

    def test_untracked_lean_file_is_refused_and_named(self):
        (self.root / "src/Dir/₂New.lean").write_text("theorem b : True := trivial\n")
        with self.assertRaisesRegex(ValueError, "src/Dir/₂New.lean"):
            cache_get.current_identity(self.root)

    def test_ignored_untracked_lean_file_is_still_refused(self):
        (self.root / ".git/info/exclude").write_text("Scratch.lean\n")
        (self.root / "src/Scratch.lean").write_text("theorem c : True := trivial\n")
        with self.assertRaisesRegex(ValueError, "src/Scratch.lean"):
            cache_get.current_identity(self.root)

    def test_long_list_is_shortened(self):
        for index in range(5):
            (self.root / f"src/New{index}.lean").write_text("\n")
        with self.assertRaisesRegex(ValueError, r"src/New2\.lean and 2 more\Z"):
            cache_get.current_identity(self.root)

    def test_modified_tracked_source_is_still_refused(self):
        (self.root / "src/Dir/A.lean").write_text("theorem a : True := True.intro\n")
        with self.assertRaises(subprocess.CalledProcessError):
            cache_get.current_identity(self.root)


if __name__ == "__main__":
    unittest.main()
