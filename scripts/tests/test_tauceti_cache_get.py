"""Tests that Tau Ceti imports are read from Lean's parsed module headers."""
import importlib.util
import os
from pathlib import Path
import shutil
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tauceti-cache-get.py"
spec = importlib.util.spec_from_file_location("tauceti_cache_get", SCRIPT)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


@unittest.skipIf(not shutil.which("lean") and not os.environ.get("CI"), "Lean must be on PATH")
class LeanImportHeaders(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name).resolve()
        (self.root / "src").mkdir()
        for name in cache.TRUSTED_FILES:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("module\n\nimport Mathlib\n", encoding="utf-8")

    def tearDown(self):
        self.directory.cleanup()

    def write_tauceti(self, module, source="module\n\nimport Mathlib\n"):
        path = (self.root / ".lake" / "packages" / "TauCeti").joinpath(
            *module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return path

    def parse(self, source):
        path = self.root / "src" / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return cache.import_headers(self.root)

    def test_comments_multiline_modifiers_and_same_line_imports(self):
        imports = self.parse("""module

import Mathlib -- TauCeti.LineComment
/-
import TauCeti.BlockComment
/- nested import TauCeti.NestedComment -/
-/
public
  import TauCeti.PublicModule -- trailing comment
meta import all TauCeti.MetaModule import TauCeti.SecondModule
import
  TauCeti.MultilineModule
""")
        self.assertEqual(imports["src/Probe.lean"], [
            "TauCeti.PublicModule", "TauCeti.MetaModule", "TauCeti.SecondModule",
            "TauCeti.MultilineModule"
        ])

    def test_ignores_text_after_header(self):
        imports = self.parse("""module

import Mathlib
#eval "import TauCeti.StringBody"
import TauCeti.AfterHeader
""")
        self.assertEqual(imports["src/Probe.lean"], [])

    def test_trusted_files_are_checked_using_parsed_headers(self):
        challenge = self.root / "Challenge.lean"
        challenge.write_text("""module

import Mathlib
/-
import TauCeti.Fake
-/
""", encoding="utf-8")
        imports = cache.import_headers(self.root)
        cache.check_trusted_files(imports)

        challenge.write_text(
            "module\n\nimport Mathlib\npublic import TauCeti.StatementDependency -- comment\n",
            encoding="utf-8")
        imports = cache.import_headers(self.root)
        with self.assertRaisesRegex(ValueError, "TauCeti.StatementDependency"):
            cache.check_trusted_files(imports)

    def test_imported_modules_are_deduplicated_and_transitively_closed(self):
        self.write_tauceti("TauCeti")
        self.write_tauceti("TauCeti.Shared", """module

/-
import TauCeti.CommentedOut
-/
import TauCeti.PrivateDep -- shake: keep
""")
        self.write_tauceti("TauCeti.Other")
        self.write_tauceti("TauCeti.PrivateDep")
        (self.root / "src" / "A.lean").write_text(
            "module\n\nimport TauCeti\nimport TauCeti.Shared\n", encoding="utf-8")
        (self.root / "src" / "B.lean").write_text(
            "module\n\nimport TauCeti.Shared\nimport TauCeti.Other\n", encoding="utf-8")
        self.assertEqual(cache.imported_modules(cache.import_headers(self.root), self.root), [
            "TauCeti", "TauCeti.Other", "TauCeti.PrivateDep", "TauCeti.Shared"
        ])

    def test_missing_tauceti_module_fails_closed(self):
        (self.root / "src" / "A.lean").write_text(
            "module\n\nimport TauCeti.Missing\n", encoding="utf-8")
        imports = cache.import_headers(self.root)
        with self.assertRaisesRegex(ValueError, "TauCeti.Missing is imported"):
            cache.imported_modules(imports, self.root)

    def test_missing_trusted_file_fails_closed(self):
        (self.root / "src" / "Statements.lean").unlink()
        imports = cache.import_headers(self.root)
        with self.assertRaisesRegex(ValueError, "src/Statements.lean is missing"):
            cache.check_trusted_files(imports)

    def test_invalid_import_header_fails_closed(self):
        probe = self.root / "src" / "Probe.lean"
        probe.write_text("public import TauCeti.BadWithoutModule\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "module-header parse error"):
            cache.import_headers(self.root)

    def test_invalid_tauceti_header_fails_closed(self):
        self.write_tauceti("TauCeti.Bad", "public import TauCeti.BadWithoutModule\n")
        (self.root / "src" / "A.lean").write_text(
            "module\n\nimport TauCeti.Bad\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "module-header parse error"):
            cache.import_headers(self.root)


if __name__ == "__main__":
    unittest.main()
