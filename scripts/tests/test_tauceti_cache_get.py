"""Check the Tau Ceti restore when a published artifact is missing."""
import importlib.util
import os
from pathlib import Path
import unittest
from unittest.mock import patch


script = Path(__file__).resolve().parents[1] / "tauceti-cache-get.py"
spec = importlib.util.spec_from_file_location("tauceti_cache_get", script)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)


class TauCetiCacheTests(unittest.TestCase):
    def test_missing_artifact(self):
        def lake_with_missing_artifact(args, env):
            if args[:2] == ["cache", "get"]:
                return 0
            self.assertEqual(args[:2], ["-q", "build"])
            self.assertIn("TauCeti.Probe", args)
            return 3 if "--no-build" in args else 0

        with (
            patch.object(cache, "check_trusted_files"),
            patch.object(cache, "check_mathlib_pin"),
            patch.object(cache, "imported_modules", return_value=["TauCeti.Probe"]),
            patch.object(cache, "run_lake", side_effect=lake_with_missing_artifact),
        ):
            for env, expected in [({}, 0), ({"RH_REQUIRE_TAUCETI_CACHE": "1"}, 3)]:
                with self.subTest(env=env), patch.dict(os.environ, env, clear=True):
                    self.assertEqual(cache.main(), expected)


if __name__ == "__main__":
    unittest.main()
