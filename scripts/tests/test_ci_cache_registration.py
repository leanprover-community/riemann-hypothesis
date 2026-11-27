#!/usr/bin/env python3
"""Tests for the Lake input-to-artifact registration shortcut.

The JSON fixtures use the format written by Lake 4.37's `cache add`.
Run with `python3 -I scripts/tests/test_ci_cache_registration.py`.
"""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "ci-cache-get.py"
spec = importlib.util.spec_from_file_location("ci_cache_get", SCRIPT)
assert spec is not None and spec.loader is not None
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)

INPUT = "0123456789abcdef"
WANTED = "aaaaaaaaaaaaaaaa.ltar"
OTHER = "bbbbbbbbbbbbbbbb.ltar"


class Registration(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.cache = Path(self.tmp.name)

    def write(self, local_scope, data, **metadata):
        path = self.cache / "outputs" / local_scope / f"{INPUT}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"schemaVersion": "2026-02-25", "service": "grh-lean",
                                    "scope": cache.SCOPE, "data": data, **metadata}))

    def registered(self):
        return cache.registered(self.cache, [(INPUT, WANTED)])

    def test_other_package_mapping_does_not_hide_wrong_project_mapping(self):
        self.write("GRH", OTHER)
        self.write("TauCeti", WANTED)
        self.assertEqual(self.registered(), set())

    def test_hash_in_scope_metadata_does_not_hide_wrong_data(self):
        self.write("GRH", OTHER, scope="remote/aaaaaaaaaaaaaaaa")
        self.assertEqual(self.registered(), set())

    def test_matching_project_mapping_is_reused(self):
        self.write("GRH", WANTED)
        self.assertEqual(self.registered(), {INPUT})

    def test_matching_data_with_wrong_remote_scope_is_rewritten(self):
        self.write("GRH", WANTED, scope="different/scope")
        self.assertEqual(self.registered(), set())

    def test_schema_mismatches_are_rewritten(self):
        for metadata in ({"schemaVersion": "old"}, {"service": "other"},
                         {"service": None}, {"extra": True}):
            with self.subTest(metadata=metadata):
                self.write("GRH", WANTED, **metadata)
                self.assertEqual(self.registered(), set())

    def test_duplicate_keys_and_invalid_encoding_are_rewritten(self):
        self.write("GRH", WANTED)
        path = self.cache / "outputs" / "GRH" / f"{INPUT}.json"
        for contents in (b'{"data": 1, "data": 2}', bytes([255])):
            with self.subTest(contents=contents):
                path.write_bytes(contents)
                self.assertEqual(self.registered(), set())

    def test_deeply_nested_json_is_rewritten(self):
        self.write("GRH", WANTED)
        path = self.cache / "outputs" / "GRH" / f"{INPUT}.json"
        for closing in ("]" * 20000, ""):
            with self.subTest(complete=bool(closing)):
                path.write_text("[" * 20000 + "0" + closing)
                self.assertEqual(self.registered(), set())

    def test_malformed_json_is_rewritten(self):
        self.write("GRH", WANTED)
        path = self.cache / "outputs" / "GRH" / f"{INPUT}.json"
        path.write_text('{"data":"aaaaaaaaaaaaaaaa.ltar"')
        self.assertEqual(self.registered(), set())


if __name__ == "__main__":
    unittest.main()
