"""Cache work budgets checked without timing or network access."""

import gzip
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
INPUT_HASH = "0123456789abcdef"
ARTIFACT = "fedcba9876543210.ltar"


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, SCRIPTS / f"{filename}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


cache = load("ci-cache-get")
fetch = load("fetch-artifacts")
stage = load("ci-cache-stage")
tauceti = load("tauceti-cache-get")


class CacheIO(unittest.TestCase):
    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory())).resolve()
        self.mapping = self.root / "map.jsonl"
        cache.write_map(self.mapping, [(INPUT_HASH, ARTIFACT)])

    def test_import_scanner_only_parses_lines_that_could_match(self):
        source = self.root / "Test.lean"
        source.write_text("theorem test : True := trivial\n" * 1000
                          + "import Mathlib\n"
                          + "private import all TauCeti.Test -- keep\n"
                          + "-- import TauCeti.Comment\n")

        with patch.object(tauceti, "IMPORT", wraps=tauceti.IMPORT) as pattern:
            imports = tauceti.tauceti_imports(source)

        self.assertEqual(imports, {"TauCeti.Test"})
        # Both lines mentioning TauCeti reach the regex, including the comment it rejects.
        self.assertEqual(pattern.match.call_count, 2)

    def test_download_checks_temp_archive_metadata_once(self):
        data = b"an archive"
        digests = self.root / "digests.json"
        digests.write_text(json.dumps({ARTIFACT: hashlib.sha256(data).hexdigest()}))
        stat_path = os.stat
        checked = []

        def fake_download(command, **kwargs):
            # curl's config sits beside the temporary archive it writes.
            path = Path(command[-1]).parent / ARTIFACT
            path.write_bytes(data)
            return subprocess.CompletedProcess(command, 0, stderr="")

        def count_stat(path, *args, **kwargs):
            if isinstance(path, (str, os.PathLike)):
                local = Path(path)
                if local.name == ARTIFACT and local.parent.name.startswith("fetch-"):
                    checked.append(local)
            return stat_path(path, *args, **kwargs)

        argv = ["fetch-artifacts.py", str(self.mapping), str(self.root), "--sha256", str(digests)]
        with (
            patch.object(sys, "argv", argv),
            patch.object(fetch.resource, "getrlimit", return_value=(65536, 65536)),
            patch.object(fetch.subprocess, "run", side_effect=fake_download),
            patch.object(os, "stat", count_stat),
            redirect_stdout(io.StringIO()),
            self.assertRaises(SystemExit) as result,
        ):
            fetch.main()

        self.assertEqual(result.exception.code, 0)
        self.assertEqual((self.root / "artifacts" / ARTIFACT).read_bytes(), data)
        self.assertEqual(len(checked), 1)

    def test_staging_bounds_each_archive_read(self):
        build = self.root / ".lake/build"
        archive = build / "ir/Test.ltar"
        trace = build / "lib/lean/Test.trace"
        archive.parent.mkdir(parents=True)
        trace.parent.mkdir(parents=True)
        data = b"a" * (4 << 20)
        archive.write_bytes(data)
        trace.write_text(json.dumps({"depHash": INPUT_HASH}))
        reads = []
        open_path = io.open

        # Track both unbounded reads and the buffer sizes requested by streaming hashes.
        class MeasuredReader(io.BufferedReader):
            def read(self, size=-1):
                reads.append(size)
                return super().read(size)

            def readinto(self, buffer):
                reads.append(len(buffer))
                return super().readinto(buffer)

        def measure_reads(path, *args, **kwargs):
            if path in (archive, str(archive)):
                return MeasuredReader(io.FileIO(path, "r"))
            return open_path(path, *args, **kwargs)

        output = self.root / "stage"
        identity = dict.fromkeys(cache.FIELDS, "test")
        argv = ["ci-cache-stage.py", str(self.mapping), str(output), "--project", str(self.root)]
        with (
            patch.object(sys, "argv", argv),
            patch.object(stage.cli, "current_identity", return_value=identity),
            patch.object(stage.cli, "published", return_value=True),
            patch.object(stage.subprocess, "check_output", return_value="Test.lean\0"),
            patch.object(io, "open", measure_reads),
            redirect_stdout(io.StringIO()),
        ):
            stage.main()

        with gzip.open(output / "modules.jsonl.gz", "rt") as manifest:
            next(manifest)
            self.assertEqual(json.loads(next(manifest)),
                             ["Test", INPUT_HASH, ARTIFACT, hashlib.sha256(data).hexdigest()])
        self.assertTrue(reads)
        self.assertTrue(all(0 < size < len(data) for size in reads), reads)


if __name__ == "__main__":
    unittest.main()
