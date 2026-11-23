"""Exercise completed and truncated HTTP transfers with real curl, without network access."""
import contextlib
import hashlib
from http.server import BaseHTTPRequestHandler
import importlib.util
import io
import json
from pathlib import Path
import shutil
import socket
import socketserver
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("fetch_artifacts", Path(__file__).with_name("fetch-artifacts.py"))
fetch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fetch)


@unittest.skipUnless(shutil.which("curl") and hasattr(socket, "AF_UNIX"), "curl and Unix sockets are required")
class ArtifactTransferTests(unittest.TestCase):
    def transfer(self, failures, verify_sha=False, retries=0):
        """Failures is the number of truncated responses to serve for each artifact."""
        names = [f"{index + 1:016x}.ltar" for index in range(len(failures))]
        payload = b"complete artifact payload"
        requests = {name: 0 for name in names}
        lock = threading.Lock()
        by_url = {"/" + name[:-5] + ".art": (name, count) for name, count in zip(names, failures)}

        class Handler(BaseHTTPRequestHandler):
            def do_GET(self):
                name, count = by_url[self.path]
                with lock:
                    requests[name] += 1
                    truncated = requests[name] <= count
                self.send_response(200)
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload[:5] if truncated else payload)
                self.wfile.flush()
                self.close_connection = True

            def log_message(self, *args):
                pass

        with tempfile.TemporaryDirectory(prefix="rh-fetch-test-") as directory:
            root = Path(directory)
            endpoint = root / "http.sock"
            server = socketserver.ThreadingUnixStreamServer(str(endpoint), Handler)
            thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
            thread.start()
            mapping = root / "map.jsonl"
            mapping.write_text(json.dumps({"schema": 1}) + "\n" + "".join(
                json.dumps([f"{index + 1:016x}", name]) + "\n" for index, name in enumerate(names)))
            cache = root / "cache"
            argv = ["fetch-artifacts.py", str(mapping), str(cache)]
            if verify_sha:
                digests = root / "sha256.json"
                digests.write_text(json.dumps({name: hashlib.sha256(payload).hexdigest() for name in names}))
                argv += ["--sha256", str(digests)]
            real_run = subprocess.run
            curl_codes = []

            def curl(args):
                # Run actual HTTP transfers over a local Unix socket. Disable curl's
                # internal retries by default so the script's settling passes are observable.
                command = [*args, "--unix-socket", str(endpoint), "--retry", str(retries), "--retry-delay", "1",
                           "--connect-timeout", "1", "--max-time", "5"]
                done = real_run(command, capture_output=True, text=True, timeout=10)
                curl_codes.append(done.returncode)
                return done

            output = io.StringIO()
            try:
                with patch.object(fetch, "PUBLIC", "http://localhost/"), patch.object(sys, "argv", argv), \
                     patch.object(fetch.subprocess, "run", side_effect=curl), contextlib.redirect_stdout(output):
                    with self.assertRaises(SystemExit) as stopped:
                        fetch.main()
                installed = {name: (cache / "artifacts" / name).read_bytes()
                             for name in names if (cache / "artifacts" / name).exists()}
                return stopped.exception.code, installed, requests, curl_codes, output.getvalue()
            finally:
                server.shutdown()
                thread.join()
                server.server_close()

    def test_complete_parallel_downloads_are_installed(self):
        code, installed, requests, curl_codes, _ = self.transfer([0, 0])
        self.assertEqual(code, 0)
        self.assertEqual(list(installed.values()), [b"complete artifact payload"] * 2)
        self.assertEqual(list(requests.values()), [1, 1])
        self.assertEqual(curl_codes, [0])

    def test_truncated_file_without_digest_never_enters_cache(self):
        code, installed, requests, curl_codes, log = self.transfer([3])
        self.assertEqual(code, 1, log)
        self.assertEqual(installed, {})
        self.assertEqual(list(requests.values()), [3])
        self.assertEqual(curl_codes, [18, 18, 18])

    def test_truncated_first_pass_is_retried(self):
        code, installed, requests, curl_codes, _ = self.transfer([1])
        self.assertEqual(code, 0)
        self.assertEqual(list(installed.values()), [b"complete artifact payload"])
        self.assertEqual(list(requests.values()), [2])
        self.assertEqual(curl_codes, [18, 0])

    def test_completed_peer_survives_another_files_failure(self):
        code, installed, requests, _, log = self.transfer([0, 3])
        self.assertEqual(code, 1, log)
        self.assertEqual(installed, {"0000000000000001.ltar": b"complete artifact payload"})
        self.assertEqual(list(requests.values()), [1, 3])

    def test_curl_internal_retry_keeps_the_completed_output(self):
        code, installed, requests, curl_codes, _ = self.transfer([1], retries=1)
        self.assertEqual(code, 0)
        self.assertEqual(list(installed.values()), [b"complete artifact payload"])
        self.assertEqual(list(requests.values()), [2])
        self.assertEqual(curl_codes, [0])

    def test_digest_verification_still_recovers_a_truncated_download(self):
        code, installed, requests, curl_codes, _ = self.transfer([1], verify_sha=True)
        self.assertEqual(code, 0)
        self.assertEqual(list(installed.values()), [b"complete artifact payload"])
        self.assertEqual(list(requests.values()), [2])
        self.assertEqual(curl_codes, [18, 0])


if __name__ == "__main__":
    unittest.main()
