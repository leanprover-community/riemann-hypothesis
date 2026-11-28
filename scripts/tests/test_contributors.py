"""Check the merged-PR links rendered by the contributor list."""
import importlib.util
import io
from pathlib import Path
import sys
import unittest
from unittest import mock
from urllib.parse import quote_plus

SCRIPT = Path(__file__).resolve().parents[1] / "contributors.py"
spec = importlib.util.spec_from_file_location("contributors", SCRIPT)
contributors = importlib.util.module_from_spec(spec)
spec.loader.exec_module(contributors)


class ContributorLinkTests(unittest.TestCase):
    def test_link_searches_all_logins_credited_to_one_person(self):
        authors = ["alice", "alice-bot", "alice-work", "bob"]
        pulls = [{"number": n, "title": "fix", "author": {"__typename": "User", "login": login}}
                 for n, login in enumerate(authors, 1)]
        with (
            mock.patch.object(contributors, "ALIASES", {"alice-bot": "alice", "alice-work": "alice"}),
            mock.patch.object(contributors, "merged", side_effect=[pulls, []]),
            mock.patch.object(sys, "argv", [str(SCRIPT)]),
            mock.patch.object(sys, "stdout", new_callable=io.StringIO) as output,
        ):
            contributors.main()

        prefix = f"https://github.com/{contributors.REPO}/pulls?q="
        alice = quote_plus("is:pr is:merged (author:alice OR author:alice-bot OR author:alice-work)")
        bob = quote_plus("is:pr is:merged author:bob")
        self.assertIn(f"[3 merged]({prefix}{alice})", output.getvalue())
        self.assertIn(f"[1 merged]({prefix}{bob})", output.getvalue())


if __name__ == "__main__":
    unittest.main()
