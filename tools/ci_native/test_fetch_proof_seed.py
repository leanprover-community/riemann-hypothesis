import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import fetch_proof_seed as download

class ProofSeedDownloadTests(unittest.TestCase):
    def fetch(self, payload, maximum=None, expected=None):
        root=Path(self.directory.name)
        sha=expected or hashlib.sha256(payload).hexdigest()
        with patch.object(download.urllib.request,'urlopen',return_value=io.BytesIO(payload)):
            return download.fetch(sha,'seed.json',root/'seed.json',maximum or download.PROOF_SEED_MAX_BYTES)

    def setUp(self):
        self.directory=tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)

    def test_seed_larger_than_old_limit_still_requires_exact_sha(self):
        payload=b'x'*(11*1024**2)
        path=self.fetch(payload)
        self.assertEqual(path.read_bytes(),payload)
        path.unlink()
        with self.assertRaisesRegex(ValueError,'SHA mismatch'):
            self.fetch(payload,expected='0'*64)
        self.assertFalse(path.exists())

    def test_oversized_seed_is_rejected_and_partial_removed(self):
        root=Path(self.directory.name)
        with self.assertRaisesRegex(ValueError,'too large'):
            self.fetch(b'x'*(download.PROOF_SEED_MAX_BYTES+1))
        self.assertFalse((root/'seed.json').exists())
        self.assertFalse((root/'seed.json.download').exists())

    def test_existing_small_seed_is_unchanged(self):
        self.assertEqual(self.fetch(b'{}').read_bytes(),b'{}')

if __name__=='__main__':unittest.main()

