"""The push build can skip staging only when the queue has an artifact to publish."""
import argparse
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

script = Path(__file__).resolve().parents[1] / "ci-github.py"
spec = importlib.util.spec_from_file_location("ci_github", script)
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)


class QueueArtifact(unittest.TestCase):
    def test_queue_skip_agrees_with_publisher_on_artifact_availability(self):
        sha = "a" * 40
        name = f"cache-{sha}"
        run = {"repository": {"full_name": ci.REPOSITORY}, "path": ci.WORKFLOW, "head_sha": sha,
               "event": "merge_group", "status": "completed", "conclusion": "success", "id": 1, "run_attempt": 1}
        jobs = [{"name": ci.JOB, "conclusion": "success", "labels": [ci.LABEL]}]
        for rows, available in (([], False), ([{"name": name, "expired": True}], False),
                                ([{"name": name, "expired": False}], True)):
            responses = {
                f"actions/workflows/build.yml/runs?head_sha={sha}&per_page=100": {"workflow_runs": [run]},
                "actions/runs/1/attempts/1/jobs?per_page=100": {"jobs": jobs},
                "actions/runs/1/artifacts?per_page=100": {"artifacts": rows},
            }
            with (self.subTest(rows=rows), patch.object(ci, "api", responses.__getitem__),
                  patch.object(ci, "outputs") as out):
                args = argparse.Namespace(sha=sha, run_id=None, wait_minutes=0)
                ci.queue_tested(args)
                out.assert_called_once_with(tested=str(available).lower())
                if available:
                    ci.find_run(args)
                    out.assert_called_with(run_id=1, artifact=name, event="merge_group")
                else:
                    with self.assertRaisesRegex(ValueError, "no successful self-hosted build"):
                        ci.find_run(args)


if __name__ == "__main__":
    unittest.main()
