#!/usr/bin/env python3
"""Offline tests for selecting a completed build to publish."""
import importlib.util
import io
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "ci-github.py"
spec = importlib.util.spec_from_file_location("ci_github", SCRIPT)
ci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci)

SHA = "a" * 40


def build_run(**overrides):
    return {
        "id": 7,
        "run_attempt": 1,
        "repository": {"full_name": ci.REPOSITORY},
        "path": ci.WORKFLOW,
        "head_sha": SHA,
        "head_branch": "main",
        "event": "push",
        "status": "completed",
        "conclusion": "success",
        **overrides,
    }


class FindRun(unittest.TestCase):
    def setUp(self):
        self.args = SimpleNamespace(sha=SHA, run_id=None, wait_minutes=1)
        self.runs = self.enterContext(patch.object(ci, "runs"))
        self.api = self.enterContext(patch.object(ci, "api"))
        self.sleep = self.enterContext(patch.object(ci.time, "sleep"))
        self.clock = self.enterContext(patch.object(ci.time, "monotonic", return_value=100))
        self.outputs = self.enterContext(patch.object(ci, "outputs"))
        self.enterContext(redirect_stdout(io.StringIO()))
        self.api.side_effect = [
            {"jobs": [{"name": ci.JOB, "conclusion": "success", "labels": [ci.LABEL]}]},
            {"artifacts": [{"name": f"cache-{SHA}", "expired": False}]},
        ]

    def assert_selected(self):
        self.outputs.assert_called_once_with(run_id=7, artifact=f"cache-{SHA}", event="push")

    def test_waits_for_an_initially_absent_build(self):
        self.runs.side_effect = [[], [build_run()]]
        ci.find_run(self.args)
        self.sleep.assert_called_once_with(30)
        self.assert_selected()

    def test_waits_when_only_out_of_scope_runs_are_visible(self):
        irrelevant = [
            build_run(id=5, event="pull_request"),
            build_run(id=6, head_branch="topic"),
            build_run(id=8, status="in_progress", head_sha="b" * 40),
        ]
        self.runs.side_effect = [irrelevant, [*irrelevant, build_run()]]
        ci.find_run(self.args)
        self.sleep.assert_called_once_with(30)
        self.assert_selected()
        self.assertEqual(self.api.call_count, 2)

    def test_waits_for_push_after_a_failed_manual_build(self):
        manual = build_run(id=6, event="workflow_dispatch", conclusion="failure")
        self.runs.side_effect = [[manual], [manual, build_run()]]
        ci.find_run(self.args)
        self.assertEqual(self.runs.call_count, 2)
        self.sleep.assert_called_once_with(30)
        self.assert_selected()

    def test_selected_run_can_appear_after_first_poll(self):
        self.args.run_id = 7
        self.runs.side_effect = [[build_run(id=9)], [build_run()]]
        ci.find_run(self.args)
        self.sleep.assert_called_once_with(30)
        self.assert_selected()

    def test_selected_out_of_scope_run_fails_immediately(self):
        self.args.run_id = 7
        self.runs.return_value = [build_run(event="pull_request"), build_run(id=9)]
        self.assert_immediate_failure()

    def test_selected_terminal_failed_build_fails_immediately(self):
        self.args.run_id = 7
        self.runs.return_value = [build_run(conclusion="failure")]
        self.assert_immediate_failure()

    def test_selected_completed_run_needs_an_unexpired_cache_artifact(self):
        self.args.run_id = 7
        self.runs.return_value = [build_run()]
        self.api.side_effect = [
            {"jobs": [{"name": ci.JOB, "conclusion": "success", "labels": [ci.LABEL]}]},
            {"artifacts": [{"name": f"cache-{SHA}", "expired": True}]},
        ]
        with self.assertRaises(ValueError):
            ci.find_run(self.args)
        self.runs.assert_called_once_with(SHA)
        self.sleep.assert_not_called()
        self.outputs.assert_not_called()

    def test_queue_tested_still_requires_correct_runner(self):
        self.runs.return_value = [build_run(event="merge_group")]
        self.api.side_effect = None
        self.api.return_value = {
            "jobs": [{"name": ci.JOB, "conclusion": "success", "labels": ["rh-pr-fork"]}],
        }
        ci.queue_tested(self.args)
        self.outputs.assert_called_once_with(tested="false")

    def test_zero_wait_only_polls_once(self):
        self.args.wait_minutes = 0
        self.runs.return_value = []
        self.assert_immediate_failure()

    def test_pending_build_can_finish_on_next_poll(self):
        self.runs.side_effect = [[build_run(status="in_progress", conclusion=None)], [build_run()]]
        ci.find_run(self.args)
        self.sleep.assert_called_once_with(30)
        self.assert_selected()

    def test_final_sleep_is_limited_to_remaining_budget(self):
        self.clock.side_effect = [100, 157, 160]
        self.runs.return_value = []
        with self.assertRaises(ValueError):
            ci.find_run(self.args)
        self.assertEqual(self.runs.call_count, 2)
        self.sleep.assert_called_once_with(3)
        self.outputs.assert_not_called()

    def assert_immediate_failure(self):
        with self.assertRaises(ValueError):
            ci.find_run(self.args)
        self.runs.assert_called_once_with(SHA)
        self.sleep.assert_not_called()
        self.api.assert_not_called()
        self.outputs.assert_not_called()


if __name__ == "__main__":
    unittest.main()
