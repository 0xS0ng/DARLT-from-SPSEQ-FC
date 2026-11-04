"""Exercise both workflows without inference or a measurement clock."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from case_study.common import Clock
from case_study.oauth import OAuthIssuer
from case_study.prefetch import PreparedClient
from case_study.server import ToolServer
from case_study.workflows import actions, run_workflow


class RecordedWorkflowTests(unittest.TestCase):
    def test_both_workflows_complete_without_reading_a_performance_clock(self):
        for workload, quota, units in [('booking', 16, 8), ('research', 64, 61)]:
            with self.subTest(workload=workload), tempfile.TemporaryDirectory() as directory:
                issuer = OAuthIssuer()
                clock = Clock()
                with ToolServer(Path(directory), None, issuer.verifier(), clock=clock) as server,\
                     PreparedClient(server, None, "oauth", "local-check", issuer,
                         positions=range(quota), steps=actions(workload, "synthetic-customer-0"),
                         quota=quota, clock=clock) as client,\
                     patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("measurement clock")):
                    result = run_workflow(client, workload, scripted=True, prepare_all=True)
                self.assertTrue(result["passed"])
                self.assertEqual(result["scope_accounting"]["expected_units"], units)
                self.assertEqual(len(result["steps"]), 5)
                self.assertTrue(all("timing" not in step for step in result["steps"]))
                self.assertEqual(result["timing_steps"], [])


if __name__ == "__main__":
    unittest.main()
