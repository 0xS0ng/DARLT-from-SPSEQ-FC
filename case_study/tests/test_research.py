"""Deterministic research backend, fixed billing and inclusive server boundaries."""
import tempfile
import threading
import unittest
from pathlib import Path
from unittest.mock import patch

import httpx

from case_study import mcp
from case_study.client import Client
from case_study.common import (AUTH_META, COSTS, DOCUMENT_IDS, RESEARCH, Clock,
                       canonical, declarations, normalize, policy, strict)
from case_study.oauth import OAuthIssuer
from case_study.server import ToolServer
from case_study.store import Denied, Store


RESEARCH_ACTIONS = [
    ("search_sources", {"query": "market"}),
    ("fetch_documents", {"document_ids": list(DOCUMENT_IDS)}),
    ("query_dataset", {"dataset_id": "market-v1"}),
    ("run_analysis", {"dataset_id": "market-v1"}),
    ("export_report", {"analysis_id": "analysis-001"}),
]
CLAIMS = {"sub": "agent", "cnf": {"jkt": "research-key"}, "period": 1}


class ResearchTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.store = Store(Path(self.directory.name) / "state.sqlite")

    def tearDown(self):
        self.directory.cleanup()

    def call(self, mode, namespace, index, **options):
        tool, arguments = RESEARCH_ACTIONS[index]
        if mode in ("darlt", "darlt-ablation", "sma"):
            serials = [f"{namespace}-{index}-{i}" for i in range(COSTS[tool])]
        else:
            serials = []
        if mode == "oauth":
            options.setdefault("claims", CLAIMS)
            options.setdefault("dpop_jti", "fresh-" + str(index))
        return self.store.commit(mode, namespace, tool, arguments, "request-" + str(index), serials, **options)

    def test_fixed_costs_and_public_policies_are_not_model_arguments(self):
        self.assertEqual([COSTS[name] for name in RESEARCH], [1, 8, 16, 4, 32])
        self.assertEqual(sum(COSTS[name] for name in RESEARCH), 61)
        tools = {tool["name"]: tool for tool in declarations()}
        for name, arguments in RESEARCH_ACTIONS:
            with self.subTest(name=name):
                self.assertEqual(tools[name]["annotations"]["org.darlt/unitCost"], COSTS[name])
                self.assertTrue(set(tools[name]["annotations"]["org.darlt/requiredAttributes"]) <= {0, 1, 2, 3})
                self.assertEqual(policy(name, arguments)["required_attrs"][0]["index"], tools[name]["annotations"]["org.darlt/requiredAttributes"][0])
                self.assertIn("Fixed cost:", tools[name]["description"])
                with self.assertRaisesRegex(ValueError, "unexpected_tool_argument"):
                    normalize(name, {**arguments, "units": 0})
        self.assertEqual(policy("delete_record", {"item_id": "hotel-101"})["required_attrs"], [{"index": 5, "value": 1}])
        self.assertEqual(policy("export_private", {"item_id": "hotel-101"})["required_attrs"], [{"index": 6, "value": 1}])

    def test_fetch_requires_all_eight_distinct_source_documents(self):
        for ids in [list(DOCUMENT_IDS)[:-1], [DOCUMENT_IDS[0]] * 8, list(DOCUMENT_IDS[:-1]) + ["unknown"]]:
            with self.subTest(ids=ids), self.assertRaisesRegex(ValueError, "fetch_requires_eight_distinct_documents"):
                normalize("fetch_documents", {"document_ids": ids})
        self.assertEqual(normalize("fetch_documents", {"document_ids": list(reversed(DOCUMENT_IDS))})["document_ids"], list(DOCUMENT_IDS))

    def test_three_native_deployments_consume_61_distinct_units_and_finish_report(self):
        for mode in ("darlt", "darlt-ablation", "sma"):
            with self.subTest(mode=mode):
                results = [self.call(mode, mode, i) for i in range(5)]
                self.assertTrue(all(row["accepted"] for row in results))
                self.assertEqual(self.store.facts(mode)["effects"], 5)
                self.assertEqual(self.store.facts(mode)["consumed"], 61)
                self.assertEqual(self.store.research_facts(mode), {"stage": 5, "documents": 8, "rows": 16, "report_complete": 1})
                report = results[-1]["tool_result"]
                self.assertIs(report["complete"], True)
                self.assertEqual(len(report["sections"]), 32)
                self.assertEqual(report["summary"], {"sum": 1360, "mean": 85.0, "minimum": 10, "maximum": 160})

    def test_out_of_order_research_rejects_without_consuming_serials_or_effects(self):
        self.call("darlt", "agent", 0)
        before = self.store.facts("agent")
        research = self.store.research_facts("agent")
        with self.assertRaisesRegex(Denied, "research_sequence"):
            self.call("darlt", "agent", 2)
        self.assertEqual(self.store.facts("agent"), before)
        self.assertEqual(self.store.research_facts("agent"), research)
        self.assertTrue(self.call("darlt", "agent", 1)["accepted"])

    def test_research_backend_failure_rolls_back_quota_dpop_and_stage(self):
        self.store.install_grant("agent", jkt=CLAIMS["cnf"]["jkt"])
        self.call("oauth", "agent", 0)
        before, research = self.store.facts("agent"), self.store.research_facts("agent")
        with self.assertRaisesRegex(Denied, "injected_backend_failure"):
            self.call("oauth", "agent", 1, inject_failure=True)
        self.assertEqual(self.store.facts("agent"), before)
        self.assertEqual(self.store.research_facts("agent"), research)
        for i in range(1, 5):
            self.assertTrue(self.call("oauth", "agent", i)["accepted"])
        self.assertEqual(self.store.facts("agent")["remaining"], 3)
        with self.store.connect() as db:
            self.assertEqual(db.execute("SELECT COUNT(*) FROM dpop").fetchone()[0], 5)

    def test_research_scopes_and_private_attributes_are_enforced_atomically(self):
        self.store.install_grant("agent", scopes=[name + ":inventory/allowed" for name in RESEARCH[:2]], jkt=CLAIMS["cnf"]["jkt"])
        self.call("oauth", "agent", 0); self.call("oauth", "agent", 1)
        before, research = self.store.facts("agent"), self.store.research_facts("agent")
        with self.assertRaisesRegex(Denied, "scope_not_granted"):
            self.call("oauth", "agent", 2)
        self.assertEqual(self.store.facts("agent"), before)
        self.assertEqual(self.store.research_facts("agent"), research)
        self.store.install_grant("private", scopes=["search_sources:owner/private"], jkt=CLAIMS["cnf"]["jkt"])
        with self.assertRaisesRegex(Denied, "attribute_not_granted"):
            self.store.commit("oauth", "private", "search_sources", {"query": "market", "resource": "owner/private"}, "private-request", claims=CLAIMS, dpop_jti="not-consumed")
        self.assertEqual(self.store.facts("private")["remaining"], 64)
        self.assertEqual(self.store.research_facts("private")["stage"], 0)

    def test_snapshot_restores_the_entire_research_workflow(self):
        self.store.install_grant("agent", jkt=CLAIMS["cnf"]["jkt"])
        snapshot = self.store.snapshot()
        try:
            for _ in range(2):
                for i in range(5):
                    self.call("oauth", "agent", i)
                self.assertEqual(self.store.research_facts("agent")["report_complete"], 1)
                self.store.restore(snapshot)
                self.assertEqual(self.store.research_facts("agent"), {"stage": 0, "documents": 0, "rows": 0, "report_complete": 0})
                self.assertEqual(self.store.facts("agent"), {"effects": 0, "bookings": 0, "consumed": 0, "remaining": 64})
        finally:
            snapshot.close()

    def test_untimed_http_research_does_not_read_performance_clock(self):
        issuer = OAuthIssuer()
        with ToolServer(Path(self.directory.name) / "server", None, issuer.verifier()) as server:
            with Client(server, None, "none", "research-dev", issuer) as client:
                with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError('untimed clock')):
                    results = [client.call(name, args) for name, args in RESEARCH_ACTIONS]
                self.assertIs(results[-1]["tool_result"]["complete"], True)
                self.assertNotIn("_ns", canonical(results).decode())

    def test_inclusive_server_timer_starts_before_json_parse_and_ends_after_commit(self):
        events = []
        class TickClock:
            enabled = True
            counter = 0
            lock = threading.Lock()
            def start(self):
                with self.lock:
                    self.counter += 100; events.append("clock_start"); return self.counter
            def elapsed(self, start):
                with self.lock:
                    self.counter += 100; events.append("clock_elapsed"); return self.counter - start
        issuer = OAuthIssuer()
        with ToolServer(Path(self.directory.name) / "timed-server", None, issuer.verifier(), clock=TickClock()) as server:
            server.register("agent", "none")
            body = mcp.request("tools/call", {"name": "search_sources", "arguments": {"query": "market"},
                               "_meta": {AUTH_META: {"instance": "agent", "nonce": "fresh-research-timing-nonce"}}})
            raw = canonical(body)
            tool = next(t for t in server.tools if t["name"] == "search_sources")
            original_commit = server.stores["none"].commit
            def parsed(data):
                events.append("strict_parse"); return strict(data)
            def committed(*args, **kwargs):
                result = original_commit(*args, **kwargs); events.append("commit_return"); return result
            def serialized(value):
                events.append("response_serialize"); return canonical(value)
            with patch("case_study.server.strict", side_effect=parsed), patch.object(server.stores["none"], "commit", side_effect=committed), patch("case_study.server.canonical", side_effect=serialized):
                response = httpx.post(server.url + "/mcp/none", content=raw, headers=mcp.request_headers(body, tool), trust_env=False)
            result = mcp.decode_response(response, body["id"])
            timing = result["_meta"][AUTH_META]["timing"]
            self.assertLess(events.index("clock_start"), events.index("strict_parse"))
            self.assertLess(events.index("commit_return"), max(i for i, e in enumerate(events) if e == "clock_elapsed"))
            self.assertLess(max(i for i, e in enumerate(events) if e == "clock_elapsed"), events.index("response_serialize"))
            self.assertGreaterEqual(timing["server_verification_commit_ns"], timing["state_backend_ns"])
            self.assertEqual(timing["request_body_bytes"], len(raw))


if __name__ == "__main__":
    unittest.main()
