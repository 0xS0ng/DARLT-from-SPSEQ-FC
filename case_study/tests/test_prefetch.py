"""Clock-controlled preparation-cache checks; no native process or model API."""
from concurrent.futures import ThreadPoolExecutor
import json
import threading
import unittest
from unittest.mock import patch

from case_study.common import AUTH_META, COSTS, DOCUMENT_IDS, Clock, declarations
from case_study.mcp import RpcError
from case_study.prefetch import PreparedClient


def hotel():
    return [
        ("search_inventory", {"query": "hotel"}),
        ("get_details", {"item_id": "hotel-101"}),
        ("book_item", {"item_id": "hotel-101", "customer": "synthetic-test"}),
        ("get_details", {"item_id": "hotel-101"}),
        ("search_inventory", {"query": "hotel"}),
    ]


def research():
    return [
        ("search_sources", {"query": "market"}),
        ("fetch_documents", {"document_ids": list(DOCUMENT_IDS)}),
        ("query_dataset", {"dataset_id": "market-v1"}),
        ("run_analysis", {"dataset_id": "market-v1"}),
        ("export_report", {"analysis_id": "analysis-001"}),
    ]


class CounterClock:
    enabled = True

    def __init__(self):
        self.value = 0
        self.lock = threading.Lock()

    def start(self):
        with self.lock:
            self.value += 100
            return self.value


class FakeServer:
    url = "http://127.0.0.1:12345"
    domain = "https://mcp.test/resource"
    period = 1
    nonce = "server-nonce"

    def __init__(self):
        self.registrations = []

    def register(self, instance, mode, **values):
        self.registrations.append((instance, mode, values))


class FakeKey:
    def public_key(self):
        return "fake-public-key"


class FakeIssuer:
    def __init__(self):
        self.calls = 0

    def issue(self, *args, **kwargs):
        self.calls += 1
        return "fake-access-token"


class FakeBridge:
    def __init__(self, block_prepare_number=None):
        self.lock = threading.RLock()
        self.calls = []
        self.prepared = {}
        self.counter = 0
        self.block_prepare_number = block_prepare_number
        self.block_entered = threading.Event()
        self.release = threading.Event()

    def command(self, operation, **values):
        with self.lock:
            self.calls.append((operation, values))
            if operation == "prepare":
                self.counter += 1
                if self.counter == self.block_prepare_number:
                    self.block_entered.set()
                    if not self.release.wait(3):
                        raise ValueError("fake_preparation_release_timeout")
                handle = "handle-" + str(self.counter)
                self.prepared[handle] = list(values["positions"])
                return {"handle": handle, "timing": {"preparation_ns": 11}}
            if operation == "online":
                self.prepared.pop(values["handle"])
                return {"wire_hex": ["aabbcc"], "timing": {"online_ns": 3}}
            raise ValueError("unexpected_fake_native_operation")


class FakeTransport:
    instances = []
    reject = False
    mismatch_body = False

    def __init__(self, url):
        self.url = url
        self.calls = []
        self.closed = False
        self.last_request_stats = {}
        self.instances.append(self)

    def send(self, method, params=None, headers=None, tool=None):
        self.calls.append((method, params, headers))
        if method == "tools/list":
            return {"tools": declarations(include_privileged=True)}
        if self.reject:
            raise RpcError(-32000, "quota_exhausted", 403)
        self.last_request_stats = {
            "http_sent_bytes": 300,
            "request_body_bytes": 201 if self.mismatch_body else 200,
            "native_token_bytes": 3 if "wire_hex" in params["_meta"][AUTH_META] else 0,
            "auth_envelope_bytes": 30,
        }
        return {
            "resultType": "complete",
            "structuredContent": {"accepted": True, "units": COSTS[params["name"]],
                                  "tool_result": {"synthetic": True}},
            "_meta": {AUTH_META: {"timing": {
                "decode_ns": 2, "verification_ns": 4,
                "server_verification_commit_ns": 9, "request_body_bytes": 200,
            }}},
        }

    def close(self):
        self.closed = True


class PrefetchChecks(unittest.TestCase):
    def setUp(self):
        self.patches = [
            patch("case_study.client.Transport", FakeTransport),
            patch("case_study.client.new_dpop_key", side_effect=FakeKey),
            patch("case_study.client.thumbprint", return_value="fake-jkt"),
            patch("case_study.prefetch.dpop_sign", return_value="fake-dpop"),
        ]
        for item in self.patches:
            item.start()
        FakeTransport.instances = []
        FakeTransport.reject = False
        FakeTransport.mismatch_body = False

    def tearDown(self):
        for item in reversed(self.patches):
            item.stop()

    def client(self, *, mode="darlt", steps=None, quota=16, positions=None, clock=None, bridge=None):
        server = FakeServer()
        bridge = bridge or FakeBridge()
        client = PreparedClient(server, bridge, mode, "test-agent", FakeIssuer(),
                                positions=range(160, 160 + quota) if positions is None else positions,
                                steps=hotel() if steps is None else steps,
                                clock=CounterClock() if clock is None else clock,
                                quota=quota)
        self.addCleanup(client.close)
        return client, server, bridge

    def run_steps(self, client):
        values = []
        for i in range(len(client.steps)):
            client.start_background()
            values.append(client.call_step(i))
        return values

    def test_hotel_initial_six_and_only_two_single_unit_refills(self):
        client, _, bridge = self.client()
        initial = client.prime()
        self.assertEqual(initial["prepared_token_count"], 3)
        self.assertEqual(initial["reserved_unit_count"], 6)
        self.assertEqual(initial["initial_native_preparation_ns"], 33)
        values = self.run_steps(client)
        self.assertEqual(client.assert_complete()["spent_units"], 8)
        self.assertEqual(client.reserved_positions, list(range(160, 168)))
        self.assertEqual(client.reserved_positions, client.spent_positions)
        self.assertEqual(len(client.preparations), 5)
        self.assertEqual([p["tool"] for p in client.preparations if p["reason"] == "replenishment"],
                         ["search_inventory", "get_details"])
        self.assertEqual([op for op, _ in bridge.calls].count("prepare"), 5)
        self.assertNotIn("init", [op for op, _ in bridge.calls])
        for value in values:
            t = value["timing"]
            self.assertEqual(t["readiness_gate_ns"] + t["request_latency_ns"], t["agent_critical_ns"])
            self.assertEqual(t["online_bridge_queue_ns"] + t["online_rpc_ns"], t["online_bridge_ns"])
            self.assertLessEqual(value["prepared_token"]["ready_at_ns"], t["online_started_at_ns"])
            self.assertEqual(value["request_body_bytes"], 200)
            self.assertEqual(t["server_verification_commit_ns"], 9)

    def test_prepare_all_preserves_live_reservations_and_consumption_order(self):
        expected = [[160], [161], [162, 163, 164, 165], [167], [166]]
        for mode in ("darlt", "darlt-ablation", "sma"):
            with self.subTest(mode=mode):
                live, _, _ = self.client(mode=mode)
                live.prime()
                live_values = self.run_steps(live)
                live_positions = [value["prepared_token"]["positions"] for value in live_values]
                self.assertEqual(live_positions, expected)

                client, _, bridge = self.client(mode=mode)
                summary = client.prepare_all()
                self.assertEqual(summary["preparation_mode"], "all")
                self.assertEqual(summary["reserved_unit_count"], 8)
                self.assertEqual(summary["prepared_entry_count"], 5)
                self.assertEqual(summary["prepared_token_count"], 5 if mode == "darlt" else 8)
                self.assertEqual(summary["all_preparation_ns"], summary["initial_preparation_ns"])
                self.assertEqual(summary["all_native_preparation_ns"], 55)
                self.assertEqual([row["positions"] for row in summary["step_allocations"]], expected)
                self.assertEqual([row["positions"] for row in summary["jobs"]],
                                 [[160], [161], [162, 163, 164, 165], [166], [167]])
                self.assertEqual([row["reason"] for row in summary["jobs"]],
                                 ["initial"] * 3 + ["replenishment"] * 2)
                prepared_count = len(bridge.calls)
                values = self.run_steps(client)
                self.assertEqual([value["prepared_token"]["positions"] for value in values], live_positions)
                self.assertEqual([args["handle"] for op, args in bridge.calls if op == "online"],
                                 ["handle-1", "handle-2", "handle-3", "handle-5", "handle-4"])
                self.assertEqual([op for op, _ in bridge.calls[prepared_count:]], ["online"] * 5)
                self.assertTrue(all(value["readiness"]["ready_before_demand"] for value in values))
                self.assertTrue(all(value["timing"]["future_wait_ns"] == 0 for value in values))
                self.assertTrue(all(value["timing"]["demand_at_ns"] > summary["finished_at_ns"]
                                    for value in values))
                self.assertFalse(bridge.prepared)
                self.assertEqual(client.assert_complete()["spent_units"], 8)

    def test_prepare_all_research_has_only_initial_sixty_one_units(self):
        expected = [[160], list(range(161, 169)), list(range(169, 185)),
                    list(range(185, 189)), list(range(189, 221))]
        for mode in ("darlt", "darlt-ablation", "sma"):
            with self.subTest(mode=mode):
                client, _, bridge = self.client(mode=mode, steps=research(), quota=64)
                summary = client.prepare_all()
                self.assertEqual(summary["reserved_unit_count"], 61)
                self.assertEqual(summary["prepared_entry_count"], 5)
                self.assertEqual(summary["prepared_token_count"], 5 if mode == "darlt" else 61)
                self.assertEqual([row["positions"] for row in summary["step_allocations"]], expected)
                self.assertTrue(all(row["reason"] == "initial" for row in summary["jobs"]))
                self.assertTrue(all(args["ablation"] == (mode == "darlt-ablation")
                                    for op, args in bridge.calls if op == "prepare"))
                self.run_steps(client)
                self.assertEqual(client.start_background(), {"jobs_started": [], "count": 0})
                self.assertEqual([op for op, _ in bridge.calls].count("prepare"), 5)
                self.assertEqual(client.assert_complete()["spent_units"], 61)

    def test_prepare_all_and_prime_are_mutually_exclusive(self):
        for first, second in (("prime", "prepare_all"), ("prepare_all", "prime"),
                              ("prepare_all", "prepare_all")):
            with self.subTest(first=first, second=second):
                client, _, bridge = self.client()
                getattr(client, first)()
                calls_before = len(bridge.calls)
                with self.assertRaisesRegex(ValueError, "state"):
                    getattr(client, second)()
                self.assertEqual(len(bridge.calls), calls_before)

    def test_prepare_all_reset_retains_connection_and_allows_live_mode_again(self):
        client, server, bridge = self.client()
        transport = client.transport
        summaries = []
        for sample in range(2):
            if sample:
                client.reset_workflow()
            summary = client.prepare_all()
            summaries.append(summary)
            self.run_steps(client)
            self.assertEqual(client.assert_complete()["spent_units"], 8)
        self.assertEqual(len(server.registrations), 1)
        self.assertIs(client.transport, transport)
        self.assertEqual([x["positions"] for x in summaries[0]["step_allocations"]],
                         [x["positions"] for x in summaries[1]["step_allocations"]])
        self.assertNotEqual(summaries[0]["step_allocations"][0]["token_id"],
                            summaries[1]["step_allocations"][0]["token_id"])
        requests = [p for m, p, _ in transport.calls if m == "tools/call"]
        self.assertEqual(len({p["_meta"][AUTH_META]["nonce"] for p in requests}), 10)
        client.reset_workflow()
        live = client.prime()
        self.assertEqual(live["reserved_unit_count"], 6)
        self.run_steps(client)
        self.assertEqual(client.assert_complete()["spent_units"], 8)
        self.assertEqual([op for op, _ in bridge.calls].count("prepare"), 15)

    def test_prepare_all_cannot_reset_partially_consumed_handles(self):
        client, _, _ = self.client()
        client.prepare_all()
        client.call_step(0)
        with self.assertRaisesRegex(ValueError, "accounting_incomplete"):
            client.reset_workflow()
        with self.assertRaisesRegex(ValueError, "accounting_incomplete"):
            client.assert_complete()

    def test_prepare_all_oauth_has_no_native_work_or_background(self):
        client, _, bridge = self.client(mode="oauth")
        summary = client.prepare_all()
        self.assertEqual(summary["prepared_token_count"], 0)
        self.assertEqual(summary["reserved_unit_count"], 0)
        self.assertEqual(summary["all_preparation_ns"], 0)
        self.assertEqual(summary["all_native_preparation_ns"], 0)
        self.assertEqual([row["positions"] for row in summary["step_allocations"]],
                         [[160], [161], [162, 163, 164, 165], [166], [167]])
        values = self.run_steps(client)
        consumed = [row["positions"] for row in client.events if row["event"] == "token_consumed"]
        self.assertEqual(consumed, [row["positions"] for row in summary["step_allocations"]])
        self.assertEqual(bridge.calls, [])
        self.assertTrue(all(value["prepared_token"] is None for value in values))
        self.assertEqual(client.assert_complete()["spent_units"], 8)

    def test_prepare_all_disabled_clock_has_no_timing_reads(self):
        with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("clock used")):
            client, _, _ = self.client(clock=Clock(False))
            summary = client.prepare_all()
            self.assertNotIn("all_preparation_ns", summary)
            values = self.run_steps(client)
            self.assertTrue(all("timing" not in value for value in values))
            self.assertTrue(all(value["readiness"]["ready_before_demand"] for value in values))
            self.assertTrue(all(event["at_ns"] is None for event in client.events))
            self.assertEqual(client.assert_complete()["spent_units"], 8)

    def test_research_reserves_sixty_one_and_never_replenishes(self):
        for mode in ("darlt", "darlt-ablation", "sma"):
            with self.subTest(mode=mode):
                client, _, bridge = self.client(mode=mode, steps=research(), quota=64)
                initial = client.prime()
                self.assertEqual(initial["reserved_unit_count"], 61)
                self.assertEqual(initial["prepared_entry_count"], 5)
                self.assertEqual(initial["prepared_token_count"], 5 if mode == "darlt" else 61)
                values = self.run_steps(client)
                self.assertEqual(sum(x["units"] for x in values), 61)
                self.assertEqual(client.assert_complete()["spent_units"], 61)
                self.assertEqual(len(client.preparations), 5)
                self.assertTrue(all(p["reason"] == "initial" for p in client.preparations))
                self.assertEqual(client.start_background()["count"], 0)
                self.assertTrue(all(args["ablation"] == (mode == "darlt-ablation")
                                    for op, args in bridge.calls if op == "prepare"))

    def test_oauth_has_no_native_prepare_and_research_scopes(self):
        client, server, bridge = self.client(mode="oauth", steps=research(), quota=64)
        initial = client.prime()
        self.assertEqual(initial["initial_preparation_ns"], 0)
        self.assertEqual(initial["prepared_token_count"], 0)
        self.assertIn("export_report:inventory/allowed", server.registrations[0][2]["scopes"])
        values = self.run_steps(client)
        self.assertEqual(bridge.calls, [])
        self.assertTrue(all(x["timing"]["native_online_ns"] == 0 for x in values))
        self.assertEqual(client.assert_complete()["spent_units"], 61)
        self.assertFalse(any(e["event"].startswith("prepare_") for e in client.events))

    def test_actual_arguments_are_bound_instead_of_replaced(self):
        client, _, bridge = self.client()
        client.prime()
        value = client.call_step(0, {"query": "actual-model-query"})
        self.assertEqual(value["arguments"]["query"], "actual-model-query")
        online = next(args for op, args in bridge.calls if op == "online")
        self.assertEqual(json.loads(online["context"])["arguments"]["query"], "actual-model-query")
        self.assertEqual(client.transport.calls[-1][1]["arguments"]["query"], "actual-model-query")

    def test_changed_actual_policy_rejected_without_consuming_prepared_handle(self):
        client, _, bridge = self.client()
        client.prime()
        with self.assertRaisesRegex(ValueError, "actual_policy_mismatch"):
            client.call_step(0, {"query": "hotel", "resource": "inventory/restricted"})
        self.assertFalse(any(op == "online" for op, _ in bridge.calls))
        self.assertEqual(client.spent_positions, [])

    def test_reset_reuses_registration_connection_and_authorized_units(self):
        client, server, bridge = self.client()
        transport = client.transport
        previous_events = None
        for sample in range(3):
            client.reset_workflow()
            client.prime()
            self.run_steps(client)
            self.assertEqual(client.assert_complete()["spent_units"], 8)
            if previous_events is not None:
                self.assertTrue(previous_events)
                self.assertIsNot(previous_events, client.events)
            previous_events = client.events
        self.assertEqual(len(server.registrations), 1)
        self.assertIs(client.transport, transport)
        self.assertEqual(len([op for op, _ in bridge.calls if op == "prepare"]), 15)
        requests = [p for m, p, _ in transport.calls if m == "tools/call"]
        self.assertEqual(len({p["_meta"][AUTH_META]["nonce"] for p in requests}), 15)

    def test_reset_cannot_hide_partially_executed_workflow(self):
        client, _, _ = self.client()
        client.prime()
        client.call_step(0)
        with self.assertRaisesRegex(ValueError, "accounting_incomplete"):
            client.reset_workflow()

    def test_scope_validation_before_registration(self):
        with self.assertRaisesRegex(ValueError, "distinct"):
            self.client(positions=[0] * 16)
        with self.assertRaisesRegex(ValueError, "insufficient_scope"):
            self.client(positions=range(7))

    def test_step_order_and_double_consumption_rejected(self):
        client, _, _ = self.client()
        client.prime()
        with self.assertRaisesRegex(ValueError, "step_order"):
            client.call_step(1)
        client.call_step(0)
        with self.assertRaisesRegex(ValueError, "step_order"):
            client.call_step(0)

    def test_rejected_request_never_marked_spent(self):
        client, _, _ = self.client()
        client.prime()
        FakeTransport.reject = True
        with self.assertRaises(RpcError):
            client.call_step(0)
        self.assertEqual(client.spent_positions, [])

    def test_body_byte_measurement_must_match_server(self):
        client, _, _ = self.client()
        client.prime()
        FakeTransport.mismatch_body = True
        with self.assertRaisesRegex(ValueError, "body_length_mismatch"):
            client.call_step(0)

    def test_disabled_clock_does_not_read_performance_clock(self):
        with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("clock used")):
            client, _, _ = self.client(clock=Clock(False))
            initial = client.prime()
            self.assertNotIn("initial_preparation_ns", initial)
            values = self.run_steps(client)
            self.assertTrue(all("timing" not in x for x in values))
            self.assertTrue(all(event["at_ns"] is None for event in client.events))

    def test_unfinished_future_wait_is_recorded_and_then_consumed(self):
        steps = [("search_inventory", {"query": "hotel"})] * 2
        bridge = FakeBridge(block_prepare_number=2)
        client, _, _ = self.client(steps=steps, quota=4, bridge=bridge)
        client.prime()
        client.call_step(0)
        client.start_background()
        self.assertTrue(bridge.block_entered.wait(2))
        waiting = threading.Event()
        original_event = client._event

        def capture(event, **values):
            row = original_event(event, **values)
            if event == "ready_wait_started":
                waiting.set()
            return row

        client._event = capture
        try:
            with ThreadPoolExecutor(max_workers=1) as executor:
                result = executor.submit(client.call_step, 1)
                try:
                    self.assertTrue(waiting.wait(2))
                finally:
                    bridge.release.set()
                value = result.result(timeout=2)
        finally:
            bridge.release.set()
        self.assertFalse(value["readiness"]["ready_before_demand"])
        self.assertGreater(value["timing"]["future_wait_ns"], 0)
        self.assertEqual(client.assert_complete()["spent_units"], 2)


if __name__ == "__main__":
    unittest.main()
