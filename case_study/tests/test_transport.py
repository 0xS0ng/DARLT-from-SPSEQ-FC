"""Correctness of stateless MCP framing and the actual local HTTP endpoint."""
import copy
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

import httpx

from case_study import mcp
from case_study.common import AUTH_META, VERSION, Clock, canonical
from case_study.server import ToolServer
from case_study.client import Client


def annotated_tool():
    return {"name": "test_tool", "inputSchema": {"type": "object", "properties": {
        "nested": {"type": "object", "properties": {
            "resource": {"type": "string", "x-mcp-header": "Resource"}}}}}}


class FramingTests(unittest.TestCase):
    def valid(self):
        tool = annotated_tool()
        body = mcp.request("tools/call", {"name": tool["name"], "arguments": {
            "nested": {"resource": "资源"}}}, request_id="request-1")
        return body, mcp.request_headers(body, tool), [tool]

    def test_each_request_is_self_contained_without_initialize(self):
        for index in (1, 2):
            body = mcp.request("tools/list", request_id=index)
            self.assertEqual(body["params"]["_meta"][mcp.PV], VERSION)
            self.assertIn(mcp.CAP, body["params"]["_meta"])
            self.assertEqual(mcp.validate(body, mcp.request_headers(body), []), body)

    def test_required_metadata_and_mirrored_headers(self):
        body, headers, tools = self.valid()
        self.assertEqual(mcp.validate(body, headers, tools), body)
        for field in (mcp.PV, mcp.CAP):
            bad = copy.deepcopy(body); bad["params"]["_meta"].pop(field)
            with self.subTest(field=field), self.assertRaises(mcp.RpcError):
                mcp.validate(bad, headers, tools)
        for field, value in [("MCP-Protocol-Version", "2025-11-25"), ("Mcp-Method", "ping"),
                             ("Mcp-Name", "another_tool"), ("Mcp-Param-Resource", "wrong")]:
            bad = dict(headers); bad[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(mcp.RpcError, "mismatch"):
                mcp.validate(body, bad, tools)

    def test_unsupported_version_differs_from_header_mismatch(self):
        body = mcp.request("tools/list"); body["params"]["_meta"][mcp.PV] = "2025-11-25"
        with self.assertRaises(mcp.RpcError) as caught:
            mcp.validate(body, mcp.request_headers(body), [])
        self.assertEqual(caught.exception.code, -32022)
        self.assertEqual(caught.exception.data["supported"], [VERSION])

    def test_header_missing_duplicate_media_and_content_type(self):
        body, headers, tools = self.valid()
        for name in ("MCP-Protocol-Version", "Mcp-Method", "Mcp-Name", "Mcp-Param-Resource"):
            bad = dict(headers); bad.pop(name)
            with self.subTest(name=name), self.assertRaises(mcp.RpcError):
                mcp.validate(body, bad, tools)
        duplicate = httpx.Headers(list(headers.items()) + [("Mcp-Method", "tools/call")])
        with self.assertRaisesRegex(mcp.RpcError, "duplicate"):
            mcp.validate(body, duplicate, tools)
        for name, value, status in [("Accept", "application/json", 406),
                                     ("Content-Type", "text/plain", 415)]:
            bad = dict(headers); bad[name] = value
            with self.subTest(name=name), self.assertRaises(mcp.RpcError) as caught:
                mcp.validate(body, bad, tools)
            self.assertEqual(caught.exception.status, status)

    def test_header_encoding_preserves_unicode_whitespace_and_reserved_marker(self):
        for value in ["资源", "\n", " leading ", "=?base64?QQ==?=", "ASCII"]:
            with self.subTest(value=value):
                self.assertEqual(mcp.decode_header(mcp.header_value(value)), value)
        self.assertEqual(mcp.header_value(True), "true")
        self.assertEqual(mcp.header_value(False), "false")
        self.assertEqual(mcp.header_value(2**53 - 1), str(2**53 - 1))
        for value in [2**53, -2**53, 0.5, None, {}]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                mcp.header_value(value)
        for value in ["\n", "资源", "=?base64?*?=", "=?base64?/w==?="]:
            with self.subTest(value=value), self.assertRaises(mcp.RpcError):
                mcp.decode_header(value)

    def test_header_annotations_require_unique_reachable_primitive_fields(self):
        self.assertEqual(mcp.annotations(annotated_tool()["inputSchema"]),
                         [("Resource", ("nested", "resource"))])
        invalid = [
            {"properties": {"x": {"type": "array", "x-mcp-header": "X"}}},
            {"properties": {"x": {"type": "string", "x-mcp-header": "bad name"}}},
            {"properties": {"x": {"type": "string", "x-mcp-header": "X"},
                            "y": {"type": "string", "x-mcp-header": "x"}}},
            {"properties": {"x": {"type": "array", "items": {
                "type": "string", "x-mcp-header": "Hidden"}}}},
        ]
        for schema in invalid:
            with self.subTest(schema=schema), self.assertRaises(ValueError):
                mcp.annotations(schema)

    def test_json_and_sse_return_the_same_final_result(self):
        final = mcp.complete(7, {"structuredContent": {"accepted": True}})
        event = {"jsonrpc": "2.0", "method": "notifications/progress", "params": {}}
        json_response = httpx.Response(200, headers={"Content-Type": "application/json"}, content=canonical(final))
        sse = b": keepalive\r\n\r\n" + b"data: " + canonical(event) + b"\n\n" + b"event: message\ndata: " + canonical(final) + b"\n\n"
        sse_response = httpx.Response(200, headers={"Content-Type": "text/event-stream"}, content=sse)
        self.assertEqual(mcp.decode_response(json_response, 7), mcp.decode_response(sse_response, 7))

    def test_sse_rejects_independent_requests_duplicate_or_missing_final(self):
        final = b"data: " + canonical(mcp.complete(7, {})) + b"\n\n"
        independent = b"data: " + canonical({"jsonrpc": "2.0", "id": 9, "method": "ping"}) + b"\n\n"
        for body in [independent + final, final + final, b": no final\n\n"]:
            response = httpx.Response(200, headers={"Content-Type": "text/event-stream"}, content=body)
            with self.subTest(body=body[:30]), self.assertRaises(ValueError):
                mcp.decode_response(response, 7)


class LogicalBoundaryTests(unittest.TestCase):
    """Integer sequence arithmetic only; no performance clock or saved data."""
    class LogicalClock:
        enabled = True

        def __init__(self):
            self.value = 0
            self.events = []

        def start(self):
            self.value += 100
            self.events.append(("boundary", self.value))
            return self.value

        def advance(self, label, value):
            self.value += value
            self.events.append((label, self.value))

    def client(self, mode, *, interactive=False):
        clock = self.LogicalClock()

        class FakeBridge:
            def command(self, op, **_):
                if op == "prepare":
                    clock.advance("native preparation", 23)
                    return {"handle": "test-handle", "timing": {"preparation_ns": 13}}
                if op == "online":
                    clock.advance("native online", 31)
                    return {"wire_hex": ["00"], "session": "test-prover" if interactive else None,
                            "timing": {"online_ns": 11}}
                if op == "client_round":
                    clock.advance("native continuation", 19)
                    return {"wire_hex": ["00"], "timing": {"online_ns": 3}}
                raise AssertionError("unexpected fake native operation")

        class FakeTransport:
            url = "http://127.0.0.1/test-only-no-socket"

            def __init__(self):
                self.requests = []

            def send(self, method, params, headers, tool):
                self.requests.append(copy.deepcopy((method, params, headers)))
                clock.advance("HTTP and parsed response", 17)
                meta = {AUTH_META: {"timing": {"decode_ns": 7, "verification_ns": 5,
                                               "native_round_ns": 40}}}
                if interactive and len(self.requests) == 1:
                    meta[AUTH_META]["wire_hex"] = ["00"]
                    return {"resultType": "input_required", "requestState": "test-request", "_meta": meta}
                return {"resultType": "complete", "structuredContent": {"accepted": True,
                            "units": 1, "tool_result": {"items": []}}, "_meta": meta}

        client = Client.__new__(Client)
        client.server = SimpleNamespace(period=1, domain="https://test-only.invalid", nonce="server-nonce")
        client.bridge, client.mode, client.instance = FakeBridge(), mode, "test-instance"
        client.clock, client.cursor, client.actor = clock, 0, "agent"
        client.dpop_key, client.access_token = "test-key-object", "test-access-token"
        client.transport, client.tools = FakeTransport(), {}
        return client, clock

    def test_none_oauth_have_exact_zero_preparation_and_dpop_is_request_work(self):
        for mode in ("none", "oauth"):
            client, clock = self.client(mode)
            def sign(*_):
                clock.advance("DPoP signing", 37)
                return "test-DPoP"
            with self.subTest(mode=mode), patch("case_study.client.dpop_sign", side_effect=sign) as signing,\
                 patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("real performance clock")):
                result = client.call("search_inventory", {"query": "hotel"}, nonce="logical-request-nonce")
            values = result["timing"]
            self.assertEqual(values["client_preparation_ns"], 0)
            self.assertEqual(values["active_tool_ns"], values["request_latency_ns"])
            if mode == "oauth":
                signing.assert_called_once()
                self.assertEqual(clock.events[0], ("boundary", 100))
                self.assertEqual(clock.events[1], ("DPoP signing", 137))
                self.assertGreater(values["request_latency_ns"], values["mcp_http_ns"])
            else:
                signing.assert_not_called()

    def test_native_windows_share_one_boundary_and_nested_segments_are_not_resummed(self):
        client, clock = self.client("darlt")
        with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("real performance clock")):
            result = client.call("search_inventory", {"query": "hotel"}, nonce="logical-request-nonce")
        values = result["timing"]
        self.assertEqual(values["client_preparation_ns"] + values["request_latency_ns"], values["active_tool_ns"])
        endpoints = [v for label, v in clock.events if label == "boundary"]
        self.assertEqual(len(endpoints), 4)  # t0, shared t1, HTTP start, t2.
        self.assertEqual(values["client_preparation_ns"], endpoints[1] - endpoints[0])
        self.assertEqual(values["request_latency_ns"], endpoints[-1] - endpoints[1])
        self.assertEqual(values["active_tool_ns"], endpoints[-1] - endpoints[0])
        self.assertEqual(values["verification_ns"], 5)
        self.assertEqual(values["native_round_ns"], 40)

    def test_live_round_components_are_accumulated_exactly_once(self):
        client, _ = self.client("msb", interactive=True)
        with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("real performance clock")):
            result = client.call("search_inventory", {"query": "hotel"}, nonce="logical-request-nonce")
        values = result["timing"]
        self.assertEqual(result["http_requests"], 2)
        self.assertEqual(values["online_ns"], 14)
        self.assertEqual(values["decode_ns"], 14)
        self.assertEqual(values["verification_ns"], 10)
        self.assertEqual(values["native_round_ns"], 80)
        self.assertEqual(values["client_preparation_ns"] + values["request_latency_ns"], values["active_tool_ns"])
        self.assertEqual(client.transport.requests[1][1]["requestState"], "test-request")
        for final in [mcp.complete(8, {}), {"jsonrpc": "2.0", "id": 7, "result": {"resultType": "other"}}]:
            response = httpx.Response(200, headers={"Content-Type": "application/json"}, content=canonical(final))
            with self.assertRaises(ValueError):
                mcp.decode_response(response, 7)


class HttpEndpointTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.server = ToolServer(Path(self.directory.name), None, None)
        self.client = httpx.Client(trust_env=False, timeout=5)
        self.url = self.server.url + "/mcp/none"

    def tearDown(self):
        self.client.close(); self.server.close(); self.directory.cleanup()

    def post(self, method="tools/list", params=None, change=None):
        body = mcp.request(method, params)
        headers = mcp.request_headers(body)
        headers.update(change or {})
        return self.client.post(self.url, content=canonical(body), headers=headers)

    def test_post_only_and_no_session_or_initialization_handshake(self):
        for method in ("GET", "DELETE"):
            response = self.client.request(method, self.url)
            self.assertEqual(response.status_code, 405)
            self.assertEqual(response.headers["Allow"], "POST")
        for _ in range(2):
            response = self.post()
            self.assertEqual(response.status_code, 200)
            self.assertNotIn("Mcp-Session-Id", response.headers)
            self.assertEqual(mcp.decode_response(response, 1)["resultType"], "complete")
        self.assertEqual(self.post("initialize").status_code, 404)

    def test_origin_is_checked_before_request_execution(self):
        self.assertEqual(self.post(change={"Origin": "https://untrusted.test"}).status_code, 403)
        self.assertEqual(self.post(change={"Origin": self.server.url}).status_code, 200)
        self.assertEqual(self.server.stores["none"].facts()["effects"], 0)

    def test_stateless_sse_endpoint_and_untimed_clock(self):
        self.server.sse = True
        self.server.register('untimed-noauth', "none")
        with patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError('untimed performance clock')):
            self.assertIsNone(Clock().start()); self.assertIsNone(Clock().elapsed(None))
            response = self.post()
            tool = next(t for t in self.server.tools if t["name"] == "search_inventory")
            body = mcp.request("tools/call", {"name": "search_inventory", "arguments": {"query": "hotel"},
                                "_meta": {AUTH_META: {"instance": 'untimed-noauth', "nonce": 'fresh-nonce-for-untimed'}}})
            result = self.client.post(self.url, content=canonical(body), headers=mcp.request_headers(body, tool))
        self.assertEqual(response.headers["Content-Type"], "text/event-stream")
        self.assertIn("tools", mcp.decode_response(response, 1))
        accepted = mcp.decode_response(result, 1)
        self.assertTrue(accepted["structuredContent"]["accepted"])
        self.assertNotIn("timing", canonical(accepted).decode())
        self.assertNotIn("_ns", canonical(accepted).decode())


if __name__ == "__main__":
    unittest.main()
