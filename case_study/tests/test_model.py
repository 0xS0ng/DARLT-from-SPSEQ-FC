"""Model routing/shape tests use in-memory fakes; no key or external API."""
import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from case_study.common import Clock, canonical
from case_study.openrouter import OpenRouter, MODEL, PROVIDER


class FakeResponse:
    def __init__(self, data, status=200):
        self.data, self.status_code = copy.deepcopy(data), status

    def json(self):
        return copy.deepcopy(self.data)


def assistant(tool="search_inventory"):
    message = {"role": "assistant", "content": "Final confirmed booking."}
    if tool:
        message["tool_calls"] = [{"id": "call-one", "type": "function", "function": {
            "name": tool, "arguments": '{"query":"hotel"}'}}]
    return {"model": MODEL, "provider": "Google Vertex", "choices": [{"finish_reason": "stop", "message": message}]}


class FakeClient:
    def __init__(self, response=None, credit=None):
        self.response = response or assistant()
        self.credit = credit or {"is_management_key": False, "limit": 3.0, "limit_remaining": 2.0}
        self.gets, self.posts, self.closed = [], [], False

    def get(self, path):
        self.gets.append(path); return FakeResponse({"data": self.credit})

    def post(self, path, json):
        self.posts.append((path, copy.deepcopy(json))); return FakeResponse(self.response)

    def close(self):
        self.closed = True


class ModelTests(unittest.TestCase):
    def test_fixed_model_provider_route_and_no_temperature_or_fallback(self):
        fake = FakeClient()
        with patch("case_study.openrouter.read_api_key", side_effect=AssertionError("key access")),\
             patch("case_study.openrouter.httpx.Client", side_effect=AssertionError("network construction")),\
             patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError('untimed performance clock')):
            model = OpenRouter(Clock(), client=fake)
            message, metadata = model.complete([], [], "search_inventory")
        payload = fake.posts[0][1]
        self.assertEqual(payload["model"], MODEL)
        self.assertEqual(payload["provider"], {"only": [PROVIDER], "order": [PROVIDER],
                                             "allow_fallbacks": False, "require_parameters": True})
        self.assertNotIn("temperature", payload)
        self.assertEqual(payload["tool_choice"], "auto")
        self.assertEqual(message["tool_calls"][0]["function"]["name"], "search_inventory")
        self.assertEqual(metadata["provider_route"], PROVIDER)
        self.assertNotIn("model_api_ns", metadata)

    def test_expected_tool_is_exactly_one_native_tool_call(self):
        valid = assistant()
        variants = []
        for calls in [[], valid["choices"][0]["message"]["tool_calls"] * 2,
                      [{"type": "function", "function": {"name": "search_inventory", "arguments": "{}"}}],
                      [{"id": "one", "type": "other", "function": {"name": "search_inventory", "arguments": "{}"}}],
                      [{"id": "one", "type": "function", "function": {"name": "book_item", "arguments": "{}"}}],
                      [{"id": "one", "type": "function", "function": {"name": "search_inventory", "arguments": {}}}]]:
            data = copy.deepcopy(valid); data["choices"][0]["message"]["tool_calls"] = calls; variants.append(data)
        for data in variants:
            with self.subTest(data=data), self.assertRaisesRegex(ValueError, "unexpected_tool_call"):
                OpenRouter(Clock(), client=FakeClient(data)).complete([], [], "search_inventory")

    def test_final_step_checks_model_chose_no_tool_and_requires_real_text(self):
        fake = FakeClient(assistant(None))
        message, metadata = OpenRouter(Clock(), client=fake).complete([], [], None)
        self.assertEqual(fake.posts[0][1]["tool_choice"], "auto")
        self.assertTrue(message["content"].strip())
        self.assertNotIn("model_api_ns", metadata)
        for content in [None, "", " "]:
            data = assistant(None); data["choices"][0]["message"]["content"] = content
            with self.subTest(content=content), self.assertRaisesRegex(ValueError, "final_reply_required"):
                OpenRouter(Clock(), client=FakeClient(data)).complete([], [], None)
        with self.assertRaisesRegex(ValueError, "final_reply_required"):
            OpenRouter(Clock(), client=FakeClient(assistant())).complete([], [], None)

    def test_model_and_provider_must_match_declared_route(self):
        for field, value in [("model", MODEL + "-preview"), ("model", "another/model"),
                             ("provider", "Google AI Studio"), ("provider", "Unknown")]:
            data = assistant(); data[field] = value
            with self.subTest(field=field, value=value), self.assertRaisesRegex(ValueError, "unexpected_"):
                OpenRouter(Clock(), client=FakeClient(data)).complete([], [], "search_inventory")

    def test_incomplete_or_ambiguous_model_reply_rejected(self):
        for finish in ["length", "error", "content_filter"]:
            data = assistant(); data["choices"][0]["finish_reason"] = finish
            with self.subTest(finish=finish), self.assertRaisesRegex(ValueError, "incomplete_reply"):
                OpenRouter(Clock(), client=FakeClient(data)).complete([], [], "search_inventory")
        data = assistant(); data["choices"] *= 2
        with self.assertRaisesRegex(ValueError, "incomplete_reply"):
            OpenRouter(Clock(), client=FakeClient(data)).complete([], [], "search_inventory")

    def test_credit_limit_management_and_nonfinite_values_are_rejected(self):
        invalid = [{"is_management_key": True, "limit": 3, "limit_remaining": 2},
                   {"limit": 4, "limit_remaining": 2}, {"limit": True, "limit_remaining": 2},
                   {"limit": 3, "limit_remaining": 0}, {"limit": 3, "limit_remaining": float("nan")},
                   {"limit": float("inf"), "limit_remaining": 2}]
        for credit in invalid:
            fake = FakeClient(credit=credit)
            with self.subTest(credit=credit), self.assertRaisesRegex(ValueError, "ordinary_limited_key_required"):
                OpenRouter(Clock(), client=fake).complete([], [], "search_inventory")
            self.assertEqual(fake.posts, [])

    def test_sixty_call_cap_is_checked_before_remote_credit_or_inference(self):
        fake = FakeClient(); model = OpenRouter(Clock(), client=fake); model.calls = 60
        with self.assertRaisesRegex(ValueError, "workflow_model_call_count"):
            model.complete([], [], "search_inventory")
        self.assertEqual(fake.gets, []); self.assertEqual(fake.posts, [])

    def test_untimed_real_network_constructor_rejects_before_key_access(self):
        with patch("case_study.openrouter.read_api_key", side_effect=AssertionError("key access")),\
             patch("case_study.openrouter.httpx.Client", side_effect=AssertionError("network construction")),\
             patch("case_study.openrouter.os.environ.get", side_effect=AssertionError("environment access")):
            with self.assertRaisesRegex(ValueError, 'requires_enabled_timing'):
                OpenRouter(Clock())


    def test_future_or_expired_window_does_not_enable_performance_clock(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "plan.json"
            for window in [{"start_unix_seconds": 200, "end_unix_seconds": None},
                           {"start_unix_seconds": 0, "end_unix_seconds": 99}]:
                path.write_bytes(canonical({'timing_enabled': True, "case_study_authorized": True,
                                           'timing_window': window}))
                with self.subTest(window=window), patch("case_study.common.time.time", return_value=100),\
                     patch("case_study.common.time.perf_counter_ns", side_effect=AssertionError("performance clock")),\
                     self.assertRaisesRegex(ValueError, "case study_timing_not_authorized"):
                    Clock.authorized(path)


if __name__ == "__main__":
    unittest.main()
