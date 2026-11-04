"""Fixed-provider model transport, constructed only in an authorized run."""
from __future__ import annotations

import math
import os

import httpx
from .common import Clock

MODEL = "google/gemini-3.8-flash"
PROVIDER = "google-vertex/global"
ROUTING = {"order": [PROVIDER], "only": [PROVIDER], "allow_fallbacks": False, "require_parameters": True}


def read_api_key():
    key = os.environ.get("OPENROUTER_API_KEY")
    if not key:
        raise ValueError("OPENROUTER_API_KEY_unavailable")
    return key


class OpenRouter:
    def __init__(self, clock, *, budget_usd=3.0, client=None, key=None):
        if not clock.enabled and client is None:
            raise ValueError('model_API_requires_enabled_timing')
        self.clock, self.budget, self.calls = clock, budget_usd, 0
        self.client = client if client is not None else httpx.Client(base_url="https://openrouter.ai/api/v1", timeout=180,
                            trust_env=False, headers={"Authorization": "Bearer " + (key or read_api_key())})

    def check_credit(self):
        r = self.client.get("/key")
        if r.status_code != 200:
            raise ValueError("OpenRouter_key_check_failed")
        data = r.json().get("data", {})
        limit, remaining = data.get("limit"), data.get("limit_remaining")
        if (data.get("is_management_key") or type(limit) not in (int, float)
                or type(remaining) not in (int, float) or not math.isfinite(limit)
                or not math.isfinite(remaining) or not 0 < limit <= self.budget or remaining <= 0):
            raise ValueError("OpenRouter_ordinary_limited_key_required")

    def complete(self, messages, tools, expected_tool=None):
        if self.calls >= 60:
            raise ValueError("workflow_model_call_count")
        self.check_credit()
        # Validate the model-selected call against the workflow sequence.
        choice = "auto"
        payload = {"model": MODEL, "provider": dict(ROUTING), "messages": messages,
                   "tools": tools, "tool_choice": choice, "max_tokens": 4096}
        start = self.clock.start()
        response = self.client.post("/chat/completions", json=payload)
        duration = self.clock.elapsed(start)
        self.calls += 1
        if response.status_code != 200:
            raise ValueError("OpenRouter_inference_failed")
        data = response.json()
        if data.get("provider") not in ("Google", "Google Vertex", "Google Vertex AI"):
            raise ValueError("OpenRouter_unexpected_provider")
        if data.get("model") != MODEL:
            raise ValueError("OpenRouter_unexpected_model")
        choices = data.get("choices", [])
        if len(choices) != 1 or choices[0].get("finish_reason") in ("length", "error", "content_filter"):
            raise ValueError("OpenRouter_incomplete_reply")
        message = choices[0].get("message")
        if not isinstance(message, dict) or message.get("role") != "assistant":
            raise ValueError("OpenRouter_reply_shape")
        calls = message.get("tool_calls") or []
        if expected_tool:
            if (len(calls) != 1 or calls[0].get("type") != "function"
                    or not isinstance(calls[0].get("id"), str) or not calls[0]["id"]
                    or calls[0].get("function", {}).get("name") != expected_tool
                    or not isinstance(calls[0].get("function", {}).get("arguments"), str)):
                raise ValueError("OpenRouter_unexpected_tool_call")
        elif calls or not isinstance(message.get("content"), str) or not message["content"].strip():
            raise ValueError("OpenRouter_final_reply_required")
        metadata = {"model": data["model"], "provider": data["provider"], "provider_route": PROVIDER}
        if duration is not None:
            metadata["model_api_ns"] = duration
        return message, metadata

    def close(self):
        self.client.close()
