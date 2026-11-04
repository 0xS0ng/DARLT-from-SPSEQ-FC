"""Shared wire format, endpoint policies, and opt-in measurement clock."""
from __future__ import annotations

import base64
import hashlib
import json
from pathlib import Path
import time

VERSION = "2026-07-28"
IMPLEMENTATION = "darlt-mcp/v0.1.0"
AUTH_META = "org.darlt/auth"
LIMIT = 2 * 1024 * 1024
MODES = ("none", "oauth", "sma", "msb", "slw", "darlt", "darlt-ablation")
NATIVE = {"sma": "SMA²RT", "msb": "MSB+23", "slw": "SLW+25",
          "darlt": "DARLT", "darlt-ablation": "DARLT-ablation"}
COSTS = {"search_inventory": 1, "get_details": 1, "book_item": 4, "batch_query": 8,
         "delete_record": 1, "export_private": 1,
         "search_sources": 1, "fetch_documents": 8, "query_dataset": 16,
         "run_analysis": 4, "export_report": 32}
RESEARCH = ("search_sources", "fetch_documents", "query_dataset", "run_analysis", "export_report")
DOCUMENT_IDS = tuple(f"doc-{i:02d}" for i in range(1, 9))
TOOL_ATTRIBUTES = {"search_inventory": 1, "get_details": 1, "book_item": 2,
                   "batch_query": 3, "delete_record": 5, "export_private": 6,
                   "search_sources": 1, "fetch_documents": 1, "query_dataset": 3,
                   "run_analysis": 2, "export_report": 2}


def canonical(value):
    result = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                        allow_nan=False).encode("utf-8")
    if len(result) > LIMIT:
        raise ValueError("oversized_json")
    return result


def strict(data):
    if not isinstance(data, (str, bytes)) or len(data) > LIMIT:
        raise ValueError("invalid_json_body")
    def pairs(items):
        out = {}
        for k, v in items:
            if k in out:
                raise ValueError("duplicate_json_key")
            out[k] = v
        return out
    return json.loads(data, object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite_json")))


def b64(data):
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def unb64(value):
    if not isinstance(value, str) or "=" in value:
        raise ValueError("base64url_shape")
    result = base64.b64decode(value + "=" * (-len(value) % 4), altchars=b"-_", validate=True)
    if b64(result) != value:
        raise ValueError("base64url_noncanonical")
    return result


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def normalize(tool, arguments):
    if tool not in COSTS or not isinstance(arguments, dict):
        raise ValueError("unknown_tool_or_arguments")
    args = dict(arguments)
    args.setdefault("resource", "inventory/allowed")
    if args["resource"] not in ("inventory/allowed", "inventory/restricted", "owner/private"):
        raise ValueError("unknown_resource")
    fields = {"resource"}
    if tool in ("search_inventory", "search_sources"):
        fields.add("query")
        if not isinstance(args.get("query"), str) or not 1 <= len(args["query"]) <= 100:
            raise ValueError("query_shape")
    elif tool == "fetch_documents":
        fields.add("document_ids")
        ids = args.get("document_ids")
        if (not isinstance(ids, list) or len(ids) != 8 or any(not isinstance(x, str) for x in ids)
                or len(set(ids)) != 8 or set(ids) != set(DOCUMENT_IDS)):
            raise ValueError("fetch_requires_eight_distinct_documents")
        args["document_ids"] = sorted(ids)
    elif tool in ("query_dataset", "run_analysis"):
        fields.add("dataset_id")
        if args.get("dataset_id") != "market-v1":
            raise ValueError("dataset_id")
    elif tool == "export_report":
        fields.add("analysis_id")
        if args.get("analysis_id") != "analysis-001":
            raise ValueError("analysis_id")
    elif tool == "batch_query":
        fields.add("items")
        if not isinstance(args.get("items"), list) or len(args["items"]) != 8:
            raise ValueError("batch_requires_eight_items")
        for item in args["items"]:
            if not isinstance(item, dict) or set(item) != {"item_id", "resource"}:
                raise ValueError("batch_item_shape")
            if item["item_id"] != "hotel-101" or item["resource"] not in ("inventory/allowed", "inventory/restricted", "owner/private"):
                raise ValueError("batch_item_value")
    else:
        fields.add("item_id")
        if args.get("item_id") != "hotel-101":
            raise ValueError("item_shape")
        if tool == "book_item":
            fields.add("customer")
            if not isinstance(args.get("customer"), str) or not 1 <= len(args["customer"]) <= 100:
                raise ValueError("customer_shape")
    if set(args) != fields:
        raise ValueError("unexpected_tool_argument")
    return args


def policy(tool, arguments, period=1):
    args = normalize(tool, arguments)
    index = TOOL_ATTRIBUTES[tool]
    resources = [args["resource"]]
    if tool == "batch_query":
        resources.extend(item["resource"] for item in args["items"])
    required = {index}
    if "inventory/restricted" in resources:
        required.add(4)
    if "owner/private" in resources:
        required.add(6)
    return {"period": period, "required_attrs": [{"index": i, "value": 1} for i in sorted(required)]}


def request_context(domain, tool, arguments, period, nonce):
    if not isinstance(nonce, str) or len(nonce) < 16:
        raise ValueError("request_nonce")
    return canonical({"domain": domain, "tool": tool, "arguments": normalize(tool, arguments),
                      "period": period, "nonce": nonce}).decode("utf-8")


def declarations(include_privileged=False):
    descriptions = {"search_inventory": "Search the local hotel inventory.",
                    "get_details": "Read hotel details and its current booking count.",
                    "book_item": "Book a hotel for the synthetic customer.",
                    "batch_query": "Read eight hotel records in one request.",
                    "search_sources": "Search the deterministic local market sources. Returns eight document IDs. Fixed cost: 1 unit; required attribute: 1.",
                    "fetch_documents": "Fetch all eight document IDs returned by search_sources. Fixed cost: 8 units; required attribute: 1.",
                    "query_dataset": "After fetching the eight documents, query market-v1 and return sixteen dataset rows. Fixed cost: 16 units; required attribute: 3.",
                    "run_analysis": "After query_dataset, compute sum, mean, minimum and maximum over market-v1. Returns analysis-001. Fixed cost: 4 units; required attribute: 2.",
                    "export_report": "After run_analysis, export analysis-001 as a complete report with 32 sections. Fixed cost: 32 units; required attribute: 2.",
                    "delete_record": "Delete a synthetic record (separate privileged grant).",
                    "export_private": "Read a synthetic private record (private-attribute policy)."}
    result = []
    names = ("search_inventory", "get_details", "book_item", "batch_query") + RESEARCH
    if include_privileged:
        names += ("delete_record", "export_private")
    for name in names:
        props = {"resource": {"type": "string", "enum": ["inventory/allowed", "inventory/restricted", "owner/private"]}}
        required = []
        if name in ("search_inventory", "search_sources"):
            props["query"] = {"type": "string"}; required.append("query")
        elif name == "fetch_documents":
            props["document_ids"] = {"type": "array", "minItems": 8, "maxItems": 8,
                                     "uniqueItems": True, "items": {"type": "string", "enum": list(DOCUMENT_IDS)}}
            required.append("document_ids")
        elif name in ("query_dataset", "run_analysis"):
            props["dataset_id"] = {"type": "string", "enum": ["market-v1"]}; required.append("dataset_id")
        elif name == "export_report":
            props["analysis_id"] = {"type": "string", "enum": ["analysis-001"]}; required.append("analysis_id")
        elif name == "batch_query":
            props["items"] = {"type": "array", "minItems": 8, "maxItems": 8,
                              "items": {"type": "object", "properties": {
                                  "item_id": {"type": "string", "enum": ["hotel-101"]},
                                  "resource": {"type": "string", "enum": ["inventory/allowed", "inventory/restricted", "owner/private"]}},
                                  "required": ["item_id", "resource"], "additionalProperties": False}}
            required.append("items")
        else:
            props["item_id"] = {"type": "string", "enum": ["hotel-101"]}; required.append("item_id")
            if name == "book_item":
                props["customer"] = {"type": "string"}; required.append("customer")
        result.append({"name": name, "description": descriptions[name], "inputSchema": {
            "type": "object", "properties": props, "required": required, "additionalProperties": False},
            "annotations": {"org.darlt/unitCost": COSTS[name], "org.darlt/requiredAttributes": [TOOL_ATTRIBUTES[name]]}})
    return result


class Clock:
    'Untimed calls do not read a performance clock or produce durations.'
    def __init__(self, enabled=False):
        self.enabled = enabled

    @classmethod
    def authorized(cls, path):
        plan = strict(Path(path).read_bytes())
        window = plan.get('timing_window') or {}
        now = time.time()
        if (plan.get("case_study_authorized") is not True or plan.get('timing_enabled') is not True
                or not isinstance(window.get("start_unix_seconds"), (int, float))
                or now < window["start_unix_seconds"]
                or (window.get("end_unix_seconds") is not None and now > window["end_unix_seconds"])):
            raise ValueError("case study_timing_not_authorized")
        return cls(True)

    def start(self):
        return time.perf_counter_ns() if self.enabled else None

    def elapsed(self, start):
        return time.perf_counter_ns() - start if self.enabled and start is not None else None


def peer_instance(run_index):
    """Return the five-byte recipient identifier for one workflow run."""
    if type(run_index) is not int or not 0 <= run_index < 20:
        raise ValueError("peer_run_index")
    return "peer" + chr(ord("A") + run_index)
