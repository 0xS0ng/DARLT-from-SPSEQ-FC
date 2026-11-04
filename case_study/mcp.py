"""MCP 2026-07-28 Streamable HTTP request/response adaptation."""
from __future__ import annotations

import base64
import httpx
from .common import VERSION, AUTH_META, canonical, strict

PV = "io.modelcontextprotocol/protocolVersion"
CAP = "io.modelcontextprotocol/clientCapabilities"
INFO = "io.modelcontextprotocol/clientInfo"


class RpcError(ValueError):
    def __init__(self, code, message, status=400, data=None):
        super().__init__(message)
        self.code, self.status, self.data = code, status, data

    def response(self, request_id=None):
        error = {"code": self.code, "message": str(self)}
        if self.data is not None:
            error["data"] = self.data
        return {"jsonrpc": "2.0", "id": request_id, "error": error}


def header_value(value):
    if type(value) is bool:
        value = str(value).lower()
    elif type(value) is int:
        if abs(value) > 2**53 - 1:
            raise ValueError("unsafe_header_integer")
        value = str(value)
    if not isinstance(value, str):
        raise ValueError("header_parameter_type")
    safe = value == value.strip() and all(0x20 <= ord(c) <= 0x7e or c == "\t" for c in value)
    if not safe or (value.startswith("=?base64?") and value.endswith("?=")):
        return "=?base64?" + base64.b64encode(value.encode()).decode() + "?="
    return value


def decode_header(value):
    if not isinstance(value, str) or any(ord(c) < 0x20 and c != "\t" or ord(c) > 0x7e for c in value):
        raise RpcError(-32020, "Malformed mirrored header")
    if value.startswith("=?base64?") and value.endswith("?="):
        try:
            return base64.b64decode(value[9:-2], validate=True).decode("utf-8")
        except (ValueError, UnicodeError) as exc:
            raise RpcError(-32020, "Malformed encoded header") from exc
    return value


def _one(headers, name):
    if hasattr(headers, "get_all"):
        values = headers.get_all(name, [])
    elif hasattr(headers, "get_list"):
        values = headers.get_list(name)
    else:
        values = [v for k, v in headers.items() if k.lower() == name.lower()]
    if len(values) != 1:
        raise RpcError(-32020, "Missing or duplicate " + name)
    return values[0]


def annotations(schema, path=(), seen=None):
    seen = set() if seen is None else seen
    out = []
    if not isinstance(schema, dict):
        raise ValueError("tool_schema")
    for key, definition in schema.get("properties", {}).items():
        if not isinstance(definition, dict):
            raise ValueError("tool_schema")
        if "x-mcp-header" in definition:
            name = definition["x-mcp-header"]
            allowed = "!#$%&'*+-.^_`|~0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
            if (not isinstance(name, str) or not name or any(c not in allowed for c in name)
                    or name.lower() in seen or definition.get("type") not in ("string", "boolean", "integer")):
                raise ValueError("invalid_header_annotation")
            seen.add(name.lower()); out.append((name, path + (key,)))
        out.extend(annotations(definition, path + (key,), seen))
        for forbidden in ("items", "oneOf", "anyOf", "allOf", "not", "if", "then", "else", "$defs"):
            if "x-mcp-header" in str(definition.get(forbidden, "")):
                raise ValueError("unreachable_header_annotation")
    return out


def _lookup(arguments, path):
    value = arguments
    for name in path:
        if not isinstance(value, dict) or name not in value:
            return None
        value = value[name]
    return value


def request(method, params=None, request_id=1):
    p = dict(params or {}); meta = dict(p.get("_meta", {}))
    meta.update({PV: VERSION, INFO: {"name": "client", "version": "0.1.0"},
                 CAP: {"extensions": {AUTH_META: {}}}})
    p["_meta"] = meta
    return {"jsonrpc": "2.0", "id": request_id, "method": method, "params": p}


def request_headers(body, tool=None):
    result = {"Content-Type": "application/json", "Accept": "application/json, text/event-stream",
              "MCP-Protocol-Version": body["params"]["_meta"][PV], "Mcp-Method": body["method"]}
    if body["method"] in ("tools/call", "resources/read", "prompts/get"):
        result["Mcp-Name"] = header_value(body["params"].get("name", body["params"].get("uri")))
    if tool:
        for name, path in annotations(tool["inputSchema"]):
            v = _lookup(body["params"].get("arguments", {}), path)
            if v is not None:
                result["Mcp-Param-" + name] = header_value(v)
    return result


def validate(body, headers, tools):
    if (not isinstance(body, dict) or body.get("jsonrpc") != "2.0" or not isinstance(body.get("method"), str)
            or type(body.get("id")) not in (str, int) or not isinstance(body.get("params"), dict)):
        raise RpcError(-32600, "Invalid JSON-RPC request")
    meta = body["params"].get("_meta")
    if (not isinstance(meta, dict) or not isinstance(meta.get(PV), str)
            or not isinstance(meta.get(CAP), dict)):
        raise RpcError(-32602, "Required per-request metadata missing")
    if _one(headers, "MCP-Protocol-Version") != meta[PV] or _one(headers, "Mcp-Method") != body["method"]:
        raise RpcError(-32020, "Header and body mismatch")
    if meta[PV] != VERSION:
        raise RpcError(-32022, "Unsupported protocol version", data={"supported": [VERSION], "requested": meta[PV]})
    accept = _one(headers, "Accept")
    media = {s.split(";")[0].strip().lower() for s in accept.split(",")}
    if not {"application/json", "text/event-stream"} <= media:
        raise RpcError(-32600, "Both response media types are required", 406)
    if _one(headers, "Content-Type").split(";")[0].lower() != "application/json":
        raise RpcError(-32600, "Expected JSON request", 415)
    if body["method"] == "tools/call":
        name = body["params"].get("name")
        if not isinstance(name, str) or decode_header(_one(headers, "Mcp-Name")) != name:
            raise RpcError(-32020, "Tool name header mismatch")
        tool = next((t for t in tools if t["name"] == name), None)
        if tool:
            for field, path in annotations(tool["inputSchema"]):
                value = _lookup(body["params"].get("arguments", {}), path)
                if value is not None and decode_header(_one(headers, "Mcp-Param-" + field)) != decode_header(header_value(value)):
                    raise RpcError(-32020, "Tool parameter header mismatch")
    return body


def complete(request_id, result):
    return {"jsonrpc": "2.0", "id": request_id, "result": {"resultType": "complete", **result}}


def decode_response(response, request_id):
    media = response.headers.get("Content-Type", "").split(";")[0].lower()
    if media == "application/json":
        final = strict(response.content)
    elif media == "text/event-stream":
        final = None; data = []
        for line in response.text.replace("\r\n", "\n").split("\n") + [""]:
            if line.startswith(":"):
                continue
            if line.startswith("data:"):
                data.append(line[5:].lstrip(" "))
            elif not line and data:
                item = strict("\n".join(data)); data = []
                if "method" in item:
                    if "id" in item:
                        raise ValueError("independent_server_request_on_SSE")
                elif item.get("id") == request_id:
                    if final is not None:
                        raise ValueError("multiple_final_responses")
                    final = item
        if final is None:
            raise ValueError("missing_SSE_final_response")
    else:
        raise ValueError("unexpected_MCP_content_type")
    if final.get("jsonrpc") != "2.0" or final.get("id") != request_id:
        raise ValueError("MCP_response_id")
    if "error" in final:
        e = final["error"]; raise RpcError(e["code"], e["message"], response.status_code, e.get("data"))
    result = final.get("result")
    if not isinstance(result, dict) or result.get("resultType") not in ("complete", "input_required"):
        raise ValueError("MCP_result_type")
    return result


class Transport:
    def __init__(self, url):
        self.url = url
        self.client = httpx.Client(timeout=120, trust_env=False)
        self.request_id = 0
        self.last_request_stats = {}

    def send(self, method, params=None, headers=None, tool=None):
        self.request_id += 1
        body = request(method, params, self.request_id)
        head = request_headers(body, tool); head.update(headers or {})
        raw = canonical(body)
        outgoing = self.client.build_request("POST", self.url, content=raw, headers=head)
        request_line = b"POST " + outgoing.url.raw_path + b" HTTP/1.1\r\n"
        header_bytes = sum(len(name) + 2 + len(value) + 2 for name, value in outgoing.headers.raw) + 2
        auth = body["params"]["_meta"].get(AUTH_META, {})
        wires = auth.get("wire_hex", []) if isinstance(auth, dict) else []
        self.last_request_stats = {
            "request_body_bytes": len(raw), "request_line_bytes": len(request_line),
            "request_header_bytes": header_bytes,
            "http_sent_bytes": len(request_line) + header_bytes + len(raw),
            "auth_envelope_bytes": len(canonical(auth)),
            "native_token_bytes": sum(len(wire) // 2 for wire in wires),
        }
        result = self.client.send(outgoing)
        return decode_response(result, self.request_id)

    def close(self):
        self.client.close()
