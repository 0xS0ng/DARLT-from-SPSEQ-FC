"""Local MCP endpoint; cryptographic acceptance precedes one SQLite commit."""
from __future__ import annotations

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
import secrets
import socket
import threading

from . import mcp
from .common import (AUTH_META, Clock, COSTS, IMPLEMENTATION, LIMIT, MODES, VERSION,
                     canonical, declarations, digest, normalize, policy, request_context, strict)
from .oauth import verify_dpop
from .store import Store, Denied


class ToolServer:
    def __init__(self, directory, bridge, oauth_verifier, *, clock=None, domain="https://mcp.test/resource",
                 verifier_id="bank-A", sse=False):
        self.directory = Path(directory); self.directory.mkdir(parents=True, exist_ok=True)
        self.bridge, self.oauth_verifier = bridge, oauth_verifier
        self.clock = clock or Clock(); self.domain, self.verifier_id = domain, verifier_id
        self.sse, self.period = sse, 1
        self.nonce = secrets.token_hex(16)
        self.instances, self.exchanges = {}, {}
        self.native_installations = {}
        self.exchange_lock = threading.RLock()
        self.stores = {mode: Store(self.directory / (mode + ".sqlite")) for mode in MODES}
        self.tools = declarations(include_privileged=True)
        for tool in self.tools:
            tool["inputSchema"]["properties"]["resource"]["x-mcp-header"] = "Resource"
        owner = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def setup(self):
                super().setup()
                self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)

            def log_message(self, *_):
                pass

            def _write(self, status, body, *, sse=False):
                data = canonical(body)
                if sse:
                    data = b"event: message\ndata: " + data + b"\n\n"
                self.send_response(status)
                self.send_header("Content-Type", "text/event-stream" if sse else "application/json")
                self.send_header("Content-Length", str(len(data)))
                if status >= 400:
                    # Early rejections may leave an unread request body.
                    self.close_connection = True
                    self.send_header("Connection", "close")
                if sse:
                    self.send_header("X-Accel-Buffering", "no")
                if status == 405:
                    self.send_header("Allow", "POST")
                self.end_headers(); self.wfile.write(data)

            def do_GET(self):
                self._write(405, mcp.RpcError(-32600, "POST endpoint", 405).response())

            do_DELETE = do_GET

            def do_POST(self):
                request_id = None
                try:
                    origin = self.headers.get_all("Origin", [])
                    if origin and (len(origin) != 1 or origin[0] != owner.url):
                        raise mcp.RpcError(-32000, "Origin rejected", 403)
                    lengths = self.headers.get_all("Content-Length", [])
                    if len(lengths) != 1 or not lengths[0].isdigit() or not 0 < int(lengths[0]) <= LIMIT:
                        raise mcp.RpcError(-32600, "Invalid content length", 400)
                    if self.headers.get("Transfer-Encoding"):
                        raise mcp.RpcError(-32600, "Unsupported transfer encoding", 400)
                    try:
                        raw_body = self.rfile.read(int(lengths[0]))
                        received_start = owner.clock.start()
                        body = strict(raw_body)
                    except (ValueError, UnicodeError):
                        raise mcp.RpcError(-32700, "Invalid JSON", 400) from None
                    if isinstance(body, dict):
                        request_id = body.get("id")
                    mcp.validate(body, self.headers, owner.tools)
                    pieces = self.path.split("/")
                    if len(pieces) != 3 or pieces[1] != "mcp" or pieces[2] not in MODES:
                        raise mcp.RpcError(-32601, "Endpoint not found", 404)
                    result = owner.dispatch(pieces[2], body, self.headers,
                                            received_start=received_start, body_bytes=len(raw_body))
                    self._write(200, {"jsonrpc": "2.0", "id": request_id, "result": result}, sse=owner.sse)
                except mcp.RpcError as exc:
                    self._write(exc.status, exc.response(request_id))
                except (ValueError, Denied) as exc:
                    self._write(403, mcp.RpcError(-32000, str(exc), 403).response(request_id))
                except Exception:
                    self._write(500, mcp.RpcError(-32603, "Local tool service error", 500).response(request_id))

        self.http = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.http.daemon_threads = True
        self.url = "http://127.0.0.1:" + str(self.http.server_port)
        self.thread = threading.Thread(target=self.http.serve_forever, daemon=True)
        self.thread.start()

    def install_native(self, instance, agent_bridge):
        """Install only public verification material outside request timing."""
        if instance in self.native_installations:
            return self.native_installations[instance]
        package = agent_bridge.command("export_verifier", instance=instance)
        installed = self.bridge.command("install_verifier", package=package)
        if installed.get("instance") != instance:
            raise ValueError("native_verifier_install_instance_mismatch")
        self.native_installations[instance] = installed
        return installed

    def register(self, instance, mode, *, subject="agent", jkt=None, quota=64,
                 scopes=None, attributes=(0, 1, 2, 3)):
        if mode not in MODES or instance in self.instances:
            raise ValueError("invalid_instance_registration")
        self.instances[instance] = mode
        if mode in ("oauth", "msb", "slw"):
            self.stores[mode].install_grant(instance, subject, quota, scopes, attributes, jkt, self.period)

    def dispatch(self, mode, body, headers, *, received_start=None, body_bytes=None):
        method, params = body["method"], body["params"]
        if method == "server/discover":
            return {"resultType": "complete", "supportedVersions": [VERSION],
                    "capabilities": {"tools": {}, "extensions": {AUTH_META: {"version": "1"}}},
                    "_meta": {"io.modelcontextprotocol/serverInfo": {"name": "server", "version": "0.1.0"}}}
        if method == "ping":
            return {"resultType": "complete"}
        if method == "tools/list":
            return {"resultType": "complete", "tools": self.tools}
        if method != "tools/call":
            raise mcp.RpcError(-32601, "Method not found", 404)
        tool = params.get("name")
        try:
            arguments = normalize(tool, params.get("arguments"))
        except ValueError as exc:
            raise mcp.RpcError(-32602, str(exc)) from exc
        meta = params["_meta"].get(AUTH_META)
        if not isinstance(meta, dict):
            raise Denied("authorization_envelope_missing")
        instance = meta.get("instance")
        if self.instances.get(instance) != mode:
            raise Denied("unknown_instance_or_mode")
        nonce = meta.get("nonce")
        context = request_context(self.domain, tool, arguments, self.period, nonce)
        expected_policy = policy(tool, arguments, self.period)
        stats = {}
        def capture(name, action):
            start = self.clock.start(); value = action(); elapsed = self.clock.elapsed(start)
            if elapsed is not None:
                stats[name] = elapsed
            return value
        evidence = None; serials = (); claims = None; jti = None
        if mode == "oauth":
            authorization = mcp._one(headers, "Authorization")
            if not authorization.startswith("DPoP "):
                raise Denied("DPoP_authorization_required")
            access_token = authorization[5:]
            claims = capture("verification_ns", lambda: self.oauth_verifier.verify(access_token, self.domain, self.period))
            jti = capture("dpop_ns", lambda: verify_dpop(mcp._one(headers, "DPoP"), access_token, claims,
                          self.url + "/mcp/oauth", self.nonce))
        elif mode != "none":
            if mode in ("msb", "slw") and AUTH_META not in params["_meta"][mcp.CAP].get("extensions", {}):
                raise mcp.RpcError(-32021, "Authorization extension required", data={
                    "requiredCapabilities": {"extensions": {AUTH_META: {}}}})
            wire = meta.get("wire_hex")
            if not isinstance(wire, list) or not wire or any(not isinstance(x, str) for x in wire):
                raise Denied("native_wire_required")
            if mode in ("msb", "slw"):
                state = params.get("requestState")
                with self.exchange_lock:
                    if state is None:
                        state = secrets.token_hex(24)
                        self.exchanges[state] = {"instance": instance, "context": context,
                                                 "round": 1, "mode": mode}
                    record = self.exchanges.get(state)
                    if record is None or (record["instance"], record["context"], record["mode"]) != (instance, context, mode):
                        raise Denied("interactive_request_binding")
                    round_number = record["round"]
                    verified = capture("native_round_ns", lambda: self.bridge.command("server_round", instance=instance,
                                       session_id=state, round=round_number, wire_hex=wire,
                                       context=context, policy=expected_policy))
                    if verified.get("complete") is False:
                        record["round"] += 1
                        result = {"resultType": "input_required", "requestState": state,
                                  "_meta": {AUTH_META: {"wire_hex": verified["wire_hex"]}}}
                        if self.clock.enabled:
                            result["_meta"][AUTH_META]["timing"] = {**stats, **verified.get("timing", {})}
                        return result
                    del self.exchanges[state]
            else:
                verified = capture("native_round_ns", lambda: self.bridge.command("verify", instance=instance,
                                   wire_hex=wire, context=context, policy=expected_policy))
            if verified.get("valid") is not True:
                raise Denied("native_verification_rejected")
            serials = verified.get("serials", [])
            if mode in ("darlt", "darlt-ablation", "sma") and verified.get("unit_count") != COSTS[tool]:
                raise Denied("native_amount_does_not_match_tool_cost")
            evidence = verified.get("evidence_handle")
            if self.clock.enabled:
                stats.update(verified.get("timing", {}))
        accepted = capture("state_backend_ns", lambda: self.stores[mode].commit(mode, instance, tool,
                           arguments, digest({"context": context}), serials, claims, jti))
        if received_start is not None and self.clock.enabled:
            stats["server_verification_commit_ns"] = self.clock.elapsed(received_start)
            stats["request_body_bytes"] = body_bytes
        content = {**accepted, "evidence_handle": evidence, "verifier_id": self.verifier_id}
        result = {"resultType": "complete", "content": [{"type": "text", "text": canonical(content).decode()}],
                  "structuredContent": content}
        if self.clock.enabled:
            result["_meta"] = {AUTH_META: {"timing": stats}}
        return result

    def close(self):
        self.http.shutdown(); self.http.server_close(); self.thread.join(timeout=5)

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
