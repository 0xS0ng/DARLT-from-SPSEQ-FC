"""Host-side authorization; the model sees only business tool schemas."""
from __future__ import annotations

import secrets
from .common import AUTH_META, COSTS, NATIVE, Clock, normalize, policy, request_context
from .mcp import Transport
from .oauth import dpop_sign, new_dpop_key, thumbprint


class Client:
    def __init__(self, server, bridge, mode, instance, issuer=None, *, clock=None,
                 initialize=True, subject="agent", quota=64, allowed_attrs=(0, 1, 2, 3),
                 scopes=None, actor="agent"):
        self.server, self.bridge, self.mode, self.instance = server, bridge, mode, instance
        self.clock = clock or Clock()
        self.cursor, self.actor = 0, actor
        self.init_result = {}
        self.dpop_key, self.access_token = None, None
        if mode in NATIVE and initialize:
            self.init_result = bridge.command("init", instance=instance, scheme=NATIVE[mode],
                                             pools=[0, 1, 2, 3], allowed_attrs=list(allowed_attrs))
        if mode in NATIVE and hasattr(server, "install_native"):
            server.install_native(instance, bridge)
        if mode == "oauth":
            if issuer is None:
                raise ValueError("oauth_issuer_required")
            self.dpop_key = new_dpop_key()
            granted_scopes = ([name + ":inventory/allowed" for name in
                              ("search_inventory", "get_details", "book_item", "batch_query")]
                              if scopes is None else scopes)
            self.access_token = issuer.issue(self.dpop_key.public_key(), server.domain, granted_scopes,
                                             quota=quota, subject=subject, period=server.period,
                                             attributes={str(i): 1 for i in allowed_attrs})
            server.register(instance, mode, subject=subject, quota=quota, scopes=granted_scopes,
                            attributes=allowed_attrs, jkt=thumbprint(self.dpop_key.public_key()))
        else:
            server.register(instance, mode, subject=subject, quota=quota, scopes=scopes, attributes=allowed_attrs)
        self.transport = Transport(server.url + "/mcp/" + mode)
        self.tools = {tool["name"]: tool for tool in self.transport.send("tools/list")["tools"]}

    def call(self, tool, arguments, *, positions=None, actor=None, nonce=None):
        args = normalize(tool, arguments)
        native_policy = policy(tool, args, self.server.period)
        nonce = nonce or secrets.token_hex(24)
        context = request_context(self.server.domain, tool, args, self.server.period, nonce)
        cost = COSTS[tool]
        stats = {}; native = {}
        started = self.clock.start()
        headers = {}; handle = None
        if self.mode in NATIVE:
            if positions is None:
                positions = list(range(self.cursor, self.cursor + cost))
            prepared = self.bridge.command("prepare", instance=self.instance, k=cost,
                                           positions=positions, actor=actor or self.actor, policy=native_policy)
            handle = prepared["handle"]
            native.update(prepared.get("timing", {}))
        # DPoP signing follows the shared preparation/request boundary.
        prepared_end = self.clock.start() if self.mode in NATIVE else started
        if self.mode == "oauth":
            proof = dpop_sign(self.dpop_key, self.access_token, self.transport.url, self.server.nonce)
            headers = {"Authorization": "DPoP " + self.access_token, "DPoP": proof}
        auth = {"instance": self.instance, "nonce": nonce}
        session = None
        if handle is not None:
            online = self.bridge.command("online", handle=handle, context=context, policy=native_policy)
            auth["wire_hex"] = online["wire_hex"]
            session = online.get("session")
            self._add(native, online.get("timing", {}))
        params = {"name": tool, "arguments": args, "_meta": {AUTH_META: auth}}
        rounds = 0; http_total = 0
        while True:
            rounds += 1
            before = self.clock.start()
            result = self.transport.send("tools/call", params, headers, self.tools.get(tool))
            received_end = self.clock.start()
            if self.clock.enabled:
                http_total += received_end - before
            if result["resultType"] == "complete":
                break
            self._add(native, result.get("_meta", {}).get(AUTH_META, {}).get("timing", {}))
            if session is None or rounds >= 3:
                raise ValueError("unexpected_authorization_round")
            challenge = result.get("_meta", {}).get(AUTH_META, {}).get("wire_hex")
            next_wire = self.bridge.command("client_round", session=session, wire_hex=challenge)
            self._add(native, next_wire.get("timing", {}))
            params["requestState"] = result["requestState"]
            auth["wire_hex"] = next_wire["wire_hex"]
        self._add(native, result.get("_meta", {}).get(AUTH_META, {}).get("timing", {}))
        self.cursor += cost
        out = {"mode": self.mode, "tool": tool, "units": cost, "http_requests": rounds,
               **result["structuredContent"]}
        if self.clock.enabled:
            preparation = prepared_end - started
            latency = received_end - prepared_end
            stats.update(client_preparation_ns=preparation, request_latency_ns=latency,
                         mcp_http_ns=http_total, active_tool_ns=received_end - started)
            out["timing"] = {**stats, **native}
        return out

    @staticmethod
    def _add(target, values):
        for name, value in values.items():
            if value is not None:
                target[name] = target.get(name, 0) + value

    def close(self):
        self.transport.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
