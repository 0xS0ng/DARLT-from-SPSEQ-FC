"""One prepared token per tool with scope-bounded replenishment."""
from __future__ import annotations

from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from contextlib import nullcontext
import secrets
import threading

from .client import Client
from .common import AUTH_META, COSTS, NATIVE, Clock, normalize, policy, request_context
from .oauth import dpop_sign


class PreparedClient(Client):
    def __init__(self, server, bridge, mode, instance, issuer=None, *,
                 positions, steps, clock=None, quota=64,
                 allowed_attrs=(0, 1, 2, 3), initialize=False):
        if mode not in ("oauth", "sma", "darlt", "darlt-ablation"):
            raise ValueError("prefetch_deployment_mode")
        self.positions = tuple(positions)
        if (any(type(x) is not int or x < 0 for x in self.positions)
                or len(set(self.positions)) != len(self.positions)):
            raise ValueError("prefetch_positions_must_be_distinct")
        self._authorized_scope = frozenset(self.positions)
        self._quota = quota
        if type(quota) is not int or quota <= 0:
            raise ValueError("prefetch_quota")
        self.steps = tuple((tool, normalize(tool, args)) for tool, args in steps)
        if not self.steps:
            raise ValueError("prefetch_empty_workflow")
        self.expected_units = sum(COSTS[tool] for tool, _ in self.steps)
        if self.expected_units > quota or self.expected_units > len(self.positions):
            raise ValueError("prefetch_insufficient_scope_for_workflow")
        self._profiles = OrderedDict()
        for tool, args in self.steps:
            expected = policy(tool, args, server.period)
            if tool in self._profiles and self._profiles[tool] != expected:
                raise ValueError("prefetch_tool_policy_is_not_fixed")
            self._profiles[tool] = expected
        scopes = set()
        for tool, args in self.steps:
            scopes.add(tool + ":" + args["resource"])
            if tool == "batch_query":
                scopes.update(tool + ":" + item["resource"] for item in args["items"])
        super().__init__(server, bridge, mode, instance, issuer, clock=clock or Clock(),
                         initialize=initialize, quota=quota, allowed_attrs=allowed_attrs,
                         scopes=sorted(scopes))
        self.events = []
        self.preparations = []
        self._state_lock = threading.RLock()
        self._executor = ThreadPoolExecutor(max_workers=1, thread_name_prefix="case_study-preparation")
        self._ready = {}
        self._step_ready = {}
        self._futures = {}
        self._pending_jobs = OrderedDict()
        self._reserved = set()
        self._spent = set()
        self._allocation_cursor = 0
        self._next_step = 0
        self._next_token = 0
        self._workflow_epoch = 0
        self._fixed_profiles = dict(self._profiles)
        self._primed = False
        self._preparation_mode = None
        self._closed = False
        self.initial_preparation = None

    def _stamp(self):
        return self.clock.start()

    def _event(self, event, *, at=None, **values):
        row = {"event": event, "at_ns": self._stamp() if at is None else at,
               "workflow_epoch": self._workflow_epoch, **values}
        with self._state_lock:
            self.events.append(row)
        return row

    def _reserve(self, tool, reason):
        cost = COSTS[tool]
        with self._state_lock:
            if self._allocation_cursor + cost > len(self.positions):
                return None
            selected = self.positions[self._allocation_cursor:self._allocation_cursor + cost]
            if self._reserved.intersection(selected) or self._spent.intersection(selected):
                raise ValueError("prefetch_reservation_overlap")
            self._allocation_cursor += cost
            self._reserved.update(selected)
            self._next_token += 1
            job = {"token_id": self._next_token, "tool": tool, "units": cost,
                   "positions": list(selected), "reason": reason,
                   "workflow_epoch": self._workflow_epoch, "scheduled_at_ns": self._stamp()}
            self._event("unit_reserved" if reason == "oauth_request_accounting" else "prepare_scheduled",
                        at=job["scheduled_at_ns"], **job)
            return job

    def _bridge_call(self, operation, **values):
        started = self._stamp()
        guard = getattr(self.bridge, "lock", None)
        with guard if guard is not None else nullcontext():
            acquired = self._stamp()
            result = self.bridge.command(operation, **values)
            finished = self._stamp()
        return result, started, acquired, finished

    def _prepare(self, job, *, step=None):
        self._event("prepare_started", token_id=job["token_id"], tool=job["tool"])
        prepared, started, acquired, finished = self._bridge_call(
            "prepare", instance=self.instance, k=job["units"], positions=job["positions"],
            actor=self.actor, policy=self._profiles[job["tool"]],
            ablation=self.mode == "darlt-ablation")
        if not isinstance(prepared.get("handle"), str):
            raise ValueError("prefetch_native_handle_missing")
        public = {**job, "started_at_ns": started, "ready_at_ns": finished}
        if self.clock.enabled:
            public.update(preparation_bridge_ns=finished - started,
                          preparation_bridge_queue_ns=acquired - started,
                          native_preparation_ns=prepared.get("timing", {}).get("preparation_ns", 0))
        record = {"metadata": public, "handle": prepared["handle"],
                  "native_timing": dict(prepared.get("timing", {}))}
        with self._state_lock:
            if step is None:
                if job["tool"] in self._ready:
                    raise ValueError("prefetch_duplicate_ready_tool")
                self._ready[job["tool"]] = record
            else:
                if step in self._step_ready:
                    raise ValueError("prefetch_duplicate_ready_step")
                self._step_ready[step] = record
            self.preparations.append(public)
        self._event("prepare_ready", at=finished, token_id=job["token_id"], tool=job["tool"])
        return record

    def prime(self):
        if self._closed or self._primed or self._preparation_mode is not None:
            raise ValueError("prefetch_prime_state")
        self._preparation_mode = "initial"
        start = self._stamp()
        if self.mode in NATIVE:
            for tool in self._profiles:
                job = self._reserve(tool, "initial")
                if job is None:
                    raise ValueError("prefetch_initial_cache_exceeds_scope")
                self._prepare(job)
        finish = self._stamp()
        self._primed = True
        token_count = (sum(p["units"] for p in self.preparations)
                       if self.mode in ("sma", "darlt-ablation") else len(self.preparations))
        result = {"prepared_tools": list(self._profiles) if self.mode in NATIVE else [],
                  "prepared_entry_count": len(self.preparations),
                  "prepared_token_count": token_count,
                  "reserved_unit_count": len(self._reserved),
                  "jobs": list(self.preparations)}
        if self.clock.enabled:
            result.update(initial_preparation_ns=finish - start if self.mode in NATIVE else 0,
                          initial_native_preparation_ns=sum(p["native_preparation_ns"] for p in self.preparations),
                          started_at_ns=start, finished_at_ns=finish)
        self.initial_preparation = result
        return result

    def prepare_all(self):
        """Prepare replay tokens with the live workflow's unit assignments."""
        if self._closed or self._primed or self._preparation_mode is not None:
            raise ValueError("prefetch_prepare_all_state")
        self._preparation_mode = "all"
        start = self._stamp()
        step_jobs = {}
        jobs = []
        if self.mode in NATIVE:
            available = {}
            for tool in self._profiles:
                job = self._reserve(tool, "initial")
                if job is None:
                    raise ValueError("prefetch_initial_cache_exceeds_scope")
                available[tool] = job
                jobs.append(job)
            for index, (tool, _) in enumerate(self.steps):
                step_jobs[index] = available.pop(tool)
                if any(future_tool == tool for future_tool, _ in self.steps[index + 1:]):
                    job = self._reserve(tool, "replenishment")
                    if job is None:
                        raise ValueError("prefetch_replay_scope_exhausted")
                    available[tool] = job
                    jobs.append(job)
            if available:
                raise ValueError("prefetch_replay_unused_reservation")
            job_steps = {job["token_id"]: index for index, job in step_jobs.items()}
            for job in jobs:
                self._prepare(job, step=job_steps[job["token_id"]])
            allocations = [{"step": index, **job} for index, job in sorted(step_jobs.items())]
        else:
            cursor = 0
            allocations = []
            for index, (tool, _) in enumerate(self.steps):
                cost = COSTS[tool]
                allocations.append({"step": index, "tool": tool, "units": cost,
                                    "token_id": None,
                                    "positions": list(self.positions[cursor:cursor + cost]),
                                    "reason": "oauth_request_accounting"})
                cursor += cost
        finish = self._stamp()
        self._primed = True
        token_count = (sum(p["units"] for p in self.preparations)
                       if self.mode in ("sma", "darlt-ablation") else len(self.preparations))
        result = {"preparation_mode": "all",
                  "prepared_tools": list(self._profiles) if self.mode in NATIVE else [],
                  "prepared_entry_count": len(self.preparations),
                  "prepared_token_count": token_count,
                  "reserved_unit_count": len(self._reserved),
                  "jobs": list(self.preparations), "step_allocations": allocations}
        if self.clock.enabled:
            total = finish - start if self.mode in NATIVE else 0
            native_total = sum(p["native_preparation_ns"] for p in self.preparations)
            result.update(initial_preparation_ns=total, all_preparation_ns=total,
                          initial_native_preparation_ns=native_total,
                          all_native_preparation_ns=native_total,
                          started_at_ns=start, finished_at_ns=finish)
        self.initial_preparation = result
        return result

    def start_background(self):
        if not self._primed or self._closed:
            raise ValueError("prefetch_background_state")
        if self._preparation_mode == "all":
            if self._pending_jobs or self._futures:
                raise ValueError("prefetch_replay_background_job")
            return {"jobs_started": [], "count": 0}
        started = []
        with self._state_lock:
            for tool, job in list(self._pending_jobs.items()):
                if tool in self._futures:
                    raise ValueError("prefetch_duplicate_background_tool")
                self._futures[tool] = self._executor.submit(self._prepare, job)
                del self._pending_jobs[tool]
                started.append({"token_id": job["token_id"], "tool": tool})
        return {"jobs_started": started, "count": len(started)}

    def _take_ready(self, tool, demand, *, step=None):
        if self._preparation_mode == "all":
            with self._state_lock:
                record = self._step_ready.pop(step, None)
            if record is None or record["metadata"]["tool"] != tool:
                raise ValueError("prefetch_replay_ready_record_mismatch")
            ready_at = record["metadata"]["ready_at_ns"]
            readiness = {"ready_before_demand": ready_at <= demand if self.clock.enabled else True,
                         "demand_at_ns": demand, "token_ready_at_ns": ready_at,
                         "token_id": record["metadata"]["token_id"]}
            if self.clock.enabled:
                readiness["future_wait_ns"] = 0
            return record, readiness
        with self._state_lock:
            future = self._futures.get(tool)
            record = self._ready.get(tool)
            was_done = future.done() if future is not None else record is not None
        wait_start = wait_end = None
        if future is not None:
            if not was_done:
                wait_start = self._stamp()
                self._event("ready_wait_started", at=wait_start, tool=tool)
            record = future.result()
            if not was_done:
                wait_end = self._stamp()
                self._event("ready_wait_finished", at=wait_end, tool=tool)
            with self._state_lock:
                self._futures.pop(tool)
        if record is None:
            raise ValueError("prefetch_required_tool_not_started_or_ready")
        ready_at = record["metadata"]["ready_at_ns"]
        ready_before = (ready_at <= demand) if self.clock.enabled else was_done
        with self._state_lock:
            if self._ready.pop(tool, None) is not record:
                raise ValueError("prefetch_ready_record_mismatch")
        readiness = {"ready_before_demand": ready_before, "demand_at_ns": demand,
                     "token_ready_at_ns": ready_at, "token_id": record["metadata"]["token_id"]}
        if self.clock.enabled:
            readiness["future_wait_ns"] = 0 if was_done else wait_end - wait_start
        return record, readiness

    def call_step(self, index, arguments=None):
        if self._closed or not self._primed or index != self._next_step or index >= len(self.steps):
            raise ValueError("prefetch_step_order")
        tool, planned_args = self.steps[index]
        args = normalize(tool, planned_args if arguments is None else arguments)
        if policy(tool, args, self.server.period) != self._profiles[tool]:
            raise ValueError("prefetch_actual_policy_mismatch")
        demand = self._stamp()
        self._event("token_demand", at=demand, step=index, tool=tool)
        native, headers = {}, {}
        record = None
        if self.mode in NATIVE:
            record, readiness = self._take_ready(tool, demand, step=index)
            selected = record["metadata"]["positions"]
        else:
            job = self._reserve(tool, "oauth_request_accounting")
            if job is None:
                raise ValueError("prefetch_scope_exhausted")
            selected = job["positions"]
            readiness = {"ready_before_demand": True, "demand_at_ns": demand,
                         "token_ready_at_ns": None, "token_id": None}
            if self.clock.enabled:
                readiness["future_wait_ns"] = 0
        readiness_end = self._stamp()
        nonce = secrets.token_hex(24)
        native_policy = self._profiles[tool]
        context = request_context(self.server.domain, tool, args, self.server.period, nonce)
        if self.mode == "oauth":
            proof = dpop_sign(self.dpop_key, self.access_token, self.transport.url, self.server.nonce)
            headers = {"Authorization": "DPoP " + self.access_token, "DPoP": proof}
        auth = {"instance": self.instance, "nonce": nonce}
        online_begin = online_acquired = online_end = readiness_end
        if record is not None:
            online, online_begin, online_acquired, online_end = self._bridge_call(
                "online", handle=record["handle"], context=context, policy=native_policy)
            auth["wire_hex"] = online["wire_hex"]
            if online.get("session") is not None:
                raise ValueError("prefetch_unexpected_interactive_deployment")
            self._add(native, online.get("timing", {}))
            self._event("online_finished", at=online_end, step=index, tool=tool,
                        token_id=record["metadata"]["token_id"])
        params = {"name": tool, "arguments": args, "_meta": {AUTH_META: auth}}
        http_begin = self._stamp()
        result = self.transport.send("tools/call", params, headers, self.tools.get(tool))
        end = self._stamp()
        if result.get("resultType") != "complete":
            raise ValueError("prefetch_unexpected_authorization_round")
        self._add(native, result.get("_meta", {}).get(AUTH_META, {}).get("timing", {}))
        content = result["structuredContent"]
        if content.get("accepted") is not True:
            raise ValueError("prefetch_tool_request_not_accepted")
        if content.get("units") != COSTS[tool]:
            raise ValueError("prefetch_tool_unit_count")
        with self._state_lock:
            if self._spent.intersection(selected):
                raise ValueError("prefetch_consumed_unit_reuse")
            self._spent.update(selected)
        self._next_step += 1
        self.cursor += COSTS[tool]
        self._event("token_consumed", at=end, step=index, tool=tool, positions=list(selected),
                    token_id=record["metadata"]["token_id"] if record is not None else None)
        byte_stats = dict(getattr(self.transport, "last_request_stats", {}) or {})
        if ("request_body_bytes" in byte_stats and "request_body_bytes" in native
                and byte_stats["request_body_bytes"] != native["request_body_bytes"]):
            raise ValueError("prefetch_client_server_body_length_mismatch")
        out = {"mode": self.mode, "tool": tool, "units": COSTS[tool], "http_requests": 1,
               **content, "arguments": args, "readiness": readiness,
               "prepared_token": dict(record["metadata"]) if record is not None else None,
               "request_bytes": byte_stats}
        for key in ("http_sent_bytes", "request_body_bytes", "native_token_bytes", "auth_envelope_bytes"):
            if key in byte_stats:
                out[key] = byte_stats[key]
        if self.clock.enabled:
            timing = {**native, "future_wait_ns": readiness["future_wait_ns"],
                      "readiness_gate_ns": readiness_end - demand,
                      "agent_critical_ns": end - demand, "active_tool_ns": end - demand,
                      "request_latency_ns": end - readiness_end, "mcp_http_ns": end - http_begin,
                      "online_bridge_ns": online_end - online_begin,
                      "online_bridge_queue_ns": online_acquired - online_begin,
                      "online_rpc_ns": online_end - online_acquired,
                      "native_online_ns": native.get("online_ns", 0),
                      "demand_at_ns": demand, "readiness_finished_at_ns": readiness_end,
                      "online_started_at_ns": online_begin, "online_finished_at_ns": online_end,
                      "http_started_at_ns": http_begin, "response_received_at_ns": end}
            if timing["readiness_gate_ns"] + timing["request_latency_ns"] != timing["agent_critical_ns"]:
                raise ValueError("prefetch_nonconsecutive_critical_windows")
            out["timing"] = timing
        # Reserve replenishment only for a later use of this tool.
        if (self._preparation_mode != "all" and self.mode in NATIVE
                and any(next_tool == tool for next_tool, _ in self.steps[self._next_step:])):
            job = self._reserve(tool, "replenishment")
            if job is not None:
                with self._state_lock:
                    if tool in self._pending_jobs:
                        raise ValueError("prefetch_duplicate_pending_tool")
                    self._pending_jobs[tool] = job
        return out

    @property
    def reserved_positions(self):
        with self._state_lock:
            return sorted(self._reserved)

    @property
    def spent_positions(self):
        with self._state_lock:
            return sorted(self._spent)

    def assert_complete(self):
        with self._state_lock:
            if (self._next_step != len(self.steps) or self._ready or self._step_ready or self._futures
                    or self._pending_jobs or self._reserved != self._spent
                    or len(self._spent) != self.expected_units):
                raise ValueError("prefetch_workflow_accounting_incomplete")
        return {"steps": self._next_step, "reserved_units": len(self._reserved),
                "spent_units": len(self._spent), "expected_units": self.expected_units}

    def reset_workflow(self, steps=None, positions=None):
        """Begin an independent replay after the caller restores its snapshot.

        Registration, native instance, long-lived caches and HTTP connection
        stay installed. This method must never be used between tool steps.
        """
        if self._closed:
            raise ValueError("prefetch_reset_closed_client")
        if self._primed:
            self.assert_complete()
        elif self._reserved or self._ready or self._step_ready or self._futures or self._pending_jobs:
            raise ValueError("prefetch_reset_incomplete_workflow")
        replayed_positions = self.positions if positions is None else tuple(positions)
        if (any(type(x) is not int or x < 0 for x in replayed_positions)
                or len(set(replayed_positions)) != len(replayed_positions)
                or not set(replayed_positions).issubset(self._authorized_scope)):
            raise ValueError("prefetch_reset_scope_changed")
        new_steps = self.steps if steps is None else tuple(
            (tool, normalize(tool, args)) for tool, args in steps)
        if not new_steps:
            raise ValueError("prefetch_empty_workflow")
        expected_units = sum(COSTS[tool] for tool, _ in new_steps)
        if expected_units > self._quota or expected_units > len(replayed_positions):
            raise ValueError("prefetch_insufficient_scope_for_workflow")
        profiles = OrderedDict()
        for tool, args in new_steps:
            expected = policy(tool, args, self.server.period)
            if self._fixed_profiles.get(tool) != expected:
                raise ValueError("prefetch_reset_policy_changed")
            profiles[tool] = expected
        self.positions, self.steps = tuple(replayed_positions), tuple(new_steps)
        self._profiles, self.expected_units = profiles, expected_units
        self._ready, self._futures = {}, {}
        self._step_ready = {}
        self._pending_jobs = OrderedDict()
        self._reserved, self._spent = set(), set()
        self._allocation_cursor = 0
        self._next_step = 0
        self._primed = False
        self._preparation_mode = None
        self._workflow_epoch += 1
        self.cursor = 0
        self.events, self.preparations = [], []
        self.initial_preparation = None
        return {"workflow_epoch": self._workflow_epoch, "expected_units": self.expected_units}

    def close(self):
        if self._closed:
            return
        self._closed = True
        try:
            self._executor.shutdown(wait=True, cancel_futures=True)
            if self._next_step == len(self.steps):
                self.assert_complete()
        finally:
            super().close()
