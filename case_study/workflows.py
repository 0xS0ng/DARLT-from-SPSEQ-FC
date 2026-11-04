"""Booking and research workflows, local checks and trace replay."""
from __future__ import annotations
import argparse
import copy
import json
import os
from pathlib import Path
import statistics
import time
from .role_bridge import native_pair, process_record
from .common import AUTH_META, COSTS, DOCUMENT_IDS, Clock, canonical, normalize, strict, peer_instance
from .oauth import OAuthIssuer
from .openrouter import OpenRouter
from .prefetch import PreparedClient
from .run import write_csv
from .server import ToolServer

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / "case_study/native/target/release/darlt-case-study-native"
MODES = ("oauth", "sma", "darlt-ablation", "darlt")

def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n")

def actions(workload, customer):
    if workload == 'booking':
        raw = [("search_inventory", {"query": "hotel"}),
               ("get_details", {"item_id": "hotel-101"}),
               ("book_item", {"item_id": "hotel-101", "customer": customer}),
               ("get_details", {"item_id": "hotel-101"}),
               ("search_inventory", {"query": "hotel"})]
    elif workload == 'research':
        raw = [("search_sources", {"query": "market"}),
               ("fetch_documents", {"document_ids": list(DOCUMENT_IDS)}),
               ("query_dataset", {"dataset_id": "market-v1"}),
               ("run_analysis", {"dataset_id": "market-v1"}),
               ("export_report", {"analysis_id": "analysis-001"})]
    else:
        raise ValueError("unknown_workload")
    return [(tool, normalize(tool, args)) for tool, args in raw]

def prompts(workload, customer):
    system = ("Use the local simulated tools one dependent call at a time. "
              "Authentication and fixed unit charging are handled by the host. "
              "Use actual tool results; do not invent a completed operation. "
              "Follow the requested dependency order, and only then give the final response.")
    if workload == 'booking':
        user = ("For " + customer + ", search hotels with query exactly 'hotel', inspect hotel-101, book it, "
                "inspect its booking count again and verify an increase of one, "
                "search once more with query exactly 'hotel', then summarize the confirmed booking.")
    else:
        user = ("Perform the local market research workflow for " + customer + ". "
                "First call search_sources with query 'market'. Fetch all eight returned document IDs "
                "in one fetch_documents call. Next query_dataset using market-v1, then run_analysis "
                "using market-v1. Export the report using the actual returned analysis_id. "
                "After export_report confirms complete=true, summarize the confirmed report ID, "
                "eight documents, sixteen dataset rows, and thirty-two report sections. "
                "Do not skip, combine, repeat or reorder these five tool calls.")
    return [{"role": "system", "content": system}, {"role": "user", "content": user}]

class InferenceClock(Clock):
    def __init__(self, callback):
        super().__init__(True)
        self.callback = callback
        self.interval = None

    def start(self):
        start = time.perf_counter_ns()
        self.callback()
        return start

    def elapsed(self, start):
        end = time.perf_counter_ns()
        self.interval = (start, end)
        return end - start

def tool_definitions(client):
    names = {tool for tool, _ in client.steps}
    result = []
    for tool in client.tools.values():
        if tool["name"] not in names:
            continue
        schema = copy.deepcopy(tool["inputSchema"])
        schema["properties"]["resource"].pop("x-mcp-header", None)
        result.append({"type": "function", "function": {"name": tool["name"],
                       "description": tool["description"], "parameters": schema}})
    return result

def workload_state(server, mode, instance, workload):
    value = server.stores[mode].facts(instance)
    if workload == 'research':
        value["research"] = server.stores[mode].research_facts(instance)
    return value

def assert_effects(client, workload, before, results):
    after = workload_state(client.server, client.mode, client.instance, workload)
    expected = 8 if workload == 'booking' else 61
    if sum(r["units"] for r in results) != expected or after["effects"] - before["effects"] != 5:
        raise ValueError("workflow_effect_or_unit_accounting_failed")
    if client.mode in ("darlt", "darlt-ablation", "sma") and after["consumed"] - before["consumed"] != expected:
        raise ValueError("native_serial_count_failed")
    if client.mode == "oauth" and before["remaining"] - after["remaining"] != expected:
        raise ValueError("OAuth_quota_accounting_failed")
    if workload == 'booking':
        details = [r["tool_result"]["bookings"] for r in results if r["tool"] == "get_details"]
        if after["bookings"] - before["bookings"] != 1 or len(details) != 2 or details[1] != details[0] + 1:
            raise ValueError("hotel_booking_effect_failed")
    else:
        report = results[-1]["tool_result"]
        if (report.get("complete"), report.get("document_count"), report.get("row_count"), report.get("section_count")) != (True, 8, 16, 32):
            raise ValueError("research_report_effect_failed")
    return after

def run_workflow(client, workload, *, model=None, run_index=0, scripted=False, prepare_all=False):
    before = workload_state(client.server, client.mode, client.instance, workload)
    initial = client.prepare_all() if prepare_all else client.prime()
    expected_steps = list(client.steps)
    customer = expected_steps[2][1].get("customer", "research-" + str(run_index)) if workload == 'booking' else "research-" + str(run_index)
    messages, results, model_records, measured_steps = prompts(workload, customer), [], [], []
    tools = tool_definitions(client)
    if model is not None:
        model.clock.callback = client.start_background
    for index, (expected, planned) in enumerate(expected_steps):
        metadata = {}
        if model is not None:
            message, metadata = model.complete(messages, tools, expected)
            messages.append(message)
            call = message["tool_calls"][0]
            actual = normalize(expected, strict(call["function"]["arguments"]))
            if actual != planned:
                raise ValueError("model_arguments_changed_workload:" + expected)
        else:
            if not prepare_all:
                client.start_background()
            actual = planned
        result = client.call_step(index, arguments=actual)
        results.append(result)
        if model is not None:
            a, b = model.clock.interval
            metadata.update(model_api_start_ns=a, model_api_end_ns=b)
            model_records.append(metadata)
            messages.append({"role": "tool", "tool_call_id": call["id"],
                             "content": canonical(result["tool_result"]).decode()})
        timing = result.get("timing", {})
        if timing:
            bounds = [timing[key] for key in ("demand_at_ns", "readiness_finished_at_ns",
                       "online_started_at_ns", "online_finished_at_ns", "http_started_at_ns",
                       "response_received_at_ns")]
            if any(b < a for a, b in zip(bounds, bounds[1:])):
                raise ValueError("non_monotone_request_windows")
            segments = [b - a for a, b in zip(bounds, bounds[1:])]
            if sum(segments) != timing["agent_critical_ns"]:
                raise ValueError("nonconsecutive_request_window_sum")
            if (timing["native_online_ns"] > timing["online_bridge_ns"] or
                    timing.get("decode_ns", 0) + timing.get("verification_ns", 0) +
                    timing.get("state_backend_ns", 0) > timing["server_verification_commit_ns"]):
                raise ValueError("native_phases_outside_host_window")
            timing.update(request_readiness_segment_ns=segments[0],
                          request_context_segment_ns=segments[1],
                          request_online_bridge_segment_ns=segments[2],
                          request_envelope_segment_ns=segments[3],
                          request_HTTP_segment_ns=segments[4],
                          request_segment_sum_ns=sum(segments),
                          request_segment_residual_ns=sum(segments)-timing["agent_critical_ns"],
                          online_adapter_ns=timing["online_bridge_ns"]-timing["native_online_ns"])
            darlt = (timing["native_online_ns"] + timing.get("decode_ns", 0)
                     + timing.get("verification_ns", 0))
            proof_path_inclusive = (timing["readiness_gate_ns"] + timing["online_bridge_ns"]
                            + timing.get("decode_ns", 0) + timing.get("verification_ns", 0))
            other = timing["agent_critical_ns"] - darlt
            non_proof_path = timing["agent_critical_ns"] - proof_path_inclusive
            if min(other, non_proof_path) < 0 or darlt > proof_path_inclusive:
                raise ValueError("overlapping_workflow_attribution")
            if darlt + other != proof_path_inclusive + non_proof_path or darlt + other != timing["agent_critical_ns"]:
                raise ValueError('attribution_partition_failed')
            measured_steps.append({"run": run_index, "workload": workload, "step": index + 1,
                                   "tool": expected, "units": result["units"],
                                   "model_api_ns": metadata.get("model_api_ns", 0),
                                   "darlt_critical_ns": darlt, "other_ns": other,
                                   'proof_path_inclusive_ns': proof_path_inclusive, 'non_proof_path_ns': non_proof_path,
                                   **timing, **result["request_bytes"],
                                   "ready_before_demand": result["readiness"]["ready_before_demand"]})
    final_reply = None
    if model is not None:
        message, metadata = model.complete(messages, tools, None)
        final_reply = message["content"]
        a, b = model.clock.interval
        metadata.update(model_api_start_ns=a, model_api_end_ns=b)
        model_records.append(metadata)
        measured_steps.append({"run": run_index, "workload": workload, "step": 6, "tool": "final_reply",
                               "units": 0, "model_api_ns": metadata["model_api_ns"],
                               "darlt_critical_ns": 0, "other_ns": 0, 'proof_path_inclusive_ns': 0, 'non_proof_path_ns': 0, "agent_critical_ns": 0})
    completed = client.assert_complete()
    after = assert_effects(client, workload, before, results)
    if [(r["tool"], r["arguments"]) for r in results] != expected_steps:
        raise ValueError("workflow_trace_mismatch")
    if client.mode != "oauth":
        prep = client.preparations
        if prepare_all and client.clock.enabled:
            first_demand = min(r["timing"]["demand_at_ns"] for r in results)
            if any(p["ready_at_ns"] > first_demand for p in prep):
                raise ValueError("replay_preparation_in_timed_workflow")
            if any(e["event"] == "prepare_started" and e["at_ns"] >= first_demand for e in client.events):
                raise ValueError("replay_background_prepare_detected")
            if any(not r["readiness"]["ready_before_demand"] or r["readiness"]["future_wait_ns"] != 0 for r in results):
                raise ValueError("replay_token_not_ready_at_start")
        if sum(p["units"] for p in prep) != completed["expected_units"]:
            raise ValueError("prepared_scope_accounting_failed")
        prepared_positions = [x for p in prep for x in p["positions"]]
        if len(prepared_positions) != len(set(prepared_positions)) or not set(prepared_positions).issubset(client.positions):
            raise ValueError("prepared_units_overlap_or_outside_scope")
        for result in results:
            if client.clock.enabled and result["prepared_token"]["ready_at_ns"] > result["timing"]["online_started_at_ns"]:
                raise ValueError("online_before_token_prepared")
        for p in prep:
            if p["reason"] == "replenishment" and model is not None:
                if not any(m["model_api_start_ns"] <= p["started_at_ns"] <= m["model_api_end_ns"] for m in model_records):
                    raise ValueError("background_prepare_not_started_in_model_HTTP")
    first_demand = min((r["timing"]["demand_at_ns"] for r in results), default=0) if client.clock.enabled else None
    prepares_during_workflow = sum(e["event"] == "prepare_started" and e["at_ns"] >= first_demand for e in client.events) if client.clock.enabled else 0
    return {"run": run_index, "workload": workload, "mode": client.mode, "passed": True,
            "preparations_during_workflow_count": prepares_during_workflow,
            'scripted_execution': scripted, "all_prepared_before_workflow": prepare_all, "initial_preparation": initial,
            "preparations": list(client.preparations), "events": list(client.events),
            "steps": results, "timing_steps": measured_steps, "model_records": model_records,
            "final_reply": final_reply, "scope_accounting": completed,
            "before": before, "after": after,
            "trace": [{"tool": tool, "arguments": args, "units": COSTS[tool]} for tool, args in expected_steps]}

def positions_for(pools):
    return [pool * 16 + offset for pool in pools for offset in range(16)]

def delegation(bridge, parent, instance, pools):
    return bridge.command("delegate_child", parent=parent, instance=instance,
                          pools=pools, allowed_attrs=[0, 1, 2, 3])

def reject_checks(client, captured):
    raw, headers = captured[-1]
    before = client.server.stores[client.mode].facts(client.instance)
    status = []
    for tamper in (False, True):
        body, head = strict(raw), dict(headers)
        if tamper and client.mode == "oauth":
            for name in list(head):
                if name.lower() == "dpop":
                    head[name] += "x"
        elif tamper:
            wire = body["params"]["_meta"][AUTH_META]["wire_hex"][0]
            body["params"]["_meta"][AUTH_META]["wire_hex"][0] = ("ff" if wire[:2] != "ff" else "00") + wire[2:]
        response = client.transport.client.post(client.transport.url, content=canonical(body), headers=head)
        if response.status_code != 403:
            raise ValueError("expected_authorization_rejection_failed")
        if client.server.stores[client.mode].facts(client.instance) != before:
            raise ValueError("rejection_mutated_state")
        status.append({"tampered": tamper, "HTTP_status": response.status_code, "effects_unchanged": True})
    return status

def correctness(out, binary, plan=None):
    clock, issuer = Clock(), OAuthIssuer()
    checks = []
    with native_pair(binary) as (bridge, verifier):
        save(out / "native_processes.json", process_record(bridge, verifier))
        parent = bridge.command("issue_parent", instance="check-parent")
        children = {}
        bridge.command("init", instance="check-sma", scheme="SMA²RT")
        for workload in ('booking', 'research'):
            child_id = "check-child-" + workload
            child_pools = [0] if workload == 'booking' else [10, 11, 12, 13]
            children[workload] = delegation(bridge, "check-parent", child_id, child_pools)
            steps = actions(workload, "synthetic-customer-check")
            quota = 16 if workload == 'booking' else 64
            for mode in MODES:
                instance = "check-sma" if mode == "sma" else child_id if mode.startswith("darlt") else "check-oauth"
                selected = positions_for(child_pools) if mode.startswith("darlt") else list(range(quota))
                directory = out / "state" / (workload + "-" + mode)
                with ToolServer(directory, verifier, issuer.verifier(), clock=clock) as server,\
                     PreparedClient(server, bridge, mode, instance, issuer, positions=selected, steps=steps, quota=quota, clock=clock) as client:
                    snapshot = server.stores[mode].snapshot()
                    captured = []
                    client.transport.client.event_hooks["request"] = [lambda request: captured.append((bytes(request.content), dict(request.headers)))]
                    try:
                        first = run_workflow(client, workload, scripted=True)
                        for result, (raw, _) in zip(first["steps"], captured[:5]):
                            auth = strict(raw)["params"]["_meta"][AUTH_META]
                            wire_count = len(auth.get("wire_hex", []))
                            expected_count = 0 if mode == "oauth" else 1 if mode == "darlt" else result["units"]
                            if wire_count != expected_count:
                                raise ValueError("deployment_token_count_gate_failed")
                        rejects = reject_checks(client, captured)
                        server.stores[mode].restore(snapshot)
                        client.reset_workflow()
                        second = run_workflow(client, workload, scripted=True, prepare_all=True)
                        if first["trace"] != second["trace"]:
                            raise ValueError("snapshot_replay_trace_changed")
                        if mode != "oauth":
                            first_positions=[r["prepared_token"]["positions"] for r in first["steps"]]
                            replayed_positions=[r["prepared_token"]["positions"] for r in second["steps"]]
                            if first_positions != replayed_positions:
                                raise ValueError("preparation_unit_assignment_changed")
                        checks.append({"workload": workload, "mode": mode, "passed": True,
                                       "first": first, "second": second, "rejects": rejects})
                    finally:
                        snapshot.close()
        meta = bridge.command("metadata")
        if meta["darlt_issuer_issue_calls_total"] != 1:
            raise ValueError('single_issue_untimed_failed')
        server_meta = verifier.command("metadata")
        if server_meta["darlt_issuer_issue_calls_total"] != 0 or server_meta.get("shared_parent_count") != 0:
            raise ValueError("service_received_private_issuance_state")
        save(out / "native_processes_final.json", process_record(bridge, verifier))
    from .misuse import run_misuse
    misuse = run_misuse(binary, out / "misuse-state")
    if any(not r.get("atomicity_passed") for r in misuse if r["applicable"]):
        raise ValueError("misuse_atomicity_gate_failed")
    save(out / "correctness.json", {"passed": True, 'timing_enabled': False, "model_API_calls": 0,
                                   "deployment_workload_checks": checks, "issuer": parent, "children": children,
                                   "misuse_cases": misuse})
    return {"gate": "correctness", "passed": True, "real_workflows": 16, "misuse_records": 36}

def workflow_totals(value):
    steps=value["steps"]
    times=[r["timing"] for r in steps]
    return {"agent_critical_ns":sum(t["agent_critical_ns"] for t in times),
            "server_verification_commit_ns":sum(t["server_verification_commit_ns"] for t in times),
            "sent_http_bytes":sum(r["http_sent_bytes"] for r in steps),
            "request_body_bytes":sum(r["request_body_bytes"] for r in steps),
            "native_token_bytes":sum(r["native_token_bytes"] for r in steps),
            "initial_preparation_ns":value["initial_preparation"]["initial_preparation_ns"],
            "all_preparation_ns":value["initial_preparation"].get("all_preparation_ns", 0),
            "preparations_during_workflow_count":value["preparations_during_workflow_count"],
            "native_preparation_ns":sum(p.get("native_preparation_ns",0) for p in value["preparations"]),
            "preparation_bridge_ns":sum(p.get("preparation_bridge_ns",0) for p in value["preparations"]),
            "future_wait_ns":sum(t["future_wait_ns"] for t in times),
            "online_bridge_queue_ns":sum(t["online_bridge_queue_ns"] for t in times),
            "tool_calls":len(steps),"units":sum(r["units"] for r in steps),
            "ready_at_demand_count":sum(r["readiness"]["ready_before_demand"] for r in steps)}

def replay_summary(trace, mode, attempt, records):
    chosen=[r for r in records if r["phase"]=="retained"]
    if len(chosen)!=10:raise ValueError("replay_retained_count")
    result={"trace_id":trace["trace_id"],"workload":trace["workload"],"mode":mode,"attempt":attempt,"n":10,"warmups":2}
    for key in workflow_totals(trace["workflow"]):
        values=[r[key] for r in chosen]
        mean,sd=statistics.mean(values),statistics.stdev(values)
        result[key+"_mean"],result[key+"_sample_sd"]=mean,sd
        result[key+"_CV_percent"]=100*sd/mean if mean else 0.
    result["stable"]=all(result[key+"_CV_percent"]<=5 for key in ("agent_critical_ns","server_verification_commit_ns"))
    return result

def run_config(out):
    value = strict((ROOT / "case_study/config.json").read_bytes())
    value.update(timing_enabled=True, case_study_authorized=True,
                 timing_window={"start_unix_seconds": time.time(),
                                         "end_unix_seconds": None})
    path = out / "run_config.json"
    save(path, value)
    return path


def run_session(out, binary, plan, *, live=False, source=None, budget_usd=3.0):
    """Record live workflows or replay saved tool traces, using separate native roles."""
    clock, issuer = Clock.authorized(plan), OAuthIssuer()
    if live and not os.environ.get("OPENROUTER_API_KEY"):
        raise ValueError("OPENROUTER_API_KEY_environment_required")
    traces, samples, attempts, selections, allocation = [], [], [], [], []
    with native_pair(binary, plan) as (bridge, verifier):
        save(out / "native_processes.json", process_record(bridge, verifier))
        parent = bridge.command("issue_parent", instance="root-peer")
        save(out / 'provisioning_issuance.json', parent)
        pool_cursor = 0
        with ToolServer(out / "workflow-state", verifier, issuer.verifier(), clock=clock) as server:
            for workload in ('booking', 'research'):
                model = OpenRouter(InferenceClock(lambda: None), budget_usd=budget_usd) if live else None
                try:
                    for index in range(10):
                        run = index + (10 if workload == 'research' else 0)
                        trace_id = workload + "-" + str(index).zfill(2)
                        pools = list(range(pool_cursor, pool_cursor + (1 if workload == 'booking' else 4)))
                        pool_cursor += len(pools)
                        instance = peer_instance(run)
                        child = delegation(bridge, "root-peer", instance, pools)
                        allocation.append({"trace_id": trace_id, "workload": workload,
                                           "pools": pools, "child": child})
                        save(out / 'provisioning_delegations.json', allocation)
                        if live:
                            with PreparedClient(server, bridge, "darlt", instance, issuer,
                                    positions=positions_for(pools),
                                    steps=actions(workload, "synthetic-customer-" + str(run)),
                                    quota=16 if workload == 'booking' else 64, clock=clock) as client:
                                value = run_workflow(client, workload, model=model, run_index=run)
                            record = {"trace_id": trace_id, "workload": workload,
                                      "pools": pools, "workflow": value}
                            save(out / (trace_id + ".json"), record)
                        else:
                            record = strict((source / (trace_id + ".json")).read_bytes())
                            if (record["trace_id"], record["workload"], record["pools"]) != (trace_id, workload, pools):
                                raise ValueError("saved_trace_identity_or_scope")
                        traces.append(record)
                finally:
                    if model is not None:
                        model.close()
        if live:
            write_csv(out / 'live_steps.csv', [row for trace in traces
                      for row in trace["workflow"]["timing_steps"]])
        metadata = bridge.command("metadata")
        if metadata["darlt_issuer_issue_calls_total"] != 1 or pool_cursor != 50:
            raise ValueError("single_issue_or_pool_count")
        if len({row["child"]["agent_public_key"] for row in allocation}) != 20:
            raise ValueError("recipient_key_reused")
        if len({row["child"]["credential_id"] for row in allocation}) != 1:
            raise ValueError("credential_not_shared")
        save(out / 'provisioning_audit.json', {"passed": True, "issuer_issue_calls": 1,
             "delegations": 20, "allocated_pools": 50, "metadata": metadata})
        bridge.command("init", instance="shared-sma-wallet", scheme="SMA²RT")
        for trace in traces:
            workload = trace["workload"]
            steps = [(step["tool"], step["arguments"]) for step in trace["workflow"]["trace"]]
            for mode in MODES:
                group = trace["trace_id"] + "-" + mode
                instance = ("shared-sma-wallet" if mode == "sma" else peer_instance(trace["workflow"]["run"])
                            if mode.startswith("darlt") else "oauth-" + peer_instance(trace["workflow"]["run"]))
                quota = 16 if workload == 'booking' else 64
                selected = positions_for(trace["pools"]) if mode.startswith("darlt") else list(range(quota))
                with ToolServer(out / "replay-state" / group, verifier, issuer.verifier(), clock=clock) as server,\
                     PreparedClient(server, bridge, mode, instance, issuer,
                                    positions=selected, steps=steps, quota=quota, clock=clock) as client:
                    snapshot = server.stores[mode].snapshot()
                    group_attempts = []
                    try:
                        for attempt in range(1, 4):
                            records = []
                            for sample in range(12):
                                server.stores[mode].restore(snapshot)
                                client.reset_workflow()
                                value = run_workflow(client, workload, scripted=True,
                                    run_index=trace["workflow"]["run"], prepare_all=True)
                                if value["trace"] != trace["workflow"]["trace"]:
                                    raise ValueError("replay_does_not_match_saved_trace")
                                if mode.startswith("darlt") and (
                                    [step["prepared_token"]["positions"] for step in value["steps"]] !=
                                    [step["prepared_token"]["positions"] for step in trace["workflow"]["steps"]]):
                                    raise ValueError("replay_positions_differ_from_saved_trace")
                                row = {"trace_id": trace["trace_id"], "workload": workload,
                                       "mode": mode, "attempt": attempt, "sample": sample,
                                       "phase": "warmup" if sample < 2 else "retained",
                                       **workflow_totals(value)}
                                samples.append(row)
                                records.append(row)
                                with (out / 'replay_samples.jsonl').open("ab") as stream:
                                    stream.write(canonical(row) + b"\n")
                                with (out / 'replay_steps.jsonl').open("ab") as stream:
                                    for result in value["steps"]:
                                        stream.write(canonical({"trace_id": trace["trace_id"],
                                            "mode": mode, "attempt": attempt, "sample": sample,
                                            "phase": row["phase"], "tool": result["tool"],
                                            "units": result["units"], "timing": result["timing"],
                                            "readiness": result["readiness"],
                                            "prepared_token": result["prepared_token"],
                                            "request_bytes": result["request_bytes"]}) + b"\n")
                            summary = replay_summary(trace, mode, attempt, records)
                            group_attempts.append(summary)
                            attempts.append(summary)
                            write_csv(out / 'replay_attempts.csv', attempts)
                            if summary["stable"]:
                                break
                    finally:
                        snapshot.close()
                stable = [row for row in group_attempts if row["stable"]]
                chosen = dict(stable[0] if stable else group_attempts[0])
                chosen.update(selected_attempt=chosen["attempt"],
                              cohort_status="stable" if stable else "unresolved")
                selections.append(chosen)
                write_csv(out / 'replay_selected.csv', selections)
        save(out / "native_processes_final.json", process_record(bridge, verifier))
    write_csv(out / 'replay_samples.csv', samples)
    from .misuse import run_misuse
    cases = run_misuse(binary, out / "misuse-state")
    save(out / "table_v.json", cases)
    result = {"passed": True, "live_model_workflows": len(traces) if live else 0,
              "model_API_calls": 120 if live else 0, "replayed_traces": len(traces),
              "replay_groups": len(selections), "replay_attempts": len(attempts),
              "replay_samples": len(samples), "misuse_records": len(cases)}
    save(out / "summary.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=["check", "live", "replay"], default="check")
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--source", type=Path, default=ROOT / "data/case_study")
    parser.add_argument("--api-budget", type=float, default=3.0)
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise ValueError("existing_case_study_output")
    out.mkdir(parents=True, exist_ok=True)
    if args.mode == "check":
        result = correctness(out, args.binary)
    else:
        plan = run_config(out)
        result = run_session(out, args.binary, plan, live=args.mode == "live",
                             source=args.source.resolve(), budget_usd=args.api_budget)
    save(out / "run_result.json", result)
    print(json.dumps(result, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
