#!/usr/bin/env python3
"""Export recorded case-study results, tables and fixed-axis Fig. 12."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

WORKLOADS = ('booking', 'research')
MODES = ("oauth", "sma", "darlt-ablation", "darlt")
DISPLAY = {"oauth": "OAuth+DPoP", "sma": "SMA²RT",
           "darlt-ablation": "DARLT ($k$ tokens)", "darlt": "DARLT"}
EXPECTED = {
    'booking': [("search_inventory", 1), ("get_details", 1), ("book_item", 4),
           ("get_details", 1), ("search_inventory", 1)],
    'research': [("search_sources", 1), ("fetch_documents", 8), ("query_dataset", 16),
           ("run_analysis", 4), ("export_report", 32)],
}
TIME_FIELDS = (
    "model_api_ns", "darlt_critical_ns", "other_ns", "agent_critical_ns",
    'proof_path_inclusive_ns', 'non_proof_path_ns',
    "server_verification_commit_ns", "readiness_gate_ns", "future_wait_ns",
    "online_bridge_ns", "online_bridge_queue_ns", "online_rpc_ns",
    "native_online_ns", "mcp_http_ns", "decode_ns", "verification_ns",
    "state_backend_ns", "request_latency_ns",
)
REPLAY_FIELDS = (
    "agent_critical_ns", "server_verification_commit_ns", "sent_http_bytes",
    "request_body_bytes", "native_token_bytes", "initial_preparation_ns",
    "native_preparation_ns", "preparation_bridge_ns", "all_preparation_ns", "future_wait_ns",
    "online_bridge_queue_ns", "ready_at_demand_count", "units", "tool_calls",
    "preparations_during_workflow_count",
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def read_csv(path):
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n", encoding="utf-8")


def write_csv(path, rows):
    if not rows:
        raise ValueError("empty_export:" + path.name)
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows({key: json.dumps(value, ensure_ascii=False, sort_keys=True)
                         if isinstance(value, (dict, list, tuple)) else value
                         for key, value in row.items()} for row in rows)


def number(row, name):
    value = 0 if row.get(name) in (None, "") else float(row[name])
    if not math.isfinite(value) or value < 0:
        raise ValueError("invalid_nonnegative_measurement:" + name)
    return value


def statistics_for(values):
    if not values:
        raise ValueError("empty_statistics")
    mean = statistics.mean(values)
    sd = statistics.stdev(values) if len(values) > 1 else 0.
    return {"mean": mean, "sample_sd": sd, "min": min(values), "max": max(values),
            "CV_percent": 100 * sd / mean if mean else 0.}


def add_statistics(target, key, values):
    for name, value in statistics_for(values).items():
        target[key + "_" + name] = value
    if key.endswith("_ns"):
        target[key[:-3] + "_mean_ms"] = target[key + "_mean"] / 1e6
        target[key[:-3] + "_sample_sd_ms"] = target[key + "_sample_sd"] / 1e6


def flattened(source, prefix=""):
    out = {}
    for key, value in source.items():
        name = prefix + key
        if isinstance(value, dict):
            out.update(flattened(value, name + "_"))
        else:
            out[name] = value
    return out


def attribution(row):
    row = dict(row)
    native = sum(number(row, key) for key in ("native_online_ns", "decode_ns", "verification_ns"))
    proof_path_inclusive = sum(number(row, key) for key in
                 ("readiness_gate_ns", "online_bridge_ns", "decode_ns", "verification_ns"))
    critical = number(row, "agent_critical_ns")
    if critical < native or critical < proof_path_inclusive:
        raise ValueError("negative_other_attribution")
    expected_source = native
    if number(row, "darlt_critical_ns") != expected_source:
        raise ValueError("source_DARLT_attribution_does_not_match_declared_input")
    if number(row, "other_ns") != critical - expected_source:
        raise ValueError("source_Other_attribution_does_not_partition")
    if 'proof_path_inclusive_ns' in row and row['proof_path_inclusive_ns'] not in (None, "") and number(row, 'proof_path_inclusive_ns') != proof_path_inclusive:
        raise ValueError('proof_path_inclusive_attribution_mismatch')
    if 'non_proof_path_ns' in row and row['non_proof_path_ns'] not in (None, "") and number(row, 'non_proof_path_ns') != critical - proof_path_inclusive:
        raise ValueError('non_proof_path_attribution_mismatch')
    row.update(darlt_critical_ns=native, other_ns=critical - native,
               proof_path_inclusive_ns=proof_path_inclusive, non_proof_path_ns=critical - proof_path_inclusive)
    return row


def export_live_workflows(data, out):
    raw = read_csv(data / 'live_steps.csv')
    if len(raw) != 120:
        raise ValueError('live_requires_20_complete_six_step_workflows')
    expected_pairs = {(w, run, step) for w in WORKLOADS
                      for run in (range(10) if w == 'booking' else range(10, 20))
                      for step in range(1, 7)}
    if {(r["workload"], int(r["run"]), int(r["step"])) for r in raw} != expected_pairs:
        raise ValueError('live_step_inventory')
    raw = [attribution(row) for row in raw]
    for row in raw:
        index = int(row["step"])
        if index <= 5:
            if (row["tool"], int(row["units"])) != EXPECTED[row["workload"]][index - 1]:
                raise ValueError('live_tool_or_unit_sequence_changed')
            expected_darlt = sum(number(row, key) for key in
                                 ("native_online_ns", "decode_ns", "verification_ns"))
            if number(row, "darlt_critical_ns") != expected_darlt:
                raise ValueError('live_native_critical_attribution_changed')
            if number(row, "darlt_critical_ns") + number(row, "other_ns") != number(row, "agent_critical_ns"):
                raise ValueError('live_critical_components_do_not_partition')
            if number(row, "readiness_gate_ns") + number(row, "request_latency_ns") != number(row, "agent_critical_ns"):
                raise ValueError('live_critical_windows_not_consecutive')
        elif (row["tool"] != "final_reply" or int(row["units"]) != 0
              or any(number(row, key) != 0 for key in ("darlt_critical_ns", "other_ns", "agent_critical_ns"))):
            raise ValueError('live_final_reply_must_only_have_model_time')
    write_csv(out / 'live_steps.csv', raw)
    grouped = defaultdict(list)
    for row in raw:
        grouped[(row["workload"], int(row["step"]))].append(row)
    aggregates = []
    for workload in WORKLOADS:
        for step in range(1, 7):
            chosen = grouped[(workload, step)]
            if len(chosen) != 10:
                raise ValueError('live_step_requires_ten_runs')
            result = {"workload": workload, "step": step, "tool": chosen[0]["tool"],
                      "units": int(chosen[0]["units"]), "n": 10}
            for key in TIME_FIELDS:
                add_statistics(result, key, [number(row, key) for row in chosen])
            aggregates.append(result)
    write_csv(out / 'live_step_statistics.csv', aggregates)

    preparations, events, readiness, workflows = [], [], [], []
    expected_traces = [f"{workload}-{i:02d}" for workload in WORKLOADS for i in range(10)]
    for trace_id in expected_traces:
        recorded = read_json(data / (trace_id + ".json"))
        value = recorded["workflow"]
        workload = recorded["workload"]
        if recorded["trace_id"] != trace_id or value.get("passed") is not True:
            raise ValueError('live_record_identity_or_completion')
        if len(value["steps"]) != 5 or len(value["model_records"]) != 6:
            raise ValueError('live_model_and_tool_call_counts')
        if [(r["tool"], r["units"]) for r in value["trace"]] != EXPECTED[workload]:
            raise ValueError('live_recorded_trace_changed')
        scope = value["scope_accounting"]
        expected_units = 8 if workload == 'booking' else 61
        if any(scope[key] != expected_units for key in ("reserved_units", "spent_units", "expected_units")):
            raise ValueError('live_scope_accounting')
        positions = [position for job in value["preparations"] for position in job["positions"]]
        allowed = {pool * 16 + offset for pool in recorded["pools"] for offset in range(16)}
        if len(positions) != expected_units or len(set(positions)) != expected_units or not set(positions) <= allowed:
            raise ValueError('live_prepared_units_overlap_or_scope_escape')
        reasons = [job["reason"] for job in value["preparations"]]
        if (workload == 'research' and reasons != ["initial"] * 5) or (
                workload == 'booking' and (reasons.count("initial"), reasons.count("replenishment")) != (3, 2)):
            raise ValueError('live_refill_rule_invariant_failed')
        for job in value["preparations"]:
            preparations.append({"trace_id": trace_id, "workload": workload, "run": value["run"], **job})
        for event in value["events"]:
            events.append({"trace_id": trace_id, "workload": workload, "run": value["run"], **event})
        for index, result in enumerate(value["steps"], 1):
            readiness.append({"trace_id": trace_id, "workload": workload, "run": value["run"],
                              "step": index, "tool": result["tool"], "units": result["units"],
                              **result["readiness"], **flattened(result["timing"], "timing_"),
                              **flattened(result.get("prepared_token") or {}, "prepared_")})
        steps = [attribution(row) for row in value["timing_steps"]]
        result = {"trace_id": trace_id, "workload": workload, "run": value["run"],
                  "pools": recorded["pools"], "tool_calls": 5, "model_inference_calls": 6,
                  "units": expected_units, "quota": len(allowed),
                  "initial_preparation_ns": value["initial_preparation"]["initial_preparation_ns"],
                  "prepared_entries": len(value["preparations"]),
                  "prepared_unit_count": len(positions),
                  "native_preparation_ns": sum(number(job, "native_preparation_ns") for job in value["preparations"]),
                  "preparation_bridge_ns": sum(number(job, "preparation_bridge_ns") for job in value["preparations"]),
                  "ready_at_demand_count": sum(r["readiness"]["ready_before_demand"] for r in value["steps"]),
                  "sent_http_bytes": sum(r["http_sent_bytes"] for r in value["steps"]),
                  "request_body_bytes": sum(r["request_body_bytes"] for r in value["steps"]),
                  "native_token_bytes": sum(r["native_token_bytes"] for r in value["steps"])}
        for key in TIME_FIELDS:
            result[key] = sum(number(row, key) for row in steps)
        result["active_ns"] = result["model_api_ns"] + result["agent_critical_ns"]
        result["darlt_critical_fraction_of_active"] = result["darlt_critical_ns"] / result["active_ns"]
        result["darlt_critical_fraction_of_agent_path"] = result["darlt_critical_ns"] / result["agent_critical_ns"]
        workflows.append(result)
    write_csv(out / 'live_workflows.csv', workflows)
    write_csv(out / 'live_preparations.csv', preparations)
    write_csv(out / 'live_events.csv', events)
    write_csv(out / 'live_readiness.csv', readiness)
    write_csv(out / "fig12a.csv", [r for r in aggregates if r["workload"] == 'research'])
    return aggregates, workflows


def export_replay_workflows(data, out):
    samples = read_csv(data / 'replay_samples.csv')
    source_choices = read_csv(data / 'replay_selected.csv')
    choices = {(row["trace_id"], row["mode"]): row for row in source_choices}
    expected_groups = {(f"{w}-{i:02d}", mode) for w in WORKLOADS for i in range(10) for mode in MODES}
    if len(source_choices) != 80 or set(choices) != expected_groups:
        raise ValueError('replay_requires_80_trace_deployment_groups')
    by_attempt = defaultdict(list)
    for row in samples:
        group = (row["trace_id"], row["mode"])
        if group not in expected_groups or row["workload"] not in WORKLOADS:
            raise ValueError('replay_unknown_group')
        if row["phase"] not in ("warmup", "retained"):
            raise ValueError('replay_unknown_sample_phase')
        if int(row["tool_calls"]) != 5 or int(row["units"]) != (8 if row["workload"] == 'booking' else 61):
            raise ValueError('replay_workflow_unit_or_step_count')
        if not number(row, "native_token_bytes") <= number(row, "request_body_bytes") <= number(row, "sent_http_bytes"):
            raise ValueError('replay_nested_byte_accounting')
        if row.get("all_preparation_ns") in (None, ""):
            raise ValueError('replay_all_preparation_time_missing')
        if number(row, "all_preparation_ns") != number(row, "initial_preparation_ns"):
            raise ValueError('replay_full_preparation_window_mismatch')
        if number(row, "future_wait_ns") != 0:
            raise ValueError('replay_wait_for_preparation_during_replay')
        if row.get("preparations_during_workflow_count") in (None, "") or number(row, "preparations_during_workflow_count") != 0:
            raise ValueError('replay_preparation_started_during_replay')
        by_attempt[(*group, int(row["attempt"]))].append(row)
    attempt_statistics, selected_samples, choice_records = [], [], []
    for trace_id, mode in sorted(expected_groups):
        indices = sorted(key[2] for key in by_attempt if key[:2] == (trace_id, mode))
        if not indices or indices != list(range(1, len(indices) + 1)) or max(indices) > 3:
            raise ValueError('replay_attempt_inventory')
        local = []
        for attempt in indices:
            rows = by_attempt[(trace_id, mode, attempt)]
            warm = [row for row in rows if row["phase"] == "warmup"]
            kept = [row for row in rows if row["phase"] == "retained"]
            if len(warm) != 2 or len(kept) != 10 or {int(row["sample"]) for row in rows} != set(range(12)):
                raise ValueError('replay_attempt_requires_2_warmup_10_retained')
            if any((int(row["sample"]) < 2) != (row["phase"] == "warmup") for row in rows):
                raise ValueError('replay_sample_phase_mismatch')
            result = {"trace_id": trace_id, "workload": rows[0]["workload"],
                      "mode": mode, "attempt": attempt, "n": 10, "warmups": 2}
            for key in REPLAY_FIELDS:
                add_statistics(result, key, [number(row, key) for row in kept])
            result["stable"] = all(result[key + "_CV_percent"] <= 5 for key in
                                    ("agent_critical_ns", "server_verification_commit_ns"))
            local.append(result)
        stable = [row for row in local if row["stable"]]
        expected_choice = stable[0]["attempt"] if stable else 1
        source = choices[(trace_id, mode)]
        selected = int(source["selected_attempt"])
        if selected != expected_choice or source["cohort_status"] != ("stable" if stable else "unresolved"):
            raise ValueError('replay_selection_does_not_follow_recorded_rule')
        chosen_stats = next(row for row in local if row["attempt"] == selected)
        for key in ("agent_critical_ns_mean", "agent_critical_ns_sample_sd",
                    "server_verification_commit_ns_mean", "server_verification_commit_ns_sample_sd"):
            if source.get(key) not in (None, "") and not math.isclose(float(source[key]), chosen_stats[key], rel_tol=1e-11, abs_tol=.01):
                raise ValueError('replay_selected_statistics_differ_from_raw:' + key)
        for row in local:
            row["selected_for_figure"] = row["attempt"] == selected
        attempt_statistics.extend(local)
        choice_records.append({**source, "selection_verified_from_raw": True})
        selected_samples.extend(row for row in by_attempt[(trace_id, mode, selected)] if row["phase"] == "retained")
    if len(selected_samples) != 800:
        raise ValueError('replay_requires_800_selected_workflows')
    write_csv(out / 'replay_all_samples.csv', samples)
    write_csv(out / 'replay_all_attempts.csv', attempt_statistics)
    write_csv(out / 'replay_group_selection.csv', choice_records)
    write_csv(out / 'replay_selected_workflows.csv', selected_samples)

    pooled = []
    for mode in MODES:
        for workload in WORKLOADS:
            kept = [row for row in selected_samples if row["mode"] == mode and row["workload"] == workload]
            traces = sorted({row["trace_id"] for row in kept})
            if len(kept) != 100 or len(traces) != 10 or any(sum(row["trace_id"] == trace for row in kept) != 10 for trace in traces):
                raise ValueError('replay_cell_requires_10_traces_by_10_retained')
            unresolved = [trace for trace in traces if choices[(trace, mode)]["cohort_status"] == "unresolved"]
            result = {"mode": mode, "display_deployment": DISPLAY[mode], "workload": workload,
                      "n": 100, "traces": 10, "retained_per_trace": 10,
                      "source_attempts_by_trace_json": {trace: int(choices[(trace, mode)]["selected_attempt"]) for trace in traces},
                      "unresolved_trace_groups": len(unresolved), "unresolved_trace_ids_json": unresolved,
                      "spread_basis": "sample SD over the 100 retained workflow totals, never a mean of SDs"}
            for key in REPLAY_FIELDS:
                add_statistics(result, key, [number(row, key) for row in kept])
            pooled.append(result)
    write_csv(out / 'replay_workload_deployment_statistics.csv', pooled)
    write_csv(out / "fig12b.csv", pooled)

    step_rows = []
    with (data / 'replay_steps.jsonl').open(encoding="utf-8") as stream:
        for line in stream:
            if not line.strip():
                continue
            row = json.loads(line)
            key = (row["trace_id"], row["mode"])
            if key not in expected_groups:
                raise ValueError('replay_step_unknown_group')
            row["selected_for_figure"] = row["phase"] == "retained" and int(row["attempt"]) == int(choices[key]["selected_attempt"])
            step_rows.append(flattened(row))
    if len(step_rows) != len(samples) * 5:
        raise ValueError('replay_step_inventory_does_not_match_workflows')
    write_csv(out / 'replay_steps.csv', step_rows)
    return pooled, attempt_statistics


def export_provisioning(data, out):
    issue = read_json(data / 'provisioning_issuance.json')
    delegations = read_json(data / 'provisioning_delegations.json')
    audit = read_json(data / 'provisioning_audit.json')
    if audit.get("passed") is not True or (audit["issuer_issue_calls"], audit["delegations"], audit["allocated_pools"]) != (1, 20, 50):
        raise ValueError('provisioning_single_issue_audit_failed')
    pools = [pool for row in delegations for pool in row["pools"]]
    if len(delegations) != 20 or len(pools) != 50 or len(set(pools)) != 50 or not all(0 <= pool < 64 for pool in pools):
        raise ValueError('provisioning_pool_inventory')
    if any(len(row["pools"]) != (1 if row["workload"] == 'booking' else 4) for row in delegations):
        raise ValueError('provisioning_per_workload_grant')
    write_csv(out / 'provisioning_issuance.csv', [flattened(issue)])
    write_csv(out / 'provisioning_delegations.csv', [flattened(row) for row in delegations])
    write_json(out / 'provisioning_audit.json', audit)



CATEGORIES = [
    ("ungranted_tool_or_resource", "Ungranted tool or resource", 2),
    ("ungranted_or_private_attribute", "Ungranted or private attribute", 2),
    ("stolen_material_without_agent_secret", "Stolen material without agent secret", 1),
    ("agent_budget_exhaustion", "Agent budget exhaustion", 1),
    ("batch_atomicity", "Batch atomicity", 3),
    ("cross_verifier_double_use", "Cross-verifier double use", 1),
    ("malicious_owner_overlapping_allocation", "Malicious owner overlapping allocation", 2),
]


def case_outcome(row):
    if row["applicable"] is not True:
        return "N/A"
    if row["blocked"] is True:
        return "Rejected"
    if row["classification"] in ("agent", "authenticated_subject_agent"):
        return "Agent"
    if row["classification"] == "user":
        return "User"
    return "Accepted"

def table_data(data, out):
    value = read_json(data / "table_v.json")
    if isinstance(value, dict):
        value = next((value[k] for k in ("misuse_cases", "cases", "records") if isinstance(value.get(k), list)), None)
    if not isinstance(value, list) or len(value) != 36 or len({r["case_id"] for r in value}) != 36:
        raise ValueError("TableV_requires_36_unique_recorded_cases")
    cases = [{**r, "display_outcome": case_outcome(r)} for r in value]
    write_csv(out / "table_v_cases.csv", cases)
    rows, cells = [], []
    for category, label, expected_count in CATEGORIES:
        row = {"category": category, "display_category": label,
               "cases_per_deployment": expected_count, "cases_all_deployments": 3 * expected_count}
        for mode in ("oauth", "sma", "darlt"):
            chosen = [r for r in cases if r["category"] == category and r["mode"] == mode]
            if len(chosen) != expected_count:
                raise ValueError("TableV_category_inventory_mismatch")
            counts = Counter(r["display_outcome"] for r in chosen)
            outcomes = list(dict.fromkeys(r["display_outcome"] for r in chosen))
            row[mode] = "; ".join(outcomes)
            for outcome in ("Accepted", "Rejected", "Agent", "User", "N/A"):
                row[mode + "_" + outcome.lower().replace("/", "_") + "_count"] = counts[outcome]
            row[mode + "_outcomes_by_case_json"] = {r["case_id"]: r["display_outcome"] for r in chosen}
            cells.append({"category": category, "display_category": label, "mode": mode,
                          "case_count": expected_count, "outcomes": "; ".join(outcomes),
                          "outcome_counts_json": dict(counts),
                          "applicable_cases": sum(r["applicable"] is True for r in chosen),
                          "attribution_method": "authenticated subject; no native unit Judge" if mode == "oauth" and category == "cross_verifier_double_use" else "native Judge/Identify" if counts["Agent"] + counts["User"] else "authorization outcome"})
        rows.append(row)
    if sum(r["cases_all_deployments"] for r in rows) != 36:
        raise ValueError("TableV_total_case_count")
    write_csv(out / "table_v.csv", rows)
    write_csv(out / "table_v_cells.csv", cells)
    write_json(out / "table_v_cases.json", cases)
    return rows

def plot_figures(root, out, live_statistics, replay_statistics, panels=("fig12a", "fig12b")):
    sys.path.insert(0, str(root / "scripts"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch
    from matplotlib.transforms import ScaledTranslation
    from PIL import Image
    import fitz
    from paper_style import (DPI, MARGINS, PANEL_HEIGHT, PANEL_WIDTH, SCHEME_STYLES,
                             apply_style, legend, log_y, power_tick_labels)
    from plot_figures import geometry_audit, label_bars, panel_figure

    apply_style()

    def save_panel(fig, ax, name, positive_values):
        if not positive_values or any(value <= 0 or not math.isfinite(value) for value in positive_values):
            raise ValueError("log_panel_requires_positive_observed_values")
        low, high = {"fig12a": (1, 100000), "fig12b": (1, 10000)}[name]
        if min(positive_values) < low or max(positive_values) > high:
            raise ValueError("observed_value_outside_fixed_axis:" + name)
        fields = ("outside_page_text", "overlapping_xtick_pairs", "legend_data_intersections",
                  "legend_number_intersections", "number_number_ink_intersections",
                  "number_other_bar_ink_intersections", "number_host_bar_ink_intersections",
                  "number_frame_ink_intersections")
        log_y(ax, low, high)
        power_tick_labels(ax)
        audit = geometry_audit(fig, ax)
        if not audit["legend_inside_axes"] or any(audit[key] for key in fields):
            raise ValueError('figure_layout_check_failed:' + name + ":" + json.dumps({key: audit[key] for key in fields if audit[key]}))
        fig.savefig(out / (name + ".pdf"))
        fig.savefig(out / (name + ".png"), dpi=DPI)
        plt.close(fig)
        return audit

    def ylabel(ax, text):
        ax.set_ylabel(text, labelpad=1)
        width = PANEL_WIDTH - MARGINS["left"] - MARGINS["right"]
        ax.yaxis.set_label_coords((9 / 72 - MARGINS["left"]) / width, .5)

    audit_a = audit_b = None
    if "fig12a" in panels:
        research_statistics = [row for row in live_statistics if row["workload"] == 'research']
        series = [("LLM", "model_api_ns_mean", "#3F7F93"),
                  ("DARLT", "darlt_critical_ns_mean", SCHEME_STYLES["DARLT"][0]),
                  ("Other", "other_ns_mean", "#74787E")]
        values_a = [row[key] / 1e6 for row in research_statistics for _, key, _ in series if row[key] > 0]
        low_a = 1
        fig, ax = panel_figure("fig12a")
        for series_index, (name, key, color) in enumerate(series):
            positions, values = [], []
            for index, row in enumerate(research_statistics):
                value = row[key] / 1e6
                if value == 0:
                    continue
                if index == 5 and name != "LLM":
                    raise ValueError("Step6_only_LLM")
                positions.append(index if index == 5 else index + (series_index - 1) * .235)
                values.append(value)
            if values:
                patches = ax.bar(positions, [value - low_a for value in values], bottom=low_a,
                                 width=.21, color=color, edgecolor="black", linewidth=.4, label=name, zorder=3)
                label_bars(ax, patches, values)
        ax.set_xticks(range(6), [f"Step {i}" for i in range(1, 7)])
        ax.set_xlim(-.5, 5.5)
        ylabel(ax, "Execution Time (ms)")
        legend(ax, loc="upper center", bbox_to_anchor=(.375, 1), ncol=3,
               borderpad=.03, borderaxespad=.12)
        audit_a = save_panel(fig, ax, "fig12a", values_a)

    if "fig12b" in panels:
        colors = {
            "oauth": {"booking": "#C9CDB0", "research": "#77833A"},
            "sma": {"booking": "#A9D8D2", "research": "#2A9D8F"},
            "darlt-ablation": {"booking": "#EBCBD3", "research": "#C7798C"},
            "darlt": {"booking": "#E3B5BC", "research": "#8E1B32"},
        }
        values_b = [row["server_verification_commit_ns_mean"] / 1e6 for row in replay_statistics]
        low_b = 1
        fig, ax = panel_figure("fig12b")
        for row in replay_statistics:
            index = MODES.index(row["mode"])
            position = index + (-.18 if row["workload"] == 'booking' else .18)
            value = row["server_verification_commit_ns_mean"] / 1e6
            patches = ax.bar(position, value - low_b, bottom=low_b, width=.30,
                             color=colors[row["mode"]][row["workload"]],
                             hatch="////" if row["workload"] == 'booking' else None,
                             edgecolor="black", linewidth=.4, zorder=3)
            label_bars(ax, patches, [value])
        ax.set_xticks(range(4), [DISPLAY[mode] for mode in MODES],
                      rotation=30, rotation_mode="anchor", ha="right", va="baseline")
        for label in ax.get_xticklabels():
            label.set_transform(ax.get_xaxis_text1_transform(1)[0] +
                                ScaledTranslation(0, -4 / 72, fig.dpi_scale_trans))
        ax.set_xlim(-.5, 3.5)
        ylabel(ax, "Server Time (ms)")
        legend(ax, handles=[
            Patch(facecolor="white", edgecolor="black", linewidth=.4, hatch="////", label="Booking"),
            Patch(facecolor="#5C5C5C", edgecolor="black", linewidth=.4, label="Research"),
        ], loc="upper left", ncol=2)
        audit_b = save_panel(fig, ax, "fig12b", values_b)

    images = [Image.open(out / (name + ".png")).convert("RGB") for name in ("fig12a", "fig12b")]
    gap = round(.08 * DPI)
    preview = Image.new("RGB", (sum(im.width for im in images) + gap, images[0].height), "white")
    preview.paste(images[0], (0, 0))
    preview.paste(images[1], (images[0].width + gap, 0))
    preview.save(out / "fig12.png", dpi=(DPI, DPI))
    combined = fitz.open()
    page = combined.new_page(width=(2 * PANEL_WIDTH + .08) * 72, height=PANEL_HEIGHT * 72)
    for index, name in enumerate(("fig12a", "fig12b")):
        doc = fitz.open(out / (name + ".pdf"))
        left = index * (PANEL_WIDTH + .08) * 72
        page.show_pdf_page(fitz.Rect(left, 0, left + PANEL_WIDTH * 72, PANEL_HEIGHT * 72), doc, 0)
        doc.close()
    combined.save(out / "fig12.pdf")
    combined.close()
    pdf_checks = {}
    for name in panels:
        doc = fitz.open(out / (name + ".pdf"))
        page = doc[0]
        spans = [span for block in page.get_text("dict")["blocks"] if "lines" in block
                 for line in block["lines"] for span in line["spans"]]
        outside = [span["text"] for span in spans if not page.rect.contains(fitz.Rect(span["bbox"]))]
        fonts = sorted({span["font"] for span in spans})
        sizes = sorted({round(span["size"], 4) for span in spans})
        if outside or not all(font.startswith("Arial") for font in fonts) or not set(sizes) <= {4.5, 5, 5.5, 6.5}:
            raise ValueError("PDF_typography_or_page_boundary_failed:" + name)
        pdf_checks[name] = {"fonts": fonts, "sizes_pt": sizes, "outside_page_text": outside,
                            "page_size_pt": list(page.rect)}
        doc.close()
    return {"fig12a": audit_a, "fig12b": audit_b, "PDF": pdf_checks,
            "error_bars": False, "spread_in_CSV": "sample SD, denominator n-1",
            "zero_values": "not plotted; no epsilon or positive surrogate",
            "y_ranges_fixed_ms": {"fig12a": [1, 100000], "fig12b": [1, 10000]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument("--root", type=Path, default=root)
    parser.add_argument("--data", type=Path, default=root / "data/case_study")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--tables-only", "--table-only", action="store_true")
    args = parser.parse_args()
    root, data, out = args.root.resolve(), args.data.resolve(), args.out.resolve()
    if out == data or out in data.parents or data in out.parents:
        raise ValueError("saved_source_directory")
    source_names = ['live_steps.csv', 'replay_samples.csv', 'replay_selected.csv', 'replay_attempts.csv', 'replay_steps.jsonl', 'provisioning_delegations.json', 'provisioning_issuance.json', 'provisioning_audit.json', "table_v.json"]
    source_names += [f"{w}-{i:02d}.json" for w in WORKLOADS for i in range(10)]
    sources = {name: digest(data / name) for name in source_names}
    out.mkdir(parents=True, exist_ok=True)
    live_statistics, workflows = export_live_workflows(data, out)
    replay_statistics, attempts = export_replay_workflows(data, out)
    export_provisioning(data, out)
    table_data(data, out)
    audit = {"measurement_calls": 0, "model_API_calls": 0, "source_sha256": sources,
             "model_workflows": len(workflows), "model_step_rows": 120,
             "step_statistics_rows": len(live_statistics), "replay_pooled_cells": len(replay_statistics),
             "replay_retained_per_cell": 100, "replay_attempts": len(attempts), "misuse_cases": 36,
             "refill_rule": "Refill only when an actual later occurrence and sufficient unallocated units remain; booking total 8/16, research initial 61/64 without refill",
             "timing_attribution": "DARLT=native_online+native_decode+native_verification; Other=agent_critical-DARLT; server window nested",
             "byte_units": "B; request body and native token are nested in sent HTTP bytes"}
    if not args.tables_only:
        audit["figures"] = plot_figures(root, out, live_statistics, replay_statistics)
    if sources != {name: digest(data / name) for name in source_names}:
        raise ValueError("source_changed_during_export")
    write_json(out / "case_study_export.json", audit)
    print(json.dumps({"status": "PASS", "measurement_calls": 0, "model_API_calls": 0}, ensure_ascii=False))

if __name__ == "__main__":
    main()
