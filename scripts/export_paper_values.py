#!/usr/bin/env python3
"""Select paper statistics and compute role totals from saved samples."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import math
import statistics as sample_statistics
from collections import Counter, defaultdict
from pathlib import Path


PAPER_POLICY = "first_stable_whole_cohort_else_attempt_1"
TOTAL_FIELDS = [
    "table_iv_total_kind", "table_iv_total_mean_ms", "table_iv_total_sample_sd_ms",
    "table_iv_total_n", "table_iv_total_uncertainty_basis", "table_iv_total_boundary",
    "table_iv_total_member_jobs_json", "table_iv_total_member_attempts_json",
    "table_iv_total_member_cohort_statuses_json",
]
INCREMENT_FIELDS = [
    "verification_unit_increment_ms", "verification_unit_increment_base_k",
    "verification_unit_increment_target_k", "verification_unit_increment_denominator",
    "verification_unit_increment_base_job_id", "verification_unit_increment_base_attempt",
    "verification_unit_increment_target_job_id", "verification_unit_increment_target_attempt",
    "verification_unit_increment_boundary_json", "verification_unit_increment_basis",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        fields = list(reader.fieldnames or [])
        return fields, list(reader)


def select_results(
    statistics: list[dict[str, str]], job_status: list[dict[str, str]]
) -> tuple[list[dict[str, str]], dict[str, object]]:
    """Validate cohort coverage and select one attempt."""
    by_job_attempt: dict[tuple[str, int], dict[str, str]] = {}
    cohort_attempts: dict[str, dict[int, list[dict[str, str]]]] = defaultdict(
        lambda: defaultdict(list)
    )
    for row in statistics:
        key = row["job_id"], int(row["attempt"])
        if key in by_job_attempt:
            raise ValueError(f"Duplicate source job/attempt: {key}")
        by_job_attempt[key] = row
        cohort_attempts[row["cohort"]][key[1]].append(row)

    status_by_job = {row["job_id"]: row for row in job_status}
    if len(status_by_job) != len(job_status):
        raise ValueError("Duplicate job in job_status.csv")
    if set(status_by_job) != {key[0] for key in by_job_attempt}:
        raise ValueError("Source job coverage differs from job_status.csv")

    chosen: dict[str, tuple[int, str, str]] = {}
    cohort_details: list[dict[str, object]] = []
    for cohort, attempts in sorted(cohort_attempts.items()):
        job_sets = [{row["job_id"] for row in rs} for rs in attempts.values()]
        if any(job_set != job_sets[0] for job_set in job_sets):
            raise ValueError(f"Incomplete whole-cohort attempt: {cohort}")
        outcomes = {}
        for attempt, rs in attempts.items():
            values = {row["cohort_outcome"] for row in rs}
            if len(values) != 1:
                raise ValueError(f"Inconsistent whole-cohort outcome: {cohort}")
            outcomes[attempt] = values.pop()
        stable = sorted(a for a, outcome in outcomes.items() if outcome == "stable")
        source_attempt = stable[0] if stable else 1
        if source_attempt not in attempts:
            raise ValueError(f"Missing first attempt: {cohort}")
        cohort_status = "stable" if stable else "unresolved"
        rule = (
            "first_stable_whole_cohort"
            if stable
            else "unresolved_cohort_attempt_1_by_user_policy"
        )
        chosen[cohort] = source_attempt, cohort_status, rule
        cohort_details.append(
            {
                "cohort": cohort,
                "cohort_status": cohort_status,
                "source_attempt": source_attempt,
                "available_attempts": sorted(attempts),
                "jobs": sorted(job_sets[0]),
                "paper_selection_rule": rule,
            }
        )

    selected = []
    for job_id, status in sorted(status_by_job.items()):
        attempt, cohort_status, rule = chosen[status["cohort"]]
        source = by_job_attempt[job_id, attempt]
        if source["cohort"] != status["cohort"]:
            raise ValueError(f"Source cohort changed: {job_id}")
        recorded_first = status["first_stable_attempt"]
        if cohort_status == "stable" and int(recorded_first) != attempt:
            raise ValueError(f"First stable attempt differs from job_status: {job_id}")
        if cohort_status == "unresolved" and recorded_first:
            raise ValueError(f"Unresolved task has recorded stable result: {job_id}")
        if int(source["n"]) != int(source["expected_samples"]):
            raise ValueError(f"Incomplete retained sample set: {job_id}")
        selected.append(
            {
                **source,
                "source_attempt": str(attempt),
                "cohort_status": cohort_status,
                "paper_policy": PAPER_POLICY,
                "paper_selection_rule": rule,
            }
        )

    unresolved_rows = [r for r in selected if r["cohort_status"] == "unresolved"]
    audit: dict[str, object] = {
        "paper_policy": PAPER_POLICY,
        "timing_or_protocol_calls": 0,
        "source_rows_preserved_without_recalculation": True,
        "source_sample_counts_preserved": True,
        "selected_tasks": len(selected),
        "unique_selected_tasks": len({r["job_id"] for r in selected}),
        "cohorts": len(chosen),
        "stable_cohorts": sum(c[1] == "stable" for c in chosen.values()),
        "unresolved_cohorts": sum(c[1] == "unresolved" for c in chosen.values()),
        "stable_selected_tasks": len(selected) - len(unresolved_rows),
        "unresolved_attempt_1_selected_tasks": len(unresolved_rows),
        "unresolved_retained_sample_counts": dict(
            sorted(Counter(r["n"] for r in unresolved_rows).items())
        ),
        "sample_count_note": (
            "The unresolved G2_MSM size-1 calibration cohort contains two tasks "
            "with 1000 retained measurements each. The other 26 unresolved tasks "
            "have 100 measurements each. Selecting attempt 1 preserves these "
            "actual n values; no calibration measurements were truncated or "
            "relabeled as n=100."
        ),
        "campaign_status_values_preserved": sorted(
            {r["campaign_status"] for r in selected}
        ),
        "paper_selection_does_not_change_stability_status": True,
        "cohort_selection": cohort_details,
    }
    return selected, audit


def workload_identity(row: dict[str, str], *, scan_k: bool = False) -> dict:
    workload = json.loads(row["workload_json"])
    ignored = {"variant", "fixture_initialization"}
    if scan_k:
        ignored |= {"k", "darlt_blocks", "native_blocks", "selected_blocks", "token_count"}
    return {key: value for key, value in workload.items() if key not in ignored}


def unique_member(anchor, selected, stages):
    identity = workload_identity(anchor)
    matches = [
        row for row in selected
        if row["scheme"] == anchor["scheme"] and row["stage"] in stages
        and row["k"] == anchor["k"] and workload_identity(row) == identity
    ]
    if len(matches) != 1:
        raise ValueError(
            f"Expected one matching role for {anchor['job_id']}, stages={stages}; "
            f"found {[r['job_id'] for r in matches]}"
        )
    return matches[0]


def paired_total(members, samples_by_job_attempt):
    mean = math.fsum(float(row["mean_ms"]) for row in members)
    attempts = {row["source_attempt"] for row in members}
    maps = [samples_by_job_attempt[row["job_id"], row["source_attempt"]] for row in members]
    if len(attempts) == 1 and maps:
        keys = set(maps[0])
        paired = all(
            set(values) == keys and len(values) == int(row["n"])
            for row, values in zip(members, maps)
        )
        if paired and len(keys) > 1:
            values = [math.fsum(sample[key] for sample in maps) / 1e6 for key in keys]
            if not math.isclose(sample_statistics.mean(values), mean, rel_tol=1e-10, abs_tol=1e-9):
                raise ValueError("Paired sample mean differs from selected component means")
            return mean, sample_statistics.stdev(values), len(values), "sample_sd_of_physically_paired_sums"
    return mean, "", "", "only_sum_of_selected_means; no_paired_total_SD"


def add_table_iv_totals(selected, samples_path):
    anchors = [
        row for row in selected
        if (row["stage"] == "issue_response" and "Table IV: Issue by role" in json.loads(row["publications_json"]))
        or (row["stage"] == "delegate_send" and "Table IV: Delegate by role" in json.loads(row["publications_json"]))
    ]
    groups = []
    for anchor in anchors:
        if anchor["stage"] == "issue_response":
            members = [unique_member(anchor, selected, {"issue_request"}), anchor,
                       unique_member(anchor, selected, {"issue_accept", "issue_receive"})]
            kind = "Issue"
            boundary = "issue_request + issuer_response + user_receive; Setup/keygen/install excluded"
        else:
            members = [anchor, unique_member(anchor, selected, {"delegate_receive"})]
            kind = "Delegate"
            boundary = "user_delegate_send + agent_delegate_receive; agent_request excluded"
        groups.append((anchor, members, kind, boundary))
    needed = {(row["job_id"], row["source_attempt"]) for _, group, _, _ in groups for row in group}
    samples = defaultdict(dict)
    for row in read_csv(samples_path)[1]:
        key = row["job_id"], row["attempt"]
        if row["phase"] == "retained" and key in needed:
            physical_key = row["physical_call"], row["trial"]
            if physical_key in samples[key]:
                raise ValueError(f"Duplicate paired sample: {key}")
            samples[key][physical_key] = int(row["elapsed_ns"])
    totals = []
    for anchor, members, kind, boundary in groups:
        mean, sd, n, uncertainty = paired_total(members, samples)
        values = {
            "table_iv_total_kind": kind,
            "table_iv_total_mean_ms": mean,
            "table_iv_total_sample_sd_ms": sd,
            "table_iv_total_n": n,
            "table_iv_total_uncertainty_basis": uncertainty,
            "table_iv_total_boundary": boundary,
            "table_iv_total_member_jobs_json": json.dumps([r["job_id"] for r in members], ensure_ascii=False),
            "table_iv_total_member_attempts_json": json.dumps([int(r["source_attempt"]) for r in members]),
            "table_iv_total_member_cohort_statuses_json": json.dumps([r["cohort_status"] for r in members]),
        }
        anchor.update(values)
        totals.append({"scheme": anchor["scheme"], "kind": kind, "cache": anchor["cache"],
                       "representative_job_id": anchor["job_id"], "workload_json": anchor["workload_json"],
                       "campaign_status": anchor["campaign_status"], "paper_policy": PAPER_POLICY, **values})
    return totals


def add_verification_unit_increments(selected):
    stages = {"inclusive_verification", "merchant_verify", "bank_verify"}
    targets = [row for row in selected if row["k"] == "64" and row["stage"] in stages]
    increments = []
    for target in targets:
        matches = [
            row for row in selected if row["k"] == "16" and row["scheme"] == target["scheme"]
            and row["stage"] == target["stage"] and row["cache"] == target["cache"]
            and row["profile"] == target["profile"]
            and workload_identity(row, scan_k=True) == workload_identity(target, scan_k=True)
        ]
        if len(matches) != 1:
            raise ValueError(f"Missing/ambiguous k16 increment base: {target['job_id']}")
        base = matches[0]
        increment = (float(target["mean_ms"]) - float(base["mean_ms"])) / 48
        values = {
            "verification_unit_increment_ms": increment,
            "verification_unit_increment_base_k": 16,
            "verification_unit_increment_target_k": 64,
            "verification_unit_increment_denominator": 48,
            "verification_unit_increment_base_job_id": base["job_id"],
            "verification_unit_increment_base_attempt": base["source_attempt"],
            "verification_unit_increment_target_job_id": target["job_id"],
            "verification_unit_increment_target_attempt": target["source_attempt"],
            "verification_unit_increment_boundary_json": json.dumps(
                {"k16": json.loads(base["boundary_json"]), "k64": json.loads(target["boundary_json"])},
                ensure_ascii=False, sort_keys=True),
            "verification_unit_increment_basis": "(selected_mean_ms_k64-selected_mean_ms_k16)/48; finite_difference_not_single_unit_timing",
        }
        target.update(values)
        display = "DARLT ablation" if json.loads(target["workload_json"]).get("ablation") else target["scheme"]
        increments.append({"scheme": target["scheme"], "display_scheme": display,
                           "cache": target["cache"], "stage": target["stage"], "profile": target["profile"],
                           "scope": "main_hot" if target["cache"] == "hot" else "additional_cold",
                           "base_n": base["n"], "target_n": target["n"],
                           "base_mean_ms": base["mean_ms"], "target_mean_ms": target["mean_ms"],
                           "base_cohort_status": base["cohort_status"], "target_cohort_status": target["cohort_status"],
                           "campaign_status": target["campaign_status"], "paper_policy": PAPER_POLICY, **values})
    return increments


def write_rows(path, rows):
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def export(data_dir: Path, output_dir: Path) -> dict[str, object]:
    data_dir = data_dir.resolve()
    output_dir = output_dir.resolve()
    if output_dir == data_dir or data_dir in output_dir.parents:
        raise ValueError("Paper-value output must be separate from the source dataset")
    sources = {
        "attempt_statistics": data_dir / "attempt_statistics.csv",
        "job_status": data_dir / "job_status.csv",
        "formal_summary": data_dir / "summary.json",
        "whole_samples": data_dir / "whole_samples.csv.gz",
    }
    hashes_before = {name: sha256(path) for name, path in sources.items()}
    fields, statistics = read_csv(sources["attempt_statistics"])
    _, statuses = read_csv(sources["job_status"])
    summary = json.loads(sources["formal_summary"].read_text(encoding="utf-8"))
    selected, audit = select_results(statistics, statuses)
    for row in selected:
        row.update({field: "" for field in TOTAL_FIELDS + INCREMENT_FIELDS})
    totals = add_table_iv_totals(selected, sources["whole_samples"])
    increments = add_verification_unit_increments(selected)
    audit["table_iv_total_cells"] = len(totals)
    audit["table_iv_total_uncertainty_counts"] = dict(Counter(r["table_iv_total_uncertainty_basis"] for r in totals))
    audit["verification_unit_increment_rows"] = len(increments)
    audit["verification_unit_increment_scopes"] = dict(Counter(r["scope"] for r in increments))
    if len(selected) != summary["executed_native_jobs"]:
        raise ValueError("Selected task count differs from formal summary")
    if audit["cohorts"] != summary["cohorts"]:
        raise ValueError("Cohort count differs from formal summary")
    if audit["stable_cohorts"] != summary["stable_cohorts"]:
        raise ValueError("Stable-cohort count differs from formal summary")
    hashes_after = {name: sha256(path) for name, path in sources.items()}
    if hashes_before != hashes_after:
        raise ValueError("Source files changed during export")
    output_dir.mkdir(parents=True, exist_ok=True)
    csv_path = output_dir / "paper_values.csv"
    added_fields = [
        "source_attempt", "cohort_status", "paper_policy", "paper_selection_rule"
    ]
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields + added_fields + TOTAL_FIELDS + INCREMENT_FIELDS)
        writer.writeheader()
        writer.writerows(selected)
    audit["source_campaign_status"] = summary["status"]
    audit["source_files"] = {
        name: {"path": str(path.relative_to(data_dir)), "sha256": hashes_before[name]}
        for name, path in sources.items()
    }
    audit["source_files_unchanged"] = True
    audit["paper_values_csv"] = {
        "path": csv_path.name, "sha256": sha256(csv_path), "rows": len(selected)
    }
    for filename, result in [("table_iv_totals.csv", totals), ("verification_unit_increment.csv", increments)]:
        path = output_dir / filename
        write_rows(path, result)
        audit[filename] = {"path": filename, "sha256": sha256(path), "rows": len(result)}
    (output_dir / "paper_selection_audit.json").write_text(
        json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return audit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=Path("data/microbench"))
    parser.add_argument(
        "--out", type=Path, default=Path("outputs/paper-values")
    )
    args = parser.parse_args()
    audit = export(args.data, args.out)
    print(json.dumps({k: v for k, v in audit.items() if k != "cohort_selection"}, indent=2))


if __name__ == "__main__":
    main()
