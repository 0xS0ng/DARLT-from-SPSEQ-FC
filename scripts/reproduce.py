#!/usr/bin/env python3
"""Reproduce figures and tables from saved measurements."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

from export_paper_values import PAPER_POLICY, export


ROOT = Path(__file__).resolve().parents[1]


def read_csv(path):
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows):
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def paper_directory(root):
    for directory in [root / "data/microbench"]:
        if (directory / "paper_values.csv").exists():
            return directory
    raise FileNotFoundError("Paper-selected measurement CSV not found")


def reproduce(target, data, paper_data, output_root, case_data=None):
    data, paper_data = data.resolve(), paper_data.resolve()
    output = output_root.resolve() / target
    for source in [data, paper_data]:
        if source == output or source in output.parents:
            raise ValueError("Reproduced output is separate from saved source data")
    output.mkdir(parents=True, exist_ok=True)
    if target in ("figure12", "table5"):
        command = [sys.executable, str(ROOT / "scripts/export_case_study.py"), "--data", str(case_data or ROOT / "data/case_study"),
                   "--out", str(output)]
        if target == "table5":
            command.append("--tables-only")
        subprocess.run(command, cwd=ROOT, check=True)
    elif target == "paper-values":
        export(data, output)
    elif target == "table3":
        for name in ["table_iii.csv", "public_parameters.csv", "inventory_storage.csv"]:
            source = paper_data / name
            if not source.exists():
                source = data / name
            shutil.copyfile(source, output / ("table3.csv" if name == "table_iii.csv" else name))
    elif target == "table4":
        selected = read_csv(paper_data / "paper_values.csv")
        bindings = []
        for row in selected:
            sections = [section for section in json.loads(row["publications_json"])
                        if section.startswith("Table IV")]
            if sections:
                bindings.append({"table_section": "; ".join(sections), **row})
        write_csv(output / "table4.csv", bindings)
        for name in ["table_iv_totals.csv", "verification_unit_increment.csv"]:
            shutil.copyfile(paper_data / name, output / name)
    elif target.startswith("figure"):
        subprocess.run(
            [sys.executable, str(ROOT / "scripts/plot_figures.py"),
             "--data-dir", str(paper_data), "--out-dir", str(output),
             "--publication-dir", str(output), "--figure", target.removeprefix("figure")],
            check=True,
        )
    else:
        raise ValueError(target)
    files = [path for path in sorted(output.iterdir())
             if path.is_file() and path.name != "reproduction.json"]
    metadata = {
        "target": target,
        "paper_policy": PAPER_POLICY,
        "timing_or_protocol_calls": 0,
        "paper_values_sha256": hashlib.sha256((paper_data / "paper_values.csv").read_bytes()).hexdigest(),
        "files": [{"path": path.name, "bytes": path.stat().st_size,
                   "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in files],
    }
    (output / "reproduction.json").write_text(
        json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=["all", "paper-values", "table3", "table4", "table5"]
                        + [f"figure{n}" for n in range(7, 13)])
    parser.add_argument("--data", type=Path, default=ROOT / "data/microbench")
    parser.add_argument("--paper-data", type=Path)
    parser.add_argument("--out", type=Path, default=ROOT / "outputs")
    parser.add_argument("--case-data", type=Path, default=ROOT / "data/case_study")
    args = parser.parse_args()
    targets = (["paper-values", "table3", "table4"] + [f"figure{n}" for n in range(7, 13)] + ["table5"]
               if args.target == "all" else [args.target])
    for target in targets:
        print(reproduce(target, args.data, args.paper_data or paper_directory(ROOT), args.out, args.case_data))


if __name__ == "__main__":
    main()
