#!/usr/bin/env python3
"""Plot algorithm costs and parameter scans from saved paper statistics."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from collections import defaultdict
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.font_manager import FontProperties
from matplotlib.patches import Patch
from matplotlib.textpath import TextPath
from matplotlib.transforms import ScaledTranslation
import numpy as np
from PIL import Image

from paper_style import (ALGORITHM_COLORS, DPI, MARGINS, PANEL_HEIGHT, PANEL_WIDTH, ROLE_COLORS, SCHEME_STYLES,
                         STAGE_STYLES, apply_style, frame, legend, log_x, log_y, power_tick_labels)

ROOT = Path(__file__).resolve().parents[1]
KS = [1, 2, 4, 8, 16, 32, 64, 96, 128]
ATTRIBUTES = [10, 20, 30]
POWERS = [1, 2, 4, 8, 16, 32, 64]
EXPECTED = dict(zip([f"fig{n}{s}" for n in range(7, 12) for s in "ab"],
                    [12, 6, 9, 9, 21, 14, 27, 45, 12, 12]))
BAR_PANELS = {"fig7a", "fig7b", "fig8a", "fig8b", "fig11a", "fig11b"}


def three_significant(value):
    decimals = max(0, 2 - math.floor(math.log10(abs(value))))
    return f"{value:.{decimals}f}"


def read_csv(path):
    with path.open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def write_csv(path, rows):
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class PaperData:
    def __init__(self, directory):
        self.directory = directory
        path = directory / "paper_values.csv"
        records = read_csv(path)
        self.jobs = {r["job_id"]: r for r in records}
        if len(self.jobs) != 332 or len(records) != 332:
            raise ValueError("Expected the 332 distinct paper-selected jobs")
        for row in records:
            if row["source_attempt"] != row["attempt"]:
                raise ValueError("Mismatched paper source attempt")
            if row["cohort_status"] == "unresolved" and row["attempt"] != "1":
                raise ValueError("Unresolved groups must retain attempt 1")
        self.sources = {"paper_values.csv": digest(path)}
        self.byte_rows = {}
        for panel in ("fig7b", "fig10b"):
            source = directory / "inputs" / f"{panel}.csv"
            self.sources[f"inputs/{panel}.csv"] = digest(source)
            self.byte_rows[panel] = read_csv(source)
        self.panels = defaultdict(list)

    def time(self, panel, series, x, jobs, **extra):
        if isinstance(jobs, str):
            jobs = [jobs]
        components = [self.jobs[j] for j in jobs]
        row = {
            "panel": panel, "series": series, "x": x,
            "mean_ms": sum(float(r["mean_ms"]) for r in components),
            "sample_sd_ms": float(components[0]["sample_sd_ms"]) if len(jobs) == 1 else "",
            "unit": "ms", "source_job_ids_json": json.dumps(jobs),
            "source_attempts_json": json.dumps([int(r["attempt"]) for r in components]),
            "source_cohort_statuses_json": json.dumps([r["cohort_status"] for r in components]),
            "source_ns_json": json.dumps([int(r["n"]) for r in components]),
            "component_means_ms_json": json.dumps([float(r["mean_ms"]) for r in components]),
            "component_sample_sds_ms_json": json.dumps([float(r["sample_sd_ms"]) for r in components]),
            "uncertainty_basis": "recorded sample SD" if len(jobs) == 1 else "component SDs retained; paired two-component SD unavailable",
            "paper_policy": components[0]["paper_policy"],
            **extra,
        }
        self.panels[panel].append(row)
        return row

    def byte(self, panel, series, x, source, column, **extra):
        row = {**source, "panel": panel, "series": series, "x": x,
               "plot_value": int(source[column]) / 1024,
               "unit": "KB", "bytes_per_KB": 1024, **extra}
        self.panels[panel].append(row)

    def paired_total(self, panel, name, jobs):
        row = self.time(panel, name, name, jobs)
        matches = [r for r in self.jobs.values() if r.get("table_iv_total_kind") == name
                   and json.loads(r["table_iv_total_member_jobs_json"]) == jobs]
        if len(matches) != 1:
            raise ValueError(f"Missing checked paired total for {name}")
        source = matches[0]
        if source["table_iv_total_uncertainty_basis"] != "sample_sd_of_physically_paired_sums":
            raise ValueError("Expected physically paired total SD")
        if abs(row["mean_ms"] - float(source["table_iv_total_mean_ms"])) > 1e-9:
            raise ValueError("Paired mean differs from selected component means")
        if json.loads(row["source_attempts_json"]) != json.loads(source["table_iv_total_member_attempts_json"]):
            raise ValueError("Paired total uses a different attempt")
        row.update(mean_ms=float(source["table_iv_total_mean_ms"]),
                   sample_sd_ms=float(source["table_iv_total_sample_sd_ms"]),
                   uncertainty_basis=source["table_iv_total_uncertainty_basis"],
                   paired_total_source_job_id=source["job_id"], paired_total_n=int(source["table_iv_total_n"]))
        return row


def prepare(data):
    specs = [
        ("Setup", "darlt/setup"),
        ("IKeyGen", "darlt/keygen"),
        ("Issue", ["darlt/issue/request", "darlt/issue/issuer", "darlt/issue/accept"]),
        ("Delegate", ["darlt/delegate/send/hot/g1", "darlt/delegate/receive/g1"]),
        ("Spend (offline)", "darlt/prepare/k1"),
        ("Spend (online)", "darlt/online/k1"),
        ("BatchSpend (offline)", "darlt/prepare/k16"),
        ("BatchSpend (online)", "darlt/online/k16"),
        ("Verify", "darlt/inclusive/RandomizedAcrossBlocks/native/k1"),
        ("BatchVerify", "darlt/inclusive/RandomizedAcrossBlocks/native/k16"),
        ("Identify", "darlt/judge/randomized"),
        ("RecoverMetadata", "darlt/metadata/validated/bit1"),
    ]
    for algorithm, jobs in specs:
        if isinstance(jobs, list):
            row = data.paired_total("fig7a", algorithm, jobs)
        else:
            row = data.time("fig7a", algorithm, algorithm, jobs)
        row["color_key"] = algorithm
    by_algorithm = {r["algorithm"]: r for r in data.byte_rows["fig7b"]}
    for category, original, sender in [
        ("Issue req.", "IssueRequest", "User"),
        ("Issue resp.", "IssueResponse", "Issuer"),
        ("Delegate req.", "DelegateRequest", "Agent (offline)"),
        ("Delegate resp.", "Delivery", "User"),
        ("Spend", "Token(k=1)", "Agent (online)"),
        ("BatchSpend", "Token(k=16)", "Agent (online)"),
    ]:
        color_key = ("Issue" if category.startswith("Issue") else "Delegate" if category.startswith("Delegate")
                     else "Spend (online)" if category == "Spend" else "BatchSpend (online)")
        data.byte("fig7b", color_key, category, by_algorithm[original], "bytes", sender=sender, color_key=color_key)
    for attrs in ATTRIBUTES:
        for stage, suffix in zip(STAGE_STYLES, ["prepare", "online", "valid-randomized/inclusive"]):
            data.time("fig8a", stage, attrs, f"darlt/scan/attributes/{attrs}/{suffix}")
    for bits in (8, 16, 32):
        for stage, suffix in zip(STAGE_STYLES, ["prepare", "online", "valid-randomized/inclusive"]):
            data.time("fig8b", stage, bits, f"darlt/scan/range/{bits}/{suffix}")
    for gamma in POWERS:
        for series, job in [
            ("Delegate", f"darlt/delegate/send/hot/g{gamma}"),
            ("Delegate + openings", f"darlt/delegate/send/cold/g{gamma}"),
            ("Receive", f"darlt/delegate/receive/g{gamma}"),
        ]:
            data.time("fig9a", series, gamma, job)
    for agents in POWERS:
        data.time("fig9b", "DARLT", agents, f"darlt/provision/issuer/{agents}", ledger="issuer")
        data.time("fig9b", "SMA²RT", agents, f"baseline/sma2rt/a10/equal-budget/A{agents}/provisioning_issuer", ledger="issuer")
    for k in KS:
        data.time("fig10a", "DARLT", k, f"darlt/inclusive/RandomizedAcrossBlocks/native/k{k}")
        data.time("fig10a", "DARLT ($k$ tokens)", k, f"darlt/inclusive/RandomizedAcrossBlocks/ablation/k{k}")
        data.time("fig10a", "SMA²RT", k, f"baseline/SMA²RT/a10/verifier/inclusive_verification/k{k}/safe_random_complete_batch")
    shown = ["DARLT", "SMA²RT", "BHN+26", "KLO26", "TJH+26"]
    for scheme in shown:
        rows = sorted([r for r in data.byte_rows["fig10b"] if r["display_scheme"] == scheme], key=lambda r: int(r["k"]))
        if [int(r["k"]) for r in rows] != KS:
            raise ValueError(f"Incomplete byte scan: {scheme}")
        for row in rows:
            data.byte("fig10b", scheme, int(row["k"]), row, "total_spend_bytes")
    for attrs in (10, 20, 30):
        data.time("fig11a", "DARLT", attrs, f"darlt/scan/attributes/{attrs}/online")
        data.time("fig11b", "DARLT", attrs, f"darlt/scan/attributes/{attrs}/valid-randomized/inclusive")
        for scheme, role, profile in [("SMA²RT", "user", "safe_random_complete_batch"),
                                      ("MSB+23", "agent", "Randomized"), ("SLW+25", "agent", "Randomized")]:
            data.time("fig11a", scheme, attrs, f"baseline/{scheme}/a{attrs}/{role}/online_generation/k16/native")
            data.time("fig11b", scheme, attrs, f"baseline/{scheme}/a{attrs}/verifier/inclusive_verification/k16/{profile}")
    if {panel: len(rows) for panel, rows in data.panels.items()} != EXPECTED:
        raise ValueError("Panel observation counts differ from the task")
    for rows in data.panels.values():
        if any(float(r.get("mean_ms", r.get("plot_value"))) <= 0 for r in rows):
            raise ValueError("All plotted observations must be positive")
    for panel in BAR_PANELS:
        for row in data.panels[panel]:
            row["bar_label"] = three_significant(row.get("mean_ms", row.get("plot_value")))


def grouped_lines(ax, rows, styles, labels=None):
    for series, (color, marker, linestyle) in styles.items():
        points = sorted([r for r in rows if r["series"] == series], key=lambda r: float(r["x"]))
        if points:
            ax.plot([r["x"] for r in points], [r.get("mean_ms", r.get("plot_value")) for r in points],
                    color=color, marker=marker, linestyle=linestyle,
                    label=(labels or {}).get(series, series), zorder=3)


def label_bars(ax, patches, values):
    font = FontProperties(family="Arial", size=4.5, weight="bold")
    for patch, value in zip(patches, values):
        label = three_significant(value)
        bounds = TextPath((0, 0), label, prop=font).get_extents()
        # Align visible glyph bounds.
        text = ax.annotate(label,
                           (patch.get_x() + patch.get_width() / 2, value),
                           xytext=((bounds.y0 + bounds.y1) / 2, 1 - bounds.x0),
                           textcoords="offset points", ha="left", va="baseline", rotation=90,
                           rotation_mode="anchor", fontproperties=font,
                           annotation_clip=False, zorder=5)
        text.set_gid("bar_value")
        text._host_bar = patch
        text._placement = "above"


def grouped_bars(ax, rows, series, colors, categories):
    gap = .08 if len(categories) >= 6 else .02
    width = (.70 - (len(series) - 1) * gap) / len(series)
    for i, name in enumerate(series):
        chosen = {r["x"]: r for r in rows if r["series"] == name}
        values = [chosen[x]["mean_ms"] for x in categories]
        patches = ax.bar([j + (i - (len(series) - 1) / 2) * (width + gap) for j in range(len(categories))],
                        values, width=width, color=colors[name], label=name,
                        edgecolor="black", linewidth=.4, zorder=3)
        label_bars(ax, patches, values)
    ax.set_xticks(range(len(categories)), [str(x) for x in categories])
    ax.set_xlim(-.55, len(categories) - .45)


def panel_figure(panel):
    fig = plt.figure(figsize=(PANEL_WIDTH, PANEL_HEIGHT))
    ax = fig.add_axes([MARGINS["left"] / PANEL_WIDTH, MARGINS["bottom"] / PANEL_HEIGHT,
                       (PANEL_WIDTH - MARGINS["left"] - MARGINS["right"]) / PANEL_WIDTH,
                       (PANEL_HEIGHT - MARGINS["bottom"] - MARGINS["top"]) / PANEL_HEIGHT])
    frame(ax)
    return fig, ax


def draw_panel(panel, rows):
    fig, ax = panel_figure(panel)
    if panel == "fig7a":
        log_y(ax, .1, 10000)
        categories = ["Setup", "IKeyGen", "Issue", "Delegate", "Spend", "BatchSpend",
                      "Verify", "BatchVerify", "Identify", "RecoverMetadata"]
        ax.set_xlim(-.5, 9.5)
        positions = [0, 1, 2, 3, 3.82, 4.18, 4.82, 5.18, 6, 7, 8, 9]
        widths = [.30 if 4 <= i <= 7 else 5 / 9.72 for i in range(12)]
        patches = ax.bar(positions, [r["mean_ms"] - .1 for r in rows], bottom=.1, width=widths,
                         color=[ALGORITHM_COLORS[r["color_key"]] for r in rows], edgecolor="black", linewidth=.4, zorder=3)
        label_bars(ax, patches, [r["mean_ms"] for r in rows])
        ax.set_xticks(range(10), categories, rotation=30, rotation_mode="anchor", ha="right", va="baseline")
        for label in ax.get_xticklabels():
            label.set_transform(ax.get_xaxis_text1_transform(1)[0] +
                                ScaledTranslation(0, -4 / 72, fig.dpi_scale_trans))
        legend(ax, handles=[Patch(facecolor=ALGORITHM_COLORS["Spend (offline)"], edgecolor="black", linewidth=.4, label="Offline")],
               loc="upper right")
        ax.set_ylabel("Execution Time (ms)", labelpad=1)
    elif panel == "fig7b":
        ax.set_xlim(-.5, 5.5)
        ax.set_ylim(0, 12)
        ax.set_yticks([0, 4, 8, 12])
        patches = ax.bar(range(6), [r["plot_value"] for r in rows], width=.7,
                         color=[ALGORITHM_COLORS[r["color_key"]] for r in rows], edgecolor="black", linewidth=.4, zorder=3)
        label_bars(ax, patches, [r["plot_value"] for r in rows])
        ax.set_xticks(range(6), [r["x"] for r in rows], rotation=30, rotation_mode="anchor", ha="right", va="top")
        ax.set_ylabel("Output Size (KB)", labelpad=1)
    elif panel in ("fig8a", "fig8b"):
        ax.set_ylabel("Execution Time (ms)", labelpad=1)
        if panel == "fig8a":
            ax.set_ylim(0, 240)
            ax.set_yticks([0, 50, 100, 150, 200])
            grouped_bars(ax, rows, list(STAGE_STYLES), {s: st[0] for s, st in STAGE_STYLES.items()}, ATTRIBUTES)
            ax.set_xlabel(r"$|\mathcal{S}|$: number of attributes", labelpad=1)
            legend(ax, loc="upper left", ncol=2)
        else:
            ax.set_ylim(0, 300)
            ax.set_yticks([0, 100, 200, 300])
            grouped_bars(ax, rows, list(STAGE_STYLES), {s: st[0] for s, st in STAGE_STYLES.items()}, [8, 16, 32])
            ax.set_xlabel(r"$\mathrm{Range\ width\ (bits)}$", labelpad=1)
            legend(ax, loc="upper left", ncol=2)
    elif panel == "fig9a":
        styles = {"Delegate": (ROLE_COLORS["User"], "o", "-"),
                  "Delegate + openings": (ROLE_COLORS["User"], "^", "--"),
                  "Receive": ("#77833A", "s", "-.")}
        grouped_lines(ax, rows, styles)
        log_x(ax, 64)
        log_y(ax, 1, 2000)
        ax.set_xlabel(r"$|\mathbfit{\Gamma}|$: number of delegated pools", labelpad=1)
        ax.set_ylabel("Execution Time (ms)", labelpad=1)
        legend(ax, loc="upper left")
    elif panel == "fig9b":
        grouped_lines(ax, rows, SCHEME_STYLES)
        log_x(ax, 64)
        log_y(ax, 1, 300)
        ax.set_xlabel(r"$A$: number of agents", labelpad=1)
        ax.set_ylabel("Issuer Time (ms)", labelpad=1)
        legend(ax, loc="upper left")
    elif panel in ("fig10a", "fig10b"):
        grouped_lines(ax, rows, SCHEME_STYLES)
        log_x(ax, 128)
        log_y(ax, 1 if panel == "fig10a" else .1, 10000 if panel == "fig10a" else 1500)
        ax.set_xlabel(r"$k$: number of units", labelpad=1)
        ax.set_ylabel("Verification Time (ms)" if panel == "fig10a" else "Token Size (KB)", labelpad=1)
        legend(ax, loc="upper left", ncol=1 if panel == "fig10a" else 2)
    else:
        schemes = ["DARLT", "SMA²RT", "MSB+23", "SLW+25"]
        ax.set_ylim(0, 75 if panel == "fig11a" else 220)
        ax.set_yticks([0, 20, 40, 60] if panel == "fig11a" else [0, 50, 100, 150, 200])
        grouped_bars(ax, rows, schemes, {s: SCHEME_STYLES[s][0] for s in schemes}, [10, 20, 30])
        ax.set_xlabel(r"$|\mathcal{S}|$: number of attributes", labelpad=1)
        ax.set_ylabel("Online Time (ms)" if panel == "fig11a" else "Verification Time (ms)", labelpad=1)
        legend(ax, loc="upper left", ncol=2)
    if ax.get_xlabel():
        ax.xaxis.labelpad = 2
        ax.xaxis.label.set_verticalalignment("top")
    ax.yaxis.set_label_coords((9 / 72 - MARGINS["left"]) / (PANEL_WIDTH - MARGINS["left"] - MARGINS["right"]), .5)
    if ax.get_yscale() == "log":
        power_tick_labels(ax)
    return fig, ax


def geometry_audit(fig, ax):
    # Check rotated glyph separation at 600 dpi.
    fig.set_dpi(DPI)
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    page, axes = fig.bbox, ax.bbox
    xticks = [t for t in ax.get_xticklabels() if t.get_visible() and t.get_text()]
    visible_text = [t for t in xticks + ax.get_yticklabels() + [ax.xaxis.label, ax.yaxis.label]
                    + ax.texts if t.get_visible() and t.get_text()]
    numbers = [t for t in ax.texts if t.get_gid() == "bar_value"]
    lg = ax.get_legend()
    if lg:
        visible_text += list(lg.get_texts())
    boxes = {t: t.get_window_extent(renderer).frozen() for t in visible_text}
    outside = [t.get_text() for t, b in boxes.items()
               if b.x0 < page.x0 - .5 or b.y0 < page.y0 - .5 or b.x1 > page.x1 + .5 or b.y1 > page.y1 + .5]
    bbox_pairs = [[i, j] for i, t in enumerate(xticks) for j, u in enumerate(xticks)
                  if j > i and boxes[t].overlaps(boxes[u])]
    collisions, number_legend = [], []
    inside = True
    if lg:
        box = lg.get_window_extent(renderer)
        inside = bool(axes.contains(box.x0, box.y0) and axes.contains(box.x1, box.y1))
        collisions += [f"bar:{i}" for i, patch in enumerate(ax.patches) if patch.get_window_extent(renderer).overlaps(box)]
        number_legend = [t.get_text() for t in numbers if boxes[t].overlaps(box)]
        padding = (2.5 / 2 + .4) * fig.dpi / 72
        padded = box.expanded(1 + 2 * padding / box.width, 1 + 2 * padding / box.height)
        for line in ax.lines:
            if line.get_transform().transform_path(line.get_path()).intersects_bbox(padded, filled=False):
                collisions.append(line.get_label())

    def ink(artist):
        renderer.clear()
        artist.draw(renderer)
        return np.asarray(renderer.buffer_rgba())[:, :, 3].copy() >= 64

    tick_inks = [ink(t) for t in xticks]
    tick_pairs = [[i, j] for i, a in enumerate(tick_inks) for j, b in enumerate(tick_inks)
                  if j > i and np.any(a & b)]
    num_inks = [ink(t) for t in numbers]
    number_pairs = [[numbers[i].get_text(), numbers[j].get_text()]
                    for i, a in enumerate(num_inks) for j, b in enumerate(num_inks)
                    if j > i and np.any(a & b)]
    bar_inks = [ink(p) for p in ax.patches]
    other_bars = [[numbers[i].get_text(), j] for i, a in enumerate(num_inks)
                  for j, b in enumerate(bar_inks)
                  if numbers[i]._host_bar is not ax.patches[j] and np.any(a & b)]
    own_bars = [numbers[i].get_text() for i, a in enumerate(num_inks)
                for j, b in enumerate(bar_inks)
                if numbers[i]._host_bar is ax.patches[j] and np.any(a & b)]
    frame_ink = np.zeros_like(tick_inks[0])
    for spine in ax.spines.values():
        frame_ink |= ink(spine)
    frame_hits = [numbers[i].get_text() for i, a in enumerate(num_inks) if np.any(a & frame_ink)]
    positions = [{"text": t.get_text(), "value": float(t.xy[1]), "mode": t._placement,
                  "rotation": t.get_rotation(), "font_pt": t.get_fontsize(), "weight": t.get_fontweight()}
                 for t in numbers]
    fig.canvas.draw()
    return {"size_inches": list(fig.get_size_inches()), "margins_inches": MARGINS,
            "axes_bounds_inches": [float(v) for v in [MARGINS["left"], MARGINS["bottom"],
             PANEL_WIDTH - MARGINS["left"] - MARGINS["right"], PANEL_HEIGHT - MARGINS["bottom"] - MARGINS["top"]]],
            "axes_scale": [ax.get_xscale(), ax.get_yscale()],
            "x_limits": list(ax.get_xlim()), "y_limits": list(ax.get_ylim()),
            "xlabel": ax.get_xlabel(), "ylabel": ax.get_ylabel(),
            "xlabel_tick_gap_pt": (min(boxes[t].y0 for t in xticks) - boxes[ax.xaxis.label].y1) * 72 / fig.dpi if ax.get_xlabel() else None,
            "axis_label_font_pt": 6.5, "tick_font_pt": 5, "legend_font_pt": 5.5, "bar_value_font_pt": 4.5,
            "outside_page_text": outside, "xtick_axis_aligned_bbox_pairs": bbox_pairs,
            "overlapping_xtick_pairs": tick_pairs, "legend_inside_axes": inside,
            "legend_data_intersections": collisions, "legend_number_intersections": number_legend,
            "number_number_ink_intersections": number_pairs, "number_other_bar_ink_intersections": other_bars,
            "number_host_bar_ink_intersections": own_bars,
            "number_frame_ink_intersections": frame_hits, "bar_labels": positions,
            "legend_entries": [t.get_text() for t in lg.get_texts()] if lg else [],
            "visible_text": [t.get_text() for t in visible_text]}


def montage(directory):
    names = list(EXPECTED)
    images = [Image.open(directory / f"{p}.png").convert("RGB") for p in names]
    cell_width = images[0].width
    row_heights = [max(image.height for image in images[start:start + 4]) for start in (0, 4, 8)]
    gap = round(.08 * DPI)
    canvas = Image.new("RGB", (cell_width * 4 + gap * 3, sum(row_heights) + gap * 2), "white")
    y = 0
    for start, height in zip((0, 4, 8), row_heights):
        for col, im in enumerate(images[start:start + 4]):
            canvas.paste(im, (col * (cell_width + gap), y))
        y += height + gap
    canvas.save(directory / "montage.png", dpi=(DPI, DPI))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=ROOT / "data/microbench")
    parser.add_argument("--out-dir", type=Path, default=ROOT / "outputs/figures")
    parser.add_argument("--publication-dir", type=Path)
    parser.add_argument("--figure", choices=["all", "7", "8", "9", "10", "11"], default="all")
    args = parser.parse_args()
    data_dir, out_dir = args.data_dir.resolve(), args.out_dir.resolve()
    publication = args.publication_dir.resolve() if args.publication_dir else out_dir / "source_data"
    for source in (data_dir, ROOT / "data/microbench"):
        if out_dir == source or source in out_dir.parents or publication == source or source in publication.parents:
            raise ValueError("Derived files must preserve saved measurements")
    data = PaperData(data_dir)
    prepare(data)
    apply_style()
    out_dir.mkdir(parents=True, exist_ok=True)
    publication.mkdir(parents=True, exist_ok=True)
    selected = [p for p in EXPECTED if args.figure == "all" or p[3:-1] == args.figure]
    audits = {}
    for panel in selected:
        rows = data.panels[panel]
        write_csv(publication / f"{panel}.csv", rows)
        fig, ax = draw_panel(panel, rows)
        audits[panel] = {"observations": len(rows), **geometry_audit(fig, ax)}
        fig.savefig(out_dir / f"{panel}.pdf")
        fig.savefig(out_dir / f"{panel}.png", dpi=DPI)
        plt.close(fig)
    if args.figure == "all":
        montage(out_dir)
    result = {"task": "Paper figures", "timing_or_protocol_calls": 0,
              "source_files_sha256": data.sources, "bytes_per_KB": 1024,
              "error_bars": False, "panel_titles": False, "panels": audits,
              "k96": "Retained at log2(96); unlabelled between power-of-two major ticks",
              "excluded": {"fig7a": "First-delegation openings and superseded ancillary operations are not plotted",
                           "fig8a": "Attributes 10,20,30; original observations remain unchanged",
                           "fig9b": "System and per-agent system ledgers are not plotted",
                           "fig10b": "MSB+23, SLW+25, RP23-C, RP23-D and LCB24 remain in Table III",
                           "fig11": "Attributes 10,20,30; attribute-independent BHN+26/KLO26/TJH+26 reference lines are not plotted"}}
    (out_dir / f"figure_audit_{args.figure}.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({p: {k: v for k, v in a.items() if k in ("observations", "outside_page_text", "overlapping_xtick_pairs", "legend_inside_axes", "legend_data_intersections")} for p, a in audits.items()}, ensure_ascii=False))


if __name__ == "__main__":
    main()
