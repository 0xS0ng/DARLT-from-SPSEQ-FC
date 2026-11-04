"""Shared typography and colours for paper panels."""
from __future__ import annotations

import math

import matplotlib as mpl
from matplotlib.font_manager import FontProperties, findfont
from matplotlib.ticker import FixedLocator, FuncFormatter, NullFormatter

PANEL_WIDTH = 1.7
PANEL_HEIGHT = 1.3
MARGINS = {"left": .32, "right": .03, "top": .10, "bottom": .42}
DPI = 600
ROLE_COLORS = {
    "User": "#3F7F93", "Issuer": "#537D59",
    "Agent (offline)": "#E3B5BC", "Agent (online)": "#5C0F1E",
    "Verifier": "#C0603A", "System": "#7B6E50",
}
SCHEME_STYLES = {
    "DARLT": ("#8E1B32", "o", "-"),
    "DARLT ($k$ tokens)": ("#C7798C", "^", "--"),
    "SMA²RT": ("#2A9D8F", "s", "-"),
    "BHN+26": ("#E08E2B", "^", ":"),
    "KLO26": ("#74787E", "D", "--"),
    "TJH+26": ("#AF7298", "v", "-."),
    "MSB+23": ("#1F4E79", "^", "-"),
    "SLW+25": ("#7B5EA7", "D", "-"),
}
STAGE_STYLES = {
    "BatchSpend (offline)": (ROLE_COLORS["Agent (offline)"], "o", "-"),
    "BatchSpend (online)": (SCHEME_STYLES["DARLT"][0], "s", "--"),
    "BatchVerify": (ROLE_COLORS["Verifier"], "^", "-."),
}
ALGORITHM_COLORS = {
    "Setup": "#8E1B32", "IKeyGen": "#8E1B32", "Issue": "#8E1B32",
    "Delegate": "#8E1B32", "Spend (offline)": "#E3B5BC",
    "Spend (online)": "#8E1B32", "BatchSpend (offline)": "#E3B5BC",
    "BatchSpend (online)": "#8E1B32", "Verify": "#8E1B32",
    "BatchVerify": "#8E1B32", "Identify": "#8E1B32", "RecoverMetadata": "#8E1B32",
}


def apply_style():
    for style, weight in [("normal", "normal"), ("italic", "normal"), ("normal", "bold")]:
        findfont(FontProperties(family="Arial", style=style, weight=weight), fallback_to_default=False)
    mpl.rcParams.update({
        "font.family": "sans-serif", "font.sans-serif": ["Arial"],
        "mathtext.fontset": "custom", "mathtext.rm": "Arial", "mathtext.it": "Arial:italic",
        "mathtext.cal": "Arial:italic", "mathtext.bf": "Arial:bold", "mathtext.bfit": "Arial:italic",
        "mathtext.sf": "Arial", "mathtext.fallback": None,
        "font.size": 6, "axes.labelsize": 6.5, "axes.titlesize": 6.5,
        "xtick.labelsize": 5, "ytick.labelsize": 5, "legend.fontsize": 5.5,
        "axes.linewidth": .6, "lines.linewidth": .75,
        "lines.markersize": 2.5, "lines.markeredgewidth": .4,
        "xtick.direction": "in", "ytick.direction": "in",
        "xtick.top": True, "ytick.right": True,
        "xtick.major.size": 2.2, "ytick.major.size": 2.2,
        "xtick.minor.size": 1.1, "ytick.minor.size": 1.1,
        "xtick.major.width": .45, "ytick.major.width": .45,
        "xtick.minor.width": .35, "ytick.minor.width": .35,
        "xtick.major.pad": 1, "ytick.major.pad": 1,
        "axes.axisbelow": True, "grid.color": "#B0B0B0",
        "grid.linestyle": ":", "grid.linewidth": .3, "grid.alpha": .8,
        "pdf.fonttype": 42, "ps.fonttype": 42, "svg.fonttype": "none",
        "savefig.dpi": DPI, "figure.dpi": 150,
        "savefig.bbox": None, "figure.autolayout": False,
        "figure.constrained_layout.use": False,
        "axes.unicode_minus": False,
    })


def plain_number(value, _position=None):
    if value >= 1000:
        return f"{value / 1000:g}k"
    return f"{value:g}"


def log_y(ax, low, high):
    ax.set_yscale("log")
    ax.set_ylim(low, high)
    decades = [10.0 ** power for power in range(math.ceil(math.log10(low)),
                                               math.floor(math.log10(high)) + 1)]
    ax.yaxis.set_major_locator(FixedLocator(decades))
    # Compose both power-label glyphs at 5 pt.
    ax.yaxis.set_major_formatter(NullFormatter())
    ax.yaxis.set_minor_formatter(NullFormatter())


def power_tick_labels(ax):
    for value in ax.get_yticks():
        if not ax.get_ylim()[0] <= value <= ax.get_ylim()[1]:
            continue
        for text, offset, alignment in [("10", (-7.8, -1.75), "right"),
                                         (str(int(round(math.log10(value)))), (-7.4, 1.05), "left")]:
            item = ax.annotate(text, (0, value), xycoords=ax.get_yaxis_transform(),
                               xytext=offset, textcoords="offset points", fontsize=5,
                               ha=alignment, va="baseline", annotation_clip=False)
            item.set_gid("log_tick")


def log_x(ax, maximum):
    ax.set_xscale("log", base=2)
    # Label powers of two; preserve the point at 96.
    ax.set_xticks([2 ** i for i in range(int(math.log2(maximum)) + 1)])
    ax.xaxis.set_major_formatter(FuncFormatter(plain_number))
    ax.xaxis.set_minor_locator(FixedLocator([]))
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(2 ** -.38, maximum * 2 ** .38)


def frame(ax):
    ax.set_axisbelow(True)
    ax.grid(True, which="major")
    for spine in ax.spines.values():
        spine.set_visible(True)
        spine.set_linewidth(.6)
        spine.set_zorder(10)


def legend(ax, **kwargs):
    options = dict(fontsize=5.5, frameon=True, fancybox=False, framealpha=1,
                   edgecolor="#555555", borderpad=.08, labelspacing=.06,
                   handlelength=.60, handletextpad=.20, columnspacing=.20,
                   borderaxespad=.25)
    options.update(kwargs)
    result = ax.legend(**options)
    result.get_frame().set_linewidth(.35)
    return result
