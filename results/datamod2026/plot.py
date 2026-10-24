"""Evaluation figure: differentiation time and speedup of the indexed search.
usage: python3 plot.py <eval-data dir> <output.pdf>   (reads results.json from analyze.py)"""
import json, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

D, out = sys.argv[1], sys.argv[2]
r = list(json.load(open(f"{D}/results.json")).values())

INDEXED, LEGACY = "#2a78d6", "#eb6834"          # categorical slots 1, 2 (validated)
INK, MUTED, GRID = "#0b0b0b", "#52514e", "#e4e3df"

plt.rcParams.update({
    "font.family": "Latin Modern Roman", "font.size": 8, "axes.titlesize": 8,
    "axes.labelsize": 8, "xtick.labelsize": 7, "ytick.labelsize": 7, "legend.fontsize": 7,
    "axes.edgecolor": MUTED, "axes.labelcolor": INK, "xtick.color": MUTED, "ytick.color": MUTED,
    "axes.spines.top": False, "axes.spines.right": False, "pdf.fonttype": 42,
})
fig, (a, b) = plt.subplots(1, 2, figsize=(4.8, 2.1), constrained_layout=True)
ms = lambda v, _: f"{v:g}"

# (a) time per differentiation, both modes
TIMEOUT_Y = 20000
a.scatter([v["size"] for v in r if v["legacy_ok"]], [v["t_legacy"] for v in r if v["legacy_ok"]],
          s=9, marker="^", facecolor=LEGACY, edgecolor="white", linewidth=0.3, label="without index")
a.scatter([v["size"] for v in r], [v["t_indexed"] for v in r],
          s=9, marker="o", facecolor=INDEXED, edgecolor="white", linewidth=0.3, label="with index")
fails = [v["size"] for v in r if not v["legacy_ok"]]
a.scatter(fails, [TIMEOUT_Y] * len(fails), s=12, marker="x", color=LEGACY, linewidth=0.8,
          label="without index: timeout")
a.set_yscale("log"); a.set_ylim(8, 40000)
a.yaxis.set_major_formatter(FuncFormatter(ms))
a.set_xlabel("function size (expression tree nodes)"); a.set_ylabel("time (ms)")
a.set_title("(a) time per differentiation", loc="left", color=INK)
a.grid(True, which="major", axis="y", color=GRID, linewidth=0.5); a.set_axisbelow(True)
a.legend(frameon=False, loc="lower right", handletextpad=0.2, borderaxespad=0.1)

# (b) per-function speedup (legacy / indexed), marker shape = computed domain
both = [v for v in r if v["legacy_ok"]]
for univ, mk, face, lbl in [(False, "o", INK, "restricted domain"), (True, "o", "none", "universal domain")]:
    sel = [v for v in both if v["universal"] == univ]
    b.scatter([v["size"] for v in sel], [v["t_legacy"] / v["t_indexed"] for v in sel], s=9, marker=mk,
              facecolor=face, edgecolor=INK, linewidth=0.5, label=lbl)
b.axhline(1, color=MUTED, linewidth=0.6, linestyle="--")
b.set_yscale("log"); b.set_ylim(0.8, 100)
b.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:g}×"))
b.set_xlabel("function size (expression tree nodes)"); b.set_ylabel("speedup")
b.set_title("(b) speedup due to indexing", loc="left", color=INK)
b.grid(True, which="major", axis="y", color=GRID, linewidth=0.5); b.set_axisbelow(True)
b.legend(frameon=False, loc="upper right", handletextpad=0.2, borderaxespad=0.1)

fig.savefig(out)
fig.savefig(out.rsplit(".", 1)[0] + ".png", dpi=200)
