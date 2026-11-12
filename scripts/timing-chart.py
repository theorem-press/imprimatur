#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The chart of imprimatur's run time (docs/ci-timing.md, part 3).

    timing-chart.py LOG OUT_DIR

reads the append-only log `timing-fold.py` keeps (one JSON line per paper
per run) and writes OUT_DIR/chart.svg and OUT_DIR/chart.png: above, each
paper's `imprimatur build` total in seconds against the night; below, the
largest paper's phases stacked, since a regression lands in one of them.
Only nightly points (`event` schedule or workflow_dispatch) are drawn.
Needs matplotlib.
"""
import collections
import datetime
import json
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

PHASES = ["scan", "load", "entries", "write", "apply", "check"]
# `export` is the wait for the extractor and, alongside it, the verified
# checker: the extractor's phases are stacked, what is left of `export` after
# them is `export (other)`, and the checker, which runs in parallel, is a
# line of its own rather than a layer.


def main(log_path, out_dir):
    # One point a night per paper: the last, when a day has several.
    by_day = collections.defaultdict(dict)
    for line in pathlib.Path(log_path).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        l = json.loads(line)
        if l.get("event") in ("schedule", "workflow_dispatch") and "ms" in l:
            by_day[l["paper"]][l["date"]] = l
    # (`checker` was the semantics example again, with the checker on, in the
    # first nights' lines; the fold no longer writes it.)
    points = {paper: [days[d] for d in sorted(days)] for paper, days in by_day.items() if paper != "checker"}
    if not points:
        print("timing-chart: no nightly points yet", file=sys.stderr)
        return 0
    out = pathlib.Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)

    fig, (top, bottom) = plt.subplots(2, 1, figsize=(9, 7), height_ratios=[3, 2])
    ymax = max(l["ms"]["total"] for ls in points.values() for l in ls) / 1000
    # The legend carries each paper's last value, so that the papers whose
    # lines hug the axis are read there; a line gets labels on its points only
    # when it is high enough for them to be read, and the last point's label
    # names the commit. Labels of the last points are staggered so that they
    # do not pile up when several papers end near one value.
    rank = 0
    for paper, ls in sorted(points.items(), key=lambda kv: -kv[1][-1]["ms"]["total"]):
        xs = [datetime.date.fromisoformat(l["date"]) for l in ls]
        ys = [l["ms"]["total"] / 1000 for l in ls]
        top.plot(xs, ys, marker="o", markersize=3, linewidth=1,
                 label=f"{paper} ({ls[-1].get('entries', '?')} entries): last {ys[-1]:.1f} s")
        if max(ys) >= 0.05 * ymax:
            for l, x, y in zip(ls[:-1], xs[:-1], ys[:-1]):
                top.annotate(f"{y:.1f} s", (x, y), textcoords="offset points", xytext=(4, 4), fontsize=6.5)
            top.annotate(f"{ys[-1]:.1f} s @ {ls[-1].get('sha') or '?'}", (xs[-1], ys[-1]),
                         textcoords="offset points", xytext=(6, 4 + 9 * rank), fontsize=6.5)
            rank += 1
    top.set_ylabel("seconds of imprimatur build")
    top.set_ylim(bottom=0)
    top.grid(True, linewidth=0.3)
    top.legend(fontsize=8, loc="upper left", title="paper (entries)", title_fontsize=8)
    top.set_title("imprimatur's run time: one point per paper per night, the last nightly run of the day\n"
                  "(seconds of `imprimatur build`, imprimatur's own phases; Lake and TeX excluded; docs/ci-timing.md)",
                  fontsize=9)

    largest = max(points, key=lambda p: points[p][-1].get("entries", 0))
    ls = points[largest]
    xs = [datetime.date.fromisoformat(l["date"]) for l in ls]
    stacks, labels = [], []
    for p in PHASES:
        ys = [l["ms"].get(p, 0) / 1000 for l in ls]
        if any(ys):
            stacks.append(ys)
            labels.append(p)
    other = [max(0, l["ms"].get("export", 0) - sum(l["ms"].get(p, 0) for p in ("load", "entries", "write"))) / 1000 for l in ls]
    if any(other):
        stacks.append(other)
        labels.append("export (other)")
    checker = [l["ms"].get("checker", 0) / 1000 for l in ls]
    if stacks and len(xs) > 1:
        bottom.stackplot(xs, stacks, labels=labels, linewidth=0)
        bottom.legend(fontsize=8, loc="upper left", ncol=3)
    elif stacks:
        # One night: a stacked bar, since a stack plot of one point is empty.
        base = 0
        for ys, label in zip(stacks, labels):
            bottom.bar(xs, ys, bottom=base, width=0.6, label=label)
            base += ys[0]
        bottom.legend(fontsize=8, loc="upper left", ncol=3)
    if any(checker):
        bottom.plot(xs, checker, color="black", linestyle="--", marker="o", markersize=3, linewidth=1,
                    label="verified checker (runs alongside)")
        run = ls[-1].get("checker_run") or {}
        tail = (f"  (leanexport {run.get('leanexport_ms', 0) / 1000:.0f} s + check {run.get('check_ms', 0) / 1000:.0f} s)"
                if run.get("check_ms") else ("  (verdict kept)" if run.get("kept") else ""))
        bottom.annotate(f"checker {checker[-1]:.0f} s{tail}", (xs[-1], checker[-1]),
                        textcoords="offset points", xytext=(6, -12), fontsize=6.5)
        bottom.legend(fontsize=7, loc="upper left", ncol=4)
    bottom.set_ylabel(f"{largest}: seconds by part")
    bottom.set_title(f"{largest}, the largest paper: the extractor's parts stacked; "
                     "the verified checker as a line, since it runs beside them", fontsize=9)
    bottom.set_ylim(top=max(bottom.get_ylim()[1], (max(checker) if any(checker) else 0) * 1.35))
    bottom.grid(True, linewidth=0.3)
    # The axis spans the nights there are, and a few days around them, rather
    # than the years matplotlib pads a lone point with.
    days = sorted({datetime.date.fromisoformat(l["date"]) for ls in points.values() for l in ls})
    pad = datetime.timedelta(days=max(2, (days[-1] - days[0]).days // 20 + 1))
    for ax in (top, bottom):
        ax.set_xlim(days[0] - pad, days[-1] + pad)
    fig.autofmt_xdate()
    fig.tight_layout()
    fig.savefig(out / "chart.svg")
    fig.savefig(out / "chart.png", dpi=110)
    print(f"timing-chart: wrote {out / 'chart.svg'} and {out / 'chart.png'} "
          f"({sum(len(v) for v in points.values())} points, {len(points)} papers)")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
