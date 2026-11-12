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
    points = {paper: [days[d] for d in sorted(days)] for paper, days in by_day.items()}
    if not points:
        print("timing-chart: no nightly points yet", file=sys.stderr)
        return 0
    out = pathlib.Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)

    fig, (top, bottom) = plt.subplots(2, 1, figsize=(9, 7), height_ratios=[3, 2])
    for paper, ls in sorted(points.items()):
        xs = [datetime.date.fromisoformat(l["date"]) for l in ls]
        ys = [l["ms"]["total"] / 1000 for l in ls]
        top.plot(xs, ys, marker="o", markersize=3, linewidth=1, label=f"{paper} ({ls[-1].get('entries', '?')} entries)")
    top.set_ylabel("imprimatur build, seconds")
    top.set_ylim(bottom=0)
    top.grid(True, linewidth=0.3)
    top.legend(fontsize=8, loc="upper left")
    top.set_title("imprimatur's run time, one point a night (docs/ci-timing.md)", fontsize=10)

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
        bottom.plot(xs, checker, color="black", linestyle="--", marker="o", markersize=3, linewidth=1, label="checker (alongside)")
        bottom.legend(fontsize=8, loc="upper left", ncol=3)
    bottom.set_ylabel(f"{largest}: phases, seconds")
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
