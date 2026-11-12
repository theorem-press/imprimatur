#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""imprimatur's run time, one line per paper per run (docs/ci-timing.md).

`imprimatur build --timing` writes `.imprimatur/timing.jsonl`, one JSON
object per phase, entry, view and formula of one command. This script folds
such files into one line per paper, keeps those lines in an append-only log,
compares a run with the log, and writes the summary a CI run shows.

    timing-fold.py fold DIR... [--paper NAME] [--out FILE]
        For each DIR, read DIR/timing-build.jsonl (and DIR/timing-check.jsonl
        if there is one; else DIR/.imprimatur/timing.jsonl) and print one
        line. DIR's name is the paper's, unless --paper says otherwise.
    timing-fold.py summary --log LOG LINES
        Markdown for $GITHUB_STEP_SUMMARY: each paper's total in LINES beside
        the median of its last WINDOW nightly points in LOG, and a chart per
        paper of the last 30 nights.
    timing-fold.py check --log LOG LINES
        Exit 1 when a paper in LINES is slower than the alarm allows, given
        LOG; say which paper and which phase grew.
    timing-fold.py append --log LOG LINES
        Append LINES to LOG (created if missing).

LINES is a file of lines `fold` wrote; `-` is standard input. Standard
library only.
"""
import argparse
import datetime
import json
import os
import pathlib
import statistics
import subprocess
import sys

# The alarm (docs/ci-timing.md, part 4): a paper's total is a regression
# when it exceeds both RATIO times the median of its last WINDOW nightly
# points and that median plus SLACK_MS (so a tenth of a second of noise on a
# one-second paper is not one), unless the paper grew as much.
WINDOW = 10
RATIO = 2.0
SLACK_MS = 2_000
CHART_POINTS = 30

# The phases a line records, in the order they happen. `total` is the sum
# of the splicer's phases, which contain the extractor's.
SPLICE_PHASES = ["scan", "export", "apply", "check"]
EXTRACT_PHASES = ["load", "entries", "write", "extractor"]
PHASES = SPLICE_PHASES + EXTRACT_PHASES + ["checker"]
# The phases a regression is attributed to: `export` less what it contains.
INSIDE_EXPORT = ["load", "entries", "write", "checker"]
ATTRIBUTED = ["scan", "load", "entries", "write", "checker", "export (other)", "apply", "check"]


def phase_ms(line, phase):
    ms = line.get("ms", {})
    if phase == "export (other)":
        return max(0, ms.get("export", 0) - sum(ms.get(p, 0) for p in INSIDE_EXPORT))
    return ms.get(phase, 0)


def read_events(path):
    events = []
    for line in pathlib.Path(path).read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line:
            events.append(json.loads(line))
    return events


def fold_events(events):
    """The phases, sizes and slowest items of one command's events."""
    ms = {}
    sizes = {"entries": 0, "views": 0, "formulas": 0, "tokens": 0, "steps": 0}
    slowest = {}

    def slower(kind, name, t):
        if name is not None and (kind not in slowest or t > slowest[kind][1]):
            slowest[kind] = [name, t]

    for e in events:
        at, phase, t = e.get("at"), e.get("phase"), int(e.get("ms", 0))
        if at == "splice" and phase in SPLICE_PHASES:
            ms[phase] = ms.get(phase, 0) + t
        elif at == "checker":
            ms["checker"] = ms.get("checker", 0) + t
        elif at == "extract":
            if phase in EXTRACT_PHASES:
                ms[phase] = ms.get(phase, 0) + t
                if phase == "entries":
                    sizes["entries"] = int(e.get("count", 0))
            elif phase == "entry":
                slower("entry", e.get("key"), t)
            elif phase == "view":
                sizes["views"] += 1
                slower("view", e.get("view"), t)
            elif phase == "formula":
                sizes["formulas"] += 1
                sizes["tokens"] += int(e.get("tokens", 0))
                sizes["steps"] += int(e.get("steps", 0))
                slower("formula", e.get("tex"), t)
    ms["total"] = sum(ms.get(p, 0) for p in SPLICE_PHASES)
    return ms, sizes, slowest


def toolchain_of(directory):
    """The Lean toolchain of the paper in `directory`: its project's."""
    d = pathlib.Path(directory)
    candidates = []
    toml = d / "imprimatur.toml"
    if toml.exists():
        for line in toml.read_text(encoding="utf-8").splitlines():
            if line.startswith("lean_project"):
                candidates.append(d / line.split("=", 1)[1].strip().strip('"'))
    candidates += [d, d / "lean"]
    for c in candidates:
        f = c / "lean-toolchain"
        if f.exists():
            return f.read_text(encoding="utf-8").strip().split(":")[-1]
    return None


def provenance():
    """Where and when: the commit, the event, the runner image."""
    sha = os.environ.get("GITHUB_SHA")
    if not sha:
        try:
            sha = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True,
                                 text=True, check=True).stdout.strip()
        except Exception:
            sha = None
    image = None
    if os.environ.get("ImageOS"):
        image = f"{os.environ['ImageOS']}/{os.environ.get('ImageVersion', '')}"
    return {
        "date": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d"),
        "sha": sha[:7] if sha else None,
        "event": os.environ.get("GITHUB_EVENT_NAME", "local"),
        "image": image,
    }


def fold_dir(directory, paper):
    d = pathlib.Path(directory)
    build = d / "timing-build.jsonl"
    check = d / "timing-check.jsonl"
    if not build.exists():
        build = d / ".imprimatur" / "timing.jsonl"
    if not build.exists():
        return None
    ms, sizes, slowest = fold_events(read_events(build))
    line = dict(provenance())
    line.update({"paper": paper, "toolchain": toolchain_of(d)})
    toml = d / "imprimatur.toml"
    if toml.exists():
        text = toml.read_text(encoding="utf-8")
        line["mode"] = "external" if 'mode = "external"' in text else ("sidecar" if 'mode = "sidecar"' in text else "in-project")
        line["checker"] = "checker" in ms
    line.update(sizes)
    line["ms"] = {p: ms[p] for p in PHASES + ["total"] if p in ms}
    if check.exists():
        cms, _, _ = fold_events(read_events(check))
        line["check_ms"] = cms.get("total", 0)
    line["slowest"] = slowest
    return line


def read_lines(path):
    text = sys.stdin.read() if path == "-" else pathlib.Path(path).read_text(encoding="utf-8")
    return [json.loads(l) for l in text.splitlines() if l.strip()]


def read_log(path):
    p = pathlib.Path(path)
    return read_lines(path) if p.exists() else []


def nightly_points(log, paper):
    """The paper's nightly points in the log, oldest first."""
    return [l for l in log if l.get("paper") == paper and l.get("event") in ("schedule", "workflow_dispatch")]


def median_total(points):
    totals = [p["ms"]["total"] for p in points[-WINDOW:] if "ms" in p]
    return statistics.median(totals) if totals else None


def grew(line, points):
    """Whether the paper itself grew by RATIO against the window: entries or formulas."""
    for size in ("entries", "formulas"):
        past = [p.get(size, 0) for p in points[-WINDOW:]]
        if past and statistics.median(past) > 0 and line.get(size, 0) >= RATIO * statistics.median(past):
            return size
    return None


def verdicts(log, lines):
    """For each line: (median or None, ratio or None, reason or None)."""
    out = []
    for line in lines:
        points = nightly_points(log, line["paper"])
        med = median_total(points)
        total = line["ms"]["total"]
        ratio = (total / med) if med else None
        reason = None
        if med is not None and total > max(RATIO * med, med + SLACK_MS):
            size = grew(line, points)
            if size:
                reason = None  # a bigger paper, not a slower tool
            else:
                # The phase that grew the most against the window's medians:
                # `export` contains the extractor's phases and the checker,
                # so what is left of it after them is judged on its own.
                worst, worst_by = None, 0
                for p in ATTRIBUTED:
                    now = phase_ms(line, p)
                    past = [phase_ms(q, p) for q in points[-WINDOW:] if "ms" in q]
                    pm = statistics.median(past) if past else 0
                    if now - pm > worst_by:
                        worst, worst_by = p, now - pm
                reason = (f"{line['paper']}: total {total / 1000:.1f} s against a median of {med / 1000:.1f} s"
                          f" over the last {min(len(points), WINDOW)} nights"
                          + (f"; the phase that grew most is `{worst}` (+{worst_by / 1000:.1f} s)" if worst else ""))
        out.append((med, ratio, reason))
    return out


def mermaid_chart(points, paper):
    pts = points[-CHART_POINTS:]
    if len(pts) < 2:
        return ""
    xs = ", ".join(f'"{p["date"][5:]}"' for p in pts)
    ys = ", ".join(f"{p['ms']['total'] / 1000:.2f}" for p in pts)
    top = max(p["ms"]["total"] for p in pts) / 1000
    return "\n".join([
        "```mermaid",
        "xychart-beta",
        f'    title "{paper}: imprimatur build, seconds, last {len(pts)} nights"',
        f"    x-axis [{xs}]",
        f'    y-axis "seconds" 0 --> {top * 1.2:.2f}',
        f"    line [{ys}]",
        "```",
    ])


def summary(log, lines):
    rows = ["| Paper | Entries | Formulas | Build | Median of last nights | Ratio |", "|---|---:|---:|---:|---:|---:|"]
    for line, (med, ratio, reason) in zip(lines, verdicts(log, lines)):
        rows.append(f"| {line['paper']} | {line.get('entries', '')} | {line.get('formulas', '')} "
                    f"| {line['ms']['total'] / 1000:.1f} s | {'' if med is None else f'{med / 1000:.1f} s'} "
                    f"| {'' if ratio is None else f'{ratio:.2f}'}{' **slow**' if reason else ''} |")
    out = ["## imprimatur's run time", "",
           "Seconds of `imprimatur build` per paper, imprimatur's own phases only (docs/ci-timing.md).", ""]
    out += rows
    for line in lines:
        # The run's own point comes last: a nightly's summary is written
        # before its line is appended to the log, and a pull request's line
        # is never appended.
        points = nightly_points(log, line["paper"])
        if not any(p.get("date") == line.get("date") and p.get("sha") == line.get("sha") for p in points):
            points = points + [line]
        chart = mermaid_chart(points, line["paper"])
        if chart:
            out += ["", chart]
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    f = sub.add_parser("fold")
    f.add_argument("dirs", nargs="+")
    f.add_argument("--paper", help="the paper's name (default: the directory's)")
    f.add_argument("--out", help="write the lines here instead of standard output")
    for name in ("summary", "check", "append"):
        s = sub.add_parser(name)
        s.add_argument("--log", required=True)
        s.add_argument("lines")
    a = ap.parse_args()

    if a.cmd == "fold":
        out = []
        for d in a.dirs:
            line = fold_dir(d, a.paper or pathlib.Path(d).resolve().name)
            if line:
                out.append(json.dumps(line, ensure_ascii=False))
            else:
                print(f"timing-fold: {d}: no timing file", file=sys.stderr)
        text = "\n".join(out) + ("\n" if out else "")
        if a.out:
            pathlib.Path(a.out).write_text(text, encoding="utf-8")
        else:
            sys.stdout.write(text)
        return 0

    log, lines = read_log(a.log), read_lines(a.lines)
    if a.cmd == "summary":
        sys.stdout.write(summary(log, lines))
        return 0
    if a.cmd == "check":
        reasons = [r for _, _, r in verdicts(log, lines) if r]
        for r in reasons:
            print(f"timing: slow: {r}")
        if not reasons:
            print("timing: no paper is slower than the alarm allows")
        return 1 if reasons else 0
    if a.cmd == "append":
        with open(a.log, "a", encoding="utf-8") as h:
            for line in lines:
                h.write(json.dumps(line, ensure_ascii=False) + "\n")
        print(f"timing: appended {len(lines)} line(s) to {a.log}")
        return 0


if __name__ == "__main__":
    sys.exit(main())
