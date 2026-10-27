"""The running example, in full: what goes into imprimatur, the bundle, and the TeX.

For Figure 1 of the paper this writes, under about/example/:

- requests.json: the requests the figure's four blocks make, each key with
  the view of its block, read from the paper itself (the blocks' keys, and
  their aliases' views in imprimatur.toml), and checked against the Lean
  constant About.figureRequests, which Section 2 shows;
- bundle.json: the bundle the extractor writes for those requests alone, by
  running it (the bundle the paper's Theorem 1.1 is about);
- figure.tex: the TeX of Figure 1, as the paper's source has it;
- readings.txt: each formula of the figure, as the validator's parser reads
  it back while the extractor writes the bundle: its readings, and the one
  the renderer expected (Pollack-consistency is that they are one and the
  same);

and example-diagram.pdf: the three as thumbnails, linked by the two
programs. Run by about/refresh.sh after `imprimatur build`, with uv:

    cd about/analytics && uv run example.py
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import tempfile
import tomllib
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch  # noqa: E402

ABOUT = Path(__file__).resolve().parent.parent
PAPER = ABOUT / "imprimatur-paper.tex"
OUT = ABOUT / "example"
FIGURE_LABEL = "fig:example"


def figure_tex(paper: str) -> str:
    """The figure environment that holds \\label{fig:example}."""
    end = paper.index("\\label{" + FIGURE_LABEL + "}")
    start = paper.rindex("\\begin{figure}", 0, end)
    stop = paper.index("\\end{figure}", end) + len("\\end{figure}")
    return paper[start:stop] + "\n"


def figure_requests(fig: str) -> list[tuple[str, list[str]]]:
    """Each block of the figure: its key, with its alias's view."""
    aliases = tomllib.loads((ABOUT / "imprimatur.toml").read_text())["aliases"]
    out = []
    for m in re.finditer(r"\\begin\{(\w+)\}(?:\[[^\]]*\])?\{([^}]*)\}", fig):
        env, key = m.group(1), m.group(2)
        if env in aliases:
            out.append((key, [aliases[env]["view"]]))
    return out


def lean_requests() -> list[tuple[str, list[str]]]:
    """About.figureRequests, as About.lean writes it."""
    src = (ABOUT / "lean" / "About.lean").read_text()
    body = src[src.index("def figureRequests") :]
    body = body[body.index(":=") + 2 : body.index("\n\n")]
    return [(k, re.findall(r'"([^"]*)"', vs)) for k, vs in re.findall(r'\("([^"]*)",\s*\[([^\]]*)\]\)', body)]


def run_extractor(rs: list[tuple[str, list[str]]]) -> tuple[dict, list[tuple[str, str, str, str]]]:
    """The bundle the extractor writes for the requests `rs` alone, and each
    formula it read back: key, TeX, readings found, reading expected."""
    full = json.loads((ABOUT / ".imprimatur" / "requests.json").read_text())
    full["requests"] = {k: {"views": vs} for k, vs in rs}
    version = (ABOUT / "lean" / "lean-toolchain").read_text().strip().split(":")[-1]
    export = Path.home() / ".cache/imprimatur/toolchains" / version / ".lake/build/bin/imprimatur-export"
    with tempfile.TemporaryDirectory() as tmp:
        req, out = Path(tmp) / "requests.json", Path(tmp) / "bundle.json"
        req.write_text(json.dumps(full))
        run = subprocess.run(
            ["lake", "env", str(export), "--requests", str(req), "--out", str(out), "--base", str(ABOUT)],
            cwd=ABOUT / "lean", check=True, capture_output=True, text=True,
            env={**os.environ, "IMPRIMATUR_VALIDATE_READINGS": "1"},
        )
        readings = []
        for line in run.stderr.splitlines():
            parts = line.split("\t")
            if parts[0] == "reading" and len(parts) == 5 and tuple(parts[1:]) not in readings:
                readings.append(tuple(parts[1:]))
        return json.loads(out.read_text()), readings


# --- The diagram --------------------------------------------------------------
#
# Three thumbnails, at the paper's text width (acmsmall: 13.5 cm), each an
# excerpt that follows one thread, the theorem Values are final, in red: its
# Lean and notation, its entry in the bundle, and its block in the paper.
# Long lines wrap; the excerpts are cut from the generated files, so the
# diagram follows them.

WIDTH_IN = 5.31
MONO_PT = 5.4
COLS = 31
LINE_IN = MONO_PT * 1.22 / 72
CHAR_IN = MONO_PT * 0.602 / 72
INK, MUTED, ACCENT, PAGE, BLUE = "#222222", "#6b6b6b", "#a8322a", "#fbfaf7", "#2f4a6d"

# A line of an excerpt, and whether it is on the thread (drawn in red).
Line = tuple[str, bool]


def wrap(lines: list[Line], width: int = COLS) -> list[Line]:
    """Lines cut to `width`, continuing indented, on the thread if their
    line is."""
    out = []
    for line, hot in lines:
        indent = len(line) - len(line.lstrip())
        while len(line) > width:
            cut = line.rfind(" ", indent + 8, width)
            cut = cut if cut > 0 else width
            out.append((line[:cut], hot))
            line = " " * (indent + 2) + line[cut:].lstrip()
        out.append((line, hot))
    return out


def block(text: str, start: str, stop: str, hot: bool = False) -> list[Line]:
    """The lines of `text` from the first containing `start` to the next
    containing `stop`, both included."""
    lines = text.splitlines()
    i = next(n for n, line in enumerate(lines) if start in line)
    j = next(n for n in range(i, len(lines)) if stop in lines[n])
    return [(line, hot) for line in lines[i : j + 1]]


def plain(*lines: str) -> list[Line]:
    return [(line, False) for line in lines]


def lean_excerpt(lean: str) -> list[Line]:
    out = block(lean, "inductive Step", "| beta") + plain("  ...", "")
    out += block(lean, "theorem values_final", "theorem values_final", hot=True)
    return wrap(out)


# The notation the figure uses, and of it, in red, what writes Values are
# final: reduction, the terms, the value convention and the terms' letter.
NOTATION = ["latex_notation Stlc.Step ", "latex_notation Stlc.Tm.lam ", "latex_notation Stlc.Tm.app ",
            "latex_notation Stlc.Tm =>", "latex_metavar_convention", "latex_category Stlc.Tm ",
            'latex_entry "Values are final"']
NOTATION_HOT = ["latex_notation Stlc.Step ", "latex_notation Stlc.Tm =>", "latex_metavar_convention",
                "latex_category Stlc.Tm ", 'latex_entry "Values are final"']


def notation_excerpt(notation: str) -> list[Line]:
    out = [(line, line.startswith(tuple(NOTATION_HOT)))
           for line in notation.splitlines() if line.startswith(tuple(NOTATION))]
    return wrap(out + plain("..."))


def bundle_excerpt(bundle: dict) -> list[Line]:
    key = "Values are final"
    e = bundle["entries"][key]
    trimmed = {"decl": e["decl"], "kind": e["kind"], "axioms": e["axioms"], "sorry": e["sorry"],
               "stmtHash": e["stmtHash"][:12] + "...",
               "views": {"prose": e["views"]["prose"], "lean": e["views"]["lean"]}}
    body = json.dumps({key: trimmed}, indent=1, ensure_ascii=False).splitlines()[1:-1]
    hot = [(line, '"prose"' in line or line.startswith(f' "{key}"')) for line in body]
    others = len(bundle["entries"]) - 1
    return wrap(plain('{ "entries": {') + hot + plain(f" ... and {others} more entries", "} }"))


def tex_excerpt(fig: str) -> list[Line]:
    out = block(fig, "\\begin{leantheorem}", "\\end{leantheorem}", hot=True)
    out += plain("") + block(fig, "\\begin{leanrules}", "{ (\\lambda") + plain("  ...", "")
    out += block(fig, "\\begin{leansource}", "\\end{leansource}")
    return wrap(out)


def page(ax, x: float, w: float, top: float, body_h: float, lines: list[Line], name: str | None = None) -> None:
    """A page of a file's lines, those on the thread in red, with the file's
    name on its tab. Lengths are in inches."""
    ax.add_patch(FancyBboxPatch((x, top - body_h), w, body_h, boxstyle="round,pad=0.01,rounding_size=0.03",
                                facecolor=PAGE, edgecolor="#a0a0a0", linewidth=0.5))
    if name:
        ax.text(x + w - 0.04, top - 0.03, name, ha="right", va="top", fontsize=5.0, color=MUTED, style="italic")
    for n, (line, hot) in enumerate(lines):
        ax.text(x + 0.05, top - 0.06 - n * LINE_IN, line, ha="left", va="top", family="monospace",
                fontsize=MONO_PT, color=ACCENT if hot else INK, parse_math=False)


def heading(ax, x: float, w: float, top: float, title: str, subtitle: str) -> None:
    ax.text(x + w / 2, top + 0.2, title, ha="center", va="bottom", fontsize=7, color=INK, weight="bold")
    ax.text(x + w / 2, top + 0.06, subtitle, ha="center", va="bottom", fontsize=5.6, color=MUTED, style="italic")


def arrow(ax, x0: float, x1: float, y: float, top: str, bottom: str) -> None:
    ax.add_patch(FancyArrowPatch((x0, y), (x1, y), arrowstyle="-|>", mutation_scale=7, color=INK, linewidth=0.7))
    ax.text((x0 + x1) / 2, y + 0.05, top, ha="center", va="bottom", fontsize=5.2, color=INK)
    ax.text((x0 + x1) / 2, y - 0.05, bottom, ha="center", va="top", fontsize=5.0, color=MUTED, style="italic")


def band_lines(rows: list[tuple[str, str]], cols: int) -> list[tuple[str, str]]:
    """The band's lines, each a formula and a reading: on one line, aligned,
    when it fits, else the reading on the lines after, wrapped."""
    fits = [f for f, r in rows if len(f) + 3 + len(r) <= cols]
    split = max((len(f) for f in fits), default=0) + 1
    out = []
    for f, r in rows:
        if len(f) + 3 + len(r) <= cols and len(f) < split:
            out.append((f.ljust(split), "↦ " + r))
        else:
            out.append((f, ""))
            text = "  ↦ " + r
            while text:
                out.append(("", text[:cols]))
                text = "      " + text[cols:] if len(text) > cols else ""
    return out


def readings_band(ax, x: float, w: float, top: float, lines: list[tuple[str, str]]) -> None:
    """The validator's parser at work: each formula, and its one reading."""
    h = 0.24 + len(lines) * LINE_IN
    ax.add_patch(FancyBboxPatch((x, top - h), w, h, boxstyle="round,pad=0.01,rounding_size=0.03",
                                facecolor="#f3f6fa", edgecolor="#8da2bb", linewidth=0.5))
    ax.text(x + 0.05, top - 0.05, "read back by the validator's parser: each formula, and its one reading",
            ha="left", va="top", fontsize=5.6, color=BLUE, style="italic")
    for n, (formula, reading) in enumerate(lines):
        y = top - 0.18 - n * LINE_IN
        ax.text(x + 0.05, y, formula, ha="left", va="top", family="monospace", fontsize=MONO_PT,
                color=INK, parse_math=False)
        ax.text(x + 0.05 + len(formula) * CHAR_IN, y, reading, ha="left", va="top", family="monospace",
                fontsize=MONO_PT, color=ACCENT, parse_math=False)


def diagram(lean: list[Line], notation: list[Line], bundle: list[Line], tex: list[Line],
            readings: list[tuple[str, str]], path: Path) -> None:
    pad, between = 0.12, 0.08
    lean_h, notation_h = pad + (len(lean) + 1) * LINE_IN, pad + (len(notation) + 1) * LINE_IN
    body_h = max(lean_h + between + notation_h, pad + max(len(bundle), len(tex)) * LINE_IN)
    band_w_cols = int((2 * (COLS * CHAR_IN + 0.12) + (WIDTH_IN - 0.04 - 3 * (COLS * CHAR_IN + 0.12)) / 2 - 0.1)
                      / CHAR_IN)
    band = band_lines(readings, band_w_cols)
    gap_v = 0.26
    height = body_h + 0.45 + gap_v + 0.24 + len(band) * LINE_IN
    fig = plt.figure(figsize=(WIDTH_IN, height))
    ax = fig.add_axes((0, 0, 1, 1))
    ax.set_xlim(0, WIDTH_IN)
    ax.set_ylim(0, height)
    ax.axis("off")
    # A panel holds COLS characters of the monospace font (about 0.6 em each).
    w = COLS * MONO_PT * 0.602 / 72 + 0.12
    gap = (WIDTH_IN - 0.04 - 3 * w) / 2
    xs = [0.02, 0.02 + w + gap, 0.02 + 2 * (w + gap)]
    top = height - 0.4
    heading(ax, xs[0], w, top, "The development", "Lean, and the paper's notation")
    page(ax, xs[0], w, top, lean_h, [("", False)] + lean, "Stlc.lean")
    notation_top = top - lean_h - between
    page(ax, xs[0], w, notation_top, body_h - lean_h - between, [("", False)] + notation, "StlcTeX.lean")
    heading(ax, xs[1], w, top, "The bundle", "bundle.json, for Figure 1")
    page(ax, xs[1], w, top, body_h, bundle)
    heading(ax, xs[2], w, top, "The paper", "the TeX of Figure 1")
    page(ax, xs[2], w, top, body_h, tex)
    y = top - body_h / 2
    arrow(ax, xs[0] + w + 0.03, xs[1] - 0.03, y, "extract", "Lean")
    arrow(ax, xs[1] + w + 0.03, xs[2] - 0.03, y, "build", "TeX")
    # Under the development and the bundle: what the extractor checks of each
    # rendering before it writes it, with arrows from the bundle's rendering
    # down into the parser, and from the readings up to the statement.
    band_top = top - body_h - gap_v
    readings_band(ax, xs[0], xs[1] + w - xs[0], band_top, band)
    ax.text(xs[2] + w / 2, band_top - 0.12, "Pollack-consistency:\nevery formula has one reading,\nand it is the one it was\nrendered from",
            ha="center", va="top", fontsize=5.6, color=BLUE, style="italic", linespacing=1.3)
    for x, (y0, y1), label in [(xs[1] + w / 2, (top - body_h, band_top), "each rendering"),
                               (xs[0] + w / 2, (band_top, top - body_h), "the statement's")]:
        ax.add_patch(FancyArrowPatch((x, y0 - 0.01), (x, y1 + 0.01), arrowstyle="-|>", mutation_scale=7,
                                     color=BLUE, linewidth=0.7))
        ax.text(x + 0.05, (y0 + y1) / 2, label, ha="left", va="center", fontsize=5.0, color=BLUE, style="italic")
    fig.savefig(path)
    plt.close(fig)


def main() -> None:
    paper = PAPER.read_text()
    fig = figure_tex(paper)
    rs = figure_requests(fig)
    if rs != lean_requests():
        raise SystemExit(f"Figure 1's blocks make the requests {rs}, but About.figureRequests says {lean_requests()}")
    bundle, readings = run_extractor(rs)
    OUT.mkdir(exist_ok=True)
    (OUT / "requests.json").write_text(json.dumps({k: {"views": vs} for k, vs in rs}, indent=2) + "\n")
    bundle_text = json.dumps(bundle, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    (OUT / "bundle.json").write_text(bundle_text)
    (OUT / "figure.tex").write_text(fig)
    lines, last = [], None
    for k, t, found, expected in readings:
        if k != last:
            lines += ([""] if last else []) + [k]
            last = k
        lines += [f"  {t}", f"    reads only as  {found}" if found == expected else
                  f"    reads as  {found}, but was rendered from  {expected}"]
    (OUT / "readings.txt").write_text("\n".join(lines) + "\n")
    lean = (ABOUT / "lean" / "Stlc.lean").read_text()
    notation = (ABOUT / "notation" / "StlcTeX.lean").read_text()
    # The band: the formulas of Values are final, and the conclusion of
    # (Beta), whose parentheses the second reading would need.
    shown = [(t, found) for k, t, found, _ in readings if k == "Values are final"]
    shown += [(t, found) for k, t, found, _ in readings if k == "Stlc.Step" and "lambda" in t][:1]
    diagram(lean_excerpt(lean), notation_excerpt(notation), bundle_excerpt(bundle), tex_excerpt(fig),
            shown, ABOUT / "example-diagram.pdf")
    print(f"{len(rs)} requests; {len(bundle['entries'])} entries; saved example/ and example-diagram.pdf")


if __name__ == "__main__":
    if shutil.which("lake") is None:
        raise SystemExit("lake is not on PATH")
    main()
