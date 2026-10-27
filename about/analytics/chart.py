"""Stacked bar chart of imprimatur's Lean, by component and declaration kind.

Each line of each file is attributed to the kind of the top-level declaration
that spans it (a declaration runs to the line before the next one); lines
before the first declaration are "other" (imports, module docs, namespace and
section directives). The chart is written next to the paper, as
about/development-chart.png, for the appendix's \\includegraphics.

Unlike the LLMbda chart this scans the sources only: the bundle, the
extractor and the splicer build at different toolchains, so there is no one
environment to dump. The kinds come from the declaration keywords.

Run with  uv run chart.py  from this directory, or through ../refresh.sh.
"""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

HERE = Path(__file__).resolve().parent
ABOUT = HERE.parent
ROOT = ABOUT.parent
OUT = ABOUT / "development-chart.png"

# The directories whose Lean is charted. Every .lean file under them (outside
# .lake/) must be in a bucket or in EXCLUDED.
ROOTS = ("bundle", "extract", "splice", "about")

# Buckets in the paper's order: the bundle, the extractor, the splicer's code,
# its model and laws, the proofs about its code, then the tests and the
# paper's own Lean. Files are enumerated, not globbed, so that a new file
# fails the coverage check until it is placed.
FILES: list[tuple[str, list[str]]] = [
    ("Bundle", [
        "bundle/Bundle.lean",
        "bundle/Layout.lean",
    ]),
    ("Extractor:\nrendering", [
        "extract/Imprimatur/Render.lean",
        "extract/Imprimatur/Notation.lean",
        "extract/Imprimatur/TeX.lean",
        "extract/Imprimatur/CustomViews.lean",
        "extract/Imprimatur/Packs.lean",
        "extract/Imprimatur/Views/Display.lean",
        "extract/Imprimatur/Views/Grammar.lean",
        "extract/Imprimatur/Views/Index.lean",
        "extract/Imprimatur/Views/Lean.lean",
        "extract/Imprimatur/Views/Math.lean",
        "extract/Imprimatur/Views/Rules.lean",
    ]),
    ("Extractor:\nvalidation", [
        "extract/Imprimatur/Validate.lean",
        "bundle/ReadBack.lean",
    ]),
    ("Extractor:\nentries, trust", [
        "extract/Imprimatur.lean",
        "extract/Main.lean",
        "extract/Imprimatur/Commands.lean",
        "extract/Imprimatur/Compat.lean",
        "extract/Imprimatur/Doc.lean",
        "extract/Imprimatur/Entry.lean",
        "extract/Imprimatur/Export.lean",
        "extract/Imprimatur/Requests.lean",
        "extract/Imprimatur/Sha256.lean",
        "extract/Imprimatur/Trust.lean",
        "extract/Imprimatur/Version.lean",
    ]),
    ("Splicer:\nreading", [
        "splice/Splice/Core/Item.lean",
        "splice/Splice/Core/Scan.lean",
        "splice/Splice/Core/Slots.lean",
        "splice/Splice/Core/Text.lean",
        "splice/Splice/Scan.lean",
        "splice/Splice/Slots.lean",
        "splice/Splice/Text.lean",
        "splice/Splice/Doc.lean",
        "splice/Splice/Config.lean",
        "splice/Splice/Toml.lean",
        "splice/Splice/Manifests.lean",
    ]),
    ("Splicer:\nwriting, checking", [
        "splice/Splice/Apply.lean",
        "splice/Splice/Check.lean",
        "splice/Splice/Core/Rewrite.lean",
        "splice/Splice/Diag.lean",
        "splice/Splice/Strip.lean",
        "splice/Splice/Sha256.lean",
    ]),
    ("Splicer:\ncommand line", [
        "splice/Main.lean",
        "splice/Splice.lean",
        "splice/SpliceWrapper.lean",
        "splice/Splice/Cli.lean",
        "splice/Splice/Version.lean",
        "splice/Splice/Wrapper.lean",
    ]),
    ("Model\nand laws", [
        "splice/SpliceModel.lean",
        "splice/SpliceModel/Basic.lean",
        "splice/SpliceModel/Laws.lean",
    ]),
    ("Model:\nprose, rules", [
        "splice/SpliceModel/Views.lean",
        "splice/SpliceModel/Prose.lean",
        "splice/SpliceModel/Rules.lean",
    ]),
    ("Proofs of\nthe code", [
        "splice/SpliceModel/Splicer.lean",
        "splice/SpliceModel/Theorem1.lean",
        "splice/SpliceModel/Formulas.lean",
        "splice/SpliceModel/ReadBack.lean",
        "splice/SpliceModel/ReadBackSound.lean",
        "splice/SpliceModel/ReadBackComplete.lean",
        "splice/SpliceModel/Pruning.lean",
        "splice/SpliceModel/ReadBackChains.lean",
        "splice/SpliceModel/Validator.lean",
        "splice/SpliceModel/Summary.lean",
    ]),
    ("Tests", [
        "extract/test/ExtractTests.lean",
        "extract/test/ExtractTest/ChainLaws.lean",
        "extract/test/ExtractTest/Doc.lean",
        "extract/test/ExtractTest/Fixtures.lean",
        "extract/test/ExtractTest/HashProps.lean",
        "extract/test/ExtractTest/SortLaws.lean",
        "extract/test/ExtractTest/Unit.lean",
        "extract/test/ExtractTest/Validate.lean",
        "splice/test/SpliceTests.lean",
        "splice/test/SpliceTest/Diff.lean",
        "splice/test/SpliceTest/Golden.lean",
        "splice/test/SpliceTest/Props.lean",
        "splice/test/SpliceTest/Reference.lean",
        "splice/test/SpliceTest/Unit.lean",
    ]),
    ("This paper:\nexample, notation", [
        "about/lean/About.lean",
        "about/lean/Stlc.lean",
        "about/notation/SpliceTeX.lean",
        "about/notation/StlcTeX.lean",
    ]),
]

# Not charted. The bundle's type is copied into the extractor and the splicer
# under their module names (the lint keeps the copies equal to bundle/), so it
# is counted once, as the Bundle bar; so is the reading back, whose source,
# bundle/ReadBack.lean, is counted with the validation it serves. StdMacros is a table generated by
# scripts/gen-std-macros.py.
EXCLUDED: tuple[str, ...] = (
    "extract/Imprimatur/Bundle.lean",
    "extract/Imprimatur/Layout.lean",
    "extract/Imprimatur/ReadBack.lean",
    "splice/Imprimatur/",
    "splice/Splice/StdMacros.lean",
)

# Declaration kinds, in stack order (bottom to top), and their colours.
KIND_ORDER = ["inductive", "def", "theorem", "notation", "other"]
KIND_COLOURS = {
    "inductive": "#E45756",  # red: types
    "def": "#4C78A8",        # blue: definitions
    "theorem": "#54A24B",    # green: proofs
    "notation": "#F58518",   # orange: a paper's notation
    "other": "#DDDDDD",      # grey: imports, docs, directives
}
KIND_LABELS = {
    "inductive": "types",
    "def": "definitions",
    "theorem": "theorems",
    "notation": "notation",
    "other": "other",
}

# The declaration keywords, and the kind each is counted as. imprimatur's own
# commands (latex_notation, latex_entry, ...) declare a paper's notation.
KIND_MERGE = {
    "inductive": "inductive",
    "structure": "inductive",
    "class": "inductive",
    "def": "def",
    "abbrev": "def",
    "instance": "def",
    "opaque": "def",
    "theorem": "theorem",
    "lemma": "theorem",
    "axiom": "theorem",
}

# A top-level declaration: attributes, a doc comment's end, modifiers, then
# the keyword, all at the start of a line.
_DECL_RE = re.compile(
    r"^(?:@\[.*?\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(" + "|".join(KIND_MERGE) + r"|latex_[a-z_]+)\b"
)


def _check_coverage() -> None:
    """Every .lean file under ROOTS is bucketed or excluded, and every
    bucketed file exists; fail otherwise, so a new file cannot silently drop
    out of the chart, nor a renamed one leave a stale entry."""
    listed = [p for _, paths in FILES for p in paths]
    on_disk = {
        str(p.relative_to(ROOT))
        for r in ROOTS
        for p in (ROOT / r).rglob("*.lean")
        if ".lake" not in p.parts
    }
    dupes = sorted({p for p in listed if listed.count(p) > 1})
    unbucketed = sorted(
        rel for rel in on_disk
        if rel not in listed and not any(rel == e or rel.startswith(e) for e in EXCLUDED)
    )
    stale = sorted(set(listed) - on_disk)
    for rel in dupes:
        print(f"✖ in more than one bucket: {rel}")
    for rel in unbucketed:
        print(f"✖ not in any bucket (add it to FILES or EXCLUDED): {rel}")
    for rel in stale:
        print(f"✖ bucketed but not on disk (renamed or deleted?): {rel}")
    if dupes or unbucketed or stale:
        raise SystemExit(1)


# A character literal: 'c', or an escape such as '\n', '\\', '\x41', '\u{2200}'.
_CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")


def _strip_comments_and_strings(text: str) -> str:
    """Blank out comments and string literals, keeping line breaks, so that a
    `sorry` or a declaration keyword in a comment or a message is not
    counted. Block comments nest; a raw string r"..." has no escapes."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif c == "'" and (m := _CHAR_RE.match(text, i)) and not (
                i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_'!?")):
            out.append("' '")
            i = m.end()
        elif c == '"':
            raw = i > 0 and text[i - 1] == "r"
            i += 1
            out.append('"')
            while i < n and text[i] != '"':
                step = 2 if text[i] == "\\" and not raw else 1
                out.extend("\n" if ch == "\n" else " " for ch in text[i:i + step])
                i += step
            i += 1
            out.append('"')
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _count_sorrys(text: str) -> int:
    return len(re.findall(r"\bsorry\b", _strip_comments_and_strings(text)))


def _line_kinds(text: str) -> list[str]:
    """The kind of each line: that of the declaration whose span holds it."""
    lines = _strip_comments_and_strings(text).split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    assert len(lines) == len(text.splitlines()), "stripping changed the lines"
    kinds = ["other"] * len(lines)
    starts = [
        (i, KIND_MERGE.get(m.group(1), "notation"))
        for i, line in enumerate(lines)
        if (m := _DECL_RE.match(line))
    ]
    for j, (start, kind) in enumerate(starts):
        end = starts[j + 1][0] if j + 1 < len(starts) else len(lines)
        for ln in range(start, end):
            kinds[ln] = kind
    return kinds


def main() -> None:
    _check_coverage()

    labels = [name for name, _ in FILES]
    counts: dict[str, list[int]] = {k: [] for k in KIND_ORDER}
    totals: list[int] = []
    sorrys: list[int] = []
    for _, paths in FILES:
        bucket: dict[str, int] = defaultdict(int)
        bucket_sorrys = 0
        for rel in paths:
            text = (ROOT / rel).read_text()
            for kind in _line_kinds(text):
                bucket[kind] += 1
            bucket_sorrys += _count_sorrys(text)
        for k in KIND_ORDER:
            counts[k].append(bucket[k])
        totals.append(sum(bucket.values()))
        sorrys.append(bucket_sorrys)

    # --- the chart -------------------------------------------------------------
    plt.rcParams.update({"font.size": 8, "font.family": "serif"})
    fig, ax = plt.subplots(figsize=(7.0, 3.4))
    x = list(range(len(labels)))
    bottom = [0] * len(labels)
    for kind in KIND_ORDER:
        values = counts[kind]
        bars = ax.bar(x, values, bottom=bottom, color=KIND_COLOURS[kind],
                      edgecolor="white", linewidth=0.5, width=0.7)
        for bar, val in zip(bars, values):
            if val >= 120:
                ax.text(bar.get_x() + bar.get_width() / 2,
                        bar.get_y() + bar.get_height() / 2, str(val),
                        ha="center", va="center", fontsize=6, color="#222222")
        bottom = [b + v for b, v in zip(bottom, values)]

    top = max(totals)
    for i, total in enumerate(totals):
        ax.text(i, total + top * 0.01, f"{total:,}", ha="center", va="bottom",
                fontsize=7, fontweight="bold")
        if sorrys[i]:
            ax.text(i, total + top * 0.07, f"{sorrys[i]} sorry", ha="center",
                    va="bottom", fontsize=6, fontweight="bold",
                    color=KIND_COLOURS["inductive"])

    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=40, ha="right", rotation_mode="anchor",
                       fontsize=7)
    ax.set_ylabel("Lines of Lean")
    ax.set_ylim(0, top * 1.08)
    ax.spines[["top", "right"]].set_visible(False)
    ax.legend(handles=[Patch(color=KIND_COLOURS[k],
                             label=f"{KIND_LABELS[k]} ({sum(counts[k]):,})")
                       for k in reversed(KIND_ORDER)],
              loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=len(KIND_ORDER),
              frameon=False, fontsize=7)
    # The total above the legend, which sits just above the axes.
    n_files = sum(len(p) for _, p in FILES)
    ax.set_title(f"{sum(totals):,} lines of Lean in {n_files} files",
                 fontsize=9, fontweight="bold", pad=20)
    fig.tight_layout()
    # No timestamp, and no software version in the metadata: the same sources
    # give the same file, so a rebuild changes nothing to commit.
    fig.savefig(OUT, dpi=300, metadata={"Software": None})

    print(f"{sum(totals):,} lines in {n_files} files; "
          f"{sum(sorrys)} sorry; saved to {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
