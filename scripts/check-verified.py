#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""lint/verified: the splicer's verified code stays provable.

The theorems about the splicer (docs/verified-splicer.md) are about the code
in splice/Splice/Core and splice/SpliceModel, and those about the extractor's
layouts and emitter (docs/verified-extractor.md) about the shared module in
bundle/. That code must not use what a proof can't see into, or what would make a theorem hollow: `partial`,
`while` and `repeat` (whose loops are opaque), `unsafe`, `implemented_by`
and `@[extern]` (which replace a definition by unproved code), `!` indexing
(which can panic), and `sorry` or `native_decide` (which prove nothing, or
trust the compiler). Comments and string literals are ignored.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIRS = [ROOT / "splice" / "Splice" / "Core", ROOT / "splice" / "SpliceModel"]
FILES = [ROOT / "bundle" / "Layout.lean", ROOT / "bundle" / "ReadBack.lean"]
FORBIDDEN = [
    (r"\bpartial\b", "partial"), (r"\bwhile\b", "while"), (r"\brepeat\b", "repeat"),
    (r"\bunsafe\b", "unsafe"), (r"\bimplemented_by\b", "implemented_by"),
    (r"@\[\s*extern\b", "@[extern]"), (r"\]!", "! indexing"), (r"\bsorry\b", "sorry"),
    (r"\bnative_decide\b", "native_decide"),
]


def strip(text):
    """The text with comments and string literals blanked, keeping lines."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text.startswith("/-", i):
            depth += 1; out.append("  "); i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('"' + "".join("\n" if c == "\n" else " " for c in text[i + 1:j]) + '"'); i = j + 1
        elif text[i] == "'" and i + 2 < n and (text[i + 2] == "'" or text[i + 1] == "\\"):
            j = text.find("'", i + 1 + (text[i + 1] == "\\"))
            out.append(" " * (j - i + 1)); i = j + 1
        else:
            out.append(text[i]); i += 1
    return "".join(out)


def main():
    errors = []
    paths = [p for d in DIRS for p in sorted(d.glob("**/*.lean"))] + FILES
    if True:
        for path in paths:
            for lineno, line in enumerate(strip(path.read_text(encoding="utf-8")).splitlines(), 1):
                for pat, what in FORBIDDEN:
                    if re.search(pat, line):
                        errors.append(f"lint/verified: {path.relative_to(ROOT)}:{lineno}: "
                                      f"the verified code must not use {what}")
    for e in errors:
        print(e, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
