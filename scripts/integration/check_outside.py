#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Check that `imprimatur-splice strip` kept every byte outside the blocks.

    check_outside.py ORIGINAL_DIR STRIPPED_DIR ENV [ENV ...]

Blocks are found by this script's own scanner, independently of the splicer:
`\\begin{ENV}` to `\\end{ENV}`, skipping comments and `\\verb`. An ENV
written `%NAME` is a comment-delimited alias: `%NAME{…}` to `%ENDNAME`. No block may
remain in the stripped files, and the text between blocks must appear in the stripped files in order. Whitespace at the
edges of each such segment is ignored, because strip removes the lines that
held only a block's markers.
"""
import pathlib
import re
import sys


def blocks(text, envs):
    spans, i, n = [], 0, len(text)
    comments = [e[1:] for e in envs if e.startswith("%")]
    envs = [e for e in envs if not e.startswith("%")]
    begin = re.compile(r"\\begin\{(" + "|".join(map(re.escape, envs)) + r")\}")
    marker = re.compile(r"%(" + "|".join(map(re.escape, comments)) + r")[\[{]") if comments else None
    while i < n:
        c = text[i]
        m = marker.match(text, i) if c == "%" and marker else None
        if m:
            end = "%END" + m.group(1)
            j = text.find(end, m.end())
            if j < 0:
                raise SystemExit(f"unclosed %{m.group(1)} at offset {i}")
            spans.append((i, j + len(end)))
            i = j + len(end)
        elif c == "%":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("\\verb", i) and not text[i + 5:i + 6].isalpha():
            d = text[i + 5] if text[i + 5] != "*" else text[i + 6]
            k = i + 6 if text[i + 5] != "*" else i + 7
            j = text.find(d, k)
            i = n if j < 0 else j + 1
        elif c == "\\":
            m = begin.match(text, i)
            if m:
                end = "\\end{" + m.group(1) + "}"
                j = text.find(end, m.end())
                if j < 0:
                    raise SystemExit(f"unclosed {m.group(0)} at offset {i}")
                spans.append((i, j + len(end)))
                i = j + len(end)
            else:
                i += 2
        else:
            i += 1
    return spans


def main():
    orig, stripped, envs = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3:]
    total_blocks = total_bytes = 0
    for out in sorted(stripped.rglob("*.tex")):
        rel = out.relative_to(stripped)
        text = (orig / rel).read_text(encoding="utf-8")
        result = out.read_text(encoding="utf-8")
        spans = blocks(text, envs)
        total_blocks += len(spans)
        left = blocks(result, envs)
        if left:
            raise SystemExit(f"{rel}: strip left {len(left)} block(s), the first at offset {left[0][0]}")
        pos, prev = 0, 0
        for a, b in spans + [(len(text), len(text))]:
            seg = text[prev:a].strip(" \t\n")
            total_bytes += len(seg)
            j = result.find(seg, pos)
            if j < 0:
                raise SystemExit(f"{rel}: text before offset {a} was changed by strip:\n{seg[:200]!r}")
            pos, prev = j + len(seg), b
    print(f"check_outside: {total_blocks} blocks; {total_bytes} bytes outside them kept, in order")


if __name__ == "__main__":
    main()
