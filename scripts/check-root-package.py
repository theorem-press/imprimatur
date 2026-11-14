#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""lint/root-package: the root lakefile.toml is the extractor's.

The repository is a Lake package at its root so that Reservoir lists it and a
`require` without a `subDir` gets the extractor (DESIGN §5, §19). The root
lakefile.toml must declare what extract/lakefile.toml declares, read from
extract/: every setting of extract/lakefile.toml appears in the root's, and
the root adds only its metadata (description, keywords, homepage, license,
licenseFiles, readmeFile) and `srcDir = "extract"`. It has no [[require]]
(DESIGN §4, constraint 6), and its lean-toolchain is extract/'s.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
METADATA = ("description", "keywords", "homepage", "license", "licenseFiles", "readmeFile")


def settings(path):
    """The lines of a lakefile.toml that say something: no comments, no blanks."""
    out = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip() if not line.strip().startswith('"') else line.strip()
        if line:
            out.append(line)
    return out


def main():
    errors = []
    root = settings(ROOT / "lakefile.toml")
    extract = settings(ROOT / "extract" / "lakefile.toml")
    for line in extract:
        if line not in root:
            errors.append(f"extract/lakefile.toml has `{line}`, which the root lakefile.toml lacks")
    for line in root:
        if line in extract:
            continue
        if line == 'srcDir = "extract"' or line.split("=", 1)[0].strip() in METADATA:
            continue
        errors.append(f"lakefile.toml has `{line}`, which is neither extract/'s nor metadata")
    if root.count('srcDir = "extract"') != sum(1 for l in root if l in ("[[lean_lib]]", "[[lean_exe]]")):
        errors.append("every [[lean_lib]] and [[lean_exe]] of the root lakefile.toml needs `srcDir = \"extract\"`")
    if "[[require]]" in root:
        errors.append("the root lakefile.toml must not have [[require]] (DESIGN §4, constraint 6)")
    for f in ("lean-toolchain",):
        if (ROOT / f).read_text() != (ROOT / "extract" / f).read_text():
            errors.append(f"{f} differs from extract/{f}")
    for e in errors:
        print(f"lint/root-package: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
