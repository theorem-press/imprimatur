#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Check the traceability matrix in docs/TESTING.md (CONTRIBUTING.md, principle 1).

Fails if a numbered section of DESIGN.md has no row, if a row names a section
that DESIGN.md doesn't have, or if a row names a test that no test source
defines. A test is defined when its name appears as a double-quoted string in
a Lean test source, or as `lint/...`, `integration/...` or `e2e/...` in a
script under scripts/.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def design_sections():
    """Leaf section numbers of DESIGN.md: '1', '6.1', 'A', ..."""
    nums = []
    in_code = False
    for line in (ROOT / "DESIGN.md").read_text(encoding="utf-8").splitlines():
        if line.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        m = re.match(r"^(##|###) (?:Appendix )?([0-9]+(?:\.[0-9]+)?|[A-Z])\.? ", line)
        if m:
            nums.append(m.group(2))
    # A section with subsections is covered by its subsections.
    return {n for n in nums if not any(o.startswith(n + ".") for o in nums)}


def matrix_rows():
    rows = []
    text = (ROOT / "docs" / "TESTING.md").read_text(encoding="utf-8")
    for lineno, line in enumerate(text.splitlines(), 1):
        m = re.match(r"^\| D§([0-9A-Z.]+) \|(.*)\|(.*)\|(.*)\|$", line)
        if m:
            tests = re.findall(r"`([a-z0-9-]+/[a-z0-9/-]+)`", m.group(3))
            rows.append((lineno, m.group(1), tests, m.group(4).strip()))
    return rows


def defined_tests():
    names = set()
    for path in ROOT.glob("**/*.lean"):
        if ".lake" in path.parts or "fixtures" in path.parts:
            continue
        if "test" in path.parts or path.parts[-2:-1] == ("testkit",) or "testkit" in path.parts:
            names.update(re.findall(r'"([a-z0-9-]+/[a-z0-9/-]+)"', path.read_text(encoding="utf-8")))
    for path in (ROOT / "scripts").rglob("*"):
        if path.is_file():
            names.update(re.findall(r"\b((?:lint|integration|e2e)/[a-z0-9/-]+)", path.read_text(encoding="utf-8")))
    return names


def main():
    errors = []
    sections = design_sections()
    rows = matrix_rows()
    covered = {r[1] for r in rows}
    tests = defined_tests()
    for s in sorted(sections - covered):
        errors.append(f"DESIGN.md section {s} has no row in docs/TESTING.md")
    for lineno, sec, names, when in rows:
        if sec not in sections:
            errors.append(f"docs/TESTING.md:{lineno}: no section D§{sec} in DESIGN.md")
        for n in names:
            if n not in tests:
                errors.append(f"docs/TESTING.md:{lineno}: test {n} is not defined in any test source")
        if not re.match(r"^(M[0-6]( \(lint\))?|n/a)$", when):
            errors.append(f"docs/TESTING.md:{lineno}: bad milestone {when!r}")
    for e in errors:
        print(e, file=sys.stderr)
    tested = sum(1 for r in rows if r[2])
    print(f"traceability: {len(sections)} sections, {len(rows)} requirements, {tested} with tests")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
