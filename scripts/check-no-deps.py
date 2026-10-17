#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""Dependency rules of the shipped packages.

lint/no-deps: the shipped packages have no Lake dependencies (DESIGN §4,
constraint 6), so they can't shift a host project's pins.

lint/splice-imports: the splicer uses nothing from Lean but its JSON library
(DESIGN §4, constraint 2), so it stays independent of Lean's internals.
"""
import re
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SHIPPED = ["extract", "splice"]


def main():
    errors = []
    for pkg in SHIPPED:
        d = ROOT / pkg
        if (d / "lakefile.lean").exists():
            errors.append(f"{pkg}: use lakefile.toml, so that this check can read it")
        text = (d / "lakefile.toml").read_text(encoding="utf-8")
        if "[[require]]" in text:
            errors.append(f"{pkg}/lakefile.toml: shipped packages must not have [[require]]")
    for path in sorted((ROOT / "splice").glob("**/*.lean")):
        if ".lake" in path.parts or "test" in path.relative_to(ROOT / "splice").parts:
            continue
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            m = re.match(r"^(?:public )?import (?:all )?(\S+)", line)
            if m and not (m.group(1) == "Splice" or m.group(1).startswith("Splice.")
                          or m.group(1).startswith("Lean.Data.Json")):
                errors.append(f"lint/splice-imports: {path.relative_to(ROOT)}:{lineno}: "
                              f"the splicer may import only Splice.* and Lean.Data.Json, not {m.group(1)}")
    for e in errors:
        print(e if e.startswith("lint/") else f"lint/no-deps: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
