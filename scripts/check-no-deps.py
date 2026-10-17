#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""lint/no-deps: the shipped packages have no Lake dependencies (DESIGN §4,
constraint 6), so they can't shift a host project's pins."""
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
    for e in errors:
        print(f"lint/no-deps: {e}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
