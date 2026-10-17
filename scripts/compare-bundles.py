#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""The cross-toolchain check (PLAN §2.1): bundles produced from the same
fixture on different toolchains must be byte-identical apart from the
`producer` field.

    compare-bundles.py DIR

DIR holds one subdirectory per toolchain (as the CI job downloads them), each
with the same set of `*.bundle.json` files.
"""
import json
import pathlib
import sys


def canonical(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    data.pop("producer", None)
    return json.dumps(data, sort_keys=True, ensure_ascii=False, indent=1)


def main():
    root = pathlib.Path(sys.argv[1])
    runs = sorted(d for d in root.iterdir() if d.is_dir()) if root.exists() else []
    if len(runs) < 2:
        print(f"compare-bundles: {len(runs)} toolchain(s) with bundles; nothing to compare yet")
        return 0
    base, errors = runs[0], 0
    names = {p.relative_to(base) for p in base.glob("**/*.bundle.json")}
    for other in runs[1:]:
        other_names = {p.relative_to(other) for p in other.glob("**/*.bundle.json")}
        for missing in sorted(names ^ other_names):
            print(f"{missing}: present for only one of {base.name}, {other.name}", file=sys.stderr)
            errors += 1
        for name in sorted(names & other_names):
            if canonical(base / name) != canonical(other / name):
                print(f"{name}: differs between {base.name} and {other.name}", file=sys.stderr)
                errors += 1
    print(f"compare-bundles: {len(names)} bundle(s) across {len(runs)} toolchains")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
