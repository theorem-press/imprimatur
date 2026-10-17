#!/usr/bin/env python3
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
"""lint/bundle-schema: validate every golden bundle (`*.bundle.json` under extract/test,
splice/test and test/) against schema/bundle.schema.json. Needs the
`jsonschema` package, which is a test-only dependency."""
import json
import pathlib
import sys

import jsonschema

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main():
    schema = json.loads((ROOT / "schema" / "bundle.schema.json").read_text(encoding="utf-8"))
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    bundles = [p for d in ["extract/test", "splice/test", "test"]
               for p in (ROOT / d).glob("**/*.bundle.json") if ".lake" not in p.parts]
    errors = 0
    for path in bundles:
        for err in validator.iter_errors(json.loads(path.read_text(encoding="utf-8"))):
            print(f"{path.relative_to(ROOT)}: {err.json_path}: {err.message}", file=sys.stderr)
            errors += 1
    print(f"bundles: {len(bundles)} checked against the schema")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
