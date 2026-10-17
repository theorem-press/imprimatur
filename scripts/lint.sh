#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The checks of the `lint` CI job (PLAN §2.5). Needs python3 with the
# `jsonschema` package (pip install -r scripts/requirements-test.txt).
set -euo pipefail
cd "$(dirname "$0")/.."
status=0
python3 scripts/check-links.py || status=1
python3 scripts/check-no-deps.py || status=1
python3 scripts/check-traceability.py || status=1
python3 scripts/check-bundles.py || status=1
exit $status
