#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Real-world integration (PLAN §2.1): run locally and before every release,
# not in CI. Host projects are found next to this repository, or through
# LLMBDA_ROOT (and, from M2, PLANET_ROOT and MATH_ROOT).
#
# M1: llmbda's oopsla2027/paper.tex goes through `scan` and `strip` without a
# byte outside its blocks changing (PLAN M1, "done when").
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
LLMBDA_ROOT=${LLMBDA_ROOT:-$ROOT/../llmbda}
SPLICE="$ROOT/splice/.lake/build/bin/imprimatur-splice"
(cd splice && lake build -q imprimatur-splice)

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

echo "== integration/llmbda-scan-strip: scan and strip llmbda's oopsla2027/paper.tex"
if [ ! -f "$LLMBDA_ROOT/oopsla2027/paper.tex" ]; then
  echo "llmbda not found at $LLMBDA_ROOT (set LLMBDA_ROOT)" >&2
  exit 1
fi
mkdir -p "$work/llmbda"
cp "$LLMBDA_ROOT"/oopsla2027/*.tex "$work/llmbda/"
cp scripts/integration/llmbda/imprimatur.toml "$work/llmbda/"
(cd "$work/llmbda" && "$SPLICE" scan -o requests.json)
python3 -c "import json,sys; r=json.load(open('$work/llmbda/requests.json'))['requests']; print(f'scan: {len(r)} keys requested')"
(cd "$work/llmbda" && "$SPLICE" strip -o stripped)
python3 scripts/integration/check_outside.py "$work/llmbda" "$work/llmbda/stripped" \
  leangrammar leanrules leantheorem leancorollary leanlemma leandef leanconventions leantranslation
echo "integration: passed"
