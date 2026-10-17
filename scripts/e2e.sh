#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# End-to-end tests (PLAN §2.1): `imprimatur build` on each project under
# examples/, in each mode, then latexmk with pdflatex and lualatex, then a
# comparison of pdftotext output with golden text. M2 adds the first example;
# until then there is nothing to run.
set -euo pipefail
cd "$(dirname "$0")/.."
shopt -s nullglob
examples=(examples/*/)
if [ ${#examples[@]} -eq 0 ]; then
  echo "e2e: no examples yet (M2 adds examples/minimal)"
  exit 0
fi
echo "e2e: examples exist but the runner isn't written yet" >&2
exit 1
