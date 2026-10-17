#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# End-to-end tests (PLAN §2.1). For each project under examples/:
#   1. copy it to e2e-out/ (the same depth, so its relative paths still work);
#   2. `imprimatur build`, then `imprimatur check`, which must pass;
#   3. compare the spliced paper.tex with examples/X/expected/paper.tex;
#   4. compile with pdflatex and with lualatex (latexmk); fail on errors,
#      undefined control sequences or missing glyphs;
#   5. compare pdftotext's output with examples/X/expected/{pdflatex,lualatex}.txt.
# UPDATE_GOLDEN=1 rewrites the expected files; review the diff.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
export TEXINPUTS="$ROOT/tex//:"
(cd splice && lake build -q imprimatur)
IMPRIMATUR="$ROOT/splice/.lake/build/bin/imprimatur"
status=0

compare() {  # compare GOT EXPECTED-FILE NAME
  local got=$1 want=$2 name=$3
  if [ "${UPDATE_GOLDEN:-}" = 1 ]; then
    mkdir -p "$(dirname "$want")"
    if ! cmp -s "$got" "$want" 2>/dev/null; then cp "$got" "$want"; echo "  updated $want"; fi
  elif ! diff -u "$want" "$got" > "$got.diff" 2>&1; then
    echo "  FAIL: $name differs from $want:"; head -40 "$got.diff" | sed 's/^/    /'
    status=1
  fi
}

normalise() {  # pdftotext output, independent of small TeX differences
  sed -e 's/ﬁ/fi/g; s/ﬂ/fl/g; s/ﬀ/ff/g; s/ﬃ/ffi/g; s/ﬄ/ffl/g' -e 's/[[:space:]]*$//' \
    | tr -d '\f' | cat -s
}

# One test per example, named so docs/TESTING.md can refer to it. An example
# without a name here is an error, so none is skipped by accident.
TESTS=(e2e/minimal e2e/sidecar)
shopt -s nullglob
for dir in examples/*/; do
  ex=$(basename "$dir")
  if [[ ! " ${TESTS[*]} " =~ " e2e/$ex " ]]; then
    echo "e2e: examples/$ex has no test name in TESTS (scripts/e2e.sh)" >&2; status=1; continue
  fi
  echo "== e2e/$ex"
  work="e2e-out/$ex"
  rm -rf "$work"; mkdir -p "$work"
  (cd "$dir" && tar --exclude=.lake --exclude=expected -cf - .) | (cd "$work" && tar -xf -)
  if ! (cd "$work" && "$IMPRIMATUR" build > build.log 2>&1); then
    echo "  FAIL: imprimatur build"; sed 's/^/    /' "$work/build.log"; status=1; continue
  fi
  if ! (cd "$work" && "$IMPRIMATUR" check > check.log 2>&1); then
    echo "  FAIL: imprimatur check after build"; sed 's/^/    /' "$work/check.log"; status=1
  fi
  compare "$work/paper.tex" "$dir/expected/paper.tex" "spliced paper.tex"
  for engine in pdflatex lualatex; do
    flag=$([ $engine = pdflatex ] && echo -pdf || echo -lualatex)
    if ! (cd "$work" && latexmk $flag -interaction=nonstopmode -halt-on-error -outdir=out-$engine paper.tex > latexmk-$engine.log 2>&1); then
      echo "  FAIL: $engine"; grep -A3 '^!' "$work/out-$engine/paper.log" | head -20 | sed 's/^/    /'; status=1; continue
    fi
    if grep -E 'Undefined control sequence|Missing character' "$work/out-$engine/paper.log" > /dev/null; then
      echo "  FAIL: $engine log has undefined macros or missing glyphs"
      grep -E 'Undefined control sequence|Missing character' "$work/out-$engine/paper.log" | head | sed 's/^/    /'
      status=1
    fi
    pdftotext "$work/out-$engine/paper.pdf" - | normalise > "$work/$engine.txt"
    compare "$work/$engine.txt" "$dir/expected/$engine.txt" "$engine text"
  done
done
[ $status = 0 ] && echo "e2e: all examples passed"
exit $status
