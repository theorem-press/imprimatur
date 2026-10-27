#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# End-to-end tests (docs/TESTING.md, Layers). For each project under examples/:
#   1. copy it to e2e-out/ (the same depth, so its relative paths still work);
#   2. run its steps (examples/X/steps, or `imprimatur build` then
#      `imprimatur check`), which must all succeed;
#   3. compare the spliced paper.tex with examples/X/expected/paper.tex;
#   4. compile with pdflatex and with lualatex (latexmk); fail on errors,
#      undefined control sequences or missing glyphs;
#   5. compare pdftotext's output (in content order) with examples/X/expected/{pdflatex,lualatex}.txt.
# UPDATE_GOLDEN=1 rewrites the expected files; review the diff.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD
export TEXINPUTS="$ROOT/tex//:"
(cd splice && lake build -q imprimatur)
IMPRIMATUR="$ROOT/splice/.lake/build/bin/imprimatur"
status=0

compare() {  # compare GOT EXPECTED-FILE NAME [loose]
  # With "loose", spaces within lines are ignored: pdftotext versions differ
  # in where they put spaces (`(m + n )` against `(m + n)`).
  local got=$1 want=$2 name=$3 loose=${4:-}
  local opts=-u
  [ "$loose" = loose ] && opts="-u --ignore-all-space"
  if [ "${UPDATE_GOLDEN:-}" = 1 ]; then
    mkdir -p "$(dirname "$want")"
    if ! cmp -s "$got" "$want" 2>/dev/null; then cp "$got" "$want"; echo "  updated $want"; fi
  elif ! diff $opts "$want" "$got" > "$got.diff" 2>&1; then
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
TESTS=(e2e/external e2e/minimal e2e/semantics e2e/sidecar)
# And three tests that are not examples: e2e/show, e2e/fixture-views and e2e/about, below.

# External mode needs an extractor built for the examples' toolchain. It goes in
# a cache inside e2e-out, so the run touches nothing outside the repository.
export IMPRIMATUR_CACHE="$ROOT/e2e-out/cache"
mkdir -p e2e-out
echo "== installing the extractor for external mode"
"$IMPRIMATUR" toolchain install "$(sed 's/.*://' examples/external/host/lean-toolchain)" | sed 's/^/  /' 
shopt -s nullglob
for dir in examples/*/; do
  ex=$(basename "$dir")
  if [[ ! " ${TESTS[*]} " =~ " e2e/$ex " ]]; then
    echo "e2e: examples/$ex has no test name in TESTS (scripts/e2e.sh)" >&2; status=1; continue
  fi
  echo "== e2e/$ex"
  work="e2e-out/$ex"
  rm -rf "$work"; mkdir -p "$work"
  (cd "$dir" && tar --exclude=.lake --exclude=expected --exclude=steps -cf - .) | (cd "$work" && tar -xf -)
  # The steps: examples/X/steps if there is one (a line starting with ! is a
  # shell command), else `build` then `check`. Every step must succeed.
  steps=$(if [ -f "$dir/steps" ]; then grep -v '^#' "$dir/steps"; else printf 'build\ncheck\n'; fi)
  # In external mode the host must not change (DESIGN §4, constraint 5):
  # fingerprint its files, apart from its build directory, before and after.
  host=""
  if grep -q 'mode = "external"' "$work/imprimatur.toml"; then
    host="$work/$(sed -n 's/^lean_project = "\(.*\)"/\1/p' "$work/imprimatur.toml")"
    fingerprint() { (cd "$host" && find . -path ./.lake -prune -o -type f -print | sort | xargs sha256sum); }
    before=$(fingerprint)
  fi
  failed=0
  while IFS= read -r step; do
    [ -z "$step" ] && continue
    if [[ $step == !* ]]; then cmd=(bash -c "${step#!}"); else read -ra words <<< "$step"; cmd=("$IMPRIMATUR" "${words[@]}"); fi
    if ! (cd "$work" && "${cmd[@]}" > step.log 2>&1); then
      echo "  FAIL: $step"; sed 's/^/    /' "$work/step.log"; status=1; failed=1; break
    fi
    # A shell step stands for the host's owners (building it, say), so the
    # host is fingerprinted again after it: only imprimatur's steps are judged.
    if [ -n "$host" ] && [[ $step == !* ]]; then before=$(fingerprint); fi
  done <<< "$steps"
  [ $failed = 1 ] && continue
  if [ -n "$host" ] && [ "$(fingerprint)" != "$before" ]; then
    echo "  FAIL: external mode changed the host project"; status=1
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
    # -raw keeps the text in the order TeX wrote it. Without it, pdftotext
    # guesses a reading order from the layout, and versions guess differently
    # (poppler 24 reorders a grammar's description column; poppler 22 doesn't).
    # The crop leaves out the page numbers (at 696pt on A4, below the text
    # block, which ends by 675pt): engines write them at different points in
    # the content stream, so in raw order they move about.
    pdftotext -raw -x 0 -y 0 -W 600 -H 685 "$work/out-$engine/paper.pdf" - | normalise > "$work/$engine.txt"
    compare "$work/$engine.txt" "$dir/expected/$engine.txt" "$engine text" loose
  done
done
# e2e/show: `imprimatur show` on the semantics example as built above. It
# prints the views the document uses for a key, with their problems, and
# fails on a key that does not exist; it writes nothing to the paper.
echo "== e2e/show"
if [ -d e2e-out/semantics ]; then
  before=$(sha256sum e2e-out/semantics/paper.tex)
  (cd e2e-out/semantics && "$IMPRIMATUR" show Preservation > show.txt 2>&1) || { echo "  FAIL: show Preservation"; status=1; }
  compare e2e-out/semantics/show.txt examples/semantics/expected/show.txt "show output"
  if (cd e2e-out/semantics && "$IMPRIMATUR" show Stlc.nonesuch > /dev/null 2>&1); then
    echo "  FAIL: show of a missing key succeeded"; status=1
  fi
  [ "$(sha256sum e2e-out/semantics/paper.tex)" = "$before" ] || { echo "  FAIL: show changed the paper"; status=1; }
fi
# e2e/fixture-views: every math, prose, rules and grammar view of the
# Notation and Semantics fixtures' golden bundles typesets with both engines.
echo "== e2e/fixture-views"
views="e2e-out/fixture-views"; rm -rf "$views"; mkdir -p "$views"
python3 - "$views/paper.tex" extract/test/golden/Notation.bundle.json extract/test/golden/Semantics.bundle.json <<'PY'
import json, sys
out = [r"\documentclass{article}", r"\usepackage{amsthm}", r"\usepackage{mathpartir}",
       r"\usepackage{imprimatur}", r"\newcommand\lub[1]{\bigsqcup\{#1\}}",
       r"\newcommand\val{v}", r"\newcommand\rulelabel[2]{}", r"\begin{document}"]
for path in sys.argv[2:]:
    for key, e in sorted(json.load(open(path))["entries"].items()):
        for view in sorted(e["views"]):
            if view.startswith(("math", "prose", "rules", "grammar")):
                out.append(r"\paragraph{%s, %s.}" % (key.replace("_", r"\_"), view.replace("_", r"\_").replace("|", "/")))
                out.append(e["views"][view])
out.append(r"\end{document}")
open(sys.argv[1], "w").write("\n".join(out) + "\n")
PY
for engine in pdflatex lualatex; do
  flag=$([ $engine = pdflatex ] && echo -pdf || echo -lualatex)
  if ! (cd "$views" && latexmk $flag -interaction=nonstopmode -halt-on-error -outdir=out-$engine paper.tex > latexmk-$engine.log 2>&1); then
    echo "  FAIL: $engine"; grep -A3 '^!' "$views/out-$engine/paper.log" | head -20 | sed 's/^/    /'; status=1
  elif grep -E 'Undefined control sequence|Missing character' "$views/out-$engine/paper.log" > /dev/null; then
    echo "  FAIL: $engine log has undefined macros or missing glyphs"; status=1
  fi
done

# e2e/about: the paper about imprimatur (about/), whose theorems are proved in
# the splicer's model (splice/SpliceModel). The committed paper must be what `build`
# makes, `check` must report nothing at all (warnings included: every formula
# reads back), and it must typeset.
echo "== e2e/about"
work="e2e-out/about"; rm -rf "$work"; mkdir -p "$work"
# The paper's Lean requires the splice package at ../../splice.
ln -sfn "$ROOT/splice" e2e-out/splice
(cd about && tar --exclude=.lake --exclude=.imprimatur --exclude=imprimatur-paper.pdf --exclude='*.aux' \
  --exclude='*.log' --exclude='*.fls' --exclude='*.fdb_latexmk' -cf - .) | (cd "$work" && tar -xf -)
if ! (cd "$work/lean" && lake build -q > ../lake.log 2>&1); then
  echo "  FAIL: the Lean model does not build"; sed 's/^/    /' "$work/lake.log"; status=1
elif ! (cd "$work" && "$IMPRIMATUR" build > build.log 2>&1 && "$IMPRIMATUR" check > check.log 2>&1); then
  echo "  FAIL: build or check"; cat "$work"/build.log "$work"/check.log 2>/dev/null | sed 's/^/    /'; status=1
elif ! grep -q "check: 0 stale, 0 errors, 0 warnings" "$work/check.log"; then
  echo "  FAIL: check reports something"; sed 's/^/    /' "$work/check.log"; status=1
else
  compare "$work/imprimatur-paper.tex" about/imprimatur-paper.tex "the built paper"
  if ! (cd "$work" && TEXINPUTS="$ROOT/tex//:" latexmk -pdf -interaction=nonstopmode -halt-on-error imprimatur-paper.tex > latexmk.log 2>&1); then
    echo "  FAIL: the paper does not typeset"; status=1
    grep -a -A3 '^!' "$work/imprimatur-paper.log" 2>/dev/null | sed 's/^/    /' | head -40
    tail -5 "$work/latexmk.log" | sed 's/^/    /'
  fi
fi

[ $status = 0 ] && echo "e2e: all examples passed"
exit $status
