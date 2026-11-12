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
# Every imprimatur step runs with --timing; the last build's and check's
# timing files are kept as e2e-out/X/timing-{build,check}.jsonl, and the end
# folds them to e2e-out/timing.jsonl, one line per paper (docs/ci-timing.md).
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

timed() {  # timed build|check|accept|show ARGS...: whether to add --timing
  case "$1" in build|check|accept|show) [[ " $* " != *" --timing "* ]] ;; *) false ;; esac
}
keep_timing() {  # keep_timing WORK COMMAND: a build's or a check's timing file, kept
  case "$2" in build|check) [ -f "$1/.imprimatur/timing.jsonl" ] && cp "$1/.imprimatur/timing.jsonl" "$1/timing-$2.jsonl" ;; esac
  return 0
}

# One test per example, named so docs/TESTING.md can refer to it. An example
# without a name here is an error, so none is skipped by accident.
TESTS=(e2e/external e2e/minimal e2e/semantics e2e/sidecar)
# And two tests that are not examples: e2e/show and e2e/fixture-views, below.

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
    if [[ $step == !* ]]; then cmd=(bash -c "${step#!}"); else read -ra words <<< "$step"; cmd=("$IMPRIMATUR" "${words[@]}"); timed "${words[@]}" && cmd+=(--timing); fi
    if ! (cd "$work" && "${cmd[@]}" > step.log 2>&1); then
      echo "  FAIL: $step"; sed 's/^/    /' "$work/step.log"; status=1; failed=1; break
    fi
    [[ $step != !* ]] && keep_timing "$work" "${words[0]}"
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
# e2e/checker: the verified checker (DESIGN §7.8) on the semantics example as
# built above. With [trust].checker set, `build` has con-leche accept the
# host and records it in the bundle; `check` passes with the verdict kept
# from the last run; `--no-checker` leaves the bundle without a verdict, and
# the splicer on its own then reports it unchecked. Skipped on a toolchain
# without con-leche.
echo "== e2e/checker"
if [ -d e2e-out/semantics ]; then
  work=e2e-out/checker
  rm -rf "$work"; cp -r e2e-out/semantics "$work"
  printf '\n[trust]\nchecker = "con-leche"\n' >> "$work/imprimatur.toml"
  if (cd "$work/host" && lake env con-leche --help > /dev/null 2>&1); then
    (cd "$work" && "$IMPRIMATUR" build --timing > build.log 2>&1) || { echo "  FAIL: build with the checker"; sed 's/^/    /' "$work/build.log"; status=1; }
    grep -q '^checker: con-leche: accepted' "$work/build.log" || { echo "  FAIL: build did not report con-leche's acceptance"; status=1; }
    grep -q '"verdict": "accepted"' "$work/.imprimatur/bundle.json" || { echo "  FAIL: the bundle has no accepted verdict"; status=1; }
    (cd "$work" && "$IMPRIMATUR" check --timing > check.log 2>&1) || { echo "  FAIL: check with the checker"; sed 's/^/    /' "$work/check.log"; status=1; }
    grep -q 'the verdict kept from the last run' "$work/check.log" || { echo "  FAIL: check did not reuse the kept verdict"; status=1; }
    (cd "$work" && "$IMPRIMATUR" build --no-checker > nocheck.log 2>&1) || { echo "  FAIL: build --no-checker"; status=1; }
    if grep -q '"checker"' "$work/.imprimatur/bundle.json"; then echo "  FAIL: --no-checker left a verdict in the bundle"; status=1; fi
    (cd "$work" && "$IMPRIMATUR" check --no-checker > nocheck.log 2>&1) || { echo "  FAIL: check --no-checker"; sed 's/^/    /' "$work/nocheck.log"; status=1; }
    if (cd "$work" && "$IMPRIMATUR" check --bundle .imprimatur/bundle.json > unchecked.log 2>&1); then
      echo "  FAIL: check passed without a verdict"; status=1
    elif ! grep -q 'error\[unchecked\]' "$work/unchecked.log"; then
      echo "  FAIL: check without a verdict did not report unchecked"; sed 's/^/    /' "$work/unchecked.log"; status=1
    fi
  else
    echo "  SKIP: the toolchain has no con-leche"
  fi
fi
# e2e/con-leche: papers/con-leche (23 entries, the verified checker on its
# own development) built for its time, the largest paper in this repository
# (docs/ci-timing.md). Its check reports three `untrusted` errors by design
# (#109: subjects, not results), so only `build` must succeed and `check`
# must find nothing stale. Skipped unless con-leche is checked out beside
# this repository and its modules are built (papers/con-leche/README.md).
echo "== e2e/con-leche"
cl_host="$ROOT/../con-leche"
if [ -f "$cl_host/.lake/build/lib/lean/ConLeche/MainTheorem.olean" ] && (cd "$cl_host" && lake env con-leche --help > /dev/null 2>&1); then
  work=e2e-out/con-leche
  rm -rf "$work"; mkdir -p "$work"
  (cd papers/con-leche && tar --exclude=out --exclude='*.pdf' --exclude='*.aux' --exclude='*.log' --exclude='*.fls' --exclude='*.fdb_latexmk' --exclude='*.out' --exclude='*.synctex.gz' -cf - .) | (cd "$work" && tar -xf -)
  (cd "$work" && "$IMPRIMATUR" build --timing > build.log 2>&1) || { echo "  FAIL: build"; sed 's/^/    /' "$work/build.log"; status=1; }
  keep_timing "$work" build
  (cd "$work" && "$IMPRIMATUR" check --timing > check.log 2>&1) || true
  keep_timing "$work" check
  grep -q '^check: 0 stale,' "$work/check.log" || { echo "  FAIL: check after build found stale blocks"; tail -5 "$work/check.log" | sed 's/^/    /'; status=1; }
else
  echo "  SKIP: con-leche is not checked out and built beside this repository"
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

# The run time, one line per paper (docs/ci-timing.md): folded from the
# timing files kept above, and shown.
dirs=(); for d in e2e-out/*/; do [ -f "$d/timing-build.jsonl" ] && dirs+=("$d"); done
if [ ${#dirs[@]} -gt 0 ]; then
  echo "== timing"
  python3 scripts/timing-fold.py fold "${dirs[@]}" --out e2e-out/timing.jsonl
  python3 - e2e-out/timing.jsonl <<'PY' | sed 's/^/  /'
import json, sys
for l in open(sys.argv[1]):
    j = json.loads(l); m = j["ms"]
    print(f"{j['paper']:<12} build {m['total']/1000:6.2f} s  (load {m.get('load',0)/1000:.2f}, entries {m.get('entries',0)/1000:.2f}, export {m.get('export',0)/1000:.2f})"
          f"  {j.get('entries',0)} entries, {j.get('formulas',0)} formulas")
PY
fi

[ $status = 0 ] && echo "e2e: all examples passed"
exit $status
