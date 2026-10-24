#!/usr/bin/env bash
#
# Refresh imprimatur-paper.tex against its Lean development, then rebuild
# imprimatur-paper.pdf. The steps are the README's, and CI's (e2e/about in
# scripts/e2e.sh), run in place:
#
#   1. lake build in lean/: the running example and the paper's view of the
#      splicer's model (lean/ requires the splice package at ../splice).
#   2. imprimatur build: regenerate every Lean-derived block of the paper
#      IN PLACE, keeping the authors' text in slots. The configuration is
#      imprimatur.toml, the notation is in notation/.
#   3. imprimatur check: must report nothing at all, warnings included, as CI
#      requires (every formula reads back, no \leancheck has drifted).
#   4. latexmk: typeset it, with BibTeX (ACM-Reference-Format.bst is here).
#
# Set IMPRIMATUR to the imprimatur command if it is not on PATH; otherwise
# the splicer's own build, ../splice/.lake/build/bin/imprimatur, is used, and
# built if it is missing. The extractor is installed once with
#   imprimatur toolchain install v4.35.0
#
# A drift error from check means a statement that hand-written prose attests
# has changed: re-read the prose against the Lean, then
#   imprimatur accept KEY
#
# Usage:
#   ./refresh.sh              # refresh all generated blocks, check, rebuild PDF
#   ./refresh.sh --dry-run    # show what build would change; write nothing
#   ./refresh.sh --no-lean    # skip lake build (the Lean is already built)
#
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"

is_dry=0
no_lean=0
for a in "$@"; do
  case "$a" in
    --dry-run) is_dry=1 ;;
    --no-lean) no_lean=1 ;;
    -h|--help) sed -n '2,/^set -uo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
    *) echo "!! unknown option: $a (try --help)"; exit 2 ;;
  esac
done

# --- the imprimatur command ---------------------------------------------------
if [ -z "${IMPRIMATUR:-}" ]; then
  if command -v imprimatur > /dev/null; then
    IMPRIMATUR=imprimatur
  else
    IMPRIMATUR="$ROOT/splice/.lake/build/bin/imprimatur"
    if [ ! -x "$IMPRIMATUR" ]; then
      echo "== building the splicer (../splice) =="
      if ! (cd "$ROOT/splice" && lake build imprimatur); then
        echo "!! the splicer does not build"
        exit 1
      fi
    fi
  fi
fi
if ! command -v "$IMPRIMATUR" > /dev/null; then
  echo "!! imprimatur not found: $IMPRIMATUR (set IMPRIMATUR, or put it on PATH)"
  exit 1
fi

# --- 1. the Lean ----------------------------------------------------------------
if [ $no_lean -eq 0 ]; then
  echo "== lake build (lean/) =="
  LAKELOG="$HERE/.refresh-lake.log"
  if ! (cd "$HERE/lean" && lake build -q) > "$LAKELOG" 2>&1; then
    echo "!! the Lean does not build; full log: $LAKELOG"
    grep -aE '^(error|✖)' "$LAKELOG" | head -10 | sed 's/^/    /'
    exit 1
  fi
  rm -f "$LAKELOG"
fi

# --- 2. imprimatur build --------------------------------------------------------
if [ $is_dry -eq 1 ]; then
  echo "== dry run: what imprimatur build would change =="
  (cd "$HERE" && "$IMPRIMATUR" check --diff) || true
  exit 0
fi
echo "== imprimatur build: re-syncing the Lean-derived blocks =="
if ! (cd "$HERE" && "$IMPRIMATUR" build); then
  echo "!! imprimatur build failed (nothing written); see the messages above"
  exit 1
fi

# --- 3. imprimatur check --------------------------------------------------------
echo "== imprimatur check =="
CHECKLOG="$HERE/.refresh-check.log"
(cd "$HERE" && "$IMPRIMATUR" check) > "$CHECKLOG" 2>&1
check_rc=$?
cat "$CHECKLOG"
if [ $check_rc -ne 0 ] || ! grep -q "check: 0 stale, 0 errors, 0 warnings" "$CHECKLOG"; then
  echo "!! check reports something; CI requires 0 stale, 0 errors, 0 warnings"
  rm -f "$CHECKLOG"
  exit 1
fi
rm -f "$CHECKLOG"

# --- 4. the PDF -----------------------------------------------------------------
echo "== latexmk (pdflatex + bibtex) =="
cd "$HERE"
# imprimatur build may have rewritten the .tex within the same second as the
# last run; force latexmk to look again.
touch imprimatur-paper.tex
if ! TEXINPUTS="$ROOT/tex//:" latexmk -pdf -interaction=nonstopmode -halt-on-error \
    imprimatur-paper.tex > .refresh-latexmk.log 2>&1; then
  echo "!! the paper does not typeset; see $HERE/.refresh-latexmk.log and imprimatur-paper.log"
  grep -a -A3 '^!' imprimatur-paper.log 2>/dev/null | head -20 | sed 's/^/    /'
  exit 1
fi
undefined=$(grep -aE "(Citation|Reference) .* undefined" imprimatur-paper.log | sort -u || true)
if [ -n "$undefined" ]; then
  echo "!! undefined references or citations:"
  echo "$undefined" | sed 's/^/    /'
  exit 1
fi
rm -f .refresh-latexmk.log
grep -a "Output written" imprimatur-paper.log | tail -1
echo "== done: $HERE/imprimatur-paper.pdf =="
