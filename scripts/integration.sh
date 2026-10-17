#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Real-world integration (PLAN §2.1): run locally and before every release,
# not in CI. Host projects are found next to this repository, or through
# LLMBDA_ROOT, PLANET_ROOT and MATH_ROOT. The Mathlib-based runs need about
# 7 GB of memory each and take a few minutes; they run one at a time.
#
# M1: llmbda's oopsla2027/paper.tex goes through `scan` and `strip` without a
# byte outside its blocks changing (PLAN M1, "done when").
# M2: the lean view of PLanet's Planet.Paper.* and of the math catalogue's
# partition-principle theorems, printed for review by hand (PLAN M2).
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
# M2: the lean view over real Mathlib-based projects, for review by hand.
# The extractor is built with each host's toolchain in a scratch copy, and run
# under the host's `lake env`, so nothing in the host changes.
extract_for() {  # extract_for TOOLCHAIN -> path of an imprimatur-export built with it
  local tc=$1 dir="$work/extract-$1"
  if [ ! -x "$dir/.lake/build/bin/imprimatur-export" ]; then
    mkdir -p "$dir"
    (cd extract && tar --exclude=.lake --exclude=test -cf - .) | (cd "$dir" && tar -xf -)
    echo "leanprover/lean4:$tc" > "$dir/lean-toolchain"
    (cd "$dir" && lake build -q imprimatur-export >&2)
  fi
  echo "$dir/.lake/build/bin/imprimatur-export"
}

render() {  # render NAME HOST_DIR MODULE STRIP KEY... : export, then print the lean views
  local name=$1 host=$2 module=$3 strip=$4; shift 4
  local tc; tc=$(sed 's/.*://' "$host/lean-toolchain")
  local exe; exe=$(extract_for "$tc")
  python3 - "$work/$name.requests.json" "$module" "$strip" "$@" <<'PY'
import json, sys
out, module, strip, keys = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
json.dump({"schema": "imprimatur-requests/1",
           "config": {"imports": [module], "strip_namespaces": [strip] if strip else []},
           "requests": {k: {"views": ["lean", "meta"]} for k in keys}}, open(out, "w"))
PY
  (cd "$host" && lake env "$exe" --requests "$work/$name.requests.json" --out "$work/$name.bundle.json")
  python3 - "$work/$name.bundle.json" <<'PY'
import json, re, sys
b = json.load(open(sys.argv[1]))
for k, e in sorted(b["entries"].items()):
    lean = e["views"]["lean"]
    plain = re.sub(r"\\Lean(?:Keyword|Const|Bound|Sort|Number|String)\{((?:[^{}]|\\[{}])*)\}", r"\1", lean)
    plain = plain.replace("\\LeanCode{%\n", "").replace("\\LeanNewline", "")
    plain = re.sub(r"\\LeanIndent\{(\d+)\}", lambda m: " " * int(m.group(1)), plain)
    plain = plain.replace("\\_", "_").replace("\\{", "{").replace("\\}", "}")[:-1]
    print(f"--- {k}  ({e['source']['path']}:{e['source']['line']}; axioms: {', '.join(e['axioms']) or 'none'})")
    print(plain)
PY
}

PLANET_ROOT=${PLANET_ROOT:-$ROOT/../exp-des-dsl-paper/named/planet-lean/planet-lean}
if [ -f "$PLANET_ROOT/Planet/Paper.lean" ]; then
  echo "== integration/planet-lean-view: the lean view of Planet.Paper.*"
  keys=$(grep -oE '^theorem [^ ]+' "$PLANET_ROOT/Planet/Paper.lean" | sed 's/^theorem /Planet.Paper./')
  # shellcheck disable=SC2086
  render planet "$PLANET_ROOT" Planet.Paper Planet $keys
else
  echo "PLanet not found at $PLANET_ROOT (set PLANET_ROOT); skipped" >&2
fi

MATH_ROOT=${MATH_ROOT:-$ROOT/../math/lean}
if [ -f "$MATH_ROOT/OAI/SetTheory/PartitionPrinciple/Models/Separation.lean" ]; then
  echo "== integration/math-lean-view: the lean view of the partition-principle theorems"
  render math "$MATH_ROOT" OAI.SetTheory.PartitionPrinciple.Models.Separation OAI \
    OAI.PartitionPilot.Forcing.TransitiveGround.exists_partitionPrinciple_without_choice \
    OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice
else
  echo "the math catalogue not found at $MATH_ROOT (set MATH_ROOT); skipped" >&2
fi
echo "integration: passed"
