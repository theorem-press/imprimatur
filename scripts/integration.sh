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
# KEEP_WORK=1 keeps the scratch directory, for investigating a failure.
[ "${KEEP_WORK:-}" = 1 ] && echo "scratch directory: $work" || trap 'rm -rf "$work"' EXIT

echo "== integration/llmbda-scan-strip: scan and strip llmbda's oopsla2027/paper.tex"
if [ ! -f "$LLMBDA_ROOT/oopsla2027/paper.tex" ]; then
  echo "llmbda not found at $LLMBDA_ROOT (set LLMBDA_ROOT)" >&2
  exit 1
fi
mkdir -p "$work/llmbda"
cp "$LLMBDA_ROOT"/oopsla2027/*.tex "$work/llmbda/"
# llmbda's own configuration, or, before llmbda adopted imprimatur, aliases
# for its environments.
if [ -f "$LLMBDA_ROOT/oopsla2027/imprimatur.toml" ]; then
  cp "$LLMBDA_ROOT/oopsla2027/imprimatur.toml" "$work/llmbda/"
else
  cp scripts/integration/llmbda-aliases.toml "$work/llmbda/imprimatur.toml"
fi
(cd "$work/llmbda" && "$SPLICE" scan -o requests.json)
python3 -c "import json,sys; r=json.load(open('$work/llmbda/requests.json'))['requests']; print(f'scan: {len(r)} keys requested')"
(cd "$work/llmbda" && "$SPLICE" strip -o stripped)
python3 scripts/integration/check_outside.py "$work/llmbda" "$work/llmbda/stripped" \
  leangrammar leanrules leantheorem leancorollary leanlemma leandef leanconventions leantranslation %LEANCLAUSE
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
# M3: trust and manifests, in external mode. Extractors are installed into a
# cache in the scratch directory, one per toolchain.
export IMPRIMATUR_CACHE="${IMPRIMATUR_CACHE:-$work/cache}"
IMPRIMATUR="$ROOT/splice/.lake/build/bin/imprimatur"
(cd splice && lake build -q imprimatur)
relpath() { python3 -c 'import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))' "$1" "$2"; }
failures=0

if [ -d "$MATH_ROOT/ComparatorChallenges" ]; then
  echo "== integration/math-manifests: the math catalogue's comparator manifests"
  stage="$work/math-manifests"; mkdir -p "$stage/all" "$stage/built"
  cp "$MATH_ROOT"/ComparatorChallenges/*.json "$stage/all/"
  # Only manifests whose solution module is built can be checked: external
  # mode reads a host as it is, and never builds it.
  python3 - "$MATH_ROOT" "$stage" <<'PY'
import glob, json, os, shutil, sys
root, stage = sys.argv[1], sys.argv[2]
for m in sorted(glob.glob(os.path.join(stage, "all", "*.json"))):
    sol = json.load(open(m)).get("solution_module", "")
    if os.path.exists(os.path.join(root, ".lake/build/lib/lean", sol.replace(".", "/") + ".olean")):
        shutil.copy(m, os.path.join(stage, "built"))
PY
  rel=$(relpath "$MATH_ROOT" "$stage")
  printf '\\documentclass{article}\\begin{document}Catalogue.\\end{document}\n' > "$stage/paper.tex"
  for set in all built; do
    printf 'schema = 1\nmain = "paper.tex"\nlean_project = "%s"\nmode = "external"\n\n[manifests]\ncomparator = ["%s/*.json"]\n' \
      "$rel" "$set" > "$stage/$set.toml"
  done
  (cd "$stage" && "$IMPRIMATUR" --config all.toml scan -o all-requests.json > scan.log 2>&1) \
    || { echo "  FAIL: scan"; cat "$stage/scan.log"; failures=1; }
  python3 -c "import json,sys; r=json.load(open('$stage/all-requests.json')); print(f'  all {len(r[\"requests\"])} theorem keys from {len(list(__import__(\"glob\").glob(\"$stage/all/*.json\")))} manifests parsed')"
  "$IMPRIMATUR" toolchain install "$(sed 's/.*://' "$MATH_ROOT/lean-toolchain")" | sed 's/^/  /'
  (cd "$stage" && "$IMPRIMATUR" --config built.toml check > check.log 2>&1) || true
  grep -v "^warning: .*repository .* has local changes" "$stage/check.log" | sed 's/^/  /'
  if grep -qE 'broken-ref|bad-manifest|^error:' "$stage/check.log"; then
    echo "  FAIL: manifests did not import cleanly"; failures=1
  fi
fi

if [ -f "$MATH_ROOT/OAI/SetTheory/PartitionPrinciple/Models/Separation.lean" ]; then
  echo "== integration/math-prose: the partition-principle theorem in the prose view"
  # PLAN M4, done when: rendered with the notation in scripts/integration/math,
  # it must match the agreed text (target-prose.tex), and typeset.
  prose="$work/math-prose"; mkdir -p "$prose"
  tc=$(sed 's/.*://' "$MATH_ROOT/lean-toolchain")
  "$IMPRIMATUR" toolchain install "$tc" > /dev/null
  key=OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice
  printf '{"schema": "imprimatur-requests/1", "config": {"imports": [], "strip_namespaces": ["OAI", "OAI.PartitionPilot.Forcing"], "notation": ["PartitionTeX.lean"]}, "requests": {"%s": {"views": ["prose", "math"]}}}' "$key" > "$prose/requests.json"
  (cd "$MATH_ROOT" && lake env "$IMPRIMATUR_CACHE/toolchains/$tc/.lake/build/bin/imprimatur-export" \
    --requests "$prose/requests.json" --out "$prose/bundle.json" --base "$ROOT/scripts/integration/math") 2>&1 \
    | grep -v "local changes" | sed 's/^/  /'
  python3 - "$prose/bundle.json" "$prose" <<'PY'
import json, sys
e = list(json.load(open(sys.argv[1]))["entries"].values())[0]
open(sys.argv[2] + "/prose.tex", "w").write(e["views"]["prose"] + "\n")
open(sys.argv[2] + "/paper.tex", "w").write("\\documentclass{article}\\usepackage{imprimatur}\\begin{document}\n"
    + e["views"]["prose"] + "\n\n\\[" + e["views"]["math"] + "\\]\n\\end{document}\n")
PY
  sed 's/^/  /' "$prose/prose.tex"
  if ! diff -u "scripts/integration/math/target-prose.tex" "$prose/prose.tex" > "$prose/diff.txt"; then
    echo "  FAIL: the prose differs from the agreed text:"; sed 's/^/    /' "$prose/diff.txt"; failures=1
  fi
  if ! (cd "$prose" && TEXINPUTS="$ROOT/tex//:" latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex > latexmk.log 2>&1); then
    echo "  FAIL: the prose doesn't typeset"; failures=1
  else
    echo "  typeset: $prose/paper.pdf"
  fi
fi

if [ -f "$PLANET_ROOT/Planet/Paper.lean" ]; then
  echo "== integration/planet-rules: PLanet's analysis rules, generated from Der and DerF (PLAN M5)"
  # PLAN M5, done when: the rules figure is generated (Lift stays hand-written),
  # with the notation in scripts/integration/planet. It must match the agreed
  # text (target-rules.tex), and typeset.
  prules="$work/planet-rules"; mkdir -p "$prules"
  tc=$(sed 's/.*://' "$PLANET_ROOT/lean-toolchain")
  "$IMPRIMATUR" toolchain install "$tc" > /dev/null
  printf '{"schema": "imprimatur-requests/1", "config": {"imports": [], "strip_namespaces": ["Planet"], "notation": ["PlanetTeX.lean"]}, "requests": {"Analysis rules": {"views": ["rules"]}}}' > "$prules/requests.json"
  (cd "$PLANET_ROOT" && lake env "$IMPRIMATUR_CACHE/toolchains/$tc/.lake/build/bin/imprimatur-export" \
    --requests "$prules/requests.json" --out "$prules/bundle.json" --base "$ROOT/scripts/integration/planet") 2>&1 \
    | grep -v "local changes" | sed 's/^/  /'
  python3 - "$prules/bundle.json" "$prules" <<'PY'
import json, sys
e = json.load(open(sys.argv[1]))["entries"]["Analysis rules"]
if "errors" in e: print("  errors:", e["errors"])
rules = e["views"].get("rules", "")
open(sys.argv[2] + "/rules.tex", "w").write(rules + "\n")
open(sys.argv[2] + "/paper.tex", "w").write("\\documentclass{article}\\usepackage{imprimatur,mathpartir,amssymb}\n"
    "\\newcommand{\\judge}[1]{\\mathsf{#1}}\\newcommand{\\lab}[1]{\\mathit{#1}}\n"
    "\\newcommand{\\nestD}[2]{#1 \\triangleright #2}\\newcommand{\\crossD}[2]{#1 \\times #2}\n"
    "\\begin{document}\n" + rules + "\n\\end{document}\n")
PY
  if ! diff -u "scripts/integration/planet/target-rules.tex" "$prules/rules.tex" > "$prules/diff.txt"; then
    echo "  FAIL: the rules differ from the agreed text:"; sed 's/^/    /' "$prules/diff.txt" | head -60; failures=1
  fi
  if ! (cd "$prules" && TEXINPUTS="$ROOT/tex//:" latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex > latexmk.log 2>&1); then
    echo "  FAIL: the rules don't typeset (see $prules/latexmk.log)"; failures=1
  else
    echo "  typeset: $prules/paper.pdf"
  fi

  echo "== integration/planet-drift: a weakened copy of a PLanet theorem is caught as drift"
  scratch="$work/planet-drift"; mkdir -p "$scratch/olean"
  tc=$(sed 's/.*://' "$PLANET_ROOT/lean-toolchain")
  "$IMPRIMATUR" toolchain install "$tc" | sed 's/^/  /'
  exe="$IMPRIMATUR_CACHE/toolchains/$tc/.lake/build/bin/imprimatur-export"
  copy() {  # copy CONCLUSION PROOF: compile a restatement of proposition1_full
    cat > "$scratch/PlanetDrift.lean" <<LEAN
import Planet.Paper
open Planet Planet.Paper
namespace PlanetDrift
/-- A restatement of Proposition 1, as a paper might quote it. -/
theorem prop1_copy {R C : Type} {n : ℕ} [Fintype R] [Fintype C]
    {M : Props.Mat R C n} (hR : Fintype.card R = n.factorial)
    (hC : Fintype.card C = n) (hn : 0 < n) :
    $1 :=
  $2
end PlanetDrift
LEAN
    # --root: Lean only compiles files under its root directory.
    (cd "$PLANET_ROOT" && lake env lean --root="$scratch" "$scratch/PlanetDrift.lean" -o "$scratch/olean/PlanetDrift.olean")
    printf '{"schema": "imprimatur-requests/1", "config": {"imports": ["PlanetDrift"]}, "requests": {"PlanetDrift.prop1_copy": {"views": []}}}' > "$scratch/requests.json"
    (cd "$PLANET_ROOT" && lake env bash -c "LEAN_PATH=\$LEAN_PATH:$scratch/olean '$exe' --requests '$scratch/requests.json' --out '$scratch/bundle.json'") > /dev/null
  }
  printf '\\documentclass{article}\\begin{document}\nProposition 1 holds \\leancheck{PlanetDrift.prop1_copy}.\n\\end{document}\n' > "$scratch/paper.tex"
  SPLICE="$ROOT/splice/.lake/build/bin/imprimatur-splice"
  copy "Des.LeafSem (Props.cbWithin R C n) M ↔ Props.RowsPerm M ∧ DistinctRows M" \
       "Planet.Paper.proposition1_full hR hC hn"
  (cd "$scratch" && "$SPLICE" --main paper.tex accept --bundle bundle.json --all && "$SPLICE" --main paper.tex check --bundle bundle.json) | sed 's/^/  /'
  grep -o '\\leancheck\[[^]]*\]' "$scratch/paper.tex" | sed 's/^/  accepted: /'
  # Weaken it: the iff becomes one direction.
  copy "Des.LeafSem (Props.cbWithin R C n) M → Props.RowsPerm M" \
       "fun h => ((Planet.Paper.proposition1_full hR hC hn).mp h).1"
  if (cd "$scratch" && "$SPLICE" --main paper.tex check --bundle bundle.json > check.log 2>&1); then
    echo "  FAIL: the weakened statement was not reported"; failures=1
  fi
  sed 's/^/  /' "$scratch/check.log"
  grep -q 'error\[drift\]' "$scratch/check.log" || { echo "  FAIL: no drift reported"; failures=1; }
fi

[ $failures = 0 ] || exit 1
echo "integration: passed"
