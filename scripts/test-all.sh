#!/usr/bin/env bash
# Copyright (c) 2026 The imprimatur authors.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Run every layer that CI runs (docs/TESTING.md, Tooling), so a contributor can reproduce CI
# with one command.
#
#   scripts/test-all.sh                       everything, on the pinned toolchains
#   scripts/test-all.sh --toolchain v4.31.0   the extractor on another toolchain
#   scripts/test-all.sh --only extract        one of: testkit splice extract lint e2e
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD

toolchain=""
only=""
while [ $# -gt 0 ]; do
  case "$1" in
    --toolchain) toolchain="$2"; shift 2 ;;
    --only) only="$2"; shift 2 ;;
    *) echo "usage: $0 [--toolchain vX.Y.Z] [--only testkit|splice|extract|lint|e2e]" >&2; exit 2 ;;
  esac
done

want() { [ -z "$only" ] || [ "$only" = "$1" ]; }
step() { printf '\n== %s\n' "$*"; }

# Build a package and run its test package, with warnings as errors.
lean_tests() {
  local pkg=$1 tc=${2:-}
  local env=()
  [ -n "$tc" ] && env=(env "ELAN_TOOLCHAIN=leanprover/lean4:$tc")
  step "$pkg${tc:+ on $tc}"
  (cd "$ROOT/$pkg" && "${env[@]}" lake build --wfail)
  (cd "$ROOT/$pkg/test" && "${env[@]}" lake build --wfail && "${env[@]}" lake test)
}

if want testkit; then
  step testkit
  (cd testkit && lake build --wfail && lake test)
fi
want splice && lean_tests splice
if want extract; then
  # The fixture Lean projects must build on every toolchain in the matrix. The
  # weak variant of Trust is built first, so the extractor tests see the
  # default (strong) one. Lake caches -K options with the configuration, so
  # each build reconfigures (-R).
  tc=${toolchain:-$(sed 's/.*://' extract/lean-toolchain)}
  step "fixture test/fixtures/Trust, weak variant, on $tc"
  (cd test/fixtures/Trust && ELAN_TOOLCHAIN="leanprover/lean4:$tc" lake build -q -R -Kweak=1)
  for fx in test/fixtures/*/; do
    step "fixture $fx on $tc"
    (cd "$fx" && ELAN_TOOLCHAIN="leanprover/lean4:$tc" lake build -q -R)
  done
  lean_tests extract "$toolchain"
fi
if want lint; then
  step lint
  scripts/lint.sh
fi
if want e2e; then
  step e2e
  scripts/e2e.sh
fi
printf '\nall tests passed\n'
