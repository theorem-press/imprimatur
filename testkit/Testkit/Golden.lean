/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Testkit.Harness

/-!
# Golden files

`golden name path actual` compares `actual` with the contents of `path`.
With `UPDATE_GOLDEN=1` in the environment it writes `actual` to `path`
instead, so that the change shows up as a diff to review (PLAN §1.4).
-/

namespace Testkit

/-- Whether this run should rewrite golden files. -/
def updatingGolden : IO Bool :=
  return (← IO.getEnv "UPDATE_GOLDEN") == some "1"

/-- Describe the first line at which `expected` and `actual` differ. -/
def firstDifference (expected actual : String) : String :=
  let es := expected.splitOn "\n"
  let as := actual.splitOn "\n"
  let rec go : Nat → List String → List String → String
    | n, e :: es, a :: as =>
      if e == a then go (n + 1) es as
      else s!"first difference at line {n}:\nexpected: {repr e}\nactual:   {repr a}"
    | n, [], a :: _ => s!"actual has extra lines from line {n}: {repr a}"
    | n, e :: _, [] => s!"actual ends early at line {n}; expected {repr e}"
    | _, [], [] => "the texts are equal"
  go 1 es as

/-- Compare `actual` with the golden file at `path`, or rewrite the file when
`UPDATE_GOLDEN=1`. Files are only rewritten when their content changes. -/
def golden (name : String) (path : System.FilePath) (actual : String) : TestM Unit := do
  if ← updatingGolden then
    let old ← if ← path.pathExists then some <$> IO.FS.readFile path else pure none
    if old != some actual then
      if let some dir := path.parent then
        IO.FS.createDirAll dir
      IO.FS.writeFile path actual
      IO.println s!"  updated golden file {path}"
    pass
  else if !(← path.pathExists) then
    fail name s!"golden file {path} is missing; run with UPDATE_GOLDEN=1 to create it"
  else
    let expected ← IO.FS.readFile path
    if expected == actual then pass
    else
      fail name s!"{path}: {firstDifference expected actual}\n\
        run with UPDATE_GOLDEN=1 to accept the new output, then review the diff"

end Testkit
