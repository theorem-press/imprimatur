/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The test harness

A deliberately small harness, modelled on the test harness of an earlier tool.
Every test has a name; `docs/TESTING.md` refers to tests by these names, so
a name should be stable and unique within its test package.
-/

namespace Testkit

/-- Running totals for one test run. -/
structure Results where
  /-- The number of checks that passed. -/
  passed : Nat := 0
  /-- The number of checks that failed. -/
  failed : Nat := 0
  /-- The names of the failed checks, in order. -/
  failures : Array String := #[]
  /-- Whether to suppress failure messages (for testing the harness itself). -/
  quiet : Bool := false

/-- The test monad: `IO` with running totals. -/
abbrev TestM := StateT Results IO

/-- Indent every line of `s` by four spaces. -/
def indent (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map ("    " ++ ·))

/-- Record a passing check. -/
def pass : TestM Unit :=
  modify fun r => { r with passed := r.passed + 1 }

/-- Record a failing check, printing `detail` beneath its name. -/
def fail (name : String) (detail : String := "") : TestM Unit := do
  unless (← get).quiet do
    IO.eprintln s!"  FAIL: {name}"
    unless detail.isEmpty do
      IO.eprintln (indent detail)
  modify fun r => { r with failed := r.failed + 1, failures := r.failures.push name }

/-- Check that a condition holds. -/
def check (name : String) (cond : Bool) (detail : String := "") : TestM Unit :=
  if cond then pass else fail name detail

/-- Check that `actual` equals `expected`, showing both if not. -/
def checkEq {α : Type} [BEq α] [Repr α] (name : String) (actual expected : α) :
    TestM Unit :=
  if actual == expected then pass
  else fail name s!"expected: {repr expected}\nactual:   {repr actual}"

/-- Check that an `Except` is an error whose message contains `needle`. -/
def checkError {α : Type} (name : String) (result : Except String α)
    (needle : String) : TestM Unit :=
  match result with
  | .ok _ => fail name s!"expected an error mentioning {repr needle}, but it succeeded"
  | .error msg =>
    if (msg.splitOn needle).length > 1 then pass
    else fail name s!"expected an error mentioning {repr needle}\nactual error: {msg}"

/-- Run a named group of checks. -/
def group (name : String) (body : TestM Unit) : TestM Unit := do
  IO.println name
  body

/-- Print a summary of results and return the process exit code. -/
def finish (r : Results) : IO UInt32 := do
  IO.println s!"{r.passed} passed, {r.failed} failed"
  if r.failed == 0 then
    return 0
  IO.eprintln "Failed:"
  for f in r.failures do
    IO.eprintln s!"  {f}"
  return 1

/-- Run a test suite, print a summary and return the process exit code. -/
def runSuite (suite : TestM Unit) : IO UInt32 := do
  let ((), r) ← suite.run {}
  finish r

end Testkit
