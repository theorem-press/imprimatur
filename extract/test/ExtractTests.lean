/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit
import ExtractTest.Unit
import ExtractTest.Fixtures
import ExtractTest.HashProps
import ExtractTest.Doc
import ExtractTest.Validate
import ExtractTest.ChainLaws
import ExtractTest.SortLaws

/-!
# Extractor tests

Run with `lake test` in this directory, after building the fixtures under
`test/fixtures/` with the same toolchain (`scripts/test-all.sh` does both).
Test names are referred to by `docs/TESTING.md`.
-/

open Testkit

/-- The version strings are well formed. -/
def testVersion : TestM Unit := group "version" do
  checkEq "extract/version/schema" Imprimatur.bundleSchema "imprimatur-bundle/1"
  check "extract/version/lean" (Imprimatur.leanVersion.startsWith "v4.")

/-- The tests that need no fixture, run in this process. -/
unsafe def inProcess : TestM Unit := do
  testVersion
  ExtractTest.Unit.tests
  ExtractTest.HashProps.tests
  ExtractTest.DocTests.tests
  ExtractTest.ValidateTests.tests
  ExtractTest.ChainLaws.tests
  ExtractTest.SortLaws.tests

/-- Run one part of the fixture tests (`ExtractTest.Fixtures.parts`) in a
process of its own, and add its results. Its output is passed on; its
summary line (`N passed, M failed`) and failed checks (after `Failed:`) are
read back. A part that does not report counts as one failure. -/
def runPart (self : System.FilePath) (name : String) : TestM Unit := do
  let out ← IO.Process.output { cmd := self.toString, args := #["--part", name] }
  IO.print out.stdout
  IO.eprint out.stderr
  let summary := (out.stdout.splitOn "\n").reverse.findSome? fun l =>
    match l.splitOn " passed, " with
    | [p, f] => do pure (← p.trimAscii.toString.toNat?, ← (f.replace " failed" "").trimAscii.toString.toNat?)
    | _ => none
  let names := ((out.stderr.splitOn "Failed:\n").getD 1 "").splitOn "\n" |>.filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty then none else some l
  match summary with
  | some (p, f) =>
    modify fun r => { r with
      passed := r.passed + p
      failed := r.failed + f
      failures := r.failures ++ names.toArray }
  | none =>
    modify fun r => { r with
      failed := r.failed + 1
      failures := r.failures.push s!"fixtures/{name} (exit {out.exitCode}, no summary)" }

/-- Entry point for `lake test`. With `--part NAME`, run that part of the
fixture tests only; with `--laws`, the properties of the chain rule and of
Lean's sorts only (docs/coercion-chains.md, B2). Otherwise run the tests that need no fixture here, and
each part of the fixture tests in a process of its own: each imports a Lean
environment, and in one process they add up to more memory than a laptop
has. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["--laws"] => runSuite (do ExtractTest.ChainLaws.tests; ExtractTest.SortLaws.tests)
  | ["--part", name] =>
    match ExtractTest.Fixtures.parts.find? (·.1 == name) with
    | some (_, t) => runSuite (group s!"fixtures/{name}" t)
    | none =>
      IO.eprintln s!"no fixture test part {name}; the parts are \
        {", ".intercalate (ExtractTest.Fixtures.parts.map (·.1)).toList}"
      return 2
  | _ =>
    let self ← IO.appPath
    let ((), r) ← (do
      inProcess
      for (name, _) in ExtractTest.Fixtures.parts do runPart self name).run {}
    finish r
