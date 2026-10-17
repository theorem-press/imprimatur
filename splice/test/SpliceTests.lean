/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceTest.Unit
import SpliceTest.Golden
import SpliceTest.Props
import Testkit

/-!
# Splicer tests

Run with `lake test` in this directory. Test names are referred to by
`docs/TESTING.md`.
-/

open Testkit

/-- The splicer accepts the current bundle schema. -/
def testVersion : TestM Unit := group "version" do
  check "splice/version/schema" (Splice.acceptedSchemas.contains "imprimatur-bundle/1")

/-- Entry point for `lake test`. -/
def main : IO UInt32 :=
  runSuite do
    testVersion
    SpliceTest.Unit.tests
    SpliceTest.Golden.tests
    SpliceTest.Props.tests
