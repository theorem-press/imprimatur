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

/-- Entry point for `lake test`. -/
unsafe def main : IO UInt32 :=
  runSuite do
    testVersion
    ExtractTest.Unit.tests
    ExtractTest.HashProps.tests
    ExtractTest.DocTests.tests
    ExtractTest.ValidateTests.tests
    ExtractTest.Fixtures.tests
