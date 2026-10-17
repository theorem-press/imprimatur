/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Extractor tests

Run with `lake test` in this directory. Test names are referred to by
`docs/TESTING.md`.
-/

open Testkit

/-- The version strings are well formed. -/
def testVersion : TestM Unit := group "version" do
  checkEq "extract/version/schema" Imprimatur.bundleSchema "imprimatur-bundle/1"
  check "extract/version/lean" (Imprimatur.leanVersion.startsWith "v4.")

/-- Entry point for `lake test`. -/
def main : IO UInt32 :=
  runSuite do
    testVersion
