/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Testkit

/-!
# Self-tests of the test harness
-/

open Testkit

/-- Run `t` in a fresh state, returning its totals without touching ours. -/
def isolated (t : TestM Unit) : TestM Results := do
  let ((), r) ← (t.run { quiet := true } : IO (Unit × Results))
  return r

/-- The harness counts passes and failures. -/
def testHarness : TestM Unit := group "harness" do
  let r ← isolated do
    check "t" true
    checkEq "e" 1 2
    checkError "x" (.error "boom: bad" : Except String Unit) "bad"
  checkEq "testkit/harness/counts" (r.passed, r.failed) (2, 1)
  checkEq "testkit/harness/failure-names" r.failures #["e"]

/-- Golden files are compared, created and reported. -/
def testGolden : TestM Unit := group "golden" do
  let dir : System.FilePath := ".lake/selftest"
  IO.FS.createDirAll dir
  let path := dir / "g.txt"
  IO.FS.writeFile path "a\nb\n"
  let same ← isolated (golden "g" path "a\nb\n")
  checkEq "testkit/golden/equal" same.failed 0
  let diff ← isolated (golden "g" path "a\nc\n")
  checkEq "testkit/golden/different" diff.failed 1
  let missing ← isolated (golden "g" (dir / "missing.txt") "x")
  checkEq "testkit/golden/missing" missing.failed 1
  checkEq "testkit/golden/first-difference" (firstDifference "a\nb" "a\nc")
    "first difference at line 2:\nexpected: \"b\"\nactual:   \"c\""

/-- The generator is deterministic and stays in range. -/
def testGen : TestM Unit := group "generator" do
  let g := Gen.listOf (Gen.nat 1000)
  checkEq "testkit/gen/deterministic" (g.run 42 20) (g.run 42 20)
  check "testkit/gen/seeds-differ" (g.run 1 20 != g.run 2 20)
  -- Pinned values: these change only if SplitMix64 or FNV-1a are broken,
  -- and must be the same on every toolchain.
  checkEq "testkit/gen/splitmix-pinned" (Rng.next ⟨0⟩).1 0xE220A8397B1DCDAF
  checkEq "testkit/gen/fnv1a-pinned" (fnv1a "imprimatur") 0xF50EDEA0087655C5
  forAll "testkit/gen/nat-in-range" (Gen.natIn 3 7) toString
    fun n => expect (3 ≤ n && n ≤ 7) s!"{n} out of range"
  forAll "testkit/gen/list-bounded-by-size"
    (do let s ← Gen.size; return (s, ← Gen.listOf Gen.bool)) (fun p => toString p.1)
    fun (s, xs) => expect (xs.length ≤ s) s!"length {xs.length} > size {s}"

/-- A failing property reports a seed that reproduces it. -/
def testProperty : TestM Unit := group "property" do
  let cfg : PropConfig := { cases := 200, seed := 7, maxSize := 30 }
  let prop := fun (n : Nat) => expect (n < 900) "too big"
  let r ← isolated (forAllWith cfg "p" (Gen.nat 1000) toString prop)
  checkEq "testkit/property/finds-failure" r.failed 1
  let r2 ← isolated (forAllWith cfg "p" (Gen.nat 1000) toString prop)
  checkEq "testkit/property/reproducible" r2.failed 1

/-- Entry point for `lake test`. -/
def main : IO UInt32 :=
  runSuite do
    testHarness
    testGolden
    testGen
    testProperty
