/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Golden bundles and trust tests on the fixture projects

Each fixture under `test/fixtures/` is built with the current toolchain
(`scripts/test-all.sh` does this first). The test imports it at the `private`
level, exports a bundle for a fixed list of keys, and compares it with
`golden/<fixture>.bundle.json`. The toolchain in `producer.lean` is masked as `v4.x`, so
one golden file must hold on every toolchain: this is the cross-toolchain
requirement (PLAN §2.1), checked directly. The unmasked bundle is also
written to `out/`, for CI's cross-toolchain job.
-/

open Testkit Imprimatur Lean

namespace ExtractTest.Fixtures

/-- Where the fixtures are, relative to this test package. -/
def fixturesDir : System.FilePath := "../../test/fixtures"

/-- A fixture: its directory, root module, namespaces to strip, and keys. -/
structure Fixture where
  /-- Directory under `test/fixtures`. -/
  dir : String
  /-- Module to import. -/
  module : Name
  /-- Namespaces stripped in views. -/
  strip : Array Name
  /-- Keys to export. -/
  keys : Array String

/-- The fixtures and the keys exported from each. -/
def fixtures : Array Fixture := #[
  { dir := "Basic", module := `Basic, strip := #[`Basic],
    keys := #["Basic.Pair", "Basic.Pair.swap", "Basic.Pair.fst", "Basic.add_comm'", "Basic.Even",
      "Basic.Even.step", "Basic.oracle", "Basic.uses_oracle", "Basic.unfinished", "Basic.my_fun'",
      "Basic.long_statement", "Basic.secret", "Basic.instInhabitedPair", "Basic.em'",
      "topLevel", "no_doc", "Basic.no_such_thing"] },
  { dir := "ModuleSys", module := `ModuleSys, strip := #[`ModuleSys],
    keys := #["ModuleSys.pub_thm", "ModuleSys.honest", "ModuleSys.via_all", "ModuleSys.plain_user"] },
  { dir := "Trust", module := `Trust, strip := #[`Trust],
    keys := #["Trust.double_even", "Trust.double_even_renamed", "Trust.pairMap_fst",
      "Trust.halve_le", "Trust.direct_sorry", "Trust.uses_direct_sorry", "Trust.deep_sorry",
      "Trust.uses_custom_axiom", "Trust.uses_standard_axioms", "Trust.collatz_stmt",
      "Trust.uses_hyp", "Trust.Hyp"] }]

/-- Mask the toolchain version in a bundle's text. -/
def maskToolchain (bundle : String) : String :=
  "\n".intercalate ((bundle.splitOn "\n").map fun l =>
    if l.trimAscii.toString.startsWith "\"lean\": \"v4." then "    \"lean\": \"v4.x\"," else l)

/-- Export a fixture's bundle in-process. -/
unsafe def exportFixture (f : Fixture) : IO ExportResult := do
  let dir := fixturesDir / f.dir
  let lib := dir / ".lake" / "build" / "lib" / "lean"
  unless ← lib.pathExists do
    throw (IO.userError s!"{dir} is not built; run scripts/test-all.sh, or lake build in it")
  initSearchPath (← findSysroot) [lib]
  let env ← try Compat.importPrivate #[f.module] catch e =>
    throw (IO.userError s!"cannot import {f.module} from {dir}: {e}\n\
      Rebuild the fixtures with the current toolchain (scripts/test-all.sh does).")
  let settings : Settings := { imports := #[f.module], stripNamespaces := f.strip }
  let reqs := f.keys.map fun k => { key := k, views := #["lean", "meta"] }
  exportBundle env dir settings reqs

/-- A bundle's entry for a key, as JSON. -/
def entry? (bundle : String) (key : String) : Option Json :=
  match Json.parse bundle with
  | .ok j => (j.getObjVal? "entries" >>= (·.getObjVal? key)).toOption
  | .error _ => none

/-- The axioms of an entry. -/
def axioms (bundle key : String) : Array String :=
  match (entry? bundle key).bind (fun e => (e.getObjValAs? (Array String) "axioms").toOption) with
  | some a => a
  | none => #["(missing)"]

/-- The `sorry` flag of an entry. -/
def usesSorry (bundle key : String) : Option Bool :=
  (entry? bundle key).bind (·.getObjValAs? Bool "sorry" |>.toOption)

/-- Golden bundles, and trust checks on them. -/
unsafe def tests : TestM Unit := group "fixtures" do
  IO.FS.createDirAll "out"
  for f in fixtures do
    let r ← exportFixture f
    IO.FS.writeFile ("out" / s!"{f.dir}.bundle.json") r.bundle
    golden s!"extract/golden/{f.dir}" ("golden" / s!"{f.dir}.bundle.json") (maskToolchain r.bundle)
    match f.dir with
    | "Basic" =>
      checkEq "extract/keys/unknown-is-warning" r.warnings
        #["Basic.no_such_thing: no declaration with this name"]
      checkEq "extract/trust/custom-axiom" (axioms r.bundle "Basic.uses_oracle") #["Basic.oracle"]
      checkEq "extract/trust/classical-axioms" (axioms r.bundle "Basic.em'")
        #["Classical.choice", "Quot.sound", "propext"]
      checkEq "extract/trust/direct-sorry" (usesSorry r.bundle "Basic.unfinished") (some true)
      checkEq "extract/trust/no-sorry" (usesSorry r.bundle "Basic.add_comm'") (some false)
    | "ModuleSys" =>
      -- Only the private level shows the `sorry` in `pub_thm`'s private helper.
      checkEq "extract/modules/private-sorry-seen" (usesSorry r.bundle "ModuleSys.pub_thm") (some true)
      checkEq "extract/modules/sorry-through-import-all" (usesSorry r.bundle "ModuleSys.via_all") (some true)
      checkEq "extract/modules/honest" (axioms r.bundle "ModuleSys.honest") #[]
    | "Trust" =>
      checkEq "extract/trust/sorry-in-proof-chain" (usesSorry r.bundle "Trust.uses_direct_sorry") (some true)
      checkEq "extract/trust/sorry-in-statement" (usesSorry r.bundle "Trust.deep_sorry") (some true)
      checkEq "extract/trust/custom-axiom-trust" (axioms r.bundle "Trust.uses_custom_axiom")
        #["Trust.custom_axiom"]
    | _ => pure ()

end ExtractTest.Fixtures
