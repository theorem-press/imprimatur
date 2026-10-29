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
requirement (docs/TESTING.md, Layers), checked directly. The unmasked bundle is also
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
  /-- Views to ask for. -/
  views : Array String := #["lean", "meta"]
  /-- What the document refers to: hypotheses by name, for prose labels. -/
  document : DocumentInfo := {}
  deriving Inhabited

/-- The fixtures and the keys exported from each. -/
def fixtures : Array Fixture := #[
  { dir := "Basic", module := `Basic, strip := #[`Basic],
    keys := #["Basic.Pair", "Basic.Pair.swap", "Basic.Pair.fst", "Basic.add_comm'", "Basic.Even",
      "Basic.Even.step", "Basic.oracle", "Basic.uses_oracle", "Basic.unfinished", "Basic.my_fun'",
      "Basic.long_statement", "Basic.secret", "Basic.instInhabitedPair", "Basic.em'",
      "topLevel", "no_doc", "Basic.no_such_thing",
      "Basic.Wrap.leaf", "Basic.Wrap"] },
  { dir := "ModuleSys", module := `ModuleSys, strip := #[`ModuleSys],
    keys := #["ModuleSys.pub_thm", "ModuleSys.honest", "ModuleSys.via_all", "ModuleSys.plain_user"] },
  { dir := "Manifests", module := `Manifests, strip := #[`Cat],
    keys := #["Cat.main", "Cat.classical", "Cat.IsEven"] },
  { dir := "Notation", module := `Notation, strip := #[`Notation],
    keys := #["Notation.arith", "Notation.logic", "Notation.sets", "Notation.order",
      "Notation.binders", "Notation.project", "Notation.triple", "Notation.long", "Notation.joins", "Notation.typed",
      "Notation.binderRules", "Notation.witnesses", "Notation.hypsOnly", "Notation.bare"],
    views := #["math", "prose", "math:named", "math:binders"],
    document := { hypRefs := #[("Notation.project", "hd")] } },
  { dir := "Semantics", module := `Semantics, strip := #[`Stlc],
    keys := #["Stlc.HasType", "Stlc.Step", "Typing and evaluation", "Stlc.Tm", "Stlc.Ty",
      "Lookup and size", "Types and terms", "Prod", "Stlc.Claim",
      "Stlc.size", "Stlc.step_app", "Preservation", "Stlc.size_pos"],
    views := #["rules", "rules|include=beta,app_right", "rules|exclude=beta", "grammar",
      "math|rule=", "math|forall=", "math|def=", "math|names=full", "fixture.rulelist",
      "clauses", "grammar|display"] },
  { dir := "Patterns", module := `Patterns, strip := #[`Patterns],
    keys := #["Patterns.three", "Patterns.nested", "Patterns.side", "Patterns.safeHead",
      "Patterns.konst", "Patterns.ident"],
    views := #["math|def="] },
  { dir := "Trust", module := `Trust, strip := #[`Trust],
    keys := #["Trust.double_even", "Trust.double_even_renamed", "Trust.pairMap_fst",
      "Trust.pairMap_fst_renamed",
      "Trust.halve_le", "Trust.direct_sorry", "Trust.uses_direct_sorry", "Trust.deep_sorry",
      "Trust.uses_custom_axiom", "Trust.uses_standard_axioms", "Trust.collatz_stmt",
      "Trust.uses_hyp", "Trust.Hyp"] }]

/-- Mask the toolchain version in a bundle's text. -/
def maskToolchain (bundle : String) : String :=
  "\n".intercalate ((bundle.splitOn "\n").map fun l =>
    if l.trimAscii.toString.startsWith "\"lean\": \"v4." then "    \"lean\": \"v4.x\"," else l)

/-- Export a fixture's bundle in-process. -/
unsafe def exportFixture (f : Fixture) (used : Option (IO.Ref (Array String)) := none)
    (document : DocumentInfo := f.document) : IO ExportResult := do
  let dir := fixturesDir / f.dir
  let lib := dir / ".lake" / "build" / "lib" / "lean"
  unless ← lib.pathExists do
    throw (IO.userError s!"{dir} is not built; run scripts/test-all.sh, or lake build in it")
  initSearchPath (← findSysroot) [lib]
  let env ← try Compat.importPrivate #[f.module] catch e =>
    throw (IO.userError s!"cannot import {f.module} from {dir}: {e}\n\
      Rebuild the fixtures with the current toolchain (scripts/test-all.sh does).")
  let settings : Settings := { imports := #[f.module], stripNamespaces := f.strip, document }
  let reqs := f.keys.map fun k => { key := k, views := f.views }
  let (entries, warnings) ← exportEntries env dir settings reqs (used := used)
  return { bundle := renderBundle entries none, entries := entries.size, warnings }

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

/-- A field of an entry, as a string. -/
def field (bundle key f : String) : Option String :=
  (entry? bundle key).bind (·.getObjValAs? String f |>.toOption)

/-- Run `lake` in a fixture, failing loudly. The toolchain is inherited (CI
sets `ELAN_TOOLCHAIN`). -/
def lakeIn (dir : System.FilePath) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd := "lake", args, cwd := dir }
  if out.exitCode != 0 then
    throw (IO.userError s!"lake {args} in {dir} failed:\n{out.stdout}{out.stderr}")

/-- The `Trust` fixture's drift case (DESIGN §7.7, §10.3): `Trust.Hyp` is
weakened to `True` by a build option. The statement of `Trust.uses_hyp`
reads the same, so `sigHash` stays; its meaning changed, so `stmtHash` must
change. The fixture is left in its default (strong) state. -/
unsafe def driftTest : TestM Unit := group "drift" do
  let dir := fixturesDir / "Trust"
  let f := (fixtures.find? (·.dir == "Trust")).get!
  let f := { f with keys := #["Trust.uses_hyp"] }
  lakeIn dir #["build", "-q", "-R", "-Kweak=1"]
  let weak ← exportFixture f
  lakeIn dir #["build", "-q", "-R"]
  let strong ← exportFixture f
  let get (b : String) (k : String) := (field b "Trust.uses_hyp" k).getD "?"
  check "extract/trust/weakened-hypothesis-drifts"
    (get weak.bundle "stmtHash" != get strong.bundle "stmtHash")
    s!"stmtHash is {get weak.bundle "stmtHash"} for both variants"
  checkEq "extract/trust/weakened-hypothesis-same-signature"
    (get weak.bundle "sigHash") (get strong.bundle "sigHash")

/-- Comparator challenges (DESIGN §10.5): a challenge's statement is
rendered from its own module, imported on its own. -/
unsafe def challengeTest : TestM Unit := group "challenges" do
  let f := (fixtures.find? (·.dir == "Manifests")).get!
  let main ← exportFixture f
  let challenges : Array (String × Name) :=
    #[("Cat.main", `ComparatorChallenges.Main), ("Cat.classical", `ComparatorChallenges.Main)]
  let s : Settings := { imports := #[f.module], stripNamespaces := f.strip, challenges }
  let reqs : Array Request := #[{ key := "Cat.main@challenge", views := #["lean"] },
    { key := "Cat.classical@challenge", views := #[] }, { key := "Cat.unknown@challenge", views := #[] }]
  let (entries, warnings) ← exportChallenges (fixturesDir / f.dir) s reqs
  let ch := renderBundle entries none
  checkEq "extract/manifests/challenge-keys" (entries.map (·.1)) #["Cat.main@challenge", "Cat.classical@challenge"]
  checkEq "extract/manifests/unknown-challenge" warnings
    #["Cat.unknown@challenge: no comparator manifest names Cat.unknown"]
  -- The challenge states what the solution proves: the same statement hash.
  checkEq "extract/manifests/challenge-statement-matches"
    (field ch "Cat.main@challenge" "stmtHash") (field main.bundle "Cat.main" "stmtHash")
  checkEq "extract/manifests/challenge-is-sorry" (usesSorry ch "Cat.main@challenge") (some true)
  checkEq "extract/manifests/solution-is-proved" (usesSorry main.bundle "Cat.main") (some false)

/-- The untrusted members of an entry's cone, as `name: reason, …`. -/
def untrustedOf (bundle key : String) : Array String :=
  match (entry? bundle key).bind (·.getObjVal? "cone" |>.toOption) with
  | some c =>
    let names := (c.getObjValAs? (Array String) "untrusted").toOption.getD #[]
    names.map fun n =>
      let rs := ((c.getObjVal? "reasons" >>= (·.getObjValAs? (Array String) n)).toOption).getD #[]
      s!"{n}: {", ".intercalate rs.toList}"
  | none => #["(no cone)"]

/-- The views that index the document (`Views/Index.lean`), on the
`Semantics` fixture: a document of two grammars, a theorem and the three
indexes, with the indexes asked for first. They are rendered last, so they
see every other block. -/
unsafe def indexTest : TestM Unit := group "index" do
  let f := (fixtures.find? (·.dir == "Semantics")).get!
  let dir := fixturesDir / f.dir
  let lib := dir / ".lake" / "build" / "lib" / "lean"
  initSearchPath (← findSysroot) [lib]
  let env ← Compat.importPrivate #[f.module]
  let blk (key view : String) (order : Nat) (label : Option String := none) : DocBlock :=
    { key, env := "leanblock", view, label, order }
  let document : DocumentInfo := { blocks := #[
    blk "Conventions" "conventions" 0, blk "Vocabulary" "vocabulary" 1,
    blk "Stlc.Ty" "grammar" 2 (some "gram:Ty"), blk "Stlc.Tm" "grammar" 3 (some "gram:Tm"),
    blk "Stlc.size_pos" "prose" 4 (some "thm:Stlc.size_pos"),
    blk "Provenance" "provenance" 5, blk "Notation" "vocabulary|scope=project" 6,
    blk "Stlc.IsValue" "rules" 7 (some "fig:values"), blk "Stlc.step_app" "prose" 8] }
  let settings : Settings := { imports := #[f.module], stripNamespaces := f.strip, document }
  let reqs : Array Request := #[
    { key := "Conventions", views := #["conventions"] }, { key := "Vocabulary", views := #["vocabulary"] },
    { key := "Provenance", views := #["provenance"] },
    { key := "Notation", views := #["vocabulary|scope=project"] },
    { key := "Stlc.Ty", views := #["grammar"] }, { key := "Stlc.Tm", views := #["grammar"] },
    { key := "Stlc.size_pos", views := #["prose"] },
    { key := "Stlc.IsValue", views := #["rules"] }, { key := "Stlc.step_app", views := #["prose"] }]
  let (entries, warnings) ← exportEntries env dir settings reqs
  checkEq "extract/index/no-warnings" warnings #[]
  let bundle := renderBundle entries none
  let view (k v : String) : String :=
    ((entry? bundle k).bind fun e => (e.getObjVal? "views" >>= (·.getObjValAs? String v)).toOption).getD ""
  let conv := view "Conventions" "conventions"
  let vocab := view "Vocabulary" "vocabulary"
  let prov := view "Provenance" "provenance"
  -- The grammars' categories, where they are shown, in document order.
  check "extract/index/conventions-shown"
    ((conv.splitOn "\\pageref{gram:Ty}").length > 1 && (conv.splitOn "\\pageref{gram:Tm}").length > 1) conv
  check "extract/index/conventions-order"
    ((conv.splitOn "gram:Ty")[0]!.length < (conv.splitOn "gram:Tm")[0]!.length) conv
  check "extract/index/provenance-theorem"
    ((prov.splitOn "Thm.~\\ref{thm:Stlc.size_pos}").length > 1) prov
  check "extract/index/vocabulary-library-only" ((vocab.splitOn "Stlc").length == 1) vocab
  -- `scope=project`: the project's notation, under the project, and not the
  -- category types the table of conventions lists.
  let own := view "Notation" "vocabulary|scope=project"
  check "extract/index/vocabulary-project"
    ((own.splitOn "\\textit{Semantics}").length == 2 && (own.splitOn "\\textit{Lean}").length == 1 &&
      (own.splitOn "\\texttt{Tm.app}").length > 1 && (own.splitOn "\\texttt{Ty}").length == 1) own
  -- A metavariable convention hides `IsValue e₂`, but not what it says
  -- (#77): the prose binds the variable in the predicate, and the table of
  -- conventions lists the metavariable, pointing to where values are shown.
  let stepApp := view "Stlc.step_app" "prose"
  check "extract/index/convention-binds" ((stepApp.splitOn "\\val_{2} \\in \\mathit{Val}").length > 1) stepApp
  check "extract/index/convention-row" ((conv.splitOn "$\\val$ & $\\mathit{Val}$").length > 1) conv
  check "extract/index/convention-shown" ((conv.splitOn "\\pageref{fig:values}").length > 1) conv
  golden "extract/index/golden" ("golden" / "Index.tex")
    (s!"% conventions\n{conv}% vocabulary\n{vocab}% provenance\n{prov}")

/-- `latex_style categories := strict`, on the `Categories` fixture. Its two
notation modules give `Prog` the metavariable $P$, and `Rep` either its own
($\overline{P}$, in `Strict`) or $P$ too (`Clash`). The style is the project's,
so each is imported on its own. -/
unsafe def categoriesTest : TestM Unit := group "categories" do
  let dir := fixturesDir / "Categories"
  let lib := dir / ".lake" / "build" / "lib" / "lean"
  initSearchPath (← findSysroot) [lib]
  let run (m : Name) : IO String := do
    let env ← Compat.importPrivate #[m]
    let settings : Settings := { imports := #[m], stripNamespaces := #[`Cats] }
    let reqs := #["Cats.lower_eq", "Cats.symm"].map fun k => { key := k, views := #["math"] }
    let (entries, _) ← exportEntries env dir settings reqs
    return renderBundle entries none
  let math (b k : String) : String :=
    ((entry? b k).bind fun e => (e.getObjVal? "views" >>= (·.getObjValAs? String "math")).toOption).getD ""
  let problems (b k : String) : Array String :=
    ((entry? b k).bind fun e =>
      (e.getObjVal? "validation" >>= (·.getObjValAs? (Array String) "math")).toOption).getD #[]
  let strict ← run `Categories.Strict
  -- `q : Prog` and `r : Rep` are written with their types' metavariables.
  let m := math strict "Cats.lower_eq"
  check "extract/categories/strict-renames"
    (m == "\\LeanMath{\\mathsf{lower}(P) = \\overline{P} \\implies \\mathsf{lower}(P) = \\overline{P}}") m
  checkEq "extract/categories/strict-clean" (problems strict "Cats.lower_eq") #[]
  -- `a b : Prog` are both $P$: an error, not a warning.
  check "extract/categories/strict-print-alike"
    ((problems strict "Cats.symm").any (·.startsWith "category: variables a and b both print as $P$"))
    (toString (problems strict "Cats.symm"))
  let clash ← run `Categories.Clash
  check "extract/categories/unique-letter"
    ((problems clash "Cats.lower_eq").any (·.startsWith "category: the metavariable $P$ stands for Cats.Prog, Cats.Rep"))
    (toString (problems clash "Cats.lower_eq"))

/-- The golden bundle of one fixture, and the checks on it. -/
unsafe def goldenTest (f : Fixture) : TestM Unit := do
  IO.FS.createDirAll "out"
  let used ← IO.mkRef #[]
  let r ← exportFixture f used
  IO.FS.writeFile ("out" / s!"{f.dir}.bundle.json") r.bundle
  golden s!"extract/golden/{f.dir}" ("golden" / s!"{f.dir}.bundle.json") (maskToolchain r.bundle)
  match f.dir with
  | "Basic" =>
    checkEq "extract/keys/unknown-is-warning" r.warnings
      #["Basic.no_such_thing: no declaration or group with this name"]
    checkEq "extract/trust/custom-axiom" (axioms r.bundle "Basic.uses_oracle") #["Basic.oracle"]
    checkEq "extract/trust/classical-axioms" (axioms r.bundle "Basic.em'")
      #["Classical.choice", "Quot.sound", "propext"]
    -- A cycle: the type's axioms include what its constructor's type depends
    -- on, and asking the constructor first (the keys' order) changes nothing.
    checkEq "extract/trust/cycle-axioms" (axioms r.bundle "Basic.Wrap") #["Classical.choice"]
    checkEq "extract/trust/axioms-order" (axioms r.bundle "Basic.Wrap.leaf") #["Classical.choice"]
    checkEq "extract/trust/direct-sorry" (usesSorry r.bundle "Basic.unfinished") (some true)
    checkEq "extract/trust/no-sorry" (usesSorry r.bundle "Basic.add_comm'") (some false)
  | "ModuleSys" =>
    -- Only the private level shows the `sorry` in `pub_thm`'s private helper.
    checkEq "extract/modules/private-sorry-seen" (usesSorry r.bundle "ModuleSys.pub_thm") (some true)
    checkEq "extract/modules/sorry-through-import-all" (usesSorry r.bundle "ModuleSys.via_all") (some true)
    checkEq "extract/modules/honest" (axioms r.bundle "ModuleSys.honest") #[]
  | "Notation" =>
    -- M4: every pack rule has a golden use.
    let usedRules ← used.get
    let unused := (Packs.all.toArray.flatMap (·.2)).filter fun r =>
      !usedRules.contains s!"{r.origin}: {r.template}"
    checkEq "extract/notation/every-pack-rule-used" (unused.map (·.template)) #[]
    -- Prose labels a hypothesis only where the paper refers to it.
    let one ← exportFixture { f with keys := #["Notation.project"], views := #["prose"] }
      (document := { hypRefs := #[("Notation.project", "hd")] })
    let prose := ((entry? one.bundle "Notation.project").bind fun e =>
      (e.getObjVal? "views" >>= (·.getObjValAs? String "prose")).toOption).getD ""
    check "extract/prose/hyp-referred-labelled" ((prose.splitOn "\\LeanHyp{hd}").length > 1) prose
    check "extract/prose/hyp-unreferred-unlabelled" ((prose.splitOn "\\LeanHyp{hr}").length == 1) prose
    -- `break`: the joins break the line before an operator.
    let joins := ((entry? r.bundle "Notation.joins").bind fun e =>
      (e.getObjVal? "views" >>= (·.getObjValAs? String "math")).toOption).getD ""
    check "extract/notation/break-before-operator"
      ((joins.splitOn "\\LeanBreak \\sqcup").length > 1) joins
    checkEq "extract/notation/no-render-errors"
      (f.keys.filter fun k => ((entry? r.bundle k).bind (·.getObjVal? "errors" |>.toOption)).isSome) #[]
  | "Semantics" =>
    -- Displays (`latex_display`): definitions as `lhs ≜ rhs` rows, types as
    -- grammar rows, with their descriptions as slots.
    let view (k v : String) : String :=
      ((entry? r.bundle k).bind fun e => (e.getObjVal? "views" >>= (·.getObjValAs? String v)).toOption).getD ""
    let clauses := view "Lookup and size" "clauses"
    check "extract/display/clauses"
      -- `lookup` by one equation, `size` by four.
      ((clauses.splitOn "\\LeanClause").length == 6 && (clauses.splitOn "\\deq").length == 6 &&
        (clauses.splitOn "\\leanslot{Stlc.lookup}").length == 2 &&
        (clauses.splitOn "\\leanslot{Stlc.size}").length == 2) clauses
    check "extract/display/clauses-one-definition"
      (((view "Stlc.size" "clauses").splitOn "\\deq").length == 5) (view "Stlc.size" "clauses")
    let grammar := view "Types and terms" "grammar|display"
    check "extract/display/grammar"
      ((grammar.splitOn "\\LeanCategory{\\tau \\in").length == 2 &&
        (grammar.splitOn "\\LeanCategory{e \\in").length == 2 &&
        (grammar.splitOn "\\leanslot{Stlc.Tm.app}").length == 2) grammar
    check "extract/display/title-names-declaration"
      (((view "Prod" "grammar|display").splitOn "\\LeanCategory{\\tau \\in").length == 2)
      (view "Prod" "grammar|display")
    check "extract/grammar/structure-header-notation"
      (((view "Stlc.Claim" "grammar").splitOn "\\LeanStructure{\\mathit{Claim}}").length == 2)
      (view "Stlc.Claim" "grammar")
    checkEq "extract/display/validated"
      (#["Lookup and size", "Types and terms"].filter fun k =>
        ((entry? r.bundle k).bind (·.getObjVal? "validation" |>.toOption)).isSome) #[]
  | "Patterns" =>
    -- A constant applied only to implicit arguments is no misread (`id`).
    checkEq "extract/validate/implicit-only-application"
      ((entry? r.bundle "Patterns.ident").bind (·.getObjVal? "validation" |>.toOption) |>.map (·.compress)) none
  | "Trust" =>
    checkEq "extract/trust/same-hash-renamed-binder"
      (field r.bundle "Trust.double_even" "stmtHash") (field r.bundle "Trust.double_even_renamed" "stmtHash")
    checkEq "extract/trust/same-hash-renamed-universes"
      (field r.bundle "Trust.pairMap_fst" "stmtHash") (field r.bundle "Trust.pairMap_fst_renamed" "stmtHash")
    check "extract/trust/different-sig-renamed"
      (field r.bundle "Trust.double_even" "sigHash" != field r.bundle "Trust.double_even_renamed" "sigHash")
    checkEq "extract/trust/cone-sorry" (untrustedOf r.bundle "Trust.deep_sorry") #["Trust.Level3: sorry"]
    checkEq "extract/trust/cone-partial" (untrustedOf r.bundle "Trust.collatz_stmt") #["Trust.collatz: partial"]
    checkEq "extract/trust/cone-clean" (untrustedOf r.bundle "Trust.double_even") #[]
    checkEq "extract/trust/sorry-in-proof-chain" (usesSorry r.bundle "Trust.uses_direct_sorry") (some true)
    checkEq "extract/trust/sorry-in-statement" (usesSorry r.bundle "Trust.deep_sorry") (some true)
    checkEq "extract/trust/custom-axiom-trust" (axioms r.bundle "Trust.uses_custom_axiom")
      #["Trust.custom_axiom"]
  | _ => pure ()

/-- The fixture tests, in parts. Each imports a Lean environment, and
environments accumulate in a process, so the driver (`ExtractTests.lean`)
runs each part in a process of its own (`--part NAME`). -/
unsafe def parts : Array (String × TestM Unit) :=
  #[("drift", driftTest), ("index", indexTest), ("categories", categoriesTest),
    ("challenges", challengeTest)] ++ fixtures.map fun f => (f.dir, goldenTest f)

/-- Every fixture test, in this process. -/
unsafe def tests : TestM Unit := group "fixtures" do
  for (_, t) in parts do t

end ExtractTest.Fixtures
