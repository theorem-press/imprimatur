/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Entry
import Imprimatur.Version

/-!
# Exporting a bundle

`exportBundle` renders an entry for every requested key that names a
declaration, and writes the bundle (DESIGN §8). Keys that name nothing are
returned as warnings; the splicer reports them where they are used.
-/

namespace Imprimatur

open Lean Meta

/-- A bundle, and what went wrong while making it. -/
structure ExportResult where
  /-- The bundle's text. -/
  bundle : String
  /-- The number of entries. -/
  entries : Nat
  /-- Problems, one per line. -/
  warnings : Array String

/-- The `producer` field. It never holds paths, user names or dates. -/
def producer (project? : Option String) : J :=
  .obj (#[("tool", .str "imprimatur-export"), ("version", .str version),
          ("lean", .str leanVersion)] ++
        (match project? with | some p => #[("project", .str p)] | none => #[]))

/-- The suffix of keys that name a comparator challenge's statement. -/
def challengeSuffix : String := "@challenge"

/-- Render an entry for each request from `env`. The declaration is the key,
less any `@challenge` suffix. -/
def exportEntries (env : Environment) (root : System.FilePath) (s : Settings)
    (reqs : Array Request) (verbose : Bool := false) : IO (Array (String × J) × Array String) := do
  let mut entries : Array (String × J) := #[]
  let mut warnings : Array String := #[]
  -- Lean's default limit of 200000 heartbeats per entry. Heartbeats count
  -- allocations, so a view that would exhaust memory (the delaborator can
  -- do unbounded work) fails with an error instead, recorded in `errors`.
  let maxHeartbeats := s.maxHeartbeats * 1000
  -- Also as an option: work Lean does in other contexts (such as generating
  -- equation lemmas) reads the limit from there.
  let options := Lean.maxHeartbeats.set ({} : Options) s.maxHeartbeats
  let coreCtx : Core.Context := { fileName := "<imprimatur>", fileMap := default, maxHeartbeats, options }
  for r in reqs do
    let declKey := if r.key.endsWith challengeSuffix then
      (r.key.dropEnd challengeSuffix.length).toString else r.key
    let some c := env.find? (toName declKey)
      | warnings := warnings.push s!"{r.key}: no declaration with this name"
        continue
    let act : CoreM J := do
      for ns in s.openScoped do activateScoped ns
      (entryFor root s r c).run' {} {}
    let t0 ← IO.monoMsNow
    try
      let (j, _) ← act.toIO coreCtx { env }
      entries := entries.push (r.key, j)
      if verbose then
        let size := (j.field? "cone").bind (·.field? "size") |>.map (·.render) |>.getD "?"
        IO.eprintln s!"imprimatur-export: {r.key}: cone {size}, {(← IO.monoMsNow) - t0} ms"
    catch e =>
      warnings := warnings.push s!"{r.key}: {e}"
  return (entries, warnings)

/-- The text of a bundle. -/
def renderBundle (entries : Array (String × J)) (project? : Option String) : String :=
  let bundle : J := .obj #[
    ("schema", .str bundleSchema),
    ("producer", producer project?),
    ("entries", .obj entries)]
  bundle.render ++ "\n"

/-- Render every requested entry from `env`, except `@challenge` keys. -/
def exportBundle (env : Environment) (root : System.FilePath) (s : Settings)
    (reqs : Array Request) (project? : Option String := none) : IO ExportResult := do
  let (entries, warnings) ← exportEntries env root s (reqs.filter (!·.key.endsWith challengeSuffix))
  return { bundle := renderBundle entries project?, entries := entries.size, warnings }

/-- Render the `@challenge` keys: each challenge module is imported on its
own, because it declares the same names as the solution (DESIGN §10.5). -/
unsafe def exportChallenges (root : System.FilePath) (s : Settings) (reqs : Array Request) :
    IO (Array (String × J) × Array String) := do
  let mut entries : Array (String × J) := #[]
  let mut warnings : Array String := #[]
  let wanted := reqs.filter (·.key.endsWith challengeSuffix)
  let mut byModule : Array (Name × Array Request) := #[]
  for r in wanted do
    let decl := (r.key.dropEnd challengeSuffix.length).toString
    match s.challenges.find? (·.1 == decl) with
    | none => warnings := warnings.push s!"{r.key}: no comparator manifest names {decl}"
    | some (_, m) =>
      match byModule.findIdx? (·.1 == m) with
      | some i => byModule := byModule.modify i fun (m, rs) => (m, rs.push r)
      | none => byModule := byModule.push (m, #[r])
  for (m, rs) in byModule do
    match ← (Compat.importPrivate #[m]).toBaseIO with
    | .error e => warnings := warnings.push s!"cannot import challenge module {m}: {e}"
    | .ok env =>
      let (es, ws) ← exportEntries env root s rs
      entries := entries ++ es
      warnings := warnings ++ ws
  return (entries, warnings)

end Imprimatur
