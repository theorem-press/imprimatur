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
def producer (project? : Option String) : Producer :=
  { tool := "imprimatur-export", version, lean := some leanVersion, project := project? }

/-- The suffix of keys that name a comparator challenge's statement. -/
def challengeSuffix : String := "@challenge"

/-- Render an entry for each request from `env`. The declaration is the key,
less any `@challenge` suffix. -/
def exportEntries (env : Environment) (root : System.FilePath) (s : Settings)
    (reqs : Array Request) (verbose : Bool := false) (used : Option (IO.Ref (Array String)) := none) :
    IO (Array (String × Entry (Image TeX) Verdict) × Array String) := do
  let used ← match used with
    | some u => pure u
    | none => IO.mkRef #[]
  let mut entries : Array (String × Entry (Image TeX) Verdict) := #[]
  let mut warnings : Array String := #[]
  -- The limit of heartbeats per entry (`Settings.maxHeartbeats`). Heartbeats
  -- count allocations, so a view that would exhaust memory (the delaborator
  -- can do unbounded work) fails with an error instead, recorded in `errors`.
  let maxHeartbeats := s.maxHeartbeats * 1000
  -- Also as an option: work Lean does in other contexts (such as generating
  -- equation lemmas) reads the limit from there.
  let options := Lean.maxHeartbeats.set ({} : Options) s.maxHeartbeats
  let coreCtx : Core.Context := { fileName := "<imprimatur>", fileMap := default, maxHeartbeats, options }
  -- The views that index the document come last, so that they see what
  -- every other block rendered.
  let isIndex (r : Request) : Bool := !r.views.isEmpty && r.views.all fun v =>
    Views.indexViews.contains (parseViewSpec v).base
  let reqs := reqs.filter (!isIndex ·) ++ reqs.filter isIndex
  Render.indexEvents.set #[]
  for r in reqs do
    let declKey := if r.key.endsWith challengeSuffix then
      (r.key.dropEnd challengeSuffix.length).toString else r.key
    -- A key is an entry's (`latex_entry`), a declaration's name, a group's
    -- title, or a key of custom views only.
    let entry := (projectEntries env).find? (·.1 == declKey)
    let extra := (entry.map (·.2.2)).getD #[]
    -- A display's title is its key even when it also names a declaration
    -- (Mathlib's `Representation`, say): the author declared the display.
    let disp := ((projectDisplays env).find? (·.1 == r.key)).map (·.2)
    let decl? := match entry, disp with
      | some (_, d, _), _ => env.find? d
      | none, some _ => none
      | none, none => env.find? (toName declKey)
    if let some (_, d, _) := entry then
      if decl?.isNone then
        warnings := warnings.push s!"{r.key}: its latex_entry names {d}, which is not a declaration"
        continue
    let some c := decl?
      | -- A key that names no declaration may name a group of rules.
        let group := (projectGroups env).find? (·.title == r.key)
        let custom := !r.views.isEmpty && r.views.all fun v =>
          (projectViews env).any (·.1 == (parseViewSpec v).base) ||
            Views.indexViews.contains (parseViewSpec v).base
        if group.isSome || disp.isSome || custom then
          let act : CoreM (Entry (Image TeX) Verdict) := (groupEntry s r group used extra root disp).run' {} {}
          let t0 ← IO.monoMsNow
          match ← (act.toIO coreCtx { env }).toBaseIO with
          | .ok (j, _) => entries := entries.push (r.key, j)
          | .error e => warnings := warnings.push s!"{r.key}: {e}"
          Timing.event "entry" ((← IO.monoMsNow) - t0) [("key", Lean.toJson r.key)]
        else warnings := warnings.push s!"{r.key}: no declaration or group with this name"
        continue
    let act : CoreM (Entry (Image TeX) Verdict) := do
      for ns in s.openScoped do activateScoped ns
      (entryFor root s r c used extra).run' {} {}
    let t0 ← IO.monoMsNow
    try
      let (j, _) ← act.toIO coreCtx { env }
      entries := entries.push (r.key, j)
      if verbose then
        let size := (j.verdict.cone.map fun c => toString c.size).getD "?"
        IO.eprintln s!"imprimatur-export: {r.key}: cone {size}, {(← IO.monoMsNow) - t0} ms"
    catch e =>
      warnings := warnings.push s!"{r.key}: {e}"
    Timing.event "entry" ((← IO.monoMsNow) - t0) [("key", Lean.toJson r.key)]
  return (entries, warnings)

/-- The text of a bundle: the file is the JSON of the type (`Imprimatur.Bundle`). -/
def renderBundle (entries : Array (String × Entry (Image TeX) Verdict)) (project? : Option String) :
    String :=
  Bundle.render { producer := producer project?, entries := entries.qsort (·.1 < ·.1) }

/-- Render every requested entry from `env`, except `@challenge` keys. -/
def exportBundle (env : Environment) (root : System.FilePath) (s : Settings)
    (reqs : Array Request) (project? : Option String := none) : IO ExportResult := do
  let (entries, warnings) ← exportEntries env root s (reqs.filter (!·.key.endsWith challengeSuffix))
  return { bundle := renderBundle entries project?, entries := entries.size, warnings }

/-- Render the `@challenge` keys: each challenge module is imported on its
own, because it declares the same names as the solution (DESIGN §10.5). -/
unsafe def exportChallenges (root : System.FilePath) (s : Settings) (reqs : Array Request) :
    IO (Array (String × Entry (Image TeX) Verdict) × Array String) := do
  let mut entries : Array (String × Entry (Image TeX) Verdict) := #[]
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
