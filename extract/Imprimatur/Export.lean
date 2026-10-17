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

/-- Render every requested entry from `env`. -/
def exportBundle (env : Environment) (root : System.FilePath) (s : Settings)
    (reqs : Array Request) (project? : Option String := none) : IO ExportResult := do
  let mut entries : Array (String × J) := #[]
  let mut warnings : Array String := #[]
  let coreCtx : Core.Context := { fileName := "<imprimatur>", fileMap := default, maxHeartbeats := 0 }
  for r in reqs do
    let n := toName r.key
    let some c := env.find? n
      | warnings := warnings.push s!"{r.key}: no declaration with this name"
        continue
    let act : CoreM J := do
      for ns in s.openScoped do activateScoped ns
      (entryFor root s r c).run' {} {}
    try
      let (j, _) ← act.toIO coreCtx { env }
      entries := entries.push (r.key, j)
    catch e =>
      warnings := warnings.push s!"{r.key}: {e}"
  let bundle : J := .obj #[
    ("schema", .str bundleSchema),
    ("producer", producer project?),
    ("entries", .obj entries)]
  return { bundle := bundle.render ++ "\n", entries := entries.size, warnings }

end Imprimatur
