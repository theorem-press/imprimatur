/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Timing

Where the extractor's time goes, for finding what to make faster. With
`IMPRIMATUR_TIMING` set to a file, each phase, entry, stage, view and
validated formula appends one JSON line to it as it finishes,

    {"at": "extract", "phase": "formula", "ms": 312, "key": "PSS", "view": "rules",
     "render_ms": 4, "tokens": 27, "steps": 144481, "readings": 1, "tex": "…"}

with what names it (`key`, `view`, `stage`) and what sizes it (`tokens`,
the parser's `steps`). `imprimatur build --timing` sets the variable, adds
the splicer's own phases, and summarises the file (`Splice.Timing`).
-/

namespace Imprimatur.Timing

open Lean

/-- The file events are appended to, if any (`IMPRIMATUR_TIMING`). -/
initialize pathRef : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- Read `IMPRIMATUR_TIMING`: nothing is logged until this runs. -/
def start : IO Unit := do
  pathRef.set ((← IO.getEnv "IMPRIMATUR_TIMING").map fun p => (p : System.FilePath))

/-- Whether events are logged. -/
def on : IO Bool := return (← pathRef.get).isSome

/-- Append an event: its `phase`, the milliseconds it took, and its fields. -/
def event (phase : String) (ms : Nat) (fields : List (String × Json) := []) : IO Unit := do
  let some p ← pathRef.get | return
  let j := Json.mkObj ([("at", toJson "extract"), ("phase", toJson phase), ("ms", toJson ms)] ++ fields)
  let h ← IO.FS.Handle.mk p .append
  h.putStrLn j.compress

end Imprimatur.Timing
