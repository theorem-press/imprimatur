/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# The validation log

What translation validation made of each formula (DESIGN §18.4), for
reading: with `IMPRIMATUR_VALIDATION_LOG` set to a file, each formula read
back appends one JSON line to it,

    {"key": "Progress", "view": "prose", "tex": "e \\in \\mathit{Val} …",
     "verdict": "validated", "readings": ["Or[Membership.mem[…]; ∃[…]]"],
     "typed": ["Or[…]"], "denotes": ["Stlc.IsValue e ∨ ∃ e', Stlc.Step e e'"],
     "rendered": "Stlc.IsValue e ∨ ∃ e', Stlc.Step e e'", "tokens": 12,
     "steps": 310, "ms": 9, "parse_ms": 1, "denote_ms": 8}

with the verdict one of `validated`, `misread`, `ambiguous`, `not validated`
and `skipped`, and a `reason` for every verdict but the first: the problem
as `check` reports it, or why the formula was skipped. `normalised` is the
formula as the notation reads it (`Render.normalise`), when that differs
from `rendered`. `imprimatur build --log` sets the variable and counts the
verdicts at the end (`Splice.ValidationLog`).
-/

namespace Imprimatur.ValidationLog

open Lean

/-- The file events are appended to, if any (`IMPRIMATUR_VALIDATION_LOG`). -/
initialize pathRef : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- Read `IMPRIMATUR_VALIDATION_LOG`: nothing is logged until this runs. -/
def start : IO Unit := do
  pathRef.set ((← IO.getEnv "IMPRIMATUR_VALIDATION_LOG").map fun p => (p : System.FilePath))

/-- Whether formulas are logged. -/
def on : IO Bool := return (← pathRef.get).isSome

/-- Append a formula's line, from its fields. -/
def event (fields : List (String × Json)) : IO Unit := do
  let some p ← pathRef.get | return
  let h ← IO.FS.Handle.mk p .append
  h.putStrLn (Json.mkObj fields).compress

end Imprimatur.ValidationLog
