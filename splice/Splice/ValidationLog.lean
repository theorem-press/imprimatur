/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Splice.Timing

/-!
# The validation log's summary

`imprimatur build --log` (and `check`, `accept`, `show`) has the extractor
write what translation validation made of each formula to
`.imprimatur/validation.jsonl` (`Imprimatur.ValidationLog`: one JSON object
per line, with the formula's `key`, `view`, `tex`, `readings`, what the
well-typed ones denote, the term it was `rendered` from, and its `verdict`,
with a `reason` for every verdict but `validated`), and ends with the
counts of the verdicts. The file is for reading what was checked against
what; the console line is for knowing how much was.
-/

namespace Splice.ValidationLog

open Lean

/-- One line of the log; the fields the summary uses. -/
structure Event where
  /-- The entry's key. -/
  key : String
  /-- The view. -/
  view : String
  /-- The formula's TeX. -/
  tex : String
  /-- `validated`, `misread`, `ambiguous`, `not validated` or `skipped`. -/
  verdict : String
  /-- Why, for every verdict but `validated`. -/
  reason : String
  deriving Inhabited, Repr

/-- Parse one line; `none` for a line that is not an event. -/
def Event.parse (line : String) : Option Event := do
  let j ← (Json.parse line).toOption
  let str (k : String) := (j.getObjValAs? String k).toOption.getD ""
  let verdict ← (j.getObjValAs? String "verdict").toOption
  return { key := str "key", view := str "view", tex := str "tex", verdict, reason := str "reason" }

/-- The verdicts, in the order the summary names them. -/
def verdicts : List String := ["validated", "misread", "ambiguous", "not validated", "skipped"]

/-- The summary of a log, as a line for the console. -/
def summary (text : String) (file : String) : String := Id.run do
  let es := (text.splitOn "\n").toArray.filterMap Event.parse
  if es.isEmpty then return s!"validation: no formula read back ({file})\n"
  let counts := verdicts.filterMap fun v =>
    let n := (es.filter (·.verdict == v)).size
    if n == 0 then none else some s!"{n} {v}"
  s!"validation: {Timing.count es.size "formula"}: {", ".intercalate counts} ({file})\n"

end Splice.ValidationLog
