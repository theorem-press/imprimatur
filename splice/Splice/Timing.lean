/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Timing

`imprimatur build --timing` (and `check`, `accept`, `show`) records where the
time went, in `.imprimatur/timing.jsonl`, and ends with a summary of it.

The file has one JSON object per line. The splicer writes its phases
(`{"at": "splice", "phase": "scan" | "export" | "apply" | …, "ms": …}`),
and the extractor, with `IMPRIMATUR_TIMING` naming the file, writes its own
(`Imprimatur.Timing`): `load`, `entries` and `write`; one `entry` per key;
one `stage` per stage of an entry (`axioms`, `lean view`, `views`, `cone`);
one `view` per view rendered, with its `setup_ms` (the context and the
grammar); and, when formulas are validated, one `formula` each, with its
`render_ms`, `tokens`, the parser's `steps`, and its `tex`.

The summary names the slowest entries, views and formulas, so that the first
thing to make faster is on the console; the file is for the rest.
-/

namespace Splice.Timing

open Lean

/-- One line of the log. Fields an event lacks are empty or zero. -/
structure Event where
  /-- Who logged it: `splice` or `extract`. -/
  at_ : String
  /-- What it times: `scan`, `export`, `load`, `entry`, `stage`, `view`, `formula`, … -/
  phase : String
  /-- How long it took. -/
  ms : Nat
  /-- The entry's key, for an entry, a stage, a view or a formula. -/
  key : String
  /-- The view, for a view or a formula. -/
  view : String
  /-- The stage, for a stage: `axioms`, `lean view`, `views`, `cone`. -/
  stage : String
  /-- A formula's tokens. -/
  tokens : Nat
  /-- The steps the parser took reading a formula back. -/
  steps : Nat
  /-- The time rendering a formula took, before reading it back. -/
  renderMs : Nat
  /-- The time a view's context and grammar took. -/
  setupMs : Nat
  /-- A formula's TeX, cut to its start. -/
  tex : String
  deriving Inhabited

/-- Parse one line; `none` for a line that is not an event. -/
def Event.parse (line : String) : Option Event := do
  let j ← (Json.parse line).toOption
  let str (k : String) := (j.getObjValAs? String k).toOption.getD ""
  let nat (k : String) := (j.getObjValAs? Nat k).toOption.getD 0
  return { at_ := str "at", phase := str "phase", ms := nat "ms", key := str "key",
           view := str "view", stage := str "stage", tokens := nat "tokens", steps := nat "steps",
           renderMs := nat "render_ms", setupMs := nat "setup_ms", tex := str "tex" }

/-- Milliseconds as seconds, to one decimal. -/
def secs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100} s"

/-- A count with thousands separated. -/
def thousands (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let r := n % 1000
    thousands (n / 1000) ++ "," ++ (if r < 10 then "00" else if r < 100 then "0" else "") ++ toString r

/-- The sum of `ms` over the events `p` selects. -/
def total (es : Array Event) (p : Event → Bool) : Nat :=
  es.foldl (fun n e => if p e then n + e.ms else n) 0

/-- The top `n` of `es` by `f`, descending. -/
def top (es : Array Event) (n : Nat) (f : Event → Nat := (·.ms)) : Array Event :=
  (es.qsort fun a b => f a > f b).extract 0 n

/-- `how many` of `what`, with the plural. -/
def count (n : Nat) (what : String) (plural : String := what ++ "s") : String :=
  s!"{thousands n} {if n == 1 then what else plural}"

/-- The summary of a log, as lines for the console. -/
def summary (text : String) (file : String) : String := Id.run do
  let es := (text.splitOn "\n").toArray.filterMap Event.parse
  let splice := es.filter (·.at_ == "splice")
  let extract := es.filter (·.at_ == "extract")
  let ephase (name : String) := total extract (·.phase == name)
  let stages := extract.filter (·.phase == "stage")
  let stage (name : String) := total stages (·.stage == name)
  let entries := extract.filter (·.phase == "entry")
  let views := extract.filter (·.phase == "view")
  let formulas := extract.filter (·.phase == "formula")
  let whole := total splice (fun _ => true)
  let steps := formulas.foldl (· + ·.steps) 0
  let mut out := #[s!"timing: {secs whole} in all: " ++
    ", ".intercalate (splice.toList.map fun e => s!"{e.phase} {secs e.ms}") ++ s!" ({file})"]
  unless extract.isEmpty do
    out := out.push s!"  export: extractor {secs (ephase "extractor")}: load {secs (ephase "load")}, \
      entries {secs (ephase "entries")}, write {secs (ephase "write")}"
    out := out.push s!"  {count entries.size "entry" "entries"}: axioms {secs (stage "axioms")}, \
      lean view {secs (stage "lean view")}, views {secs (stage "views")}, cone {secs (stage "cone")}"
    let line := s!"  {count views.size "view"}: setup {secs (views.foldl (· + ·.setupMs) 0)}"
    out := out.push <| if formulas.isEmpty then line ++ " (no formula validated)" else
      line ++ s!", rendering {secs (formulas.foldl (· + ·.renderMs) 0)}, \
        validation {secs (total formulas fun _ => true)} \
        ({count formulas.size "formula"}, {thousands steps} steps)"
    unless entries.isEmpty do
      out := out.push ("  slowest entries: " ++
        ", ".intercalate ((top entries 5).toList.map fun e => s!"{e.key} {secs e.ms}"))
    unless views.isEmpty do
      out := out.push ("  slowest views: " ++
        ", ".intercalate ((top views 5).toList.map fun e => s!"{e.key}/{e.view} {secs e.ms}"))
    unless formulas.isEmpty do
      out := out.push "  slowest formulas:"
      for e in top formulas 5 do
        out := out.push s!"    {secs e.ms}  {thousands e.steps} steps  {count e.tokens "token"}  \
          {e.key}/{e.view}  {e.tex}"
  return String.join (out.toList.map (· ++ "\n"))

end Splice.Timing
