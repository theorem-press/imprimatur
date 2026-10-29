/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Timing
import Testkit

/-!
# The timing log's summary (`Splice.Timing`)

A log as the splicer and the extractor write it, and what the summary says
of it: the phases, the breakdowns, and the slowest entry, view and formula.
-/

open Testkit Splice

namespace SpliceTest.Timing

/-- Whether `needle` occurs in `haystack`. -/
def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- A log of a small run: two entries, one of them a group with a view that
validates two formulas. -/
def log : String := String.join <| List.map (· ++ "\n") [
  "{\"at\": \"splice\", \"phase\": \"scan\", \"ms\": 30}",
  "{\"at\":\"extract\",\"phase\":\"load\",\"ms\":1200,\"what\":\"notation\"}",
  "{\"at\":\"extract\",\"phase\":\"stage\",\"ms\":5,\"key\":\"Stlc.Step\",\"stage\":\"axioms\"}",
  "{\"at\":\"extract\",\"phase\":\"view\",\"ms\":700,\"key\":\"Stlc.Step\",\"view\":\"rules\",\"setup_ms\":40,\"problems\":0}",
  "{\"at\":\"extract\",\"phase\":\"formula\",\"ms\":600,\"key\":\"Stlc.Step\",\"view\":\"rules\",\"render_ms\":3,\"tokens\":27,\"steps\":144481,\"readings\":1,\"tex\":\"a \\\\to b\"}",
  "{\"at\":\"extract\",\"phase\":\"formula\",\"ms\":20,\"key\":\"Stlc.Step\",\"view\":\"rules\",\"render_ms\":1,\"tokens\":5,\"steps\":90,\"readings\":1,\"tex\":\"x\"}",
  "{\"at\":\"extract\",\"phase\":\"stage\",\"ms\":710,\"key\":\"Stlc.Step\",\"stage\":\"views\"}",
  "{\"at\":\"extract\",\"phase\":\"stage\",\"ms\":2500,\"key\":\"Stlc.Step\",\"stage\":\"cone\"}",
  "{\"at\":\"extract\",\"phase\":\"entry\",\"ms\":3300,\"key\":\"Stlc.Step\"}",
  "{\"at\":\"extract\",\"phase\":\"entry\",\"ms\":100,\"key\":\"Stlc.Tm\"}",
  "{\"at\":\"extract\",\"phase\":\"entries\",\"ms\":3400,\"count\":2}",
  "{\"at\":\"extract\",\"phase\":\"write\",\"ms\":10,\"entries\":2}",
  "{\"at\":\"extract\",\"phase\":\"extractor\",\"ms\":4700}",
  "{\"at\": \"splice\", \"phase\": \"export\", \"ms\": 5000}",
  "not an event",
  "{\"at\": \"splice\", \"phase\": \"check\", \"ms\": 200}"]

/-- The summary of the log. -/
def tests : TestM Unit := group "timing" do
  -- One line of each kind parses to its fields; a line that is no event is skipped.
  match Timing.Event.parse "{\"at\":\"extract\",\"phase\":\"formula\",\"ms\":600,\"key\":\"K\",\"view\":\"rules\",\"render_ms\":3,\"tokens\":27,\"steps\":144481,\"tex\":\"t\"}" with
  | none => fail "splice/timing/parse" "a formula event did not parse"
  | some e =>
    pass
    checkEq "splice/timing/parse-fields" (e.at_, e.phase, e.ms, e.key, e.view) ("extract", "formula", 600, "K", "rules")
    checkEq "splice/timing/parse-sizes" (e.renderMs, e.tokens, e.steps, e.tex) (3, 27, 144481, "t")
  checkEq "splice/timing/parse-junk" (Timing.Event.parse "not an event").isNone true
  checkEq "splice/timing/secs" (Timing.secs 5230) "5.2 s"
  checkEq "splice/timing/thousands" (Timing.thousands 1002003) "1,002,003"
  let s := Timing.summary log ".imprimatur/timing.jsonl"
  -- The whole run is the splicer's phases, in order.
  check "splice/timing/summary-phases"
    (contains s "timing: 5.2 s in all: scan 0.0 s, export 5.0 s, check 0.2 s (.imprimatur/timing.jsonl)")
  -- The extractor's own total shows what `lake env` added to the export.
  check "splice/timing/summary-extractor" (contains s "extractor 4.7 s: load 1.2 s, entries 3.4 s, write 0.0 s")
  -- The entries' stages, and the views' setup, rendering and validation.
  check "splice/timing/summary-stages" (contains s "2 entries: axioms 0.0 s, lean view 0.0 s, views 0.7 s, cone 2.5 s")
  check "splice/timing/summary-views"
    (contains s "1 view: setup 0.0 s, rendering 0.0 s, validation 0.6 s (2 formulas, 144,571 steps)")
  -- The slowest come first, named.
  check "splice/timing/summary-slowest-entry" (contains s "slowest entries: Stlc.Step 3.3 s, Stlc.Tm 0.1 s")
  check "splice/timing/summary-slowest-view" (contains s "slowest views: Stlc.Step/rules 0.7 s")
  check "splice/timing/summary-slowest-formula"
    (contains s "0.6 s  144,481 steps  27 tokens  Stlc.Step/rules  a \\to b")
  -- Without formulas, the views line says so instead of showing zeros.
  let noFormulas := Timing.summary (String.join ((log.splitOn "\n").filter (!contains · "\"formula\"") |>.map (· ++ "\n"))) "t"
  check "splice/timing/summary-no-validation" (contains noFormulas "(no formula validated)")

end SpliceTest.Timing
