/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.ValidationLog
import Testkit

/-!
# The validation log's summary (`Splice.ValidationLog`)

A log as the extractor writes it under `--log`, and what the summary says
of it: the formulas counted by verdict.
-/

open Testkit Splice

namespace SpliceTest.ValidationLog

/-- A log of a small run: three formulas validated, one misread, one skipped. -/
def log : String := String.join <| List.map (· ++ "\n") [
  "{\"key\":\"Progress\",\"view\":\"prose\",\"tex\":\"e \\\\in \\\\mathit{Val}\",\"verdict\":\"validated\",\"readings\":[\"Membership.mem[Stlc.IsValue; e]\"],\"typed\":[\"Membership.mem[Stlc.IsValue; e]\"],\"denotes\":[\"Stlc.IsValue e\"],\"rendered\":\"Stlc.IsValue e\",\"tokens\":3,\"steps\":12,\"ms\":2,\"parse_ms\":0,\"denote_ms\":2}",
  "{\"key\":\"Progress\",\"view\":\"prose\",\"tex\":\"e\",\"verdict\":\"validated\",\"readings\":[\"e\"],\"typed\":[\"e\"],\"denotes\":[\"e\"],\"rendered\":\"e\",\"tokens\":1,\"steps\":1,\"ms\":0,\"parse_ms\":0,\"denote_ms\":0}",
  "{\"key\":\"Stlc.Tm\",\"view\":\"grammar\",\"tex\":\"x\",\"verdict\":\"misread\",\"reason\":\"misread: $x$ reads as x, which is not well typed as `Stlc.Tm.var x` is\",\"readings\":[\"x\"],\"typed\":[],\"denotes\":[],\"rendered\":\"Stlc.Tm.var x\",\"tokens\":1,\"steps\":1,\"ms\":1,\"parse_ms\":0,\"denote_ms\":1}",
  "not an event",
  "{\"key\":\"Stlc.Ty\",\"view\":\"grammar\",\"tex\":\"\\\\mathsf{b}\",\"verdict\":\"validated\",\"readings\":[\"Stlc.Ty.base\"],\"typed\":[\"Stlc.Ty.base\"],\"denotes\":[\"Stlc.Ty.base\"],\"rendered\":\"Stlc.Ty.base\",\"tokens\":1,\"steps\":1,\"ms\":0,\"parse_ms\":0,\"denote_ms\":0}",
  "{\"key\":\"Alike\",\"view\":\"math\",\"tex\":\"x = x\",\"verdict\":\"skipped\",\"reason\":\"two free variables print alike\",\"readings\":[\"Eq[x; x]\"],\"typed\":[\"Eq[x; x]\"],\"denotes\":[\"x = x\"],\"rendered\":\"x = x✝\",\"tokens\":3,\"steps\":4,\"ms\":1,\"parse_ms\":0,\"denote_ms\":1}"]

/-- The summary of the log. -/
def tests : TestM Unit := group "log" do
  -- A line parses to its fields; a line that is no event, or has no verdict, is skipped.
  match ValidationLog.Event.parse "{\"key\":\"K\",\"view\":\"rules\",\"tex\":\"t\",\"verdict\":\"misread\",\"reason\":\"why\"}" with
  | none => fail "splice/log/parse" "a formula line did not parse"
  | some e =>
    pass
    checkEq "splice/log/parse-fields" (e.key, e.view, e.tex, e.verdict, e.reason) ("K", "rules", "t", "misread", "why")
  checkEq "splice/log/parse-junk" (ValidationLog.Event.parse "not an event").isNone true
  checkEq "splice/log/parse-no-verdict" (ValidationLog.Event.parse "{\"key\":\"K\"}").isNone true
  -- The verdicts counted, in a fixed order, those with none left out.
  checkEq "splice/log/summary" (ValidationLog.summary log ".imprimatur/validation.jsonl")
    "validation: 5 formulas: 3 validated, 1 misread, 1 skipped (.imprimatur/validation.jsonl)\n"
  -- An empty log says so.
  checkEq "splice/log/summary-empty" (ValidationLog.summary "" "f") "validation: no formula read back (f)\n"

end SpliceTest.ValidationLog
