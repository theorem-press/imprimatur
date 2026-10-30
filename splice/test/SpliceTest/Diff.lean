/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import Testkit
import SpliceTest.Reference
import SpliceTest.Props

/-!
# Differential tests (docs/verified-splicer.md, phase 0)

The verified core must behave exactly as the code it replaces. Each test
runs both, on generated text and on a corpus of real files (every `.tex`
file of the repository's test cases, examples and the about paper), and
compares them.
-/

open Testkit

namespace SpliceTest.Diff

/-- Text with what the text kernel cares about: line endings, blanks,
blank lines, and characters outside ASCII. -/
def text : Gen String :=
  Gen.stringOf #['a', 'b', ' ', '\t', '\r', '\n', '\n', 'é', '𝔽', '%']

/-- The text kernel agrees with the reference on one text. -/
def textAgrees (t : String) : Except String Unit := do
  let lf := Splice.toLf t
  expect (lf == Reference.toLf t) s!"toLf: {repr lf} ≠ {repr (Reference.toLf t)}"
  let n := Splice.normalize t
  expect (n == Reference.normalize t) s!"normalize: {repr n} ≠ {repr (Reference.normalize t)}"
  for eol in ["\n", "\r\n"] do
    let w := Splice.withEol eol lf
    expect (w == Reference.withEol eol lf) s!"withEol {repr eol}: {repr w} ≠ {repr (Reference.withEol eol lf)}"
  let cs := t.toList.toArray
  expect (Splice.dominantEol cs == Reference.dominantEol cs) "dominantEol differs"

/-- The `.tex` files of the corpus, relative to this directory. -/
partial def corpus : IO (Array System.FilePath) := do
  let mut out := #[]
  for root in ["../../test/tex", "../../examples"] do
    out := out ++ (← walk root)
  return out.qsort (·.toString < ·.toString)
where
  walk (d : System.FilePath) : IO (Array System.FilePath) := do
    unless ← d.isDir do return #[]
    let mut out := #[]
    for e in ← d.readDir do
      if e.fileName.startsWith "." then continue
      if ← e.path.isDir then out := out ++ (← walk e.path)
      else if e.path.extension == some "tex" then out := out.push e.path
    return out

/-- What a scan gives, as text: its result, or its error. -/
def scanShown (r : Splice.ScanM (Splice.ScanResult × Splice.Switches)) : String :=
  match r with
  | .ok v => (repr v).pretty
  | .error d => d.render

/-- The scanner agrees with the reference on one file, typeset or not, and
with or without switches declared. -/
def scanAgrees (cfg : Splice.Config) (path text : String) : Except String Unit := do
  let s := Splice.Src.ofString path text
  for live in [true, false] do
    for sw in [#[], #[("draft", true), ("final", false)]] do
      let new := scanShown (Splice.scanSrcWith cfg s sw live)
      let old := scanShown (Reference.scanSrcWith cfg s sw live)
      expect (new == old) s!"scan (live={live}, switches={sw}) differs:\n  new: {new}\n  old: {old}"

/-- The configuration a corpus file is scanned with: its directory's
`imprimatur.toml`, or the nearest above it, or the property tests'. -/
partial def configFor (f : System.FilePath) : IO Splice.Config := do
  let rec up (d : System.FilePath) (n : Nat) : IO Splice.Config := do
    let t := d / "imprimatur.toml"
    if ← t.pathExists then
      match Splice.Config.parse (← IO.FS.readFile t) with
      | .ok c => return c
      | .error _ => return Props.config
    match d.parent with
    | some p => if n == 0 then return Props.config else up p (n - 1)
    | none => return Props.config
  up (f.parent.getD ".") 4

/-- A region's text, with what the slot finder must get right: `\leanslot`s,
repeated ids, slots by position (some holding exactly one `\leanslot`),
comments, spacing, malformed macros and unbalanced braces. -/
def region : Gen String := do
  let parts ← Gen.listOf (Gen.frequency [
    (3, Props.content true), (2, Props.grammarContent),
    (1, Gen.elem #["\\entry{v}{ \\leanslot{s1}{inner} }", "\\entry{x}{\\leanslot{s0}{a}b}",
      "% \\leanslot{s0}{in a comment}\n", "\\leanslot{s2}", "\\leanslot {s0} {spaced}",
      "\\entry{x}", "{", "}", "\\leanslot{s0}{", "\\\\leanslot", "100\\%", "\r\n"])])
  return "\n".intercalate parts

/-- What a slot list is, as text. -/
def slotsShown (sl : Array Splice.Slot) : String := (repr sl).pretty

/-- The slot finder and the merge agree with the reference on one region,
and one pair of regions. -/
def slotsAgree (old new : String) : Except String Unit := do
  for spec in [none, some { macros := #["\\entry"], arg := 2, idArg := 1 : Splice.SlotSpec }] do
    for t in [old, new] do
      let a := slotsShown (Splice.findSlots spec t)
      let b := slotsShown (Reference.findSlots spec t)
      expect (a == b) s!"findSlots differs on {repr t}:\n  new: {a}\n  old: {b}"
    for renames in [#[], #[("s0", "s1")], #[("x", "v"), ("s2", "s0")]] do
      let o : Splice.ApplyOpts := { renames }
      let (m1, o1) := Splice.mergeSlots o spec old new
      let (m2, o2) := Reference.mergeSlots o spec old new
      expect (m1 == m2) s!"mergeSlots differs (renames {renames}):\n  old: {repr old}\n  new: {repr new}\n  got: {repr m1}\n  ref: {repr m2}"
      expect (slotsShown o1 == slotsShown o2) s!"orphans differ (renames {renames})"

/-- How long scanning takes, in milliseconds, and the length of what it
gives (which forces the work). -/
def timeScan (f : Unit → String) : IO (Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let n := (f ()).length
  let t1 ← IO.monoMsNow
  return (t1 - t0, n)

/-- The timing gate (docs/verified-splicer.md, Performance): on the built
semantics example repeated to about 0.8 MB and 1.6 MB, the scanner is at
most five times slower than the reference, and doubling the input at most
about doubles its time. The largest also checks that the scanner's recursion
is not as deep as the file. -/
def scanSpeed : TestM Unit := do
  let path : System.FilePath := "../../examples/semantics/expected/paper.tex"
  let base ← IO.FS.readFile path
  let cfg ← configFor path
  let mut times : Array Nat := #[]
  for k in [64, 128] do
    let s := Splice.Src.ofString "big.tex" (String.join (List.replicate k base))
    let (tn, n1) ← timeScan fun _ => scanShown (Splice.scanSrcWith cfg s #[] true)
    let (to, n2) ← timeScan fun _ => scanShown (Reference.scanSrcWith cfg s #[] true)
    IO.println s!"  scan of {s.size / 1000} K characters: {tn} ms, reference {to} ms"
    check s!"splice/diff/scan-speed-{k}" (n1 == n2 && tn ≤ 5 * to + 100)
      s!"the scanner took {tn} ms, the reference {to} ms"
    times := times.push tn
  if let #[t1, t2] := times then
    check "splice/diff/scan-linear" (t2 ≤ 3 * t1 + 100)
      s!"doubling the input took the scanner from {t1} ms to {t2} ms"

/-- The differential tests. -/
def tests : TestM Unit := group "differential" do
  forAll "splice/diff/text" text (fun t => (repr t).pretty) textAgrees
  let files ← corpus
  check "splice/diff/corpus-found" (files.size > 20) s!"only {files.size} corpus files"
  let mut bad := #[]
  for f in files do
    match textAgrees (← IO.FS.readFile f) with
    | .ok () => pure ()
    | .error e => bad := bad.push s!"{f}: {e}"
  check "splice/diff/text-corpus" bad.isEmpty ("\n".intercalate bad.toList)
  -- The scanner, on generated documents and noise, and on the corpus.
  forAll "splice/diff/scan" Props.docAndBundle (fun x => Props.showFiles x.1) fun (fs, _) =>
    fs.forM fun (p, t) => scanAgrees Props.config p t
  forAll "splice/diff/scan-noise" Props.texNoise (fun t => (repr t).pretty)
    (scanAgrees Props.config "r.tex")
  forAll "splice/diff/scan-truncated" Props.truncated (fun t => (repr t).pretty)
    (scanAgrees Props.config "r.tex")
  let mut badScan := #[]
  for f in files do
    match scanAgrees (← configFor f) f.toString (← IO.FS.readFile f) with
    | .ok () => pure ()
    | .error e => badScan := badScan.push s!"{f}: {e}"
  check "splice/diff/scan-corpus" badScan.isEmpty ("\n".intercalate badScan.toList)
  scanSpeed
  -- Slots: on generated regions, and on whole corpus files as regions.
  forAll "splice/diff/slots" (do return (← region, ← region)) (fun p => (repr p).pretty)
    fun (a, b) => slotsAgree a b
  let mut badSlots := #[]
  for f in files do
    let t ← IO.FS.readFile f
    match slotsAgree t t with
    | .ok () => pure ()
    | .error e => badSlots := badSlots.push s!"{f}: {e}"
  check "splice/diff/slots-corpus" badSlots.isEmpty ("\n".intercalate badSlots.toList)

end SpliceTest.Diff
