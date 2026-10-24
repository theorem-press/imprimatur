/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import Testkit
import SpliceTest.Reference

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
  for root in ["../../test/tex", "../../examples", "../../about"] do
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

end SpliceTest.Diff
