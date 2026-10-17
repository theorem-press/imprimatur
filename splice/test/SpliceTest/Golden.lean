/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import Testkit

/-!
# Golden tests of the splicer

Each directory under `test/tex/` is a case: a small document, its
configuration and bundles, and a `steps` file. Each line of `steps` is either
the arguments of one `imprimatur-splice` command; `!in DIR ARGS…`, which runs
the command from a subdirectory; or `!replace FILE "FROM" "TO"`, which edits
a file as an author would.

The test copies the case to `.lake/work/`, runs the steps through the real
command line (`Splice.Cli.run`), and compares a transcript with
`golden/<case>.txt`. The transcript holds every command, its output and exit
code, and then every `.tex` and `requests.json` file as it ends up, with
carriage returns shown as `␍`.
-/

open Testkit

namespace SpliceTest.Golden

/-- Where the cases are, relative to this test package. -/
def casesDir : System.FilePath := "../../test/tex"

/-- Where the golden transcripts are. -/
def goldenDir : System.FilePath := "golden"

/-- Where cases run. -/
def workDir : System.FilePath := ".lake/work"

/-- Split a line into words, honouring double quotes; inside quotes, `\"`
stands for a quote and every other backslash is literal. -/
def splitWords (line : String) : List String := Id.run do
  let cs := line.toList.toArray
  let mut words : Array String := #[]
  let mut cur := ""
  let mut inQuote := false
  let mut started := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if inQuote && c == '\\' && cs.getD (i + 1) ' ' == '"' then
      cur := cur.push '"'; i := i + 2; continue
    if c == '"' then
      inQuote := !inQuote; started := true
    else if c == ' ' && !inQuote then
      if started then words := words.push cur
      cur := ""; started := false
    else
      cur := cur.push c; started := true
    i := i + 1
  if started then words := words.push cur
  return words.toList

/-- Copy a directory tree. -/
partial def copyTree (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if ← e.path.isDir then
      copyTree e.path (dst / e.fileName)
    else
      IO.FS.writeBinFile (dst / e.fileName) (← IO.FS.readBinFile e.path)

/-- All files under a directory, as sorted relative paths. -/
def listFiles (dir : System.FilePath) : IO (Array String) := do
  let all ← dir.walkDir
  let mut out := #[]
  for p in all do
    unless ← p.isDir do
      let rel := (p.toString.drop (dir.toString.length + 1)).toString
      out := out.push rel
  return out.qsort (· < ·)

/-- Show carriage returns. -/
def visible (s : String) : String :=
  s.replace "\r" "␍"

/-- Run one case and return its transcript. -/
def transcript (name : String) : IO String := do
  let work := workDir / name
  if ← work.pathExists then IO.FS.removeDirAll work
  copyTree (casesDir / name) work
  let steps ← IO.FS.readFile (work / "steps")
  let mut out := ""
  for line in steps.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match splitWords line with
    | ["!replace", file, a, b] =>
      let t ← IO.FS.readFile (work / file)
      match t.splitOn a with
      | first :: rest@(_ :: _) =>
        IO.FS.writeFile (work / file) (first ++ b ++ a.intercalate rest)
        out := out ++ s!"! replace in {file}: {a} => {b}\n\n"
      | _ => out := out ++ s!"! replace in {file} FAILED: {a} not found\n\n"
    | "!in" :: dir :: args =>
      let (code, o) ← Splice.Cli.run args (work / dir)
      out := out ++ s!"$ (in {dir}) imprimatur-splice {" ".intercalate args}\n{visible o}[exit {code}]\n\n"
    | args =>
      let (code, o) ← Splice.Cli.run args work
      out := out ++ s!"$ imprimatur-splice {line}\n{visible o}[exit {code}]\n\n"
  for f in ← listFiles work do
    if f.endsWith ".tex" || f.endsWith "requests.json" then
      out := out ++ s!"== {f}\n{visible (← IO.FS.readFile (work / f))}\n"
  return out

/-- The cases, by test name. A case directory not listed here is an error,
so none is skipped by accident. -/
def cases : Array String := #[
  "splice/golden/basic",
  "splice/golden/blueprint",
  "splice/golden/bundle-errors",
  "splice/golden/comments-verbatim",
  "splice/golden/cone",
  "splice/golden/config-errors",
  "splice/golden/crlf",
  "splice/golden/drift",
  "splice/golden/failures",
  "splice/golden/hand-edit",
  "splice/golden/macro-args",
  "splice/golden/manifests",
  "splice/golden/meta-source",
  "splice/golden/migrate-slots",
  "splice/golden/notation-config",
  "splice/golden/outside",
  "splice/golden/parse-errors",
  "splice/golden/positional-slots",
  "splice/golden/refs",
  "splice/golden/slots",
  "splice/golden/strip",
  "splice/golden/unicode"]

/-- Every case, compared with its golden transcript. -/
def tests : TestM Unit := group "golden" do
  let mut dirs := #[]
  for e in ← casesDir.readDir do
    if ← e.path.isDir then dirs := dirs.push e.fileName
  let listed := cases.map (·.drop "splice/golden/".length |>.toString)
  checkEq "splice/golden/all-cases-listed" (listed.qsort (· < ·)) (dirs.qsort (· < ·))
  for c in cases do
    let dir := (c.drop "splice/golden/".length).toString
    golden c (goldenDir / s!"{dir}.txt") (← transcript dir)

end SpliceTest.Golden
