/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Bundle
import Splice.Sha256

/-!
# The verified checker

With `[trust].checker = "con-leche"` (DESIGN §7.8), `imprimatur build` has
the development checked by con-leche, the checker the Lean toolchain ships
with a proof that whatever it accepts has a model: `leanexport` writes
everything the extractor's modules import as one stream of declarations,
`con-leche` reads it, and its verdict goes into the bundle, where `check`
requires it to be *accepted*.

A verdict is on the whole development, and costs minutes on a large one,
so it is kept: `.imprimatur/checker.json` holds the last verdict with a
fingerprint of what it was about, the toolchain, the modules, and every
`.olean` on the project's search path (by Lake's hash of it, or its size and
modification time), and a run whose fingerprint matches reads the verdict
back instead of checking again.
-/

namespace Splice.Checker

open Imprimatur

/-- The verdicts, by con-leche's exit code (the Lean kernel arena's): 0
accepted, 1 rejected, 2 declined. 3 is an error of the run, not a verdict. -/
def verdictOfExit : UInt32 → Option Checker.Verdict
  | 0 => some .accepted
  | 1 => some .rejected
  | 2 => some .declined
  | _ => none

/-- The last line that says something, which is con-leche's verdict line. -/
def lastLine (out : String) : String :=
  ((out.splitOn "\n").filter (!·.trimAscii.isEmpty)).getLast?.getD "" |>.trimAscii.toString

/-- Run a command under the project's `lake env`. -/
def lakeEnv (leanDir : System.FilePath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "lake", args := #["env"] ++ args, cwd := leanDir }

/-- What a verdict depends on, as one hash: the tool, the toolchain, the
modules, and each `.olean` on the search path with Lake's hash of it, or,
without one, its size and modification time. Anything else that changes the
stream (`leanexport` itself) comes with the toolchain. -/
def fingerprint (leanDir : System.FilePath) (tool : String) (modules : Array String) :
    ExceptT String IO String := do
  let toolchain ← (do
    let f := leanDir / "lean-toolchain"
    if ← f.pathExists then IO.FS.readFile f else pure "" : IO String)
  let out ← lakeEnv leanDir #["printenv", "LEAN_PATH"]
  if out.exitCode != 0 then
    throw s!"`lake env printenv LEAN_PATH` failed in {leanDir}:\n{out.stdout}{out.stderr}"
  let mut lines : Array String := #[s!"tool {tool}", s!"toolchain {toolchain.trimAscii}"]
  for m in modules do lines := lines.push s!"module {m}"
  for dir in System.SearchPath.parse out.stdout.trimAscii.toString do
    unless ← dir.isDir do continue
    for p in (← dir.walkDir).qsort (·.toString < ·.toString) do
      unless p.extension == some "olean" do continue
      let hashFile : System.FilePath := p.toString ++ ".hash"
      let stamp ← if ← hashFile.pathExists then IO.FS.readFile hashFile else do
        let md ← p.metadata
        pure s!"{md.byteSize} {md.modified.sec}.{md.modified.nsec}"
      lines := lines.push s!"{p} {stamp.trimAscii}"
  return Sha256.hexOf ("\n".intercalate lines.toList)

/-- Where the last verdict is kept. -/
def cacheFile (work : System.FilePath) : System.FilePath := work / "checker.json"

/-- The kept verdict, if it is about what `fp` fingerprints. -/
def cached (work : System.FilePath) (fp : String) : IO (Option Checker) := do
  let f := cacheFile work
  unless ← f.pathExists do return none
  let some j := (Lean.Json.parse (← IO.FS.readFile f)).toOption | return none
  unless (j.getObjValAs? String "fingerprint").toOption == some fp do return none
  let some c := (j.getObjVal? "checker").toOption | return none
  return (Checker.ofJson c).toOption

/-- Keep a verdict with its fingerprint. -/
def keep (work : System.FilePath) (fp : String) (c : Checker) : IO Unit :=
  IO.FS.writeFile (cacheFile work)
    ((Lean.Json.mkObj [("fingerprint", .str fp), ("checker", c.toJson)]).pretty ++ "\n")

/-- Write a process's standard output to a file as it comes, since an export
is too large to hold; returns the exit code and the standard error. -/
def spawnToFile (leanDir : System.FilePath) (args : Array String) (file : System.FilePath) :
    IO (UInt32 × String) := do
  let spawnArgs : IO.Process.SpawnArgs :=
    { cmd := "lake", args := #["env"] ++ args, cwd := leanDir, stdout := .piped, stderr := .piped }
  let child ← IO.Process.spawn spawnArgs
  let h ← IO.FS.Handle.mk file .write
  repeat
    let buf ← child.stdout.read (1048576 : USize)
    if buf.isEmpty then break
    h.write buf
  h.flush
  -- Read after the output is drained: `leanexport` says little on stderr,
  -- so the pipe does not fill while the file is written.
  let err ← child.stderr.readToEnd
  let code ← child.wait
  return (code, err)

/-- The hint when a tool is missing: the toolchains that have it, and how to
go without. -/
def hint : String :=
  "\n(leanexport and con-leche come with Lean v4.35 and later; to go by Lean's own verdict \
   instead, unset [trust].checker, or run with --no-checker)"

/-- The two halves of a run that was not kept, in milliseconds: `leanexport`
writing the stream, and the checker reading it. Both zero for a kept verdict. -/
structure Times where
  /-- `leanexport` writing the stream of the modules. -/
  export_ms : Nat := 0
  /-- The checker reading and checking it. -/
  check_ms : Nat := 0

/-- Check the development with `tool`: the kept verdict when the development
has not changed, else `leanexport` of the modules into `work`, read by the
checker, and the verdict kept. Returns the verdict, whether it was kept
from before, and the time each half took. -/
def run (leanDir work : System.FilePath) (tool : String) (modules : Array String) :
    ExceptT String IO (Checker × Bool × Times) := do
  let fp ← fingerprint leanDir tool modules
  if let some c ← cached work fp then return (c, true, {})
  let stream := work / "export.ndjson"
  try
    let t0 ← IO.monoMsNow
    let (code, err) ← spawnToFile leanDir (#["leanexport"] ++ modules) stream
    let t1 ← IO.monoMsNow
    if code != 0 then
      throw s!"`lake env leanexport {" ".intercalate modules.toList}` failed in {leanDir}:\n{err}{hint}"
    let out ← lakeEnv leanDir #[tool, stream.toString]
    let t2 ← IO.monoMsNow
    let report := lastLine (out.stdout ++ "\n" ++ out.stderr)
    let some verdict := verdictOfExit out.exitCode
      | throw s!"`lake env {tool}` failed in {leanDir}:\n{out.stdout}{out.stderr}{hint}"
    let c : Checker := { tool, verdict, modules, report }
    keep work fp c
    return (c, false, { export_ms := t1 - t0, check_ms := t2 - t1 })
  finally
    if ← stream.pathExists then IO.FS.removeFile stream

end Splice.Checker
