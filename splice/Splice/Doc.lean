/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Scan
import Splice.Manifests

/-!
# Documents

A document is the main file and every file it reaches through `\input`,
`\include` and `\subfile` (DESIGN §10.1). As in LaTeX, input paths are
relative to the directory of the main file. Loading is generic in how files
are read, so tests can load documents held in memory.
-/

namespace Splice

/-- A file of a document, with what scanning it found. -/
structure SourceFile where
  /-- The text. -/
  src : Src
  /-- What the scanner found. -/
  scan : ScanResult
  /-- The file cut into chunks, text and items, by the verified scanner;
  they print back to the text (`Core.Scan.print_scan`). -/
  chunks : List Core.Scan.Chunk := []
  /-- The `\newif` switches declared before the file was scanned. -/
  switchesIn : Switches := #[]
  /-- Whether the file was scanned as typeset (before the document's own
  liveness is applied). -/
  scannedLive : Bool := true
  /-- Whether the file is typeset: reached from a branch that is on. -/
  live : Bool := true

/-- A loaded document. -/
structure Doc where
  /-- The configuration. -/
  cfg : Config
  /-- The files, the main file first, then in the order they were reached.
  Files that failed to scan are left out. -/
  files : Array SourceFile
  /-- Problems found while loading. -/
  diags : Array Diag
  /-- Comparator manifests (DESIGN §10.5). -/
  manifests : Array Manifest := #[]

/-- Normalise a `/`-separated relative path: drop `.` and empty components,
and resolve `..` where possible. -/
def normPath (p : String) : String := Id.run do
  let mut out : Array String := #[]
  for c in p.splitOn "/" do
    if c == "" || c == "." then continue
    if c == ".." && !out.isEmpty && out.back! != ".." then
      out := out.pop
    else
      out := out.push c
  return "/".intercalate out.toList

/-- The directory part of a relative path (`""` for the top). -/
def dirOf (p : String) : String :=
  match p.splitOn "/" with
  | [] | [_] => ""
  | parts => "/".intercalate parts.dropLast

/-- The paths LaTeX tries for an input, most likely first. -/
def inputCandidates (mainDir macroName path : String) : List String :=
  let base := normPath (if mainDir.isEmpty then path else mainDir ++ "/" ++ path)
  if macroName == "include" then [base ++ ".tex"]
  else if base.endsWith ".tex" then [base]
  else [base ++ ".tex", base]

/-- Load a document, reading files with `read` (which returns `none` for a
missing file). Paths are relative to the project root. -/
def Doc.load {m : Type → Type} [Monad m] (cfg : Config) (read : String → m (Option String)) :
    m Doc := do
  let main := normPath cfg.main
  let mainDir := dirOf main
  let mut files : Array SourceFile := #[]
  let mut diags : Array Diag := #[]
  let mut seen : Array String := #[main]
  -- Each file to scan: its path, where it was reached from, and whether it
  -- is typeset (a file reached only from branches that are off is not).
  let mut queue : Array (String × String × Bool) := #[(main, "", true)]
  let mut qi := 0
  -- `\newif` switches carry over from one file to the next.
  let mut switches : Switches := #[]
  let mut liveFiles : Array String := #[main]
  while h : qi < queue.size do
    let (path, from_, live) := queue[qi]
    qi := qi + 1
    let some text ← read path
      | if from_.isEmpty then
          diags := diags.push (Diag.err "missing-main" "" s!"the main file {path} does not exist")
        else
          diags := diags.push (Diag.warn "missing-input" from_
            s!"{path} does not exist, so it was not scanned (it may be generated later)")
        continue
    let src := Src.ofString path text
    match scanChunks cfg src switches live with
    | .error d => diags := diags.push d
    | .ok (chunks, scan, sw) =>
      files := files.push { src, scan, chunks, switchesIn := switches, scannedLive := live }
      switches := sw
      for (macroName, p, pos, inputLive) in scan.inputs do
        if p.startsWith "/" || p.startsWith "\\" || (p.toList.getD 1 ' ') == ':' then
          let d := Diag.warn "absolute-input" (src.locString pos)
            s!"{p} is an absolute path, so it was not followed (use a path relative to the main file)"
          diags := diags.push d
          continue
        let cands := inputCandidates mainDir macroName p
        -- Prefer a candidate that exists.
        let mut chosen := cands.headD p
        for c in cands do
          if (← read c).isSome then chosen := c; break
        if seen.contains chosen then
          -- Reached again, from a typeset place: the file is typeset.
          if live && inputLive then
            queue := queue.map fun (q, f, l) => if q == chosen then (q, f, true) else (q, f, l)
            liveFiles := liveFiles.push chosen
        else
          seen := seen.push chosen
          queue := queue.push (chosen, src.locString pos, live && inputLive)
          if live && inputLive then liveFiles := liveFiles.push chosen
  -- Items of a file that is not typeset are not typeset; nor are its labels.
  files := files.map fun f =>
    if liveFiles.contains f.src.path then f
    else { f with live := false, scan := { f.scan with
      items := f.scan.items.map ({ · with live := false }), labels := #[] } }
  return { cfg, files, diags }

/-- Load a document, and its comparator manifests, from disk; paths are
relative to `root`. -/
def Doc.loadIO (cfg : Config) (root : System.FilePath) : IO Doc := do
  let doc ← Doc.load cfg fun p => do
    let f := root / p
    if ← f.pathExists then
      if ← f.isDir then return none
      return some (← IO.FS.readFile f)
    else return none
  let (manifests, ds) ← loadManifests cfg root
  return { doc with manifests, diags := doc.diags ++ ds }

/-- Load a document held in memory as `(path, text)` pairs. -/
def Doc.ofFiles (cfg : Config) (files : Array (String × String)) : Doc :=
  Id.run <| Doc.load cfg fun p => pure ((files.find? (·.1 == p)).map (·.2))

end Splice
