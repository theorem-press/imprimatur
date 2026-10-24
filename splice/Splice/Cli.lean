/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Strip
import Splice.Version

/-!
# The command line of `imprimatur-splice`

`Cli.run` takes the arguments and the project directory, and returns the
exit code and everything it would print, so tests can compare the output
with golden files. Exit codes: 0 for success (warnings allowed), 1 when
`check` or `apply` finds a problem, 2 for a usage, configuration or bundle
error.
-/

namespace Splice.Cli

open Imprimatur

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur-splice [--config FILE | --main FILE.tex] COMMAND [OPTIONS]

commands:
  scan [-o requests.json]      list the keys and views the document asks for
  apply --bundle B.json        regenerate blocks from a bundle
      [--force KEY]... [--keep-stale] [--rename-slot OLD=NEW]...
      [--profile P] [--commit SHA]
  check --bundle B.json        report, without writing, what apply would change
      [--diff] [--check-fail-msg MSG] [--keep-stale] [--profile P]
  strip -o DIR                 write a copy with imprimatur's markers removed
  migrate-slots --bundle B.json
                               rewrite slots declared by position as \\leanslot
  accept --bundle B.json KEY... | --all
                               record the current statement hashes in \\leancheck

The configuration is imprimatur.toml in the current directory, unless
--config or --main is given."

/-- Parsed arguments. -/
structure Args where
  /-- `--config`. -/
  config : Option String := none
  /-- `--main`. -/
  main : Option String := none
  /-- The command. -/
  command : String := ""
  /-- `--bundle`. -/
  bundle : Option String := none
  /-- `-o`. -/
  out : Option String := none
  /-- `--force`. -/
  force : Array String := #[]
  /-- `--keep-stale`. -/
  keepStale : Bool := false
  /-- `--rename-slot`. -/
  renames : Array (String × String) := #[]
  /-- `--profile`. -/
  profile : Option String := none
  /-- `--commit`. -/
  commit : Option String := none
  /-- `--diff`. -/
  diff : Bool := false
  /-- `--check-fail-msg`. -/
  failMsg : Option String := none
  /-- Keys given after the command (`accept`). -/
  keys : Array String := #[]
  /-- `--all` (`accept`). -/
  all : Bool := false
  /-- `show`'s views (`--view`); none means the document's, or `math`. -/
  views : Array String := #[]

/-- Parse the arguments. -/
partial def parseArgs (args : List String) (a : Args := {}) : Except String Args :=
  match args with
  | [] => .ok a
  | "--config" :: v :: rest => parseArgs rest { a with config := some v }
  | "--main" :: v :: rest => parseArgs rest { a with main := some v }
  | "--bundle" :: v :: rest => parseArgs rest { a with bundle := some v }
  | "-o" :: v :: rest => parseArgs rest { a with out := some v }
  | "--force" :: v :: rest => parseArgs rest { a with force := a.force.push v }
  | "--keep-stale" :: rest => parseArgs rest { a with keepStale := true }
  | "--rename-slot" :: v :: rest =>
    match v.splitOn "=" with
    | [o, n] => parseArgs rest { a with renames := a.renames.push (o, n) }
    | _ => .error s!"--rename-slot takes OLD=NEW, not {v}"
  | "--profile" :: v :: rest => parseArgs rest { a with profile := some v }
  | "--commit" :: v :: rest => parseArgs rest { a with commit := some v }
  | "--diff" :: rest => parseArgs rest { a with diff := true }
  | "--check-fail-msg" :: v :: rest => parseArgs rest { a with failMsg := some v }
  | "--all" :: rest => parseArgs rest { a with all := true }
  | "--view" :: v :: rest => parseArgs rest { a with views := a.views.push v }
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown or incomplete option {arg}"
    else if a.command.isEmpty then parseArgs rest { a with command := arg }
    else if a.command == "accept" || a.command == "show" then parseArgs rest { a with keys := a.keys.push arg }
    else .error s!"unexpected argument {arg}"

/-- Accumulated output. -/
abbrev CliM := StateT String IO

private def say (s : String) : CliM Unit :=
  modify (· ++ s ++ "\n")

private def report (ds : Array Diag) : CliM Unit := do
  for d in ds do say d.render

/-- Write a file atomically: write a temporary file, then rename it. -/
def writeAtomic (path : System.FilePath) (text : String) : IO Unit := do
  if let some dir := path.parent then
    IO.FS.createDirAll dir
  let tmp := path.toString ++ ".imprimatur-tmp"
  IO.FS.writeFile tmp text
  IO.FS.rename tmp path

private def loadConfig (root : System.FilePath) (a : Args) : ExceptT String CliM Config := do
  match a.main with
  | some m => return { main := m }
  | none =>
    let file := root / (a.config.getD "imprimatur.toml")
    unless ← file.pathExists do
      throw s!"{a.config.getD "imprimatur.toml"} not found (give --config or --main)"
    match Config.parse (← IO.FS.readFile file) with
    | .ok c => return c
    | .error e => throw s!"{a.config.getD "imprimatur.toml"}: {e}"

private def loadBundle (root : System.FilePath) (a : Args) :
    ExceptT String CliM (Bundle (Image TeX) Verdict) := do
  let some b := a.bundle | throw s!"{a.command} needs --bundle FILE"
  let file := root / b
  unless ← file.pathExists do throw s!"bundle {b} not found"
  match Bundle.parse (← IO.FS.readFile file) with
  | .ok bundle => return bundle
  | .error e => throw s!"bundle {b}: {e}"

private def applyOpts (cfg : Config) (a : Args) : Except String ApplyOpts := do
  let name := a.profile.getD cfg.defaultProfile
  let some links := cfg.profile? name | throw s!"no profile named {name}"
  return { force := a.force, keepStale := a.keepStale, renames := a.renames, links,
           commit := a.commit }

private def summary (ds : Array Diag) : String :=
  let e := (ds.filter (·.severity == .error)).size
  let w := ds.size - e
  s!"{e} error{if e == 1 then "" else "s"}, {w} warning{if w == 1 then "" else "s"}"

/-- Run a command in project directory `root`. -/
def runIn (root : System.FilePath) (a : Args) : ExceptT String CliM UInt32 := do
  let cfg ← loadConfig root a
  let doc ← (Doc.loadIO cfg root : IO Doc)
  match a.command with
  | "scan" =>
    report doc.diags
    if hasErrors doc.diags then return 1
    let text := requests doc
    match a.out with
    | some o => writeAtomic (root / o) text; say s!"scan: wrote {o}"
    | none => modify (· ++ text)
    return 0
  | "apply" | "check" | "migrate-slots" =>
    let bundle ← loadBundle root a
    let opts ← (match applyOpts cfg a with | .ok o => pure o | .error e => throw e : ExceptT String CliM _)
    let opts := { opts with migrate := a.command == "migrate-slots" }
    let o := plan doc bundle opts
    if a.command == "check" then
      -- The paper's own packages define macros too: those beside its main
      -- file, and the local files they load.
      let dir := ((root / cfg.main).parent).getD root
      let mut queue : Array System.FilePath := #[]
      for d in ← (dir.readDir : IO _) do
        if d.fileName.endsWith ".sty" || d.fileName.endsWith ".cls" then queue := queue.push d.path
      let mut seen : Array System.FilePath := #[]
      let mut extra : Array String := #[]
      while h : 0 < queue.size do
        let p := queue[0]
        queue := queue.extract 1 queue.size
        if seen.contains p || seen.size > 200 then continue
        seen := seen.push p
        let text ← (IO.FS.readFile p : IO _)
        extra := extra ++ definedMacros text
        for f in loadedFiles text do
          for c in [f, f ++ ".tex", f ++ ".sty"] do
            let q := (p.parent.getD dir) / c
            if ← (q.isDir : IO _) then continue
            if ← (q.pathExists : IO _) then queue := queue.push q
      let ds := checkDoc doc bundle opts extra a.diff
      report ds
      let failed := hasErrors ds
      if failed then
        if let some m := a.failMsg then say m
      say s!"check: {(o.changes.filter (·.contentChanged)).size} stale, {summary ds}"
      return if failed then 1 else 0
    report (sortDiags doc o.diags)
    if hasErrors o.diags then
      say s!"{a.command}: nothing written; {summary o.diags}"
      return 1
    for (path, text) in o.outputs do
      writeAtomic (root / path) text
    say s!"{a.command}: {o.changes.size} item{if o.changes.size == 1 then "" else "s"} updated in \
      {o.outputs.size} file{if o.outputs.size == 1 then "" else "s"}; {summary o.diags}"
    return 0
  | "accept" =>
    let bundle ← loadBundle root a
    if a.keys.isEmpty && !a.all then throw "accept needs the keys to accept, or --all"
    let mut ds : Array Diag := doc.diags.filter (·.severity == .error)
    let mut outputs : Array (String × String) := #[]
    let mut accepted : Array String := #[]
    let mut mentioned : Array String := #[]
    for f in doc.files do
      let mut edits : Array Edit := #[]
      for it in f.scan.items do
        unless it.kind == .check && it.name == "leancheck" do continue
        unless a.all || it.keys.any (a.keys.contains ·) do continue
        mentioned := mentioned ++ it.keys
        match checkHashes bundle it.keys with
        | none =>
          let d := Diag.err "no-hash" (f.src.locString it.start)
            s!"cannot accept {", ".intercalate it.keys.toList}: a key is missing from the bundle or has no hash"
          ds := ds.push d
        | some (stmt, sig) =>
          edits := edits ++ optEdits f.src it #[("stmt", stmt), ("sig", sig)]
          accepted := accepted ++ it.keys.filter (!accepted.contains ·)
      unless edits.isEmpty do
        outputs := outputs.push (f.src.path, applyEdits f.src edits)
    for k in a.keys do
      unless mentioned.contains k do
        ds := ds.push (Diag.warn "not-checked" "" s!"no \\leancheck mentions {k}")
    report ds
    if hasErrors ds then
      say "accept: nothing written"
      return 1
    for (path, text) in outputs do
      writeAtomic (root / path) text
    say s!"accept: recorded the hashes of {accepted.size} key{if accepted.size == 1 then "" else "s"} \
      in {outputs.size} file{if outputs.size == 1 then "" else "s"}"
    return 0
  | "strip" =>
    let some dir := a.out | throw "strip needs -o DIR"
    report doc.diags
    if hasErrors doc.diags then return 1
    let mut written := 0
    for (path, text) in stripDoc doc do
      -- A file reached through `..` is outside the project; writing it under
      -- DIR would escape DIR.
      if path.startsWith "../" || path == ".." then
        say (Diag.warn "outside-project" "" s!"{path} is outside the project, so it was not stripped").render
      else
        writeAtomic (root / dir / path) text
        written := written + 1
    say s!"strip: wrote {written} file{if written == 1 then "" else "s"} to {dir}"
    return 0
  | "" => throw "no command given"
  | c => throw s!"unknown command {c}"

/-- Run with arguments `args` in directory `root`, returning the exit code and
the output. -/
def run (args : List String) (root : System.FilePath) : IO (UInt32 × String) := do
  match args with
  | ["--version"] => return (0, s!"imprimatur-splice {version}\n")
  | ["--help"] | ["-h"] => return (0, usage ++ "\n")
  | _ =>
  match parseArgs args with
  | .error e => return (2, s!"error: {e}\n\n{usage}\n")
  | .ok a =>
    try
      let (r, out) ← (runIn root a).run.run ""
      match r with
      | .ok code => return (code, out)
      | .error e => return (2, out ++ s!"error: {e}\n")
    catch e =>
      return (2, s!"error: {e}\n")

end Splice.Cli
