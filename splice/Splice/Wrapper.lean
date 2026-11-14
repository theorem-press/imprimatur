/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Cli
import Splice.Checker
import Splice.Timing

/-!
# The `imprimatur` command

`imprimatur build` runs the whole flow (DESIGN §5): `scan`, then the
extractor, then `apply`. `imprimatur check` and `imprimatur accept` do the
same with `check` or `accept` instead of `apply`. `imprimatur show KEY`
runs the extractor for one key and prints its renderings, writing nothing.
Every other command is the splicer's.

With `[trust].checker` set, the verified checker runs alongside the
extractor, on the same modules, and its verdict is written into the bundle
(`Splice.Checker`, DESIGN §7.8); `--no-checker` leaves it out for a run.

How the extractor runs depends on the mode (DESIGN §6.3):

- **in-project, sidecar:** `lake exe imprimatur-export`, run in `lean_project`,
  a package that requires `imprimatur` (the host itself, or a sidecar next to
  it). The modules in `imports` are built first.
- **external:** an extractor built for the host's toolchain, by
  `imprimatur toolchain install` ahead of time or by the first `build`,
  `check` or `show` that finds none cached (`--no-install` fails instead),
  run under the host's `lake env`. The host doesn't change and isn't built.

Requests and the bundle go in `.imprimatur/` next to `imprimatur.toml`.
With `--timing`, so does `timing.jsonl`, where the splicer and the extractor
record where the time went, summarised at the end (`Splice.Timing`).
-/

namespace Splice.Wrapper

open Cli Imprimatur

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur [--config FILE] build [--timing] [--no-checker] [--no-install] [apply options]
       imprimatur [--config FILE] check [--timing] [--no-checker] [--no-install] [check options]
       imprimatur [--config FILE] accept KEY... | --all
       imprimatur [--config FILE] show KEY [--view VIEW]... [--timing] [--no-checker] [--no-install]
       imprimatur toolchain install VERSION   (external mode; build does it when none is cached)
       imprimatur [--config FILE] scan|apply|check|strip|migrate-slots ...  (see imprimatur-splice --help)"

/-- Run `lake` in `dir`, with `env` added to the environment; on failure,
return its output as an error. -/
def lake (dir : System.FilePath) (args : Array String) (env : Array (String × Option String) := #[]) :
    ExceptT String IO String := do
  let out ← IO.Process.output { cmd := "lake", args, cwd := dir, env }
  if out.exitCode != 0 then
    throw s!"`lake {" ".intercalate args.toList}` failed in {dir}:\n{out.stdout}{out.stderr}"
  return out.stdout ++ out.stderr

/-- The toolchain version a `lean-toolchain` file names: `v4.31.0` for
`leanprover/lean4:v4.31.0`, `leanprover/lean4:4.31.0` or `v4.31.0`. -/
def toolchainVersion (text : String) : String :=
  let t := text.trimAscii.toString
  let v := ((t.splitOn ":").getLast?.getD t)
  if v.startsWith "v" then v else "v" ++ v

/-- Where external mode keeps extractors, one per toolchain: `IMPRIMATUR_CACHE`,
or `$XDG_CACHE_HOME/imprimatur`, or `~/.cache/imprimatur`. -/
def cacheDir : IO System.FilePath := do
  if let some d := ← IO.getEnv "IMPRIMATUR_CACHE" then return d
  if let some d := ← IO.getEnv "XDG_CACHE_HOME" then return (d : System.FilePath) / "imprimatur"
  let home := (← IO.getEnv "HOME").getD "."
  return (home : System.FilePath) / ".cache" / "imprimatur"

/-- The extractor for a toolchain, in the cache. -/
def cachedExtractor (version : String) : IO System.FilePath := do
  return (← cacheDir) / "toolchains" / version / ".lake" / "build" / "bin" / "imprimatur-export"

/-- The extractor's sources: `IMPRIMATUR_SOURCE`, or `extract/` in the
repository this program was built in. -/
def sourceDir : IO System.FilePath := do
  if let some d := ← IO.getEnv "IMPRIMATUR_SOURCE" then return d
  return (← IO.appDir) / ".." / ".." / ".." / ".." / "extract"

/-- Copy a directory tree, leaving out `.lake` and `test`. -/
partial def copySources (src dst : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if e.fileName == ".lake" || e.fileName == "test" then continue
    if ← e.path.isDir then copySources e.path (dst / e.fileName)
    else IO.FS.writeBinFile (dst / e.fileName) (← IO.FS.readBinFile e.path)

/-- `imprimatur toolchain install VERSION`: build the extractor for a
toolchain into the cache (DESIGN §6.3 A). -/
def installToolchain (version : String) : ExceptT String IO String := do
  let version := toolchainVersion version
  let src ← (sourceDir : IO _)
  unless ← (src / "Imprimatur.lean").pathExists do
    throw s!"the extractor's sources are not at {src}; set IMPRIMATUR_SOURCE to imprimatur's extract/ directory"
  let dst := (← (cacheDir : IO _)) / "toolchains" / version
  if ← dst.pathExists then IO.FS.removeDirAll dst
  copySources src dst
  IO.FS.writeFile (dst / "lean-toolchain") s!"leanprover/lean4:{version}\n"
  discard <| lake dst #["build", "-q", "imprimatur-export"]
  return s!"imprimatur: the extractor for Lean {version} is in {dst}\n"

/-- The views the document asks for `key`, if it uses it. -/
def docViews (doc : Doc) (key : String) : Option (Array String) := Id.run do
  let mut vs : Array String := #[]
  for f in doc.files do
    for it in f.scan.items do
      if (it.kind == .block || it.kind == .inline) && it.key == key then
        let v := itemView doc.cfg it
        unless vs.contains v do vs := vs.push v
  return if vs.isEmpty then none else some vs

/-- The timing log of a run with `--timing`, relative to `root`. -/
def timingFile : String := ".imprimatur/timing.jsonl"

/-- Record a phase of the splicer's in the timing log, if there is one. -/
def timingEvent (root : System.FilePath) (a : Args) (phase : String) (ms : Nat) : IO Unit := do
  unless a.timing do return
  let h ← IO.FS.Handle.mk (root / timingFile) .append
  h.putStrLn s!"\{\"at\": \"splice\", \"phase\": \"{phase}\", \"ms\": {ms}}"

/-- The summary of the timing log, if there is one, for the end of the output. -/
def timingSummary (root : System.FilePath) (a : Args) : IO String := do
  unless a.timing do return ""
  let text ← IO.FS.readFile (root / timingFile)
  return Timing.summary text timingFile

/-- Load the document, write requests (all of the document's, or `only`
one key's), and run the extractor. Returns the bundle's path relative to
`root`, and the extractor's warnings; or, if the document has errors, those
as `Except.error` of the exit code and report. -/
def runExport (root : System.FilePath) (a : Args) (only : Option (String × Array String) := none) :
    ExceptT String IO (Except (UInt32 × String) (Doc × String × String)) := do
  let cfgFile := a.config.getD "imprimatur.toml"
  let cfgText ← (IO.FS.readFile (root / cfgFile) : IO String)
  let cfg ← match Config.parse cfgText with
    | .ok c => pure c
    | .error e => throw s!"{cfgFile}: {e}"
  let tScan ← IO.monoMsNow
  let doc ← (Doc.loadIO cfg root : IO Doc)
  let scanMs := (← IO.monoMsNow) - tScan
  if cfg.imports.isEmpty && doc.manifests.all (·.solutionModule.isNone) then
    throw s!"{cfgFile}: set imports, the Lean modules to read declarations from"
  if hasErrors doc.diags then
    return .error (1, "\n".intercalate (doc.diags.map (·.render)).toList ++ "\n")
  let work := root / ".imprimatur"
  IO.FS.createDirAll work
  let workAbs ← IO.FS.realPath work
  let reqs := workAbs / "requests.json"
  let bundle := workAbs / "bundle.json"
  -- A run's timing log starts empty; the extractor appends to it.
  let timing := workAbs / "timing.jsonl"
  let env : Array (String × Option String) ← if a.timing then do
      if ← timing.pathExists then IO.FS.removeFile timing
      timingEvent root a "scan" scanMs
      pure #[("IMPRIMATUR_TIMING", some timing.toString)]
    else pure #[]
  let only := only.map fun (k, vs) =>
    (k, if vs.isEmpty then (docViews doc k).getD #["math"] else vs)
  writeAtomic reqs (requests doc only)
  let leanDir := root / cfg.leanProject
  unless ← leanDir.pathExists do throw s!"lean_project {cfg.leanProject} does not exist"
  -- External mode's extractor (DESIGN §6.3 A): the one cached for the host's
  -- toolchain, built now if there is none, unless `--no-install`. Before the
  -- export phase is timed, so that a first run's build does not count as
  -- export; and announced on stderr at once, since it takes a while.
  let external : Option System.FilePath ← if cfg.mode == "external" then do
      let tcFile := leanDir / "lean-toolchain"
      unless ← tcFile.pathExists do throw s!"{cfg.leanProject} has no lean-toolchain file"
      let version := toolchainVersion (← IO.FS.readFile tcFile)
      let exe ← cachedExtractor version
      unless ← exe.pathExists do
        if a.noInstall then
          throw s!"no extractor for Lean {version}; run: imprimatur toolchain install {version}"
        IO.eprintln s!"imprimatur: no extractor for Lean {version}; building one in \
          {← (cacheDir : IO _)}, once per version (imprimatur toolchain install {version} does it ahead of time)"
        IO.eprint (← installToolchain version)
      pure (some exe)
    else pure none
  let exportArgs := #["--requests", reqs.toString, "--out", bundle.toString,
    "--base", (← IO.FS.realPath root).toString]
  let tExport ← IO.monoMsNow
  -- The verified checker (DESIGN §7.8) reads the modules the extractor
  -- imports, alongside it, once they are built: the export phase is the
  -- wait for both.
  let modules := doc.manifests.foldl (fun acc m => match m.solutionModule with
    | some sm => if acc.contains sm then acc else acc.push sm
    | none => acc) cfg.imports
  let startChecker : IO (Option (Task (Except IO.Error (Except String (Checker × Bool × Checker.Times) × Nat)))) :=
    match cfg.checker with
    | some tool => if a.noChecker then pure none else
      some <$> IO.asTask do
        let t0 ← IO.monoMsNow
        let r ← (Checker.run leanDir workAbs tool modules).run
        return (r, (← IO.monoMsNow) - t0)
    | none => pure none
  let (exportOut, checking) ← match external with
    | some exe =>
      -- External mode (DESIGN §6.3 A): the cached extractor runs under the
      -- host's `lake env`. Nothing in the host changes, and the host is not
      -- built: it must be built already.
      let checking ← startChecker
      pure (← lake leanDir (#["env", exe.toString] ++ exportArgs) env, checking)
    | none => do
      -- In-project and sidecar modes: the package requires imprimatur.
      let modules := doc.manifests.foldl (fun acc m =>
        (match m.solutionModule with | some sm => acc.push sm | none => acc) |>
        fun acc => match m.challengeModule with | some cm => acc.push cm | none => acc) cfg.imports
      discard <| lake leanDir (#["build", "-q"] ++ modules)
      let checking ← startChecker
      pure (← lake leanDir (#["exe", "imprimatur-export"] ++ exportArgs) env, checking)
  -- The checker's verdict goes into the bundle, and one line to the console.
  let mut notes := ""
  if let some t := checking then
    let ((c, kept, times), ms) ← match ← IO.wait t with
      | .ok (.ok r, ms) => pure (r, ms)
      | .ok (.error e, _) => throw e
      | .error e => throw s!"{e}"
    if a.timing then
      -- One event: the whole wait, and its two halves when it was not kept.
      let h ← IO.FS.Handle.mk (root / timingFile) .append
      h.putStrLn s!"\{\"at\": \"checker\", \"phase\": \"{c.tool}\", \"ms\": {ms}, \"kept\": {kept}, \
        \"leanexport_ms\": {times.export_ms}, \"check_ms\": {times.check_ms}}"
    let text ← (IO.FS.readFile bundle : IO String)
    let b ← match Bundle.parse text with
      | .ok b => pure b
      | .error e => throw s!"{bundle}: {e}"
    writeAtomic bundle (Bundle.render { b with checker := some c })
    notes := s!"checker: {c.report}{if kept then " (from the last run; the development is unchanged)" else ""}\n"
  timingEvent root a "export" ((← IO.monoMsNow) - tExport)
  -- Only warnings are of interest: the extractor's, and Lean's about the
  -- notation files it elaborates (`file:line:col: warning: …`).
  let warnings := (exportOut.splitOn "\n").filter fun l =>
    l.startsWith "imprimatur-export: warning" || (l.splitOn ": warning: ").length > 1
  let rel := (bundle.toString.drop ((← IO.FS.realPath root).toString.length + 1)).toString
  return .ok (doc, rel, notes ++ String.join (warnings.map (· ++ "\n")))

/-- The whole flow: export, then the splicer's `apply`, `check` or `accept`. -/
def flow (root : System.FilePath) (a : Args) : ExceptT String IO (UInt32 × String) := do
  match ← runExport root a with
  | .error r => return r
  | .ok (_, rel, warnings) =>
    let t0 ← IO.monoMsNow
    let (code, out) ← (Cli.run (cliArgs a rel) root : IO _)
    timingEvent root a (if a.command == "build" then "apply" else a.command) ((← IO.monoMsNow) - t0)
    return (code, warnings ++ out ++ (← timingSummary root a))
where
  /-- The splicer's arguments for the same run. -/
  cliArgs (a : Args) (bundle : String) : List String :=
    (match a.config with | some c => ["--config", c] | none => []) ++
    [if a.command == "build" then "apply" else a.command, "--bundle", bundle] ++
    a.keys.toList ++ (if a.all then ["--all"] else []) ++
    (a.force.toList.flatMap (["--force", ·])) ++
    (if a.keepStale then ["--keep-stale"] else []) ++
    (if a.noChecker then ["--no-checker"] else []) ++
    (a.renames.toList.flatMap fun (o, n) => ["--rename-slot", s!"{o}={n}"]) ++
    (match a.profile with | some p => ["--profile", p] | none => []) ++
    (match a.commit with | some c => ["--commit", c] | none => []) ++
    (if a.diff then ["--diff"] else []) ++
    (match a.failMsg with | some m => ["--check-fail-msg", m] | none => [])

/-- `imprimatur show KEY [--view VIEW]...`: one key's renderings, with the
problems translation validation found in each, and its trust status. For
working on notation (DESIGN §12): nothing in the document is written. -/
def «show» (root : System.FilePath) (a : Args) : ExceptT String IO (UInt32 × String) := do
  let some key := a.keys[0]? | throw "show takes a key: imprimatur show KEY [--view VIEW]"
  match ← runExport root a (some (key, a.views)) with
  | .error r => return r
  | .ok (doc, rel, warnings) =>
    -- The views asked for, as `runExport` asked for them; the extractor adds
    -- `lean` and `meta` to every key, which are not shown unless asked for.
    let wanted := if a.views.isEmpty then (docViews doc key).getD #["math"] else a.views
    let text ← (IO.FS.readFile (root / rel) : IO String)
    let bundle ← match Bundle.parse text with
      | .ok b => pure b
      | .error e => throw s!"{rel}: {e}"
    let some e := bundle.find? key | return (1, s!"{key}: no declaration or group with this name\n")
    let mut out := warnings
    let mut problems := 0
    for (view, tex) in e.statement.views.filter (wanted.contains ·.1) do
      out := out ++ s!"== {key} ({view})\n{tex}\n"
      for p in e.statement.problems view do
        problems := problems + 1
        out := out ++ s!"  {if p.startsWith "category: " then "error" else "warning"}: {p}\n"
    for (view, err) in e.statement.errors do
      problems := problems + 1
      out := out ++ s!"== {key} ({view})\n  error: {err}\n"
    unless e.verdict.axioms.isEmpty do out := out ++ s!"axioms: {", ".intercalate e.verdict.axioms.toList}\n"
    if e.verdict.usesSorry then out := out ++ "uses sorry\n"
    let n := (e.statement.views.filter (wanted.contains ·.1)).size
    return (if e.statement.errors.isEmpty then 0 else 1,
      out ++ s!"show: {n} view{if n == 1 then "" else "s"}, {problems} problem{if problems == 1 then "" else "s"}\n" ++
        (← timingSummary root a))

/-- Run `imprimatur` with arguments `args` in directory `root`. -/
def run (args : List String) (root : System.FilePath) : IO (UInt32 × String) := do
  match args with
  | ["--help"] | ["-h"] | [] => return (0, usage ++ "\n")
  | ["--version"] => return (0, s!"imprimatur {version}\n")
  | ["toolchain", "install", v] =>
    match ← (installToolchain v).run with
    | .ok out => return (0, out)
    | .error e => return (2, s!"error: {e}\n")
  | _ =>
  match parseArgs args with
  | .error e => return (2, s!"error: {e}\n\n{usage}\n")
  | .ok a =>
    if a.command == "show" then
      try
        match ← («show» root a).run with
        | .ok r => return r
        | .error e => return (2, s!"error: {e}\n")
      catch e => return (2, s!"error: {e}\n")
    else if a.command == "build" || ((a.command == "check" || a.command == "accept") && a.bundle.isNone) then
      try
        match ← (flow root a).run with
        | .ok r => return r
        | .error e => return (2, s!"error: {e}\n")
      catch e => return (2, s!"error: {e}\n")
    else Cli.run args root

end Splice.Wrapper
