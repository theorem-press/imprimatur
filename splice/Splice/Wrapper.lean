/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Cli

/-!
# The `imprimatur` command

`imprimatur build` runs the whole flow (DESIGN §5): `scan`, then the
extractor, then `apply`. `imprimatur check` and `imprimatur accept` do the
same with `check` or `accept` instead of `apply`. Every other command is the
splicer's.

How the extractor runs depends on the mode (DESIGN §6.3):

- **in-project, sidecar:** `lake exe imprimatur-export`, run in `lean_project`,
  a package that requires `imprimatur` (the host itself, or a sidecar next to
  it). The modules in `imports` are built first.
- **external:** an extractor built for the host's toolchain by
  `imprimatur toolchain install`, run under the host's `lake env`. The host
  doesn't change and isn't built.

Requests and the bundle go in `.imprimatur/` next to `imprimatur.toml`.
-/

namespace Splice.Wrapper

open Cli

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur [--config FILE] build [apply options]
       imprimatur [--config FILE] check [check options]
       imprimatur [--config FILE] accept KEY... | --all
       imprimatur toolchain install VERSION   (for mode = \"external\")
       imprimatur [--config FILE] scan|apply|check|strip|migrate-slots ...  (see imprimatur-splice --help)"

/-- Run `lake` in `dir`; on failure, return its output as an error. -/
def lake (dir : System.FilePath) (args : Array String) : ExceptT String IO String := do
  let out ← IO.Process.output { cmd := "lake", args, cwd := dir }
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

/-- `build` or `check`. -/
def flow (root : System.FilePath) (a : Args) : ExceptT String IO (UInt32 × String) := do
  let cfgFile := a.config.getD "imprimatur.toml"
  let cfgText ← (IO.FS.readFile (root / cfgFile) : IO String)
  let cfg ← match Config.parse cfgText with
    | .ok c => pure c
    | .error e => throw s!"{cfgFile}: {e}"
  let doc ← (Doc.loadIO cfg root : IO Doc)
  if cfg.imports.isEmpty && doc.manifests.all (·.solutionModule.isNone) then
    throw s!"{cfgFile}: set imports, the Lean modules to read declarations from"
  if hasErrors doc.diags then
    return (1, "\n".intercalate (doc.diags.map (·.render)).toList ++ "\n")
  let work := root / ".imprimatur"
  IO.FS.createDirAll work
  let workAbs ← IO.FS.realPath work
  let reqs := workAbs / "requests.json"
  let bundle := workAbs / "bundle.json"
  writeAtomic reqs (requests doc)
  let leanDir := root / cfg.leanProject
  unless ← leanDir.pathExists do throw s!"lean_project {cfg.leanProject} does not exist"
  let exportArgs := #["--requests", reqs.toString, "--out", bundle.toString,
    "--base", (← IO.FS.realPath root).toString]
  let exportOut ← if cfg.mode == "external" then
      -- External mode (DESIGN §6.3 A): a cached extractor built with the host's
      -- toolchain runs under the host's `lake env`. Nothing in the host changes,
      -- and the host is not built: it must be built already.
      let tcFile := leanDir / "lean-toolchain"
      unless ← tcFile.pathExists do throw s!"{cfg.leanProject} has no lean-toolchain file"
      let version := toolchainVersion (← IO.FS.readFile tcFile)
      let exe ← cachedExtractor version
      unless ← exe.pathExists do
        throw s!"no extractor for Lean {version}; run: imprimatur toolchain install {version}"
      lake leanDir (#["env", exe.toString] ++ exportArgs)
    else do
      -- In-project and sidecar modes: the package requires imprimatur.
      let modules := doc.manifests.foldl (fun acc m =>
        (match m.solutionModule with | some sm => acc.push sm | none => acc) |>
        fun acc => match m.challengeModule with | some cm => acc.push cm | none => acc) cfg.imports
      discard <| lake leanDir (#["build", "-q"] ++ modules)
      lake leanDir (#["exe", "imprimatur-export"] ++ exportArgs)
  -- Only warnings are of interest: the extractor's, and Lean's about the
  -- notation files it elaborates (`file:line:col: warning: …`).
  let warnings := (exportOut.splitOn "\n").filter fun l =>
    l.startsWith "imprimatur-export: warning" || (l.splitOn ": warning: ").length > 1
  let rel := (bundle.toString.drop ((← IO.FS.realPath root).toString.length + 1)).toString
  let (code, out) ← (Cli.run (cliArgs a rel) root : IO _)
  return (code, String.join (warnings.map (· ++ "\n")) ++ out)
where
  /-- The splicer's arguments for the same run. -/
  cliArgs (a : Args) (bundle : String) : List String :=
    (match a.config with | some c => ["--config", c] | none => []) ++
    [if a.command == "build" then "apply" else a.command, "--bundle", bundle] ++
    a.keys.toList ++ (if a.all then ["--all"] else []) ++
    (a.force.toList.flatMap (["--force", ·])) ++
    (if a.keepStale then ["--keep-stale"] else []) ++
    (a.renames.toList.flatMap fun (o, n) => ["--rename-slot", s!"{o}={n}"]) ++
    (match a.profile with | some p => ["--profile", p] | none => []) ++
    (match a.commit with | some c => ["--commit", c] | none => []) ++
    (if a.diff then ["--diff"] else []) ++
    (match a.failMsg with | some m => ["--check-fail-msg", m] | none => [])

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
    if a.command == "build" || ((a.command == "check" || a.command == "accept") && a.bundle.isNone) then
      try
        match ← (flow root a).run with
        | .ok r => return r
        | .error e => return (2, s!"error: {e}\n")
      catch e => return (2, s!"error: {e}\n")
    else Cli.run args root

end Splice.Wrapper
