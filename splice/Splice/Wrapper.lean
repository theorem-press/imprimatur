/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Cli

/-!
# The `imprimatur` command

`imprimatur build` runs the whole flow (DESIGN §5): `scan`, then the
extractor, then `apply`. `imprimatur check` does the same with `check`
instead of `apply`, so it writes nothing but the bundle. Every other command
is the splicer's.

In the `in-project` and `sidecar` modes (DESIGN §6.3), the extractor is
`lake exe imprimatur-export`, run in `lean_project`: a package that requires
`imprimatur`, either the host itself or a sidecar next to it. The modules in
`imports` are built first. Requests and the bundle go in `.imprimatur/` next
to `imprimatur.toml`.
-/

namespace Splice.Wrapper

open Cli

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur [--config FILE] build [apply options]
       imprimatur [--config FILE] check [check options]
       imprimatur [--config FILE] scan|apply|check|strip|migrate-slots ...  (see imprimatur-splice --help)"

/-- Run `lake` in `dir`; on failure, return its output as an error. -/
def lake (dir : System.FilePath) (args : Array String) : ExceptT String IO String := do
  let out ← IO.Process.output { cmd := "lake", args, cwd := dir }
  if out.exitCode != 0 then
    throw s!"`lake {" ".intercalate args.toList}` failed in {dir}:\n{out.stdout}{out.stderr}"
  return out.stdout ++ out.stderr

/-- `build` or `check`. -/
def flow (root : System.FilePath) (a : Args) : ExceptT String IO (UInt32 × String) := do
  let cfgFile := a.config.getD "imprimatur.toml"
  let cfgText ← (IO.FS.readFile (root / cfgFile) : IO String)
  let cfg ← match Config.parse cfgText with
    | .ok c => pure c
    | .error e => throw s!"{cfgFile}: {e}"
  if cfg.mode == "external" then
    throw "mode = \"external\" is not available yet (PLAN M3); use in-project or sidecar"
  if cfg.imports.isEmpty then
    throw s!"{cfgFile}: set imports, the Lean modules to read declarations from"
  let doc ← (Doc.loadIO cfg root : IO Doc)
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
  discard <| lake leanDir (#["build", "-q"] ++ cfg.imports)
  let exportOut ← lake leanDir #["exe", "imprimatur-export", "--requests", reqs.toString,
    "--out", bundle.toString]
  -- Only the extractor's warnings are of interest.
  let warnings := (exportOut.splitOn "\n").filter (·.startsWith "imprimatur-export: warning")
  let rel := (bundle.toString.drop ((← IO.FS.realPath root).toString.length + 1)).toString
  let (code, out) ← (Cli.run (cliArgs a rel) root : IO _)
  return (code, String.join (warnings.map (· ++ "\n")) ++ out)
where
  /-- The splicer's arguments for the same run. -/
  cliArgs (a : Args) (bundle : String) : List String :=
    (match a.config with | some c => ["--config", c] | none => []) ++
    [if a.command == "build" then "apply" else "check", "--bundle", bundle] ++
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
  | _ =>
  match parseArgs args with
  | .error e => return (2, s!"error: {e}\n\n{usage}\n")
  | .ok a =>
    if a.command == "build" || (a.command == "check" && a.bundle.isNone) then
      try
        match ← (flow root a).run with
        | .ok r => return r
        | .error e => return (2, s!"error: {e}\n")
      catch e => return (2, s!"error: {e}\n")
    else Cli.run args root

end Splice.Wrapper
