/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur

/-!
# `imprimatur-export`

The extractor's command line (DESIGN §12):

    imprimatur-export --requests requests.json --out bundle.json [--project NAME]

It runs in the Lean project, under `lake env` or `lake exe`, so that the
project's modules are on the search path. Source paths in the bundle are
relative to the current directory.
-/

open Imprimatur

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur-export --requests requests.json --out bundle.json [--project NAME]\n\
   \x20      imprimatur-export --version"

/-- Parse `--flag value` pairs. -/
def flag (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

/-- Entry point. -/
unsafe def main (args : List String) : IO UInt32 := do
  if args == ["--version"] then
    IO.println s!"imprimatur-export {version} (Lean {leanVersion})"
    return 0
  let (some reqPath, some outPath) := (flag args "--requests", flag args "--out")
    | IO.eprintln usage; return 2
  let text ← match ← (IO.FS.readFile reqPath).toBaseIO with
    | .ok t => pure t
    | .error e => IO.eprintln s!"imprimatur-export: cannot read {reqPath}: {e}"; return (2 : UInt32)
  let (settings, reqs) ← match parseRequests text with
    | .ok r => pure r
    | .error e => IO.eprintln s!"imprimatur-export: {reqPath}: {e}"; return (2 : UInt32)
  if settings.imports.isEmpty then
    IO.eprintln "imprimatur-export: no modules to import; set imports in imprimatur.toml"
    return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← match ← (Compat.importPrivate settings.imports).toBaseIO with
    | .ok env => pure env
    | .error e =>
      IO.eprintln s!"imprimatur-export: cannot import {settings.imports}: {e}\n\
        (is the Lean project built? run `lake build` in it)"
      return (1 : UInt32)
  let r ← exportBundle env (← IO.currentDir) settings reqs (flag args "--project")
  for w in r.warnings do IO.eprintln s!"imprimatur-export: warning: {w}"
  let tmp := outPath ++ ".imprimatur-tmp"
  IO.FS.writeFile tmp r.bundle
  IO.FS.rename tmp outPath
  IO.println s!"imprimatur-export: {r.entries} entries written to {outPath}"
  return 0
