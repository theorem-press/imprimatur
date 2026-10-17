/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur

/-!
# `imprimatur-export`

The extractor's command line (DESIGN §12):

    imprimatur-export --requests requests.json --out bundle.json [--base DIR] [--project NAME]

Notation files named in the requests are relative to `--base`, the directory
of `imprimatur.toml`. It runs in the Lean project, under `lake env` or `lake exe`, so that the
project's modules are on the search path. Source paths in the bundle are
relative to the current directory.
-/

open Imprimatur

/-- The usage message. -/
def usage : String :=
  "usage: imprimatur-export --requests requests.json --out bundle.json [--base DIR] [--project NAME] [--verbose]\n\
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
  if settings.imports.isEmpty && settings.notationFiles.isEmpty then
    IO.eprintln "imprimatur-export: no modules to import; set imports in imprimatur.toml"
    return 2
  -- The host's search path (from `lake env`), and this program's own library,
  -- which a notation module may import (external mode, DESIGN §6.3 A).
  Lean.initSearchPath (← Lean.findSysroot) [(← IO.appDir) / ".." / "lib" / "lean"]
  let root ← IO.currentDir
  let main := reqs.filter (!·.key.endsWith challengeSuffix)
  -- Notation files (external mode) are elaborated, with the imports; otherwise
  -- the imports are imported.
  let base : System.FilePath := (flag args "--base").getD "."
  let load : IO Lean.Environment :=
    match settings.notationFiles.toList with
    | [] => Compat.importPrivate settings.imports
    | [f] => Compat.elaborateNotation (base / f) settings.imports
    | _ => throw (IO.userError "only one notation file is supported; import the others from it")
  let (entries, warnings) ← match ← load.toBaseIO with
    | .ok env => exportEntries env root settings main (args.contains "--verbose")
    | .error e =>
      IO.eprintln s!"imprimatur-export: cannot import {settings.imports}: {e}\n\
        (is the Lean project built? run `lake build` in it)"
      return (1 : UInt32)
  -- The main environment is no longer used, so challenge modules don't add to it.
  let (chEntries, chWarnings) ← exportChallenges root settings reqs
  for w in warnings ++ chWarnings do IO.eprintln s!"imprimatur-export: warning: {w}"
  let all := entries ++ chEntries
  let tmp := outPath ++ ".imprimatur-tmp"
  IO.FS.writeFile tmp (renderBundle all (flag args "--project"))
  IO.FS.rename tmp outPath
  IO.println s!"imprimatur-export: {all.size} entries written to {outPath}"
  return 0
