/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur

/-!
# `imprimatur-export`

The extractor's command line (DESIGN §12). Only `--version` exists so far.
-/

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
    IO.println s!"imprimatur-export {Imprimatur.version} (Lean {Imprimatur.leanVersion})"
    return 0
  | _ =>
    IO.eprintln "usage: imprimatur-export --version"
    return 2
