/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice

/-!
# `imprimatur-splice`

The splicer's command line (DESIGN §12). Only `--version` exists so far.
-/

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
    IO.println s!"imprimatur-splice {Splice.version}"
    return 0
  | _ =>
    IO.eprintln "usage: imprimatur-splice --version"
    return 2
