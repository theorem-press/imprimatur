/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice

/-!
# `imprimatur-splice`

The splicer's command line (DESIGN §10, §12). See `Splice.Cli`.
-/

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  let (code, out) ← Splice.Cli.run args (← IO.currentDir)
  IO.print out
  return code
