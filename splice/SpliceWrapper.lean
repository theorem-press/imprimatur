/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice

/-!
# `imprimatur`

The command that runs the whole flow (DESIGN §5, §12). See `Splice.Wrapper`.
-/

/-- Entry point. -/
def main (args : List String) : IO UInt32 := do
  let (code, out) ← Splice.Wrapper.run args (← IO.currentDir)
  IO.print out
  return code
