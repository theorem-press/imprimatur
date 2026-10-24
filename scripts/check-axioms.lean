/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# lint/axioms: the splicer's theorems rest on Lean's standard axioms only

Every theorem in the modules of the splicer's verified code and its proofs
(`Splice.Core.*` and `SpliceModel.*`) may depend on `propext`,
`Classical.choice` and `Quot.sound`, and on nothing else: no `sorryAx`, no
axiom of the project's, and no `Lean.ofReduceBool` (`native_decide`).
Run in `splice/` with `lake env lean --run ../scripts/check-axioms.lean`
after `lake build SpliceModel` (scripts/test-all.sh does).
-/

open Lean

/-- The axioms a theorem may depend on. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a module is the verified code or its proofs. -/
def checked (m : Name) : Bool :=
  (`Splice.Core).isPrefixOf m || (`SpliceModel).isPrefixOf m

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `SpliceModel }] {}
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    if checked mod && ci matches .thmInfo _ && !n.isInternal then thms := thms.push n
  let ctx : Core.Context := { fileName := "<check-axioms>", fileMap := default }
  let (bad, _) ← (do
      let mut bad : Array (Name × Array Name) := #[]
      for n in thms do
        let axs ← collectAxioms n
        let extra := axs.filter (!allowed.contains ·)
        unless extra.isEmpty do bad := bad.push (n, extra)
      return bad : CoreM _).toIO ctx { env }
  for (n, extra) in bad do
    IO.eprintln s!"lint/axioms: {n} depends on {extra.toList}, beyond propext, Classical.choice and Quot.sound"
  IO.println s!"axioms: {thms.size} theorems checked"
  return if bad.isEmpty then 0 else 1
