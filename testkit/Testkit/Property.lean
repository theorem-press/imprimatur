/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Testkit.Harness
import Testkit.Gen

/-!
# Property tests

`forAll name gen render prop` checks `prop` on generated cases. The number of
cases comes from `IMPRIMATUR_CASES` (default 100), and the base seed from
`IMPRIMATUR_SEED` (default: the clock). The seed of each case is derived from
the base seed, the property's name and the case number, so rerunning with the
printed `IMPRIMATUR_SEED` reproduces a failure exactly.
-/

namespace Testkit

/-- How a property run is configured. -/
structure PropConfig where
  /-- Cases to try per property. -/
  cases : Nat
  /-- The base seed. -/
  seed : UInt64
  /-- The largest size bound handed to generators. -/
  maxSize : Nat

/-- Read the property configuration from the environment. -/
def PropConfig.fromEnv : IO PropConfig := do
  let cases := (← IO.getEnv "IMPRIMATUR_CASES").bind String.toNat? |>.getD 100
  let maxSize := (← IO.getEnv "IMPRIMATUR_MAX_SIZE").bind String.toNat? |>.getD 30
  let seed ← match (← IO.getEnv "IMPRIMATUR_SEED").bind String.toNat? with
    | some s => pure s.toUInt64
    | none => pure (← IO.monoNanosNow).toUInt64
  return { cases, seed, maxSize }

/-- The seed of case `i` of property `name`. -/
def caseSeed (base : UInt64) (name : String) (i : Nat) : UInt64 :=
  (Rng.next ⟨base ^^^ fnv1a name ^^^ (i.toUInt64 * 0x9E3779B97F4A7C15)⟩).1

/-- The size bound of case `i`: sizes cycle from 0 up to `maxSize`. -/
def caseSize (cfg : PropConfig) (i : Nat) : Nat :=
  i % (cfg.maxSize + 1)

/-- Check `prop` on `cfg.cases` generated values, stopping at the first
failure and printing the seed that reproduces it. -/
def forAllWith {α : Type} (cfg : PropConfig) (name : String) (gen : Gen α)
    (render : α → String) (prop : α → Except String Unit) : TestM Unit := do
  for i in [0:cfg.cases] do
    let x := gen.run (caseSeed cfg.seed name i) (caseSize cfg i)
    if let .error msg := prop x then
      fail name s!"case {i} of {cfg.cases} (size {caseSize cfg i}): {msg}\n\
        input: {render x}\n\
        reproduce with IMPRIMATUR_SEED={cfg.seed} IMPRIMATUR_CASES={i + 1}"
      return
  pass

/-- `forAllWith`, configured from the environment. -/
def forAll {α : Type} (name : String) (gen : Gen α) (render : α → String)
    (prop : α → Except String Unit) : TestM Unit := do
  forAllWith (← PropConfig.fromEnv) name gen render prop

/-- Turn a condition into a property result. -/
def expect (cond : Bool) (msg : String) : Except String Unit :=
  if cond then .ok () else .error msg

end Testkit
