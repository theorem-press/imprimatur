/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ModuleSys.Lib

/-! An ordinary (non-`module`) file importing a `module` file. -/

namespace ModuleSys

/-- Builds on `honest`. -/
theorem plain_user : (1 : Nat) + 1 = 2 ∧ True := ⟨honest, trivial⟩

end ModuleSys
