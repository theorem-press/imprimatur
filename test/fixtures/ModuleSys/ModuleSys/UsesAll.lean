/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ModuleSys.Lib
import all ModuleSys.Lib

/-! A `module` file that imports `Lib` with `all`. -/

namespace ModuleSys

/-- Builds on `pub_thm`. -/
public theorem via_all : (2 : Nat) + 2 = 4 ∧ True := ⟨pub_thm, trivial⟩

end ModuleSys
