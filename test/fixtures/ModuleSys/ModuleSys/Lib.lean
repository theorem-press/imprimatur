/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-! A `module` file. The proof of `pub_thm` uses a private lemma that is
`sorry`; only the `private` level of the `.olean` shows it. -/

namespace ModuleSys

private theorem helper : (2 : Nat) + 2 = 4 := sorry

/-- A public theorem with a private, unfinished proof. -/
public theorem pub_thm : (2 : Nat) + 2 = 4 := helper

/-- A public theorem with an honest proof. -/
public theorem honest : (1 : Nat) + 1 = 2 := rfl

end ModuleSys
