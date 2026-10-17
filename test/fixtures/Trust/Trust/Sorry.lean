/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
`sorry` in a proof, and `sorry` three levels deep in a statement's
dependency cone (DESIGN §7.7).
-/

namespace Trust

theorem direct_sorry : 2 + 2 = 5 := sorry

theorem uses_direct_sorry : 2 + 2 = 5 ∧ True := ⟨direct_sorry, trivial⟩

/-- Third level: the `sorry`. -/
def Level3 (_n : Nat) : Prop := sorry

/-- Second level. -/
def Level2 (n : Nat) : Prop := Level3 n ∧ n = n

/-- First level. -/
def Level1 (n : Nat) : Prop := Level2 n

/-- The proof is honest, but the statement depends on `sorry`. -/
theorem deep_sorry (n : Nat) (h : Level1 n) : Level1 n := h

end Trust
