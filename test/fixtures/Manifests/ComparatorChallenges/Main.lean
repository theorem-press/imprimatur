/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The challenge: the statements, with `sorry` for proofs. -/

namespace Cat

/-- Evenness. -/
def IsEven (n : Nat) : Prop := n % 2 = 0

/-- The main theorem to prove. -/
theorem main : ∀ n : Nat, IsEven (2 * n) := sorry

/-- A second theorem to prove. -/
theorem classical (p : Prop) : p ∨ ¬p := sorry

end Cat
