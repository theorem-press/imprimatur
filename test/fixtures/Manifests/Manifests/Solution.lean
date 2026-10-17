/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The solution: the challenge's definitions, and proofs of its theorems. -/

namespace Cat

/-- Evenness, as the challenge defines it. -/
def IsEven (n : Nat) : Prop := n % 2 = 0

/-- The challenge's main theorem, proved. -/
theorem main : ∀ n : Nat, IsEven (2 * n) := by
  intro n
  unfold IsEven
  omega

/-- A second theorem, proved with classical logic. -/
theorem classical (p : Prop) : p ∨ ¬p := Classical.em p

end Cat
