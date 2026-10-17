/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
A custom axiom, a `partial` definition and an `unsafe` definition.
-/

namespace Trust

/-- A custom axiom, which is not in the default `allowed_axioms`. -/
axiom custom_axiom : ∀ n : Nat, n + 0 = n

theorem uses_custom_axiom (n : Nat) : n + 0 = n := custom_axiom n

theorem uses_standard_axioms (p : Prop) : p ∨ ¬p := Classical.em p

/-- A `partial` definition: opaque to the kernel. -/
partial def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 0 else if n % 2 = 0 then collatz (n / 2) + 1 else collatz (3 * n + 1) + 1

/-- A statement whose cone contains a `partial` definition. -/
theorem collatz_stmt (n : Nat) (h : collatz n = 0) : collatz n = 0 := h

/-- An `unsafe` definition. -/
unsafe def unsafeId (n : Nat) : Nat := n

end Trust
