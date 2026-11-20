/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The development: statements a view shows other than as they are written. -/

namespace Statements

/-- A named proposition, as Mathlib names the Riemann hypothesis. -/
def Named : Prop := ∀ n : Nat, 0 < n → n ≠ 0

/-- A theorem whose statement is a named proposition, and whose proof is not
here: the `unfold` modifier shows the proposition, and `claim` says the proof
is elsewhere (#137). -/
theorem named : Named := by sorry

/-- A named proposition with an argument. -/
def Bounded (n : Nat) : Prop := n < 10

/-- A statement that applies a named proposition: `unfold` shows its body at
the argument. -/
theorem bounded (n : Nat) (h : n = 3) : Bounded n := by
  subst h; show 3 < 10; decide

/-- A class the paper has notation for: its instance binder is a hypothesis. -/
class Positive (n : Nat) : Prop where
  pos : 0 < n

/-- A class the paper has no notation for: its instance binder is not shown. -/
class Quiet (n : Nat) : Prop where
  quiet : True

/-- A theorem with instance binders. -/
theorem withInstance (n : Nat) [Positive n] [Quiet n] : n ≠ 0 :=
  Nat.pos_iff_ne_zero.mp Positive.pos

end Statements
