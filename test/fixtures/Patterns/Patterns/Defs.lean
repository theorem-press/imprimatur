/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The development: definitions by cases, and list literals. -/

namespace Patterns

/-- A list literal. -/
def three : List Nat := [1, 2, 3]

/-- Nested cases whose patterns bind the same name: the inner `x` is not the
outer one. (The discriminants are not variables, so the cases are not split
into equations.) -/
def nested (o p : Option (Nat × Nat)) : Nat :=
  match id o with
  | some (x, _) =>
    match id p with
    | some (x, y) => x + y
    | none => x
  | none => 0

/-- A case on a disjoint union, whose injections the patterns test. -/
def side : Nat ⊕ Nat → Bool
  | .inl _ => true
  | .inr _ => false

/-- A dependent `if`, whose branches bind a proof. -/
def safeHead (l : List Nat) : Nat :=
  if h : l ≠ [] then l.head h else 0

/-- Functions that ignore their arguments, and one whose binder is named as a
variable in scope. -/
def konst (x : Nat) : List (Nat → Nat → Nat) := [fun _ _ => x, fun x _ => x + 1]

/-- A constant applied only to an implicit argument (`@id Nat`), which shows
no argument and reads back as an atom. -/
def ident : Nat → Nat := id

end Patterns
