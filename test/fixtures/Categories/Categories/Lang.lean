/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Two kinds of program, and a statement about each. -/

namespace Cats

/-- Programs. -/
inductive Prog where
  | mk (n : Nat)

/-- Programs, as represented. -/
inductive Rep where
  | mk (n : Nat)

/-- A program, as represented. -/
def lower : Prog → Rep
  | .mk n => .mk n

/-- Variables named for neither type: written with their types' letters. -/
theorem lower_eq (q : Prog) (r : Rep) (h : lower q = r) : lower q = r := h

/-- Two programs named `a` and `b`: both written `P`. -/
theorem symm (a b : Prog) (h : a = b) : b = a := h.symm

end Cats
