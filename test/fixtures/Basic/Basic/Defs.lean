/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Declarations of every kind, with docstrings, for the `lean` and `meta` views.
-/

namespace Basic

universe u

/-- A pair of values of one type. -/
structure Pair (α : Type u) where
  /-- The first component. -/
  fst : α
  /-- The second component. -/
  snd : α

/-- Swap the components: an explicit binder and an implicit one. -/
def Pair.swap {α : Type u} (p : Pair α) : Pair α := ⟨p.snd, p.fst⟩

/-- Commutativity, with implicit, instance and explicit binders. -/
theorem add_comm' {α : Type u} [Add α] (comm : ∀ a b : α, a + b = b + a) (x y : α) :
    x + y = y + x :=
  comm x y

/-- An inductive predicate. -/
inductive Even : Nat → Prop
  | /-- Zero is even. -/ zero : Even 0
  | /-- Add two. -/ step {n : Nat} : Even n → Even (n + 2)

/-- A custom axiom. -/
axiom oracle : Nonempty Nat → Nat

/-- Uses the custom axiom. Markdown in a docstring: `code`, **bold**, *emphasis*,
the maths $x_1 + y^2$, and TeX specials # % & _ ~. -/
theorem uses_oracle : ∃ n : Nat, n = oracle ⟨0⟩ := ⟨_, rfl⟩

/-- Unfinished. -/
theorem unfinished : 1 + 1 = 3 := sorry

/-- A name with an underscore and a prime. -/
def my_fun' (n : Nat) : Nat := n + 1

/-- A statement long enough to break across lines when printed at the
default width. -/
theorem long_statement (a b c d e f g h : Nat) (h₁ : a + b + c + d = e + f + g + h)
    (h₂ : e + f + g + h = 0) : a + b + c + d = 0 ∧ e + f + g + h = 0 ∧ my_fun' a = a + 1 :=
  ⟨h₁.trans h₂, h₂, rfl⟩

/-- An opaque constant. -/
opaque secret : Nat

/-- An instance. -/
instance instInhabitedPair : Inhabited (Pair Nat) := ⟨⟨0, 0⟩⟩

/-- Uses classical logic. -/
theorem em' (p : Prop) : p ∨ ¬p := Classical.em p

/-- A number an axiom chooses, for `Wrap`. -/
noncomputable def pick : Nat := Classical.choice ⟨0⟩

/-- An inductive type in a cycle with its constructors, one of whose types
depends on an axiom through `pick`. Its axioms are `Classical.choice`,
whichever of the type and the constructor is asked first; Lean's own
`collectAxioms` can answer none for the type. -/
inductive Wrap where
  | leaf (h : pick = pick) : Wrap
  | node : Wrap → Wrap

end Basic

/-- Outside the namespace, with no docstring on the theorem below. -/
def topLevel : Nat := 1

theorem no_doc : topLevel = 1 := rfl
