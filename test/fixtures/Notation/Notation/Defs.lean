/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! The development: declarations whose statements use every pack rule. -/

namespace Notation

/-- A toy set type, with the set operations of core Lean. -/
def MySet (α : Type) := α → Prop

instance {α : Type} : Membership α (MySet α) := ⟨fun s a => s a⟩
instance {α : Type} : HasSubset (MySet α) := ⟨fun s t => ∀ a, s a → t a⟩
instance {α : Type} : HasSSubset (MySet α) := ⟨fun s t => (∀ a, s a → t a) ∧ ¬ ∀ a, t a → s a⟩
instance {α : Type} : Union (MySet α) := ⟨fun s t a => s a ∨ t a⟩
instance {α : Type} : Inter (MySet α) := ⟨fun s t a => s a ∧ t a⟩
instance {α : Type} : SDiff (MySet α) := ⟨fun s t a => s a ∧ ¬ t a⟩
instance {α : Type} : EmptyCollection (MySet α) := ⟨fun _ => False⟩
instance {α : Type} : Singleton α (MySet α) := ⟨fun a b => b = a⟩
instance {α : Type} : LE (MySet α) := ⟨fun s t => ∀ a, s a → t a⟩

/-- Doubling, with notation `2n`. -/
def double (n : Nat) : Nat := n + n

/-- A satisfaction relation, with notation `U ⊨ φ` when the environment is empty. -/
def Realize (U φ : Nat) (_ρ : Fin 0 → Nat) : Prop := U = φ

/-- A join, flattened into `\lub{a, b, c}`. -/
def lub (a b : Nat) : Nat := max a b

/-- An infix operator at precedence 60 (left-associative, the default). -/
def cons (a b : Nat) : Nat := a * 10 + b

/-- A named judgement. -/
def Judg (n : Nat) : Prop := n = n

/-- A constant shown as a symbol. -/
def zeroish : Nat := 0

/-- Arithmetic: every operator of the core pack. -/
theorem arith (a b c : Nat) (i : Int) (spec : Nat) :
    a + b - c * 2 / 1 % 3 = b ^ 2 ∧ -i ≠ i ∧ a < b ∧ a ≤ b ∧ b > a ∧ b ≥ a ∧
      Nat.succ a = a + 1 ∧ (id ∘ id) a = a ∧ (a, b) = (a, b) ∧ (spec : Int) = Int.cast i ∧
      (⟨a, rfl⟩ : {x : Nat // x = a}).val = a := by
  sorry

/-- Logic: every connective of the logic pack. -/
theorem logic (p q : Prop) : (p ∧ q ∨ ¬ p) ↔ (True ∨ False) := by
  sorry

/-- Sets: every operation of the sets pack. -/
theorem sets {α : Type} (s t : MySet α) (a : α) :
    a ∈ s ∪ t ∩ (s \ t) ∧ s ⊆ t ∧ s ⊂ t ∧ (∅ : MySet α) ⊆ {a} := by
  sorry

/-- Order: max and min. -/
theorem order (a b : Nat) : max a b = min a b := by
  sorry

/-- Binders: bounded quantifiers, ∃, implication, function types, λ, an
applied variable, and a `match`, which falls back to Lean's printer. -/
theorem binders (s : MySet Nat) (f : Nat → Nat) (h : ∀ x ∈ s, f x = x) :
    (∃ y ∈ s, f y = y) → (∃ z, z = f 0) ∧ (fun n => n + 1) 0 = 1 ∧
      (match f 0 with | 0 => true | _ => false) = true ∧ true ≠ false := by
  sorry

/-- Notation from the project: every feature of a rule. -/
theorem project (n m k : Nat) (ρ : Fin 0 → Nat) (spec : Nat) (hd : double n = m)
    (hr : ¬ Realize n m ρ) (hl : lub (lub n m) (lub k n) = k) (hz : zeroish = 0) :
    cons n (cons m k) = cons (cons n m) k ∧ Judg spec ∧ (n = m → Realize n m Fin.elim0) := by
  sorry

/-- A typed pattern: `≤` on sets has its own notation; on numbers it doesn't. -/
theorem typed (s t : MySet Nat) (m n : Nat) : s ≤ t ∧ m ≤ n := by
  sorry

/-- A sum over a function, for a binder pattern `bigsum (fun k => f)`. -/
def bigsum (f : Nat → Nat) : Nat := f 0 + f 1

/-- Binder patterns (the `binders` variant): chains of ∃ and ∀ folded into
one list, an implication, a λ, a function taken by a binder pattern, and an
operator with `assoc := none`. -/
theorem binderRules (f : Nat → Nat) (p : Prop) :
    (∃ a b : Nat, a = b) ∧ (∀ a b : Nat, a = a → b = b → p) ∧
      bigsum (fun k => k + 1) = bigsum f ∧ (fun n => n) 1 = 1 ∧ (p ∧ p) ∧ ¬ ∃ c : Nat, c = c ∧
      ¬ p ∧ ∀ acc₁ : Nat, acc₁ = acc₁ := by
  sorry

/-- A definition, shown as `f x ≔ body`. -/
def triple (n : Nat) : Nat := double n + n

/-- A long statement, broken across lines in the math view. -/
theorem long (a b c d e f g : Nat) (h₁ : a + b + c + d = e + f + g)
    (h₂ : e + f + g = a + b + c + d) (h₃ : a * b * c * d = e * f * g) :
    a + b + c + d + e + f + g = e + f + g + a + b + c + d ∧ a + b + c = c + b + a ∧
      c + d + e = e + d + c ∧ a * b * c * d * e = e * d * c * b * a := by
  sorry

/-- The greater of two numbers, for a rule that may break the line. -/
def join (a b : Nat) : Nat := max a b

/-- A statement whose chain of `join`s is longer than a line, so it breaks
before a `⊔` (`break`). -/
theorem joins (alpha beta gamma delta epsilon zeta eta theta iota kappa lambda' mu : Nat) :
    0 < join (join (join (join alpha beta) (join gamma delta)) (join (join epsilon zeta)
      (join eta theta))) (join (join iota kappa) (join lambda' mu)) + 1 := by
  sorry

/-- Existentials in the conclusion: "there is … such that", nested, over
numbered conjuncts. -/
theorem witnesses (n : Nat) : ∃ m : Nat, ∃ k : Nat, m = n ∧ k = m :=
  ⟨n, n, rfl, rfl⟩

/-- Hypotheses but no variables: an "Assume" sentence first, then "if and
only if". -/
theorem hypsOnly (h : 1 = 1) (h' : 2 = 2) : True ↔ True :=
  Iff.rfl

/-- A conclusion alone: no "Let", no "Assume", no "Then". -/
theorem bare : True :=
  trivial

end Notation
