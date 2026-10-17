/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Declarations whose statements are trusted, with every kind of definition
whose elaborated form might differ between toolchains: structural and
well-founded recursion, pattern matching, structures, instances and
universe polymorphism.
-/

namespace Trust

/-- Structural recursion. -/
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

/-- Well-founded recursion. -/
def halve (n : Nat) : Nat :=
  if n < 2 then 0 else halve (n - 2) + 1
termination_by n
decreasing_by omega

/-- Pattern matching without recursion. -/
def isZero : Nat → Bool
  | 0 => true
  | _ => false

/-- An inductive predicate. -/
inductive Even : Nat → Prop
  | zero : Even 0
  | step {n : Nat} : Even n → Even (n + 2)

/-- A structure. -/
structure Point where
  /-- First coordinate. -/
  x : Nat
  /-- Second coordinate. -/
  y : Nat
deriving Repr

/-- An instance. -/
instance : Add Point := ⟨fun p q => ⟨p.x + q.x, p.y + q.y⟩⟩

/-- A projection-based definition. -/
def Point.norm1 (p : Point) : Nat := p.x + p.y

universe u v

/-- Universe polymorphism. -/
def pairMap {α : Type u} {β : Type v} (f : α → β) (p : α × α) : β × β :=
  (f p.1, f p.2)

theorem double_even (n : Nat) : Even (double n) := by
  induction n with
  | zero => exact Even.zero
  | succ k ih => exact Even.step ih

/-- `double_even` with a different binder name: same `stmtHash`. -/
theorem double_even_renamed (m : Nat) : Even (double m) := double_even m

theorem norm1_add (p q : Point) : (p + q).norm1 = p.norm1 + q.norm1 := by
  show (p.x + q.x) + (p.y + q.y) = (p.x + p.y) + (q.x + q.y)
  omega

theorem pairMap_fst {α : Type u} {β : Type v} (f : α → β) (p : α × α) :
    (pairMap f p).1 = f p.1 := rfl

/-- `pairMap_fst` with different universe and binder names: same `stmtHash`. -/
theorem pairMap_fst_renamed.{a, b} {γ : Type a} {δ : Type b} (g : γ → δ) (q : γ × γ) :
    (pairMap g q).1 = g q.1 := rfl

theorem halve_le (n : Nat) : halve n ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold halve
    split
    · omega
    · have := ih (n - 2) (by omega)
      omega

theorem isZero_iff (n : Nat) : isZero n = true ↔ n = 0 := by
  cases n <;> simp [isZero]

end Trust
