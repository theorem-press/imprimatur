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

/-- Two programs named `a` and `b`: written `P₁` and `P₂`, in order. -/
theorem symm (a b : Prog) (h : a = b) : b = a := h.symm

/-- Two programs named `a₁` and `b₁`: both written `P₁`. -/
theorem symm' (a₁ b₁ : Prog) (h : a₁ = b₁) : b₁ = a₁ := h.symm

/-- A function of a program, applied to one. -/
def apply (f : Prog → Nat) : Nat := f (.mk 0)

/-- A λ whose binder nothing uses: `_`, not `P`. -/
def ignore : Nat := apply fun _ => 0

/-- Two programs, as a list the notation writes in braces. -/
def two : List Prog := [.mk 1, .mk 2]

/-- One program, as a list the notation writes as its element. -/
def one : List Prog := [.mk 1]

/-- Designs. -/
inductive Des where
  /-- `n` copies of each program -/
  | copies (n : Nat) (ps : List Prog)
  /-- side by side -/
  | beside (d₁ d₂ : Des)

/-- Numbers named `n` and `k`, both metavariables of `Nat` in `Strict`, and
`m`, which is written with the category's own letter, numbered apart from `n`. -/
theorem nats (n k m : Nat) (h : n = k) : k + m = n + m := by rw [h]

/-- An integer named `k`, a metavariable of `Nat` in `Strict`: allowed where
the statement declares it (`Let k ∈ ℤ`), not where it is free. -/
theorem int_k (k : Int) (h : 0 ≤ k) : 0 ≤ k := h

/-- A list of programs, which a category may be declared for, and a list of
numbers, which none is. -/
theorem lists (ps : List Prog) (ns : List Nat) (h : ps.length = ns.length) :
    ns.length = ps.length := h.symm

end Cats
