/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The paper's example: a simply typed λ-calculus

Terms with de Bruijn variables, values, and small-step reduction, whose
substitution is a stand-in: `subst e v` is `e`. The paper replaces it to
show what the statement hash sees.
-/

namespace Stlc

/-- Types. -/
inductive Ty where
  /-- the base type -/
  | base
  /-- functions -/
  | arrow (a b : Ty)

/-- Terms, with de Bruijn variables. -/
inductive Tm where
  /-- a variable -/
  | var (i : Nat)
  /-- an abstraction -/
  | lam (t : Ty) (e : Tm)
  /-- an application -/
  | app (e₁ e₂ : Tm)
  /-- the unit value -/
  | unit

/-- Values: abstractions and unit. -/
inductive IsValue : Tm → Prop
  /-- an abstraction is a value -/
  | lam {t e} : IsValue (.lam t e)
  /-- unit is a value -/
  | unit : IsValue .unit

/-- Substitution, as a stand-in: the body is returned unchanged. -/
def subst (e e' : Tm) : Tm := e

/-- Small-step reduction. -/
inductive Step : Tm → Tm → Prop
  /-- β-reduction -/
  | beta {t e v} (hv : IsValue v) : Step (.app (.lam t e) v) (subst e v)
  /-- reduction of the function -/
  | app_left {e₁ e₁' e₂} (h : Step e₁ e₁') : Step (.app e₁ e₂) (.app e₁' e₂)
  /-- reduction of the argument, once the function is a value -/
  | app_right {v e₂ e₂'} (hv : IsValue v) (h : Step e₂ e₂') : Step (.app v e₂) (.app v e₂')

/-- Values are final: a value does not reduce. -/
theorem values_final {v e : Tm} (hv : IsValue v) : ¬ Step v e := by
  intro hs
  cases hv <;> cases hs

end Stlc
