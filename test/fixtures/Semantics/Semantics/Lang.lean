/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! A small simply-typed λ-calculus. -/

namespace Stlc

/-- Types. -/
inductive Ty where
  /-- The base type. -/
  | base
  /-- Functions. -/
  | arrow (a b : Ty)

/-- Terms, with de Bruijn variables. -/
inductive Tm where
  /-- A variable. -/
  | var (i : Nat)
  /-- An abstraction. -/
  | lam (t : Ty) (e : Tm)
  /-- An application. -/
  | app (e₁ e₂ : Tm)
  /-- The unit value. -/
  | unit

/-- Values. -/
inductive IsValue : Tm → Prop
  | lam {t e} : IsValue (.lam t e)
  | unit : IsValue .unit

/-- Contexts. -/
abbrev Ctx := List Ty

/-- Well-formed contexts (a side condition that papers leave implicit). -/
def Ctx.WF (_Γ : Ctx) : Prop := True

/-- Lookup in a context. -/
def lookup (Γ : Ctx) (i : Nat) : Option Ty := Γ[i]?

/-- Substitution (a stand-in). -/
def subst (e _v : Tm) : Tm := e

/-- Typing. Labels come from docstrings. -/
inductive HasType : Ctx → Tm → Ty → Prop
  | /-- T-Var: a variable has its type in the context. -/
    var {Γ i t} (wf : Ctx.WF Γ) (h : lookup Γ i = some t) : HasType Γ (.var i) t
  | /-- T-Abs: abstraction. -/
    lam {Γ t₁ t₂ e} (h : HasType (t₁ :: Γ) e t₂) : HasType Γ (.lam t₁ e) (.arrow t₁ t₂)
  | /-- T-App: application. -/
    app {Γ t₁ t₂ e₁ e₂} (h₁ : HasType Γ e₁ (.arrow t₁ t₂)) (h₂ : HasType Γ e₂ t₁) :
      HasType Γ (.app e₁ e₂) t₂
  | /-- T-Unit. -/
    unit {Γ} (wf : Ctx.WF Γ) : HasType Γ .unit .base

/-- Small-step reduction. Labels come from the constructor names. -/
inductive Step : Tm → Tm → Prop
  /-- Reduce: a β-step. (Prose, not a label: see `doc_labels := false`.) -/
  | beta {t e v} (hv : IsValue v) : Step (.app (.lam t e) v) (subst e v)
  | app_left {e₁ e₁' e₂} (h : Step e₁ e₁') : Step (.app e₁ e₂) (.app e₁' e₂)
  | app_right {v e₂ e₂'} (hv : IsValue v) (h : Step e₂ e₂') : Step (.app v e₂) (.app v e₂')

/-- The size of a term, by recursion (for the `def` modifier). -/
def size : Tm → Nat
  | .var _ => 1
  | .lam _ e => size e + 1
  | .app e₁ e₂ => size e₁ + size e₂ + 1
  | .unit => 1

/-- A theorem with hypotheses (for the `rule` and `forall` modifiers). -/
theorem step_app {e₁ e₁' e₂ : Tm} (h : Step e₁ e₁') (hv : IsValue e₂) :
    Step (.app e₁ e₂) (.app e₁' e₂) :=
  Step.app_left h

end Stlc
