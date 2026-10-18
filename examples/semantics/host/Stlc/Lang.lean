/-! A small simply-typed λ-calculus with name-carrying terms, a typing
relation and a small-step reduction relation.

Names are handled as in Pitts, "Alpha-structural recursion and induction"
(J. ACM 53(3), 2006): the basic operation on names is *swapping*, which
exchanges two names everywhere in a term, bound and free occurrences alike.
α-equivalence is defined by swapping a binder's name with a fresh one, and
substitution by recursion that renames each binder to a fresh name by
swapping. -/

namespace Stlc

/-- Names of variables. -/
abbrev Atom := Nat

/-- types -/
inductive Ty where
  /-- the base type -/
  | base
  /-- functions -/
  | arrow (t₁ t₂ : Ty)

/-- terms, with names -/
inductive Tm where
  /-- a variable -/
  | var (x : Atom)
  /-- an abstraction, binding $x$ in $e$ -/
  | lam (x : Atom) (t : Ty) (e : Tm)
  /-- an application -/
  | app (e₁ e₂ : Tm)
  /-- the unit value -/
  | unit

/-! ## Swapping -/

/-- Swapping two names: `a` becomes `b`, `b` becomes `a`, and other names
are unchanged. -/
def swapAtom (a b c : Atom) : Atom := if c = a then b else if c = b then a else c

/-- Swapping two names throughout a term: bound, binding and free
occurrences alike. -/
def Tm.swap (a b : Atom) : Tm → Tm
  | .var x => .var (swapAtom a b x)
  | .lam x t e => .lam (swapAtom a b x) t (e.swap a b)
  | .app e₁ e₂ => .app (e₁.swap a b) (e₂.swap a b)
  | .unit => .unit

/-- The names that occur in a term, bound or free. -/
def Tm.atoms : Tm → List Atom
  | .var x => [x]
  | .lam x _ e => x :: e.atoms
  | .app e₁ e₂ => e₁.atoms ++ e₂.atoms
  | .unit => []

/-- A name that is not in a list. -/
def fresh (l : List Atom) : Atom := l.foldr max 0 + 1

/-- The size of a term. -/
def Tm.size : Tm → Nat
  | .var _ => 1
  | .lam _ _ e => e.size + 1
  | .app e₁ e₂ => e₁.size + e₂.size + 1
  | .unit => 1

theorem swapAtom_swapAtom (a b c : Atom) : swapAtom a b (swapAtom a b c) = c := by
  unfold swapAtom
  by_cases h₁ : c = a <;> by_cases h₂ : c = b <;> simp [h₁, h₂] <;> omega

/-- Swapping is its own inverse. -/
theorem Tm.swap_swap (a b : Atom) (e : Tm) : (e.swap a b).swap a b = e := by
  induction e with
  | var x => simp [Tm.swap, swapAtom_swapAtom]
  | lam x t e ih => simp [Tm.swap, swapAtom_swapAtom, ih]
  | app e₁ e₂ ih₁ ih₂ => simp [Tm.swap, ih₁, ih₂]
  | unit => rfl

/-- Swapping preserves size. -/
theorem Tm.size_swap (a b : Atom) (e : Tm) : (e.swap a b).size = e.size := by
  induction e with
  | var => rfl
  | lam x t e ih => simp [Tm.swap, Tm.size, ih]
  | app e₁ e₂ ih₁ ih₂ => simp [Tm.swap, Tm.size, ih₁, ih₂]
  | unit => rfl

/-! ## α-equivalence and substitution -/

/-- α-equivalence. Two abstractions are equivalent when swapping each
binder's name with a name `c` fresh for both makes their bodies equivalent. -/
inductive Alpha : Tm → Tm → Prop
  | var {x} : Alpha (.var x) (.var x)
  | lam {a b c t e e'} (hc : c ∉ a :: b :: e.atoms ++ e'.atoms)
      (h : Alpha (e.swap a c) (e'.swap b c)) : Alpha (.lam a t e) (.lam b t e')
  | app {e₁ e₂ e₁' e₂'} (h₁ : Alpha e₁ e₁') (h₂ : Alpha e₂ e₂') :
      Alpha (.app e₁ e₂) (.app e₁' e₂')
  | unit : Alpha .unit .unit

/-- Capture-avoiding substitution of `u` for `x` in `e`. At an abstraction
the bound name is first swapped with a name fresh for everything in sight,
so no free name of `u` is captured; swapping preserves size, so the
recursion terminates. -/
def subst (x : Atom) (u : Tm) : Tm → Tm
  | .var y => if y = x then u else .var y
  | .lam a t e =>
    let c := fresh (x :: a :: e.atoms ++ u.atoms)
    .lam c t (subst x u (e.swap a c))
  | .app e₁ e₂ => .app (subst x u e₁) (subst x u e₂)
  | .unit => .unit
termination_by e => e.size
decreasing_by
  all_goals simp_wf
  all_goals simp only [Tm.size, Tm.size_swap]
  all_goals omega

/-! ## Typing and reduction -/

/-- Values. -/
inductive IsValue : Tm → Prop
  | lam {x t e} : IsValue (.lam x t e)
  | unit : IsValue .unit

/-- Contexts: names with their types, the most recent first. -/
abbrev Ctx := List (Atom × Ty)

/-- Well-formed contexts: a side condition that the paper leaves implicit. -/
def Ctx.WF (_Γ : Ctx) : Prop := True

/-- The type of a name in a context. -/
def lookup (Γ : Ctx) (x : Atom) : Option Ty := (Γ.find? (·.1 == x)).map (·.2)

/-- Typing. The rules' labels are in their docstrings. -/
inductive HasType : Ctx → Tm → Ty → Prop
  | /-- T-Var: a variable has its type in the context. -/
    var {Γ x t} (wf : Ctx.WF Γ) (h : lookup Γ x = some t) : HasType Γ (.var x) t
  | /-- T-Abs: abstraction. -/
    lam {Γ x t₁ t₂ e} (h : HasType ((x, t₁) :: Γ) e t₂) : HasType Γ (.lam x t₁ e) (.arrow t₁ t₂)
  | /-- T-App: application. -/
    app {Γ t₁ t₂ e₁ e₂} (h₁ : HasType Γ e₁ (.arrow t₁ t₂)) (h₂ : HasType Γ e₂ t₁) :
      HasType Γ (.app e₁ e₂) t₂
  | /-- T-Unit: the unit value. -/
    unit {Γ} (wf : Ctx.WF Γ) : HasType Γ .unit .base

/-- Small-step reduction, call by value. -/
inductive Step : Tm → Tm → Prop
  | beta {x t e v} (hv : IsValue v) : Step (.app (.lam x t e) v) (subst x v e)
  | app_left {e₁ e₁' e₂} (h : Step e₁ e₁') : Step (.app e₁ e₂) (.app e₁' e₂)
  | app_right {v e₂ e₂'} (hv : IsValue v) (h : Step e₂ e₂') : Step (.app v e₂) (.app v e₂')

/-- Values do not reduce. -/
theorem value_irreducible {v e : Tm} (hv : IsValue v) : ¬ Step v e := by
  intro h
  cases hv <;> cases h

/-- The unit value has only the base type. -/
theorem unit_type {Γ : Ctx} {t : Ty} (h : HasType Γ .unit t) : t = .base := by
  cases h
  rfl

/-- Reduction is a congruence on the function of an application. -/
theorem step_app {e₁ e₁' e₂ : Tm} (h : Step e₁ e₁') : Step (.app e₁ e₂) (.app e₁' e₂) :=
  Step.app_left h

end Stlc
