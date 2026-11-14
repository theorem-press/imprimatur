import Stlc.Safety

/-! Examples: concrete instances of the judgements and theorems, two or three
for each section of the paper. The names `x`, `y`, `z` and `f` are fixed
atoms, so the examples can be read as a paper would write them. -/

namespace Stlc

namespace Names
/-- The name $\mathtt{x}$. -/
def x : Atom := 0
/-- The name $\mathtt{y}$. -/
def y : Atom := 1
/-- The name $\mathtt{z}$, fresh for $\mathtt{x}$ and $\mathtt{y}$. -/
def z : Atom := 2
/-- The name $\mathtt{f}$. -/
def f : Atom := 3
end Names

open Names

/-! ## Syntax -/

/-- Terms carry names, so two abstractions that differ only in the name
they bind are different terms. -/
theorem ex_names : Tm.lam x .base (.var x) ≠ Tm.lam y .base (.var y) := by
  intro h
  injection h with h
  exact absurd h (by decide)

/-- In $\lambda x{:}\mathsf{b}.\, x\; y$ the name $x$ is bound and $y$ is free. -/
theorem ex_fv :
    x ∉ (Tm.lam x .base (.app (.var x) (.var y))).fv ∧
    y ∈ (Tm.lam x .base (.app (.var x) (.var y))).fv := by
  constructor <;> simp [Tm.fv, x, y]

/-! ## Names, α-equivalence and substitution -/

/-- Two abstractions that bind their names in opposite order are
α-equivalent: swapping each binder with the fresh name $z$ makes the bodies
equal. -/
theorem ex_alpha :
    Alpha (.lam x .base (.lam y .base (.var x))) (.lam y .base (.lam x .base (.var y))) := by
  refine .lam (c := z) (by decide) ?_
  have h₁ : (Tm.lam y .base (.var x)).swap x z = .lam y .base (.var z) := rfl
  have h₂ : (Tm.lam x .base (.var y)).swap y z = .lam x .base (.var z) := rfl
  rw [h₁, h₂]
  refine .lam (c := 3) (by decide) ?_
  have h₃ : (Tm.var z).swap y 3 = .var z := rfl
  have h₄ : (Tm.var z).swap x 3 = .var z := rfl
  rw [h₃, h₄]
  exact .var

/-- Substitution avoids capture: substituting $y$ for $x$ under a binder
$y$ renames the binder to the fresh name $z$. -/
theorem ex_subst : subst x (.var y) (.lam y .base (.var x)) = .lam z .base (.var y) := by
  unfold subst
  have hc : fresh (x :: y :: (Tm.var x).atoms ++ (Tm.var y).atoms) = z := by decide
  simp only [hc]
  have hs : (Tm.var x).swap y z = .var x := rfl
  rw [hs]
  unfold subst
  simp

/-! ## Typing -/

/-- A typing with a non-empty context: $f$ is a function, applied to the
bound variable. -/
theorem ex_typing :
    HasType [(f, .arrow .base .base)] (.lam x .base (.app (.var f) (.var x))) (.arrow .base .base) :=
  .lam (.app (.var trivial rfl) (.var trivial rfl))

/-- Not every term has a type: the unit value is no function, so applying
it is ill typed. -/
theorem ex_untypable : ¬ ∃ t, HasType [] (.app .unit .unit) t := by
  rintro ⟨t, h⟩
  cases h with
  | app h₁ _ => cases h₁

/-! ## Reduction -/

theorem subst_var_self (a : Atom) (u : Tm) : subst a u (.var a) = u := by
  unfold subst; simp

/-- A β-reduction: the identity applied to the unit value. -/
theorem ex_beta : Step (.app (.lam x .base (.var x)) .unit) .unit := by
  have h := @Step.beta x .base (.var x) .unit .unit
  rwa [subst_var_self] at h

/-- Call by value: the argument of an application reduces before the
application itself, and the outer β-reduction waits for it. -/
theorem ex_cbv :
    Step (.app (.lam x .base (.var x)) (.app (.lam y .base (.var y)) .unit))
      (.app (.lam x .base (.var x)) .unit) := by
  have h := @Step.beta y .base (.var y) .unit .unit
  rw [subst_var_self] at h
  exact .app_right .lam h

/-! ## Results -/

/-- Swapping renames every occurrence of the two names, the binder
included. -/
theorem ex_swap : (Tm.lam x .base (.var y)).swap x y = .lam y .base (.var x) := rfl

/-- The unit value has no function type. -/
theorem ex_unit_not_arrow : ¬ HasType [] .unit (.arrow .base .base) := by
  intro h
  cases h

/-! ## Type safety -/

/-- Equivariance, applied to the typing above: swapping $f$ and $x$
throughout, the function is now called $x$ and the bound variable $f$. -/
theorem ex_equivariance :
    HasType [(x, .arrow .base .base)] (.lam f .base (.app (.var x) (.var f))) (.arrow .base .base) := by
  have h := ex_typing.swap f x
  simpa [Ctx.swap, Tm.swap, swapAtom, x, f] using h

/-- Preservation along a step: a well-typed term reduces to a term of the
same type. -/
theorem ex_preservation :
    HasType [] (.app (.lam f (.arrow .base .base) (.app (.var f) .unit)) (.lam x .base (.var x))) .base ∧
    Step (.app (.lam f (.arrow .base .base) (.app (.var f) .unit)) (.lam x .base (.var x)))
      (.app (.lam x .base (.var x)) .unit) ∧
    HasType [] (.app (.lam x .base (.var x)) .unit) .base := by
  refine ⟨.app (.lam (.app (.var trivial rfl) (.unit trivial))) (.lam (.var trivial rfl)), ?_,
    .app (.lam (.var trivial rfl)) (.unit trivial)⟩
  have hs : subst f (.lam x .base (.var x)) (.app (.var f) .unit) = .app (.lam x .base (.var x)) .unit := by
    unfold subst; simp [subst, subst_var_self]
  have h := @Step.beta f (.arrow .base .base) (.app (.var f) .unit) (.lam x .base (.var x)) .lam
  rwa [hs] at h

/-- Progress needs a closed term: an open term can be well typed, yet
neither a value nor able to reduce. -/
theorem ex_stuck :
    HasType [(x, .arrow .base .base)] (.app (.var x) .unit) .base ∧
    ¬ IsValue (.app (.var x) .unit) ∧
    ∀ e, ¬ Step (.app (.var x) .unit) e := by
  refine ⟨.app (.var trivial rfl) (.unit trivial), ⟨(fun h => by cases h), fun e h => ?_⟩⟩
  cases h with
  | app_left h => cases h
  | app_right _ h => cases h

end Stlc
