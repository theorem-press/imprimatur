import Mathlib

/-! # What the archive claims

The five theorems that the Lean archive released by Levent Alpöge on
2026-11-20 (https://alpo.ge/remark.pdf) claims to prove, stated with
Mathlib's definitions only, as the Comparator challenge file of
https://github.com/Deicyde/riemann-hypothesis states them. Every proof here
is `sorry`: this file says what is claimed, and proves nothing. -/

namespace Riemann

/-- The Riemann Hypothesis, as Mathlib states it: every zero of `riemannZeta`
other than the trivial zeros at the negative even integers, and other than
the point `1` where Mathlib's `riemannZeta` takes a junk value, has real part
one half. -/
theorem riemannHypothesis : RiemannHypothesis := by sorry

/-- The Riemann Hypothesis, with the hypotheses written as implications. -/
theorem riemannZeta_eq_zero_re (s : ℂ) (h : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hone : s ≠ 1) : s.re = 1 / 2 := by sorry

/-- A Dirichlet L-function has no zero to the right of the critical line,
except that the trivial character's L-function is the zeta function, which
has its pole at `1`. -/
theorem LFunction_ne_zero_of_half_lt_re (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ) (hs : 1 / 2 < s.re) (h : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by sorry

/-- The Generalized Riemann Hypothesis: every zero of a Dirichlet L-function
in the critical strip lies on the critical line. -/
theorem LFunction_eq_zero_re (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h₀ : 0 < s.re) (h₁ : s.re < 1) (h : DirichletCharacter.LFunction χ s = 0) :
    s.re = 1 / 2 := by sorry

/-- The Generalized Riemann Hypothesis for primitive characters. -/
theorem LFunction_eq_zero_re_of_isPrimitive (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (s : ℂ) (h₀ : 0 < s.re) (h₁ : s.re < 1)
    (h : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 := by sorry

end Riemann
