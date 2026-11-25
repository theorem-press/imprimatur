import Riemann
import Imprimatur

/-! # How the note writes the statements

The notation module, outside the host project (external mode). The first
group writes the five claims; the rest writes Mathlib's definitions behind
them, which the note's preliminaries state. -/

open DirichletCharacter HurwitzZeta

-- The zeta function and the L-functions.
latex_notation riemannZeta s => r"\zeta(#s)"
latex_notation LFunction χ s => r"L(#χ, #s)"
-- The real part, and the complex numbers.
latex_notation Complex.re s => r"\Re #s" prec := 100
latex_notation Complex => r"\mathbb{C}"
-- A Dirichlet character modulo N; the trivial one is written 1 by the core pack.
latex_notation DirichletCharacter ℂ N => r"\mathrm{Char}(#N)"
latex_notation IsPrimitive χ => r"#χ \text{ is primitive}" prec := 50
-- Not a trivial zero: s is none of -2, -4, -6, …
latex_notation ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) => r"#s \ne -2(#n + 1) \text{ for every } #n \in \mathbb{N}" prec := 50
-- One half, as a fraction.
latex_notation (1 : ℝ) / 2 => r"\tfrac{1}{2}"

-- ## The definitions behind ζ

-- The Hurwitz zeta function at a point a of ℝ/ℤ, its even and odd parts, and
-- their completed forms.
latex_notation hurwitzZeta a s => r"\zeta_{#a}(#s)"
latex_notation hurwitzZetaEven a s => r"\zeta^{+}_{#a}(#s)"
-- The same functions unapplied, as the point-free definitions write them.
latex_notation riemannZeta => r"\zeta"
latex_notation hurwitzZetaEven a => r"\zeta^{+}_{#a}"
latex_notation hurwitzZetaOdd a s => r"\zeta^{-}_{#a}(#s)"
latex_notation completedHurwitzZetaEven a s => r"\Lambda^{+}_{#a}(#s)"
latex_notation completedHurwitzZetaOdd a s => r"\Lambda^{-}_{#a}(#s)"
-- The functional-equation pairs behind them, and a pair's data.
latex_notation hurwitzEvenFEPair a => r"\mathcal{P}^{+}_{#a}"
latex_notation hurwitzOddFEPair a => r"\mathcal{P}^{-}_{#a}"
latex_notation WeakFEPair.Λ P s => r"\Lambda_{#P}(#s)"
latex_notation WeakFEPair.Λ₀ P s => r"\Lambda^{0}_{#P}(#s)"
latex_notation WeakFEPair.Λ₀ P => r"\Lambda^{0}_{#P}"
latex_notation WeakFEPair.f_modif P => r"\tilde{f}_{#P}"
latex_notation WeakFEPair.f P => r"f_{#P}"
latex_notation WeakFEPair.g P => r"g_{#P}"
latex_notation WeakFEPair.k P => r"k_{#P}"
latex_notation WeakFEPair.ε P => r"\varepsilon_{#P}"
latex_notation WeakFEPair.f₀ P => r"f^{0}_{#P}"
latex_notation WeakFEPair.g₀ P => r"g^{0}_{#P}"
-- The Mellin transform, and integrals over a set.
latex_notation mellin f s => r"\mathcal{M}(#f)(#s)"
latex_notation mellin f => r"\mathcal{M}(#f)"
latex_notation ∫ t in S, f => r"\int_{#S} #f \,\mathrm{d}#t" prec := 67
latex_notation Set.Ioi a => r"(#a, \infty)"
latex_notation Set.Ioo a b => r"(#a, #b)"
latex_notation Set.indicator S f => r"\mathbf{1}_{#S}\,#f" prec := 70
-- The theta kernels and Jacobi's theta function.
latex_notation evenKernel a x => r"K^{+}_{#a}(#x)"
latex_notation cosKernel a x => r"K^{\cos}_{#a}(#x)"
latex_notation oddKernel a x => r"K^{-}_{#a}(#x)"
latex_notation sinKernel a x => r"K^{\sin}_{#a}(#x)"
latex_notation jacobiTheta₂ z τ => r"\theta(#z, #τ)"
latex_notation jacobiTheta₂_term n z τ => r"\theta_{#n}(#z, #τ)"
latex_notation jacobiTheta₂' z τ => r"\theta'(#z, #τ)"
latex_notation jacobiTheta₂'_term n z τ => r"\theta'_{#n}(#z, #τ)"
latex_notation jacobiTheta₂'' z τ => r"\theta''(#z, #τ)"
-- The Gamma function, Deligne's Γ_ℝ, and the integral that defines Γ.
latex_notation Complex.Gamma s => r"\Gamma(#s)"
latex_notation Complex.Gammaℝ s => r"\Gamma_{\mathbb{R}}(#s)"
latex_notation Complex.GammaIntegral s => r"\Gamma^{\!\int}(#s)"
-- Elementary pieces of those definitions that the packs do not write.
latex_notation Complex.exp z => r"e^{#z}"
latex_notation Real.exp x => r"\exp(#x)"
-- A real number as a point of the circle: the cast is invisible.
latex_notation ((a : ℝ) : UnitAddCircle) => r"#a"
-- π as a complex number is written as π: a synonym, so that the reading is
-- tried only where the real π makes no sense, as the base of a complex power.
latex_notation (Real.pi : ℂ) => r"\pi" synonym
-- A natural number cast to ℂ and raised to a complex power.
latex_notation ((N : ℕ) : ℂ) ^ (-s) => r"#N^{-#s}" prec := 75
latex_notation Complex.ofReal x => r"#x"
latex_notation Function.update f a b => r"#f[#a \mapsto #b]"
latex_notation (if c then a else b : ℂ) => r"(#a \text{ if } #c\text{, else } #b)"
latex_notation a • b => r"#a \bullet #b" prec := 70 assoc := none
latex_notation UnitAddCircle => r"\mathbb{R}/\mathbb{Z}"

-- ## The definitions behind L(χ, s)

latex_notation ZMod.LFunction Φ s => r"\mathcal{L}(#Φ, #s)"
-- A bundled homomorphism applied to an argument goes through a coercion the
-- pattern language cannot write, so these two rules name the homomorphism
-- itself, and the core pack writes the application. Implicit arguments are
-- not matched, so the modulus cannot be shown.
latex_notation ZMod.toAddCircle => r"\iota"
latex_notation DirichletCharacter.conductor χ => r"\mathfrak{f}(#χ)"
latex_notation conductorSet χ => r"\mathcal{F}(#χ)"
latex_notation FactorsThrough χ d => r"#χ \text{ factors through } #d" prec := 50
latex_notation changeLevel h => r"\mathrm{lift}" hide h := _
latex_notation sInf S => r"\inf #S" prec := 100
