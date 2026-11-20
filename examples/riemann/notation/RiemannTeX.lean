import Riemann
import Imprimatur

/-! # How the note writes the statements

The notation module, outside the host project (external mode). -/

open DirichletCharacter

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
