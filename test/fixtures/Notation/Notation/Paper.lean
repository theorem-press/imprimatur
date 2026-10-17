/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Notation.Defs
import Imprimatur

/-! The notation module: one rule for each feature of `latex_notation`. -/

open Notation

-- A rule with a precedence.
latex_notation double n => r"2#n" prec := 70
-- A nested pattern, and a hidden argument that must be `Fin.elim0`.
latex_notation ¬ Realize U φ ρ => r"#U \not\models #φ" hide ρ := Fin.elim0 prec := 50
latex_notation Realize U φ ρ => r"#U \models #φ" hide ρ := Fin.elim0 prec := 50
-- A variant, chosen with notation=named.
latex_notation (variant := "named") double n => r"\mathrm{dbl}(#n)"
-- Flattening a chain into one n-ary call.
latex_notation lub a b => r"\lub{#a, #b}" flatten
-- An infix operator; the width is given, not estimated from the TeX.
latex_notation cons a b => r"#a \mathbin{\triangleright} #b" prec := 60 width := 3
-- A pattern with a constant in it.
latex_notation Judg n => r"\vdash #n"
-- A constant with no arguments.
latex_notation zeroish => r"\mathbf{0}"
-- A metavariable name.
latex_metavar spec => "L"
-- A typed pattern (the `@` form names implicit arguments): it applies only
-- where the type is a `MySet`.
latex_notation @LE.le (MySet _) _ a b => r"#a \sqsubseteq #b" prec := 50
