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

-- Binder patterns, in a variant so that the built-in forms stay in use in
-- the default notation. A chain of binders folds (`flatten`) into one list,
-- separated by `sep`.
latex_notation (variant := "binders") ∃ x, p => r"\exists #x.\, #p" flatten sep := ", " prec := 10
latex_notation (variant := "binders") ∀ x, p => r"\forall #x.\, #p" flatten prec := 10
latex_notation (variant := "binders") p → q => r"#p \Rightarrow #q" prec := 20 assoc := right
latex_notation (variant := "binders") fun x => e => r"(#x \mapsto #e)"
latex_notation (variant := "binders") bigsum (fun k => f) => r"\sum_{#k} #f"
latex_notation (variant := "binders") bigsum f => r"\sum #f"
-- A nested binder pattern, and an operator whose chains are parenthesised on
-- both sides.
latex_notation (variant := "binders") p ∧ q => r"#p \wedge #q" prec := 35 assoc := none
-- A guard: the rule applies only when `p` is an existential, and shows it.
latex_notation (variant := "binders") ¬ p => r"\neg(#p)" when p := (Exists _)
-- `break`: a long chain of joins may break the line before each operator.
latex_notation join a b => r"#a \sqcup #b" prec := 65 break
-- A metavariable renamed under subscripts too: `acc₁` is `a_{1}`.
latex_metavar acc => "a" decorated
