/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Patterns.Defs
import Imprimatur

/-! The notation module: cases, and list literals. -/

open Patterns

latex_style pattern_matching := cases
latex_style lists := literal

-- An element of either side is written as it is, except in a case's
-- patterns, where the injection is shown.
latex_notation Sum.inl a => r"#a"
latex_notation Sum.inr b => r"#b"
latex_notation Sum.inl a => r"\mathsf{inl}\,#a" prec := 1023
latex_notation Sum.inr b => r"\mathsf{inr}\,#b" prec := 1023
latex_notation Option.some a => r"\mathsf{some}\,#a" prec := 1023
latex_notation Option.none => r"\mathsf{none}"
latex_notation List.nil => r"[\,]"
latex_notation List.head l h => r"\mathsf{head}(#l)" hide h := _
latex_notation dite c t e => r"\mathsf{if}\ #c\ \mathsf{then}\ #t\ \mathsf{else}\ #e" prec := 0
