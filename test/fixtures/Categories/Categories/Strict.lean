/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categories.Lang
import Imprimatur

/-! The notation, with `latex_style categories := strict`. -/

open Cats

latex_style categories := strict
latex_category Prog => "P"
latex_category Rep => r"\overline{P}"
latex_category Des => "D"
latex_category Nat => "n" "k"
-- A category at arguments: lists of programs, not lists of numbers.
latex_category List Prog => r"\vec{P}"
latex_notation lower p => r"\mathsf{lower}(#p)"
latex_notation Des.copies n ps => r"\mathsf{copies}(#n, #ps)"
latex_notation Des.beside a b => r"#a \parallel #b" prec := 60
-- A list of programs is written by the project's rules, not as `[a, b]`.
latex_style lists := literal
latex_notation Prog.mk n => r"\mathsf{prog}(#n)"
latex_notation List.cons (α := Prog) h t => r"\{#h; #t\}" prec := 5
