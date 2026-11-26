/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categories.Lang
import Imprimatur

/-! The notation of `Strict` without a metavariable for `Nat`: the grammar of
`Des` has a production whose variable `n` the reader cannot type. -/

open Cats

latex_style categories := strict
latex_category Prog => "P"
latex_category Rep => r"\overline{P}"
latex_category Des => "D"
latex_category List Prog => r"\vec{P}"
latex_notation lower p => r"\mathsf{lower}(#p)"
latex_notation Des.copies n ps => r"\mathsf{copies}(#n, #ps)"
latex_notation Des.beside a b => r"#a \parallel #b" prec := 60
