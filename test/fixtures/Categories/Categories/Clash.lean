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
latex_category Rep => "P"
latex_notation lower p => r"\mathsf{lower}(#p)"
