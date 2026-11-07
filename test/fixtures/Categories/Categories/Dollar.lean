/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categories.Lang
import Imprimatur

/-! A notation that is not plain: a template with a dollar in it. The
`prose` view's sentence then does not come apart into its formulas, and the
extractor reports the sentence as not validated (DESIGN §18.4). -/

open Cats

latex_category Prog => "P"
latex_category Rep => r"\overline{P}"
latex_notation lower p => r"\text{\$}\mathsf{lower}(#p)\text{\$}"
