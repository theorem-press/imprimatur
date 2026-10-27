import Stlc
import Imprimatur

/-! # How the paper writes its example

Terms are M, types A; the model's letters (e, b, d, …) are untouched. -/

open Stlc

latex_notation Stlc.Step e e' => r"#e \longrightarrow #e'" prec := 10
-- `v ∈ Val` is membership in the predicate `Val`, which is `IsValue v`.
latex_notation Stlc.IsValue v => r"#v \in \mathit{Val}" prec := 50 synonym
latex_notation Stlc.IsValue => r"\mathit{Val}"
latex_notation Stlc.subst e v => r"#e[#v]"
latex_notation Stlc.Tm.var i => r"x_{#i}"
latex_notation Stlc.Tm.lam t e => r"\lambda{:}#t.\, #e" prec := 0
latex_notation Stlc.Tm.app e₁ e₂ => r"#e₁\; #e₂" prec := 100
latex_notation Stlc.Tm.unit => r"()"
latex_notation Stlc.Ty.base => r"\mathsf{b}"
latex_notation Stlc.Ty.arrow a b => r"#a \to #b" prec := 25
latex_notation Stlc.Tm => r"\mathit{Term}"
latex_notation Stlc.Ty => r"\mathit{Type}"

-- Values are written V, and their IsValue premises are left implicit: a
-- theorem binds V in Val, and the conventions table lists V.
latex_metavar_convention Stlc.IsValue v => r"V"

latex_category Stlc.Tm => "M"
latex_category Stlc.Ty => "A"

latex_rules Stlc.Step label := r"(#)"
latex_rules Stlc.IsValue label := r"(#)"

latex_entry "Values are final" => Stlc.values_final
