/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Planet.Paper
import Imprimatur

/-!
# Notation for PLanet's analysis rules (DESIGN §16, M5)

The `rules` view of `Der` and `DerF` in the paper's notation: judgements
`\judge{main}(x)`, labels `\lab{cb}(x)`, and the design left implicit. The
Lift rules (`nest_l`, …) stay hand-written in the paper. Labels come from the
constructors' docstrings (`T-CB: …`).
-/

open Planet Planet.Structural Planet.Factors Planet.Fig1

-- The paper's variables are x and y, and k_x is a variable's number of
-- conditions.
latex_style applied_variables := subscript
latex_metavar i => "x"
latex_metavar v => "x"
latex_metavar j => "y"
latex_metavar w => "y"
latex_metavar spec => "L"
latex_metavar mx => r"p = p_{\max}"
latex_notation Des.leaf _ _ _ spec => r"#spec"
latex_notation Des.nest A B => r"\nestD{#A}{#B}"
latex_notation Des.cross A B => r"\crossD{#A}{#B}"
latex_notation LeafSpec.cb spec i = true => r"\lab{cb}(#i)"
latex_notation LeafSpec.within spec i = true => r"\lab{within}(#i)"
latex_notation Option.isSome (LeafSpec.order spec i) = true => r"\lab{ord}(#i)"
latex_notation free D i = true => r"\lab{free}(#i)"
latex_notation @LE.le ℕ _ 2 n => r"#n \geq 2"
latex_notation Dvd.dvd a b => r"#a \mid #b"
latex_notation Fintype.card C => r"|#C|"
-- Variables of a composite design are those of its parts.
latex_notation Sum.inl i => r"#i"
latex_notation Sum.inr j => r"#j"
latex_notation Fac.var v => r"#v"
latex_notation Fac.comp mf j => r"#mf_{#j}"
-- Judgements, with the design left implicit as in the paper.
latex_notation Der _ _ (Judg.ord i) => r"\judge{ord}(#i)"
latex_notation Der _ _ (Judg.time i) => r"\judge{time}(#i)"
latex_notation Der _ _ (Judg.main i) => r"\judge{main}(#i)"
latex_notation Der _ _ (Judg.within i) => r"\judge{within}(#i)"
latex_notation Der _ _ (Judg.inter v w) => r"\judge{inter}(#v, #w)"
latex_notation Der _ _ (Judg.time2 v w) => r"\judge{time}(#v, #w)"
latex_notation Der _ _ (Judg.within2 v w) => r"\judge{within}(#v, #w)"
latex_notation DerF _ _ (JudgF.main f) => r"\judge{main}(#f)"
latex_notation DerF _ _ (JudgF.inter f g) => r"\judge{inter}(#f, #g)"

latex_group "Analysis rules" := [Der.t_cb, Der.t_max, Der.ord, Der.m_ord, Der.w_nr, Der.m_cb,
  Der.i_cb, Der.i_ord, Der.t_int, DerF.m_mf, DerF.i_mf, Der.i_nest, Der.w_nest, Der.i_cross_l,
  Der.i_cross_r]
