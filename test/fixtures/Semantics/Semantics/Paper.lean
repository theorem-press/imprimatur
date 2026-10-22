/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Semantics.Lang
import Imprimatur

/-! The paper's notation: judgements, metavariables, conventions and groups. -/

open Stlc

latex_notation HasType Γ e t => r"#Γ \vdash #e : #t" prec := 10
latex_notation Step e e' => r"#e \longrightarrow #e'" prec := 10
latex_notation Tm.var i => r"x_{#i}"
latex_notation Tm.lam t e => r"\lambda{:}#t.\, #e" prec := 0
latex_notation Tm.app e₁ e₂ => r"#e₁\; #e₂" prec := 100
latex_notation Tm.unit => r"()"
-- A structure without a category, headed in the grammar view by its notation.
latex_notation Claim => r"\mathit{Claim}"
latex_notation Ty.base => r"\mathsf{b}"
latex_notation Ty.arrow a b => r"#a \to #b" prec := 25
latex_notation List.cons t Γ => r"#Γ, #t" prec := 20
latex_notation lookup Γ i = some t => r"#Γ(#i) = #t" prec := 50
latex_notation subst e v => r"#e[#v]"

-- Values are written v, and their IsValue premises are left implicit.
latex_metavar_convention IsValue v => r"\val"
-- Well-formedness side conditions are not shown.
latex_hide_premise Ctx.WF _

-- Step rules are labelled (\longrightarrow-App Left), with words separated
-- by a space, and can be referred to. Their docstrings are prose, not labels.
latex_rules Step label := r"($\longrightarrow$-#)" label_macro := "rulelabel" sep := " " doc_labels := false
latex_rule_label Step.app_right "App-R"

-- The paper's binder names are TeX, and applied variables are written f(x).
latex_style names := raw
latex_style applied_variables := call

-- A key that is a title rather than a name, with an option for its views.
latex_entry "Preservation" => Stlc.step_app options := "forall"

latex_group "Typing and evaluation" := [HasType.app, Step.beta, Step.app_left]
-- Displays: definitions as `lhs ≜ rhs` rows (clauses), and types as grammar
-- rows (grammar|display), each block keyed by its title.
latex_display "Lookup and size" := [lookup, size]
latex_display "Types and terms" := [Ty, Tm]
-- A title that also names a declaration (core's `Prod`) is the display's.
latex_display "Prod" := [Ty]

latex_category Tm => "e"
latex_category Ty => r"\tau"

/-- A custom view (DESIGN §7.3): the names of an inductive's rules, as a list. -/
@[latex_view "fixture.rulelist"]
def ruleList : Imprimatur.ViewFn := fun key c _ => do
  match c with
  | some (.inductInfo i) =>
    return s!"\\textsf\{{key}}: " ++ ", ".intercalate (i.ctors.map fun n => n.getString!)
  | _ => return s!"\\textsf\{{key}}"
