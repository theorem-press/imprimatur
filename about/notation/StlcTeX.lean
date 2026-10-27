import Stlc
import Imprimatur

/-! # How the paper writes its example

Terms are M, types A; the model's letters (e, b, d, …) are untouched. -/

open Stlc

latex_notation Stlc.Step e e' => r"#e \longrightarrow #e'" prec := 10
latex_notation Stlc.IsValue v => r"#v \in \mathit{Val}" prec := 50
latex_notation Stlc.subst e v => r"#e[#v]"
latex_notation Stlc.Tm.var i => r"x_{#i}"
latex_notation Stlc.Tm.lam t e => r"\lambda{:}#t.\, #e" prec := 0
latex_notation Stlc.Tm.app e₁ e₂ => r"#e₁\; #e₂" prec := 100
latex_notation Stlc.Tm.unit => r"()"
latex_notation Stlc.Ty.base => r"\mathsf{b}"
latex_notation Stlc.Ty.arrow a b => r"#a \to #b" prec := 25
latex_notation Stlc.Tm => r"\mathit{Term}"
latex_notation Stlc.Ty => r"\mathit{Type}"

-- Values are written V, and their IsValue premises are left implicit.
latex_metavar_convention Stlc.IsValue v => r"V"

latex_category Stlc.Tm => "M"
latex_category Stlc.Ty => "A"

latex_rules Stlc.Step label := r"(#)"

latex_entry "Values are final" => Stlc.values_final

/-! ## The anatomy of a prose block

A view for the paper's example of Theorem 1.3: the TeX of a key's prose
rendering, as a string, and the formulas the prose parser
(`Imprimatur.Layout.proseSentence`, the one the theorems are about) takes
it apart into, each with the part of the sentence it is and how it is
typeset. It is computed from the rendering when the paper is built, so it
cannot drift from the block it describes. With `pin=C`, the rendering must
also be the string constant `C`, which a theorem is about
(`About.valuesFinal_parses`); a rendering that has changed is an error. -/

latex_notation About.valuesFinalTeX => r"t_{1}"
latex_notation About.valuesFinalSentence => r"\mathit{pr}_{1}"
latex_entry "Values are final, taken apart" => About.valuesFinal_parses

open Imprimatur in
/-- A string of TeX source, shown as a string in code. -/
def texString (cs : List Char) : String :=
  "\\LeanCodeInline{\"" ++ TeX.escape (String.ofList cs) ++ "\"}"

open Imprimatur Imprimatur.Layout in
/-- The prose rendering of a key, and the formulas it comes apart into. -/
@[latex_view "about.prose-anatomy"]
def proseAnatomy : Imprimatur.ViewFn := fun key c opts => do
  let some c := c | return s!"\\textit\{no declaration for {TeX.escape key}}"
  let tex ← Views.proseView c 0
  if let some (_, pin) := opts.find? (·.1 == "pin") then
    let pinned : Option String := match (← Lean.getEnv).find? pin.toName with
      | some (.defnInfo d) => match d.value with
        | .lit (.strVal s) => some s
        | _ => none
      | _ => none
    match pinned with
    | none => throwError "pin={pin}: no string constant of that name"
    | some s =>
      unless s == tex do
        throwError "the prose rendering of {key} is no longer {pin}, which a theorem is about: \
          update {pin} to {repr tex}, and the theorem's sentence with it"
  let row (role : String) (f : List Char) : String :=
    s!"{role} & {texString f} & ${String.ofList f}$\\\\\n"
  let rows : String := match proseSentence tex.toList with
    | some (.statement s) =>
      let vars := s.vars.foldl (fun acc g =>
        let names := g.names.foldl (fun acc n => acc ++ row "a variable" n) ""
        acc ++ names ++ match g.kind with
          | .ofType t => row "its range" t
          | _ => "") ""
      let hyps := s.hyps.foldl (fun acc h => acc ++ row "a hypothesis" h.formula) ""
      let concl := match s.concl with
        | .formula f => row "the conclusion" f
        | .conjuncts fs => fs.foldl (fun acc f => acc ++ row "a conjunct" f) ""
        | .iff l r => row "the left side" l ++ row "the right side" r
        | .exists_ _ _ => "the conclusion & \\multicolumn{2}{l}{(an existential)}\\\\\n"
      vars ++ hyps ++ concl
    | some (.define f) => row "the definition" f
    | none => "\\multicolumn{3}{l}{\\textit{the prose parser does not read it}}\\\\\n"
  return "\\begin{center}\\small\n" ++ texString tex.toList ++ "\n\\\\[1ex]\n" ++
    "\\begin{tabular}{@{}l@{\\quad}l@{\\quad}l@{}}\n" ++
    "\\textit{Part} & \\textit{Formula, as TeX} & \\textit{Typeset}\\\\\n\\hline\n" ++ rows ++
    "\\end{tabular}\n\\end{center}\n"
