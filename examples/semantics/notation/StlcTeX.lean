import Stlc
import Imprimatur

/-! # How the paper writes the calculus

The notation module, outside the host project (external mode): one line per
construct, and the conventions the paper's rules follow. -/

open Stlc

-- Judgements.
latex_notation HasType Γ e t => r"#Γ \vdash #e : #t" prec := 10
latex_notation HasType [] e t => r"\vdash #e : #t" prec := 10
latex_notation Step e e' => r"#e \longrightarrow #e'" prec := 10
latex_notation Alpha e e' => r"#e =_{\alpha} #e'" prec := 10

-- Terms and types.
latex_notation Tm.var x => r"#x"
latex_notation Tm.lam x t e => r"\lambda #x{:}#t.\, #e" prec := 0
-- Application, with both operands parenthesised unless atomic or tighter, so
-- that it reads unambiguously next to swapping.
latex_notation Tm.app e₁ e₂ => r"#e₁\; #e₂" prec := 100  assoc := none
latex_notation Tm.unit => r"()"
latex_notation Ty.base => r"\mathsf{b}"
latex_notation Ty.arrow t₁ t₂ => r"#t₁ \to #t₂" prec := 25  assoc := right
latex_notation Tm => r"\mathit{Term}"
latex_notation Ty => r"\mathit{Type}"
latex_notation Atom => r"\mathit{Name}"

-- Names: swapping, written (a\ b)·e as in Pitts's paper, and freshness,
-- c # a, b, e, e' for "c occurs in none of them".
latex_notation swapAtom a b c => r"(#a\ #b)(#c)"
-- Swapping binds like application: (a b)·(e₁ e₂), and ((a b)·e₁) ((a b)·e₂).
latex_notation Tm.swap a b e => r"(#a\ #b) \cdot #e" prec := 100  assoc := none
latex_notation c ∉ a :: b :: Tm.atoms e ++ Tm.atoms e' => r"#c \mathrel{\#} #a, #b, #e, #e'" prec := 50
latex_notation subst x u e => r"#e[#u/#x]"
latex_notation Ctx.swap a b Γ => r"(#a\ #b) \cdot #Γ" prec := 100  assoc := none
latex_notation Tm.fv e => r"\mathit{fv}(#e)"
latex_notation Ctx => r"\mathit{Context}"

-- Contexts.
latex_notation List.cons (x, t) Γ => r"#Γ, #x{:}#t" prec := 20
latex_notation lookup Γ x = some t => r"#Γ(#x) = #t" prec := 50
-- `v ∈ Val` is membership in the predicate `Val`, which is `IsValue v`; a
-- theorem binds a value in `Val` (the convention below).
latex_notation IsValue v => r"#v \in \mathit{Val}"  synonym
latex_notation IsValue => r"\mathit{Val}"

-- A type variable is written τ, with its subscript: t₁ is τ₁.
latex_metavar t => r"\tau" decorated

-- A premise `IsValue v` is left implicit: v is written \val instead.
latex_metavar_convention IsValue v => r"\val"
-- Well-formedness side conditions are not shown.
latex_hide_premise Ctx.WF _

-- Reduction rules are labelled from their names, (⟶-App Left), and each
-- carries a \rulelabel anchor so prose can refer to it.
latex_rules Step label := r"($\longrightarrow$-#)" label_macro := "rulelabel" sep := " "
-- So are the rules of α-equivalence: (α-Lam).
latex_rules Alpha label := r"($\alpha$-#)"

-- The metavariables of the grammar.
latex_category Tm => "e"
latex_category Ty => r"\tau"

-- The key of a block can be a title rather than a Lean name.
latex_entry "Values are final" => Stlc.value_irreducible
latex_entry "Swapping is involutive" => Stlc.Tm.swap_swap
latex_entry "Equivariance" => Stlc.HasType.swap
latex_entry "Preservation" => Stlc.preservation
latex_entry "Progress" => Stlc.progress
