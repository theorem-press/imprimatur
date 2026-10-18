/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Unit tests of the `Doc` emitter (PLAN M4)

Escaping, widths, precedence and parentheses, line breaking and templates.
-/

open Testkit Imprimatur

namespace ExtractTest.DocTests

/-- An infix node: `a op b` at `prec`, left-associative. -/
def infixDoc (prec : Nat) (op : String) (a b : Doc) : Doc :=
  .node prec #[.child prec a, .brk, .tex s!" {op} ", .child (prec + 1) b]

/-- All the emitter tests. -/
def tests : TestM Unit := group "doc" do
  -- Escaping: every TeX special character.
  checkEq "extract/doc/escape-specials" (TeX.escape "\\ { } # $ % & _ ~ ^")
    "\\textbackslash{} \\{ \\} \\# \\$ \\% \\& \\_ \\textasciitilde{} \\textasciicircum{}"
  -- Widths: symbols count one, wrappers, spacing and braces nothing.
  checkEq "extract/doc/width-symbols" (texWidth "a \\oplus b") 3
  checkEq "extract/doc/width-wrappers" (texWidth "\\mathrm{dbl}(x)") 6
  checkEq "extract/doc/width-spacing" (texWidth "f\\,x\\;y") 3
  checkEq "extract/doc/width-scripts" (texWidth "x_{1}^{2}") 3
  checkEq "extract/doc/width-given" (Doc.text "\\veryLongMacroName" 1).width 1
  -- Precedence: parentheses only where needed.
  let a := Doc.tex "a"
  let b := Doc.tex "b"
  let c := Doc.tex "c"
  let sum := infixDoc 65 "+" a b
  checkEq "extract/doc/no-parens-left-assoc" (infixDoc 65 "+" sum c).render "a + b + c"
  checkEq "extract/doc/parens-right" (infixDoc 65 "+" a sum).render "a + (a + b)"
  checkEq "extract/doc/parens-tighter" (infixDoc 70 "\\cdot" sum c).render "(a + b) \\cdot c"
  checkEq "extract/doc/no-parens-looser" (infixDoc 65 "+" (infixDoc 70 "\\cdot" a b) c).render
    "a \\cdot b + c"
  checkEq "extract/doc/width-counts-parens" (infixDoc 65 "+" a sum).width 7
  -- Line breaking: none when it fits; at the outermost breaks when not.
  let long := infixDoc 25 "\\implies" (infixDoc 65 "+" (.tex "aaaaaaaaaa") (.tex "bbbbbbbbbb"))
    (infixDoc 65 "+" (.tex "cccccccccc") (.tex "dddddddddd"))
  checkEq "extract/doc/fits-unbroken" (long.render 100) "aaaaaaaaaa + bbbbbbbbbb \\implies cccccccccc + dddddddddd"
  checkEq "extract/doc/breaks-outermost" (long.render 30)
    "aaaaaaaaaa + bbbbbbbbbb \\LeanBreak \\implies cccccccccc + dddddddddd"
  checkEq "extract/doc/breaks-deeper-when-needed" (long.render 15)
    "aaaaaaaaaa \\LeanBreak + bbbbbbbbbb \\LeanBreak \\implies cccccccccc \\LeanBreak + dddddddddd"
  -- Templates: the longest pattern variable wins, and unknown ones are errors.
  checkEq "extract/doc/template-prime" (splitTemplate "#k'" #["k"]).toOption
    (some #[.inr "k", .inl "'"])
  checkEq "extract/doc/template-longest" (splitTemplate "#ab+#a" #["a", "ab"]).toOption
    (some #[.inr "ab", .inl "+", .inr "a"])
  checkEq "extract/doc/template-unknown" (match splitTemplate "#x" #["y"] with
    | .error v => v | .ok _ => "") "x"
  -- Metavariables: subscripts, primes, long names, and latex_metavar.
  let mv : Array MetavarRule := #[{ name := `spec, tex := "L" }]
  checkEq "extract/doc/metavar-subscript" (Render.varTeX mv `x₁) "x_{1}"
  checkEq "extract/doc/metavar-digits" (Render.varTeX mv `h12) "h_{12}"
  checkEq "extract/doc/metavar-prime" (Render.varTeX mv `x') "x'"
  checkEq "extract/doc/metavar-long" (Render.varTeX mv `acc) "\\mathit{acc}"
  checkEq "extract/doc/metavar-renamed" (Render.varTeX mv `spec) "L"
  checkEq "extract/doc/metavar-whole-name-only" (Render.varTeX mv `spec₁) "\\mathit{spec}_{1}"
  let dec : Array MetavarRule := #[{ name := `idx, tex := "i", decorated := true }]
  checkEq "extract/doc/metavar-decorated" (Render.varTeX dec `idx₁') "i_{1}'"

end ExtractTest.DocTests
