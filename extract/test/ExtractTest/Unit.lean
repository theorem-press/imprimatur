/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Unit tests of the extractor
-/

open Testkit Imprimatur Lean

namespace ExtractTest.Unit

/-- TeX escaping and docstrings. -/
def testTeX : TestM Unit := group "tex" do
  checkEq "extract/tex/escape" (TeX.escape "a_b#c%d&e{f}g$h~i^j\\k")
    "a\\_b\\#c\\%d\\&e\\{f\\}g\\$h\\textasciitilde{}i\\textasciicircum{}j\\textbackslash{}k"
  checkEq "extract/tex/unicode-kept" (TeX.escape "∀ α₁ → ℕ") "∀ α₁ → ℕ"
  checkEq "extract/markdown/code" (TeX.markdown "use `x_1` here") "use \\LeanCodeInline{x\\_1} here"
  checkEq "extract/markdown/bold-emph" (TeX.markdown "**b** and *e*") "\\textbf{b} and \\emph{e}"
  checkEq "extract/markdown/maths" (TeX.markdown "the maths $x_1^{2}$") "the maths $x_1^{2}$"
  checkEq "extract/markdown/unbalanced-maths" (TeX.markdown "a $x}$ b") "a \\$x\\}\\$ b"
  checkEq "extract/markdown/percent-in-maths" (TeX.markdown "$50%$") "\\$50\\%\\$"
  checkEq "extract/markdown/unclosed" (TeX.markdown "a `b and *c") "a `b and *c"
  check "extract/tex/balanced" (TeX.balanced "{a\\}b}" && !TeX.balanced "}{" && !TeX.balanced "{")

/-- Tokens of printed Lean. -/
def testTokens : TestM Unit := group "tokens" do
  let toks := Views.tokenize "  ∀ (x : Nat.succ 0), «weird name».y = \"s\\\"t\" ∧ h.1"
  checkEq "extract/tokens/line" toks #[.space 2, .sym "∀", .space 1, .sym "(", .ident "x", .space 1,
    .sym ":", .space 1, .ident "Nat.succ", .space 1, .num "0", .sym ")", .sym ",", .space 1,
    .ident "«weird name»", .sym ".", .ident "y", .space 1, .sym "=", .space 1, .str "\"s\\\"t\"",
    .space 1, .sym "∧", .space 1, .ident "h", .sym ".", .num "1"]
  checkEq "extract/tokens/subscripts-and-primes" (Views.tokenize "h₁' x!")
    #[.ident "h₁'", .space 1, .ident "x!"]
  -- What a variable keeps of its name under `latex_style categories := strict`.
  checkEq "extract/names/decorations" (#[`P, `D₁, `a', `x12', `σ₂₃].map Render.nameDecorations)
    #["", "_{1}", "'", "_{12}'", "_{23}"]
  checkEq "extract/names/strip" (Views.stripName #[`A, `A.B] `A.B.c) `c
  checkEq "extract/names/strip-not-self" (Views.stripName #[`A] `A) `A
  checkEq "extract/names/from-key" (toName "MyPaper.Results.theorem1_main") `MyPaper.Results.theorem1_main

/-- The JSON writer and requests. -/
def testJson : TestM Unit := group "json" do
  let j := Lean.Json.mkObj [("b", 1), ("a", .arr #[.str "x\"y", .bool true]), ("c", Lean.Json.mkObj [])]
  checkEq "extract/json/sorted" (renderJson j) "{\n  \"a\": [\"x\\\"y\", true],\n  \"b\": 1,\n  \"c\": {}\n}"
  checkEq "extract/json/macros" (macrosOf "\\LeanConst{a} \\LeanBound{b} \\LeanConst{c} \\\\")
    #["\\LeanBound", "\\LeanConst"]
  match parseRequests "{\"schema\": \"imprimatur-requests/1\", \"config\": {\"imports\": [\"A.B\"],
      \"strip_namespaces\": [\"A\"]}, \"requests\": {\"z\": {\"views\": [\"lean\"]}, \"a\": {\"views\": []}}}" with
  | .ok (s, rs) =>
    checkEq "extract/requests/imports" s.imports #[`A.B]
    checkEq "extract/requests/sorted" (rs.map (·.key)) #["a", "z"]
  | .error e => fail "extract/requests/imports" e
  checkError "extract/requests/schema" (parseRequests "{\"schema\": \"x\", \"requests\": {}}") "schema"

/-- All unit tests. -/
def tests : TestM Unit := do
  testTeX
  testTokens
  testJson

end ExtractTest.Unit
