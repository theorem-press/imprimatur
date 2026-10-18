/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Unit tests of translation validation (DESIGN §18.4)

Tokens, the productions of notation rules, and counting the readings of a
formula in small grammars.
-/

open Testkit Imprimatur Imprimatur.Validate Lean

namespace ExtractTest.ValidateTests

/-- A rule over constant `c`'s variables, with sorts. -/
def mk (c : Name) (vars : Array (Name × String)) (template : String) (sort : String)
    (prec : Nat := 1024) (assoc : String := "left") (flatten : Bool := false) : NotationRule :=
  { pat := .app c (vars.map (.var ·.1)), template, prec, assoc, flatten, sort, holeSorts := vars }

/-- An atom of a sort. -/
def atom (tex sort : String) : Prod :=
  { name := tex, sort, prec := Doc.maxPrec, syms := (tokenize tex).map .tok }

/-- The readings of `tex` as sort `s`, in the grammar of `rules` and `atoms`. -/
def readings (rules : Array NotationRule) (atoms : Array Prod) (tex s : String) : Nat :=
  (count (Grammar.of (rules.filterMap ofRule ++ builtins ++ atoms)) (tokenize tex) s).1

/-- Application and swapping, both written by juxtaposition. -/
def app (prec : Nat) (assoc := "left") : NotationRule :=
  mk `app #[(`a, "Tm"), (`b, "Tm")] "#a\\; #b" "Tm" prec assoc
/-- See `app`. -/
def swap (prec : Nat) (assoc := "left") : NotationRule :=
  mk `swap #[(`x, "Nat"), (`y, "Nat"), (`e, "Tm")] "(#x\\ #y) \\cdot #e" "Tm" prec assoc

/-- The atoms of the examples. -/
def atoms : Array Prod :=
  #[atom "a" "Nat", atom "b" "Nat", atom "e" "Tm", atom "f" "Tm", atom "P" "Prop", atom "Q" "Prop"]

/-- All the validation tests. -/
def tests : TestM Unit := group "validate" do
  -- Tokens: control words and symbols, characters; spaces and breaks dropped.
  checkEq "extract/validate/tokens" (tokenize "\\Gamma \\vdash e_{1}\\; x\\,y \\LeanBreak z")
    #["\\Gamma", "\\vdash", "e", "_", "{", "1", "}", "\\;", "x", "\\,", "y", "z"]
  checkEq "extract/validate/tokens-code" (tokenize "\\LeanMathCode{match x \\{ y \\}} = 1")
    #["\\LeanMathCode{match x \\{ y \\}}", "=", "1"]
  -- A rule's production: its holes at the precedence the emitter needs.
  let p := (ofRule (app 100 "none")).get!
  checkEq "extract/validate/production" (repr p.syms).pretty
    (repr #[Sym.hole "Tm" 101, .tok "\\;", .hole "Tm" 101]).pretty
  let p := (ofRule (mk `subst #[(`x, "Nat"), (`u, "Tm"), (`e, "Tm")] "#e[#u/#x]" "Tm")).get!
  checkEq "extract/validate/production-atomic" (repr p.syms).pretty
    (repr #[Sym.hole "Tm" 0, .tok "[", .hole "Tm" 0, .tok "/", .hole "Nat" 0, .tok "]"]).pretty
  check "extract/validate/production-coercion"
    (ofRule (mk `Tm.var #[(`x, "Nat")] "#x" "Tm")).get!.coercion
  -- Swapping next to application: ambiguous unless precedences separate them.
  checkEq "extract/validate/ambiguous" (readings #[app 1024, swap 1024] atoms "(a\\ b) \\cdot e\\; f" "Tm") 2
  -- With them, the formula needs parentheses, and has one reading with them.
  checkEq "extract/validate/no-reading-without-parens"
    (readings #[app 100 "none", swap 100 "none"] atoms "(a\\ b) \\cdot e\\; f" "Tm") 0
  checkEq "extract/validate/one-reading-with-parens"
    (readings #[app 100 "none", swap 100 "none"] atoms "((a\\ b) \\cdot e)\\; f" "Tm") 1
  -- Associativity: a left-associative chain reads one way.
  checkEq "extract/validate/assoc-left" (readings #[app 100] atoms "e\\; f\\; e" "Tm") 1
  checkEq "extract/validate/assoc-none" (readings #[app 100 "none"] atoms "e\\; f\\; e" "Tm") 0
  -- Sorts: a hole reads only expressions of its sort.
  checkEq "extract/validate/sorts" (readings #[swap 100] atoms "(e\\ b) \\cdot e" "Tm") 0
  -- Coercions are invisible: `x` read as a term through `Tm.var` is one reading.
  let var := mk `Tm.var #[(`x, "Nat")] "#x" "Tm"
  checkEq "extract/validate/coercion-one-reading"
    (readings #[var, app 100] atoms "a\\; e" "Tm") 1
  -- A flattened chain reads back however long it is.
  let comp := mk `comp #[(`a, "Tm"), (`b, "Tm")] "#a \\circ #b" "Tm" 90 (flatten := true)
  checkEq "extract/validate/flatten" (readings #[comp] atoms "e \\circ f \\circ e" "Tm") 1
  -- Built-in forms: implication, ∀, and the emitter's parentheses.
  checkEq "extract/validate/builtin-implies" (readings #[] atoms "P \\implies Q \\implies P" "Prop") 1
  checkEq "extract/validate/builtin-forall"
    (readings #[] (atoms ++ #[{ atom "x" "*" with isVar := true }, atom "\\mathrm{Prop}" "Sort"])
      "\\forall x : \\mathrm{Prop},\\ P" "Prop") 1
  -- Type variables: the holes of `=` share a sort, so `a = b = c` has no
  -- reading (it would compare a proposition with a label); with holes of
  -- unknown sort it would have two.
  let eqv (holes : String) : NotationRule :=
    mk `Eq #[(`x, holes), (`y, holes)] "#x = #y" "Prop"
  let labels := #[atom "a" "L", atom "b" "L", atom "c" "L"]
  checkEq "extract/validate/tyvar-ill-sorted" (readings #[eqv "?α"] labels "a = b = c" "Prop") 0
  checkEq "extract/validate/tyvar-unknown" (readings #[eqv "*"] labels "a = b = c" "Prop") 2
  checkEq "extract/validate/tyvar-binds" (readings #[eqv "?α"] labels "a = b" "Prop") 1
  -- Function sorts are compared part by part, type variables included.
  check "extract/validate/sort-arrow" (compat "(?α → ENNReal)" "('x → ENNReal)")
  check "extract/validate/sort-arrow-differs" (!compat "(Nat → ENNReal)" "(Nat → Real)")
  -- What the grammar does not cover is not validated.
  checkEq "extract/validate/unmodelled" (readings #[] atoms "\\frac{e}{f}" "Tm") 0

/-- A function with two arguments, for the warning below. -/
def pick (a _b : Nat) : Nat := a

/--
warning: the template does not show #b, so expressions that differ only in b render alike; show it, or say what it must be with `when b := …` or `hide b := …`
-/
#guard_msgs in
latex_notation pick a b => "#a"

end ExtractTest.ValidateTests
