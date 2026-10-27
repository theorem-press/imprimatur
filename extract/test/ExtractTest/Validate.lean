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
  { name := tex, sort, prec := Doc.maxPrec, syms := (tokenize tex).toList.map .tok }

/-- A reading: a leaf, or a node with children. -/
def l (n : String) : Reading := .node n []
/-- See `l`. -/
def n (name : String) (kids : List Reading) : Reading := .node name kids

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

/-- The one reading of `tex` as sort `s`, if it has exactly one. -/
def theReading (rules : Array NotationRule) (atoms : Array Prod) (tex s : String) : Option String :=
  match readBack (Grammar.of (rules.filterMap ofRule ++ builtins ++ atoms)) (tokenize tex) s with
  | (#[r], flags) => if flags.any then none else some r.text
  | _ => none

/-- All the validation tests. -/
def tests : TestM Unit := group "validate" do
  -- The one reading is compared with the reading the renderer expected
  -- (`Render.Expect`); `⁇` stands for a subterm it does not say how to read.
  checkEq "extract/validate/matches"
    (#[(n "app" [l "a", l "b"], n "app" [l "a", l "b"]),
      (n "app" [.any, l "b"], n "app" [n "f" [l "x", l "y"], l "b"]),
      (.any, n "anything" [l "at", l "all"]),
      (n "app" [.any, .any], n "app" [l "a", l "b"]),
      (n "app" [l "a", l "b"], n "app" [l "b", l "a"]),
      (n "app" [.any], n "app" [l "a", l "b"]),
      (n "app" [.any, l "c"], n "app" [l "a", l "b"])].map fun (e, g) => e.matches g)
    #[true, true, true, true, false, false, false]
  -- Readings print as the bundle records them.
  checkEq "extract/validate/text" (n "app" [n "f" [l "x", .any], l "b"]).text "app[f[x; ⁇]; b]"
  -- Left-associated application reads `e\; f\; e` as `(e f) e`. Had the
  -- renderer rendered `e (f e)` without its parentheses, the one reading
  -- would not be what it expected, and the check reports it.
  let r := theReading #[app 100] atoms "e\\; f\\; e" "Tm"
  checkEq "extract/validate/reading-left" r (some "app[app[e; f]; e]")
  check "extract/validate/misread-caught"
    (r.any fun r => r != (n "app" [l "e", n "app" [l "f", l "e"]]).text && r == (n "app" [n "app" [l "e", l "f"], l "e"]).text)
  -- Tokens: control words and symbols, characters; spaces and breaks dropped.
  checkEq "extract/validate/tokens" (tokenize "\\Gamma \\vdash e_{1}\\; x\\,y \\LeanBreak z")
    #["\\Gamma", "\\vdash", "e", "_", "{", "1", "}", "\\;", "x", "\\,", "y", "z"]
  checkEq "extract/validate/tokens-code" (tokenize "\\LeanMathCode{match x \\{ y \\}} = 1")
    #["\\LeanMathCode{match x \\{ y \\}}", "=", "1"]
  -- A rule's production: its holes at the precedence the emitter needs.
  let p := (ofRule (app 100 "none")).get!
  checkEq "extract/validate/production" (repr p.syms).pretty
    (repr [Sym.hole "Tm" 101, .tok "\\;", .hole "Tm" 101]).pretty
  let p := (ofRule (mk `subst #[(`x, "Nat"), (`u, "Tm"), (`e, "Tm")] "#e[#u/#x]" "Tm")).get!
  checkEq "extract/validate/production-atomic" (repr p.syms).pretty
    (repr [Sym.hole "Tm" Doc.maxPrec, .tok "[", .hole "Tm" 0, .tok "/", .hole "Nat" 0, .tok "]"]).pretty
  check "extract/validate/production-coercion"
    (ofRule (mk `Tm.var #[(`x, "Nat")] "#x" "Tm")).get!.coercion
  -- `latex_style lists := literal`: a list literal is a list, and a type of
  -- the form `[n]` (`Fin n`) is not read as one where a type is expected.
  let fin := mk `Fin #[(`n, "Nat")] "[#n]" "Sort"
  let lit (tex s : String) : Nat :=
    (count (Grammar.of (#[fin].filterMap ofRule ++ builtins (lists := true) ++ atoms))
      (tokenize tex) s).1
  checkEq "extract/validate/list-literal" (lit "[a,\\ b]" "List(Nat)") 1
  checkEq "extract/validate/list-or-type" (lit "[a]" "*") 2
  checkEq "extract/validate/type-not-list" (lit "[a]" "Sort*") 1
  -- `Sort*` (a universe that may be `Prop`) takes a type or a proposition,
  -- but not a value of a datatype.
  check "extract/validate/sort-star-type" (compat "Sort" "Sort*" && compat "Prop" "Sort*")
  check "extract/validate/sort-star-not-value" (!compat "List(Nat)" "Sort*")
  -- A constant applied, however the rules write it, is one reading.
  checkEq "extract/validate/app-constant"
    (mkReading "application" none #[l "Sum.inr", l "y"]).text "Sum.inr[y]"
  checkEq "extract/validate/app-curried-reading"
    (mkReading "application" none #[n "app" [l "f", l "a"], l "b"]).text "app[f; a; b]"
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
  -- Sorts with type arguments: an `Option(Label)` is not an `Option(Prop)`,
  -- and a type written without arguments stands for it with any.
  check "extract/validate/sort-args-differ" (!compat "Option(Label)" "Option(Prop)")
  check "extract/validate/sort-args-open" (compat "Option(Label)" "Option")
  -- Coercions are read with the sorts they make: `x : A` and `y : B` reach
  -- the sum `A ⊎ B` through `inl` and `inr`, so a rule whose two holes share
  -- a type reads `J(x, y)`.
  let jr : NotationRule := mk `J #[(`a, "?t"), (`b, "?t")] "J(#a, #b)" "Prop"
  let inl : NotationRule := mk `Sum.inl #[(`x, "?l")] "#x" "Sum(?l, ?r)"
  let inr : NotationRule := mk `Sum.inr #[(`y, "?r2")] "#y" "Sum(?l2, ?r2)"
  checkEq "extract/validate/coercion-sorts"
    (readings #[jr, inl, inr] #[atom "x" "'A", atom "y" "'B"] "J(x, y)" "Prop") 1
  checkEq "extract/validate/coercion-sorts-needed"
    (readings #[jr] #[atom "x" "'A", atom "y" "'B"] "J(x, y)" "Prop") 0
  -- Application is one reading however written: `f(a)(b)` is `f` applied
  -- to `a` and `b`.
  checkEq "extract/validate/application-curried"
    (count (Grammar.of (builtins true false ++ #[atom "f" "*", atom "a" "*", atom "b" "*"]))
      (tokenize "f(a)(b)") "*").1 1
  -- An application has the function's codomain for its sort (#90): with
  -- `\le` written alike at two types, `f(x) \le 1` has one reading when `f`
  -- is a function to one of them, and still reads when `f` is of a named
  -- type or of unknown sort, with a result of unknown sort.
  let leAt (t : String) : NotationRule :=
    { mk `LE.le #[(`a, t), (`b, t)] "#a \\le #b" "Prop" 50 "none" with
      pat := .constrained (.app `LE.le #[.var `a, .var `b]) #[(0, .app (.mkSimple t) #[])] }
  let typed (fs : String) : Nat :=
    (count (Grammar.of (#[leAt "NNReal", leAt "ENNReal"].filterMap ofRule ++ builtins true false ++
      #[atom "f" fs, atom "x" "Nat", atom "1" "*"])) (tokenize "f(x) \\le 1") "Prop").1
  checkEq "extract/validate/application-typed" (typed "(Nat → NNReal)") 1
  checkEq "extract/validate/application-named" (typed "Pred") 2
  checkEq "extract/validate/application-unknown" (typed "*") 2
  checkEq "extract/validate/application-ill-typed" (typed "(Bool → NNReal)") 0
  -- A synonym adds no production.
  check "extract/validate/synonym" (ofRule { mk `Nat.card #[(`a, "*")] "|#a|" "Nat" with synonym := true }).isNone
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
