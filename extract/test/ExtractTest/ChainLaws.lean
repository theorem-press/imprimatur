/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# The chain rule, against unbounded chains (docs/coercion-chains.md, route A)

The parser lets a chain of invisible coercions apply a coercion only if no
coercion above it has the same argument sort, and cast no cast
(`Imprimatur.Validate.Chain`). That loses readings on purpose: `g(x)` is
not read as `g(some(some(some x)))`. What makes it sound is that the
renderer obeys the same rule, showing any coercion it does not allow, so a
rendering never needs a chain the parser does not read. These properties
test both halves end to end, on random grammars of the shapes the
counterexamples used (growing, projecting, forgetful and size-preserving
coercions; wrappers with deep holes; a comparison with a type variable):

- the counterexample's two terms print apart, and each reads as itself;
- a text printed from a random term, hiding a coercion only where the rule
  allows it and showing it elsewhere, is read as that term whenever the
  reading the printer means is well sorted, premise by premise.
-/

open Testkit Imprimatur Imprimatur.Validate

namespace ExtractTest.ChainLaws

/-- An atom of a sort. -/
def atom (n s : String) : Prod := { name := n, sort := s, prec := 1024, syms := [.tok n] }

/-- An invisible coercion from hole sort `h` to sort `t`. -/
def coe (n t h : String) : Prod := { name := n, sort := t, prec := 1024, syms := [.hole h 0], coercion := true }

/-- A wrapper `tok ( _ )` of sort `Prop`, around a hole of sort `h`. -/
def wrap (n tok h : String) : Prod :=
  { name := n, sort := "Prop", prec := 1024, syms := [.tok tok, .tok "(", .hole h 0, .tok ")"] }

/-- The sorts atoms and holes are drawn from, towers and all. -/
def palette : Array String :=
  #["Nat", "Char", "Bool", "Prop", "*", "?α", "List(Nat)", "Option(Nat)", "Option(Option(Nat))",
    "Option(Option(Option(Nat)))", "Box(Nat)", "Wrap(Nat)", "Box(Wrap(Nat))", "Wrap(Box(Nat))",
    "Array(Nat)", "List(Option(Nat))", "Option(List(Nat))"]

/-- The coercions a grammar may have. -/
def coercions : Array Prod := #[
  coe "Option.some" "Option(?α)" "?α", coe "box" "Box(?α)" "?α", coe "wrap" "Wrap(?α)" "?α",
  coe "unbox" "?α" "Box(?α)", coe "unwrap" "?α" "Wrap(?α)",
  coe "Nat.cast" "*" "Nat", coe "Char.cast" "*" "Char", coe "toBool" "Bool" "Nat",
  coe "toArray" "Array(?α)" "List(?α)", coe "toList" "List(?α)" "Array(?α)"]

/-- A random grammar: four atoms, some coercions, three wrappers (two
sharing a token, so that a pun is possible) and a comparison. -/
def genGrammar : Gen (Array Prod) := do
  let mut ps : Array Prod := #[]
  for n in ["x", "y", "z", "w"] do
    ps := ps.push (atom n (← Gen.elem palette))
  for c in coercions do
    if ← Gen.bool then ps := ps.push c
  ps := ps.push (wrap "f" "f" (← Gen.elem palette))
  ps := ps.push (wrap "g" "g" (← Gen.elem palette))
  ps := ps.push (wrap "h" "g" (← Gen.elem palette))
  ps := ps.push { name := "Eq", sort := "Prop", prec := 50, syms := [.hole "?α" 51, .tok "=", .hole "?α" 51] }
  return ps

/-- A random text the grammar might read: an atom, a wrapper around one, or
a comparison, nested twice at most. -/
partial def genText (depth : Nat) : Gen (List String) := do
  let leaf : Gen (List String) := do return [← Gen.elem #["x", "y", "z", "w"]]
  if depth == 0 then leaf else
  Gen.frequency [
    (2, leaf),
    (2, do return [← Gen.elem #["f", "g"], "("] ++ (← genText (depth - 1)) ++ [")"]),
    (1, do return (← genText (depth - 1)) ++ ["="] ++ (← genText (depth - 1)))]

/-- The readings' texts, sorted, as one string to compare. -/
def verdict (res : Array Reading × Flags) : String :=
  s!"{(res.1.map (·.text)).qsort (· < ·)}"

/-- A term of a random grammar: an atom, a coercion of one, a wrapper
around one (`n` the production, `tok` its token), or a comparison. -/
inductive Term where
  /-- an atom -/
  | leaf (n : String)
  /-- a coercion of a term -/
  | coe (c : Prod) (t : Term)
  /-- a wrapper around a term -/
  | wrap (n tok : String) (t : Term)
  /-- a comparison -/
  | eq (a b : Term)
  deriving Inhabited

/-- The production that shows coercion `c`, as the renderer shows a constant
applied: `c! ( _ )`. -/
def shown (c : Prod) : Option Prod :=
  match c.syms with
  | [.hole h _] =>
    let n := c.name ++ "!"
    some { name := n, sort := c.sort, prec := 1024, syms := [.tok n, .tok "(", .hole h 0, .tok ")"] }
  | _ => none

/-- The hole sort of a coercion. -/
def holeOf (c : Prod) : String := match c.syms with | [.hole h _] => h | _ => "*"

/-- Print a term as the renderer does, below the chain `ch`: a coercion is
hidden where the rule allows it, and shown elsewhere; any other form starts
a new chain. With the expected reading. -/
def print (g : Grammar) : Chain → Term → List String × Reading
  | _, .leaf n => ([n], .node n [])
  | ch, .coe c t =>
    if ch.allows algebra c (holeOf c) then print g (ch.push algebra c (holeOf c)) t
    else
      let (ts, r) := print g g.chain0 t
      ([c.name ++ "!", "("] ++ ts ++ [")"], .node (c.name ++ "!") [r])
  | _, .wrap n tok t =>
    let (ts, r) := print g g.chain0 t
    ([tok, "("] ++ ts ++ [")"], .node n [r])
  | _, .eq a b =>
    let paren (t : Term) (ts : List String) := match t with | .eq .. => ["("] ++ ts ++ [")"] | _ => ts
    let (as, ra) := print g g.chain0 a
    let (bs, rb) := print g g.chain0 b
    (paren a as ++ ["="] ++ paren b bs, .node "Eq" [ra, rb])

/-- The sort of the term as `print` writes it, read as an expression of
sort `s` below the chain `ch`, if every step of that reading is well
sorted: the derivation the renderer means, checked premise by premise as in
`SpliceModel.Reads`. -/
def sortIn (ps : Array Prod) (s : String) : Chain → Term → Option String
  | _, .leaf n => do
    let p ← ps.find? (·.name == n)
    let σ := algebra.expected #[] p.sort
    if algebra.compat p.sort s && algebra.compat σ s then some σ else none
  | ch, .coe c t => do
    let h := holeOf c
    let hidden := ch.allows algebra c h
    let σ ← sortIn ps (algebra.expected #[] h) (if hidden then ch.push algebra c h else (Grammar.of ps).chain0) t
    let res := algebra.expected (algebra.bind #[] h σ) c.sort
    if algebra.compat c.sort s && algebra.compat res s then some res else none
  | _, .wrap n _ t => do
    let p ← ps.find? (·.name == n)
    let h ← match p.syms with | [_, _, .hole h _, _] => some h | _ => none
    let _ ← sortIn ps (algebra.expected #[] h) (Grammar.of ps).chain0 t
    if algebra.compat "Prop" s then some "Prop" else none
  | _, .eq a b => do
    let σa ← sortIn ps (algebra.expected #[] "?α") (Grammar.of ps).chain0 a
    let _ ← sortIn ps (algebra.expected (algebra.bind #[] "?α" σa) "?α") (Grammar.of ps).chain0 b
    if algebra.compat "Prop" s then some "Prop" else none

/-- A random term over a grammar's atoms, coercions and wrappers, with
towers of coercions three high at most. -/
partial def genTerm (atoms : Array String) (coes : Array Prod) (wraps : Array (String × String)) :
    Nat → Gen Term
  | depth => do
    let leaf : Gen Term := do return .leaf (← Gen.elem atoms)
    let rec tower : Nat → Gen Term
      | 0 => leaf
      | n + 1 => do
        if coes.isEmpty || (← Gen.chance 1 3) then leaf
        else return .coe (← Gen.elem coes) (← tower n)
    if depth == 0 then tower 3 else
    Gen.frequency [
      (2, tower 3),
      (2, do
        let (n, tok) ← Gen.elem wraps
        let t ← genTerm atoms coes wraps (depth - 1)
        if coes.isEmpty || (← Gen.bool) then return .wrap n tok t
        else return .wrap n tok (.coe (← Gen.elem coes) t)),
      (1, do return .eq (← genTerm atoms coes wraps (depth - 1)) (← genTerm atoms coes wraps (depth - 1)))]

/-- The counterexample of docs/coercion-chains.md: with `Option.some`
hidden, `g(some(some(some x)))` would print as `g(x)`, which reads as
`h[x]`. The renderer shows the `some`s the rule does not allow, so the two
terms print apart, and each reads as itself. -/
def pun : Except String Unit := do
  let ps : Array Prod := #[atom "x" "Nat", coe "Option.some" "Option(?α)" "?α",
    wrap "g" "g" "Option(Option(Option(Nat)))", wrap "h" "g" "Nat"]
  let ps := ps ++ (ps.filter (·.coercion)).filterMap shown
  let g := Grammar.of ps
  let c := coe "Option.some" "Option(?α)" "?α"
  let pun := Term.wrap "g" "g" (.coe c (.coe c (.coe c (.leaf "x"))))
  let plain := Term.wrap "h" "g" (.leaf "x")
  let (ts₁, r₁) := print g g.chain0 pun
  let (ts₂, r₂) := print g g.chain0 plain
  expect (ts₁ != ts₂) s!"both print as {ts₁}"
  expect ((sortIn ps "Prop" g.chain0 pun).isSome && (sortIn ps "Prop" g.chain0 plain).isSome) "a term is ill-sorted"
  for (ts, r) in [(ts₁, r₁), (ts₂, r₂)] do
    let res := readBack g ts.toArray "Prop"
    expect (!res.2.any && verdict res == s!"{#[r.text]}") s!"{ts} reads as {verdict res}, not {r.text}"

/-- All the properties. -/
def tests : TestM Unit := group "chain-laws" do
  match pun with
  | .ok () => check "extract/chain/pun-printed-apart" true
  | .error e => fail "extract/chain/pun-printed-apart" e
  -- About one random term in seven is well sorted, and checking one costs
  -- milliseconds, so this runs on ten times the cases.
  let cfg ← PropConfig.fromEnv
  forAllWith { cfg with cases := 10 * cfg.cases } "extract/prop/chain-rule-reads-renderings"
      (do
        let ps ← genGrammar
        let coes := ps.filter (·.coercion)
        let atoms := (ps.filter fun p => p.syms.length == 1 && !p.coercion).map (·.name)
        let t ← genTerm atoms coes #[("f", "f"), ("g", "g"), ("h", "g")] 2
        let s ← Gen.elem #["Prop", "*"]
        return (ps ++ coes.filterMap shown, t, s))
      (fun (ps, t, s) =>
        let (ts, r) := print (Grammar.of ps) (Grammar.of ps).chain0 t
        s!"{ps.map (·.name)} ⊢ {ts} as {r.text} : {s}") fun (ps, t, s) => do
    let g := Grammar.of ps
    let (ts, r) := print g g.chain0 t
    let ruled := readBack g ts.toArray s
    -- An ill-sorted term is read by no parser, and a flag says nothing.
    if (sortIn ps s g.chain0 t).isNone || ruled.2.any then return ()
    expect (ruled.1.any (·.text == r.text)) s!"the rule does not read {r.text}; it reads {verdict ruled}"

end ExtractTest.ChainLaws
