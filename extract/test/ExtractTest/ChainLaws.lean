/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# The chain rule, against unbounded chains (docs/coercion-chains.md, B2)

The parser lets a chain of invisible coercions visit a sort once but for
growth, grow a sort at most the grammar's depth and one more times, and
cast no cast (`Imprimatur.Validate.Chain`). The claim phase B4 is to prove
is that this loses no reading against chains of any length, for Lean's
sorts, once readings deeper than the grammar's depth and one more are
dropped. These properties test the claim end to end, on random grammars of
the shapes the counterexamples used (growing, projecting, forgetful and
size-preserving coercions; wrappers with deep holes; a comparison with a
type variable) and random texts: the parser under the rule and under a
plain count of twelve coercions must return the same readings, with no
flag; and a looser depth cap must change nothing.
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

/-- The rule's readings against a reference parser's: the same, unless the
reference gave up, which says nothing; and the rule never gives up where
the reference does not. -/
def agree (ruled reference : Array Reading × Flags) (what : String) : Except String Unit := do
  expect (!ruled.2.any || reference.2.any) s!"the rule gives up where {what} does not"
  if reference.2.any then return ()
  expect (verdict ruled == verdict reference) s!"the rule reads {verdict ruled}, {what} {verdict reference}"

/-- All the properties. -/
def tests : TestM Unit := group "chain-laws" do
  forAll "extract/prop/chain-rule-complete"
      (do let ps ← genGrammar; let t ← genText 2; let s ← Gen.elem #["Prop", "*"]; return (ps, t, s))
      (fun (ps, t, s) => s!"{ps.map (·.name)} ⊢ {t} : {s}") fun (ps, t, s) =>
    let g := Grammar.of ps
    agree (readBack g t.toArray s) (readBack { g with count := some 12 } t.toArray s) "a count of twelve"
  forAll "extract/prop/depth-cap-complete"
      (do let ps ← genGrammar; let t ← genText 2; let s ← Gen.elem #["Prop", "*"]; return (ps, t, s))
      (fun (ps, t, s) => s!"{ps.map (·.name)} ⊢ {t} : {s}") fun (ps, t, s) =>
    let g := Grammar.of ps
    agree (readBack g t.toArray s) (readBack { g with depth := g.depth + 3 } t.toArray s) "a cap three deeper"

end ExtractTest.ChainLaws
