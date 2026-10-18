/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Notation

/-!
# Notation packs

Rules shipped with imprimatur (DESIGN §7.5), selected with `notation_packs`
in `imprimatur.toml`. They name constants rather than elaborate them, so
imprimatur needs no library to define them: a rule whose constant isn't in
the environment just never matches. Every rule is used by the `Notation`
fixture's golden bundle.

| Pack | Covers |
|---|---|
| `core` | equality, arithmetic, order relations, numerals, `Nat.succ`, composition, pairs, `ℕ`, `ℤ`, Booleans, and coercions, which are not shown |
| `logic` | `∧`, `∨`, `¬`, `↔`, `True`, `False` (`∀`, `∃` and `→` are built in) |
| `sets` | `∈`, `⊆`, `⊂`, `∪`, `∩`, `\`, `∅`, singletons |
| `order` | `max`, `min` |

Precedences follow Lean's: 50 for relations, 65 for `+`, 70 for `*`, 75 for
`^`, 35 for `∧`, 30 for `∨`, 20 for `↔`.
-/

namespace Imprimatur.Packs

open Lean

/-- A rule over a constant's explicit arguments, named `#a`, `#b`, … in order.
Packs are not elaborated, so the sorts the validator reads them at
(DESIGN §18.3) are given: what the rule renders, and its arguments. -/
def rule (pack : String) (head : Name) (arity : Nat) (template : String)
    (prec : Nat := 1024) (assoc : String := "left") (breakBefore : Bool := false)
    (sort : String := "*") (holes : String := "*") : NotationRule :=
  let vars := #[`a, `b, `c, `d].extract 0 arity
  { pat := .app head (vars.map .var), template, prec, assoc, breakBefore,
    origin := s!"pack {pack}", sort, holeSorts := vars.map (·, holes) }

/-- The `core` pack. -/
def core : Array NotationRule := #[
  rule "core" ``Eq 2 "#a = #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``Ne 2 "#a \\ne #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``HAdd.hAdd 2 "#a + #b" 65,
  rule "core" ``HSub.hSub 2 "#a - #b" 65,
  rule "core" ``HMul.hMul 2 "#a \\cdot #b" 70,
  rule "core" ``HDiv.hDiv 2 "#a / #b" 70,
  rule "core" ``HMod.hMod 2 "#a \\bmod #b" 70,
  rule "core" ``HPow.hPow 2 "#a^{#b}" 75 "right",
  rule "core" ``Neg.neg 1 "-#a" 75,
  rule "core" ``LT.lt 2 "#a < #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``LE.le 2 "#a \\le #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``GT.gt 2 "#a > #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``GE.ge 2 "#a \\ge #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``OfNat.ofNat 1 "#a" (holes := "Nat"),
  -- `n + 1` is `Nat.succ n` by definition, and Lean writes it so.
  { rule "core" ``Nat.succ 1 "#a + 1" 65 (sort := "Nat") (holes := "Nat") with synonym := true },
  rule "core" ``Function.comp 2 "#a \\circ #b" 90,
  rule "core" ``Prod.mk 2 "(#a, #b)",
  rule "core" ``Nat 0 "\\mathbb{N}" (sort := "Sort"),
  rule "core" ``Int 0 "\\mathbb{Z}" (sort := "Sort"),
  rule "core" ``Nat.cast 1 "#a" (holes := "Nat"),
  rule "core" ``Int.cast 1 "#a" (holes := "Int"),
  rule "core" ``Subtype.val 1 "#a" (holes := "Subtype"),
  rule "core" ``Bool.true 0 "\\mathrm{true}",
  rule "core" ``Bool.false 0 "\\mathrm{false}"]

/-- The `logic` pack. -/
def logic : Array NotationRule := #[
  rule "logic" ``And 2 "#a \\wedge #b" 35 "right" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Or 2 "#a \\vee #b" 30 "right" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Not 1 "\\neg #a" 40 (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Iff 2 "#a \\iff #b" 20 "none" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``True 0 "\\top" (sort := "Prop"),
  rule "logic" ``False 0 "\\bot" (sort := "Prop")]

/-- The `sets` pack. `Membership.mem` takes the collection first. -/
def sets : Array NotationRule := #[
  { rule "sets" ``Membership.mem 2 "#b \\in #a" 50 "none" (sort := "Prop") with },
  rule "sets" ``HasSubset.Subset 2 "#a \\subseteq #b" 50 "none" (sort := "Prop") (holes := "?α"),
  rule "sets" ``HasSSubset.SSubset 2 "#a \\subset #b" 50 "none" (sort := "Prop") (holes := "?α"),
  rule "sets" ``Union.union 2 "#a \\cup #b" 65 (sort := "?α") (holes := "?α"),
  rule "sets" ``Inter.inter 2 "#a \\cap #b" 70 (sort := "?α") (holes := "?α"),
  rule "sets" ``SDiff.sdiff 2 "#a \\setminus #b" 70 (sort := "?α") (holes := "?α"),
  rule "sets" ``EmptyCollection.emptyCollection 0 "\\emptyset",
  rule "sets" ``Singleton.singleton 1 "\\{#a\\}"]

/-- The `order` pack. -/
def order : Array NotationRule := #[
  rule "order" ``Max.max 2 "\\max(#a, #b)" (sort := "?α") (holes := "?α"),
  rule "order" ``Min.min 2 "\\min(#a, #b)" (sort := "?α") (holes := "?α")]

/-- The packs by name. -/
def all : List (String × Array NotationRule) :=
  [("core", core), ("logic", logic), ("sets", sets), ("order", order)]

/-- The rules of the named packs, in the order given. -/
def select (names : Array String) : Array NotationRule :=
  names.foldl (fun acc n => acc ++ ((all.find? (·.1 == n)).map (·.2)).getD #[]) #[]

end Imprimatur.Packs
