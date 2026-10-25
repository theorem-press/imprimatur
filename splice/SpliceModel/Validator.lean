/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBackComplete
import SpliceModel.Views

/-!
# The validator's world

`Anatomy.Sound` (`SpliceModel.Views`) assumes that a rendering which reads
back reads back formula by formula. Here that assumption is discharged for
the world as the validator sees it: a rendering reads back as a statement
when the validator accepts each formula the notation prints of it, and the
validator accepts a formula when the parser returns one reading, with no
flag set, that matches the reading the renderer expects. By
`pollack` (`SpliceModel.ReadBackComplete`), such a formula then has, in the
grammar, no reading but the expected one: `Validated.sound`. Theorem 1's
`prose_true` and `rules_true` then say of a document that checks clean
(`document_pollack`, `document_pollack_rules`) that each formula of each
block reads, in the notation's grammar, only as the part it was printed
from.
-/

namespace SpliceModel

open Imprimatur.Validate

/-- What the validator knows of a world's parts: a grammar, an algebra of
sorts, and for each part its sort and the reading the renderer expects. -/
structure Validator (Part : Type) where
  /-- the sorts -/
  A : SortAlgebra
  /-- the notation's grammar -/
  G : Grammar
  /-- the sort a part is read at -/
  sort : Part → String
  /-- the reading the renderer expects of a part -/
  expect : Part → Reading

namespace Validator

variable {Part : Type} (V : Validator Part)

/-- The tokens of a formula. -/
def tokens (t : List Char) : Array String := tokenize (String.ofList t)

/-- A formula reads back as a part: every reading of it in the grammar, as
an expression of the part's sort, matches the expected one. -/
def ReadsPart (t : List Char) (q : Part) : Prop :=
  ∀ rd σ, Exp V.A V.G (tokens t) (V.sort q) 0 none [] 0 (tokens t).size rd σ → Matches (V.expect q) rd

/-- The validator accepts a formula as a part: the parser returns one
reading, with no flag set, and it matches the expected one. This is what
`Render` checks of each formula it emits. -/
def Accepts (t : List Char) (q : Part) : Prop :=
  ∃ rd, (readBackWith V.A V.G (tokens t) (V.sort q)).1 = #[rd] ∧
    (readBackWith V.A V.G (tokens t) (V.sort q)).2.any = false ∧ (V.expect q).matches rd = true

/-- **A formula the validator accepts reads back as its part.** -/
theorem accepts_readsPart {t : List Char} {q : Part} (h : V.Accepts t q) : V.ReadsPart t q := by
  obtain ⟨rd, h1, h2, h3⟩ := h
  exact (pollack _ _ _ h1 h2 h3).2

end Validator

/-- A world with the anatomy of its statements and a validator for the
parts: what the extractor is, with `base.Reads` set aside for the
validator's. -/
structure Validated where
  /-- the world, but for when a rendering reads back -/
  base : World
  /-- a part of a statement, as the notation shows it -/
  Part : Type
  /-- a part printed as a formula, by the notation -/
  print : Part → List Char
  /-- what the prose view says of a statement -/
  gather : base.Stmt → Option (Imprimatur.Layout.Prose Part)
  /-- what the rules view says of an inductive predicate -/
  ctors : base.Stmt → Option (List (Imprimatur.Layout.Rule Part))
  /-- the validator -/
  V : Validator Part

namespace Validated

variable (X : Validated)

/-- The validator accepts every formula printed of a statement, in the
prose view and in the rules view. -/
def AcceptsAll (S : X.base.Stmt) : Prop :=
  (∀ u, X.gather S = some u → ∀ q ∈ u.parts, X.V.Accepts (X.print q) q) ∧
  (∀ qs, X.ctors S = some qs → ∀ q ∈ (qs.map Imprimatur.Layout.Rule.parts).flatten, X.V.Accepts (X.print q) q)

/-- The world as the validator sees it: a rendering reads back as a
statement when the validator accepts every formula printed of it. -/
def world : World := { X.base with Reads := fun _ S => X.AcceptsAll S }

/-- The anatomy, reading a formula as a part when every reading of it in
the grammar is the expected one. -/
def anatomy : Anatomy X.world :=
  { Part := X.Part, ReadsPart := X.V.ReadsPart, print := X.print, gather := X.gather, ctors := X.ctors }

/-- **The validator's anatomy is sound**, given that the world prints as the
anatomy says: the two assumptions about reading back are theorems. -/
theorem sound (hplain : ∀ S u, X.gather S = some u → (u.map X.print).Plain)
    (hprose : ∀ S r, X.world.render "prose" S = some r → X.anatomy.PrintsProse S r)
    (hrulesPlain : ∀ S qs, X.ctors S = some qs → ∀ q ∈ qs, (q.map X.print).Plain)
    (hrules : ∀ S r, X.world.render "rules" S = some r → X.anatomy.PrintsRules S r) : X.anatomy.Sound where
  plain := hplain
  prose := hprose
  formulas := fun _ _ _ hR u hu q hq => X.V.accepts_readsPart (hR.1 u hu q hq)
  rulesPlain := hrulesPlain
  rules := hrules
  ruleFormulas := fun _ _ _ hR qs hqs q hq => X.V.accepts_readsPart (hR.2 qs hqs q hq)

section
variable {b : Bundle} {d : Doc}

/-- **Pollack-consistency of a document, prose.** If the bundle is true of
the world as the validator sees it, and `check` reports nothing, a prose
block names a statement Lean proved, is its rendering, and its sentence
comes apart into the formulas printed from the statement's parts, each of
which reads, in the notation's grammar, only as the reading expected of its
part. -/
theorem document_pollack (hplain : ∀ S u, X.gather S = some u → (u.map X.print).Plain)
    (hprose : ∀ S r, X.world.render "prose" S = some r → X.anatomy.PrintsProse S r)
    (hrulesPlain : ∀ S qs, X.ctors S = some qs → ∀ q ∈ qs, (q.map X.print).Plain)
    (hrules : ∀ S r, X.world.render "rules" S = some r → X.anatomy.PrintsRules S r)
    (hb : b.True X.world id) (hc : check b d = []) {k : Imprimatur.Key} {r : Body} (hp : Piece.block k "prose" r ∈ d) :
    ∃ S, X.world.stmt k = some S ∧ X.world.trusted k = true ∧ X.world.render "prose" S = some r ∧
      X.anatomy.Prose r S :=
  prose_true (X.sound hplain hprose hrulesPlain hrules) hb hc hp

/-- **Pollack-consistency of a document, rules.** The same of a rules
block: each rule's formulas read only as the constructor's parts. -/
theorem document_pollack_rules (hplain : ∀ S u, X.gather S = some u → (u.map X.print).Plain)
    (hprose : ∀ S r, X.world.render "prose" S = some r → X.anatomy.PrintsProse S r)
    (hrulesPlain : ∀ S qs, X.ctors S = some qs → ∀ q ∈ qs, (q.map X.print).Plain)
    (hrules : ∀ S r, X.world.render "rules" S = some r → X.anatomy.PrintsRules S r)
    (hb : b.True X.world id) (hc : check b d = []) {k : Imprimatur.Key} {r : Body} (hp : Piece.block k "rules" r ∈ d) :
    ∃ S, X.world.stmt k = some S ∧ X.world.trusted k = true ∧ X.world.render "rules" S = some r ∧
      X.anatomy.Rules r S :=
  rules_true (X.sound hplain hprose hrulesPlain hrules) hb hc hp

end

end Validated

end SpliceModel
