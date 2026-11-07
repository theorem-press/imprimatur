/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBackComplete
import SpliceModel.Views

/-!
# The development, the notation, and the world they present

What the extractor reads is two things, written by different hands: the
`Development`, the Lean the paper is about, and the `Notation`, the module
its authors write to say how a part of a statement is printed and read. The
world the paper is true or false of is a function of the two
(`Development.world`): a rendering reads back as a statement when the
validator accepts everything the notation prints of it (`AcceptsAll`): each
formula returns one reading, with no flag set, that matches the reading the
renderer expects, and the sentence or figure is plain, so that the parser
undoes its layout. By `pollack` (`SpliceModel.ReadBackComplete`), an
accepted formula then has, in the grammar, no reading but the expected one,
and the two reading-back assumptions of `Anatomy.Sound` (`SpliceModel.Views`)
are theorems, as are its layout clauses, since the world prints by
definition as the anatomy says: `Development.sound`, with no hypothesis.
Theorem 1's `prose_true` and `rules_true` then say of a document that checks
clean (`document_pollack`, `document_pollack_rules`, and
`document_pollack_formula` for the views that show one formula) that each
formula of each block reads, in the notation's grammar, only as the part it
was printed from.
-/

namespace SpliceModel

open Imprimatur Imprimatur.Layout Imprimatur.Validate

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
  ∀ rd σ, Exp V.A V.G (tokens t) (V.sort q) 0 none V.G.chain0 0 (tokens t).size rd σ → Matches (V.expect q) rd

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

/-! ## The two inputs

What the extractor reads is two things, written by different hands: the
development, the Lean the paper is about, and the notation, the module its
authors write to say how a part of a statement is printed. The model keeps
them apart: a `Development` says nothing of how anything is printed, a
`Notation` nothing of what is proved, and the world the paper is true or
false of is a function of the two. -/

/-- The development, as the extractor reads it: the Lean environment (what
each key names and states, whether its proof is trusted, how a statement is
hashed), and which subterms each view shows of a statement. Nothing here
depends on the notation. -/
structure Development where
  /-- statements -/
  Stmt : Type
  /-- what a key names -/
  kind : Key → Kind
  /-- what a key states, if it is declared -/
  stmt : Key → Option Stmt
  /-- whether a key's proof is trusted -/
  trusted : Key → Bool
  /-- the hash of a statement's meaning -/
  hash : Stmt → Hash
  /-- the hash of a statement as written -/
  sig : Stmt → Hash
  /-- a part of a statement: a subterm a view shows as a formula -/
  Part : Type
  /-- what the prose view says of a statement: its parts, in their places -/
  gather : Stmt → Option (Layout.Prose Part)
  /-- what the rules view says of an inductive predicate: its constructors,
  as rules -/
  ctors : Stmt → Option (List (Layout.Rule Part))
  /-- the part a view that shows a statement as one formula (`math`, and
  the rest) shows it as -/
  formula : View → Stmt → Option Part

/-- A notation for the parts of a development, as its authors write it: how
a part is printed, and, read as a grammar, what the validator knows (the
sorts, the grammar, and for each part the sort it is read at and the
reading the renderer expects). -/
structure Notation (Part : Type) extends Validator Part where
  /-- a part printed as a formula -/
  print : Part → List Char

namespace Development

variable (L : Development) (N : Notation L.Part)

/-- A statement rendered in a view, by the notation: in `prose`, the parts
the view says, each printed, and the sentence set out by the layout; in
`rules`, the constructors as rules, each formula printed, and the figure
set out by the layout; in any other view, the one part it shows, printed. -/
def render (v : View) (S : L.Stmt) : Option Body :=
  match v with
  | "prose" => (L.gather S).map fun u => [.gen (proseLayout (u.map N.print))]
  | "rules" => (L.ctors S).map fun qs => [.gen (figureLayout (ruleItems (qs.map (Layout.Rule.map N.print))))]
  | _ => (L.formula v S).map fun q => [.gen (String.ofList (N.print q))]

theorem render_prose (S : L.Stmt) :
    L.render N "prose" S = (L.gather S).map fun u => [.gen (proseLayout (u.map N.print))] := rfl

theorem render_rules (S : L.Stmt) :
    L.render N "rules" S =
      (L.ctors S).map fun qs => [.gen (figureLayout (ruleItems (qs.map (Layout.Rule.map N.print))))] := rfl

theorem render_other {v : View} (hv : v ≠ "prose") (hw : v ≠ "rules") (S : L.Stmt) :
    L.render N v S = (L.formula v S).map fun q => [.gen (String.ofList (N.print q))] := by
  unfold render
  split <;> simp_all

/-- The validator accepts what the notation prints of a statement: the
sentence of the prose view is plain and each of its formulas is accepted;
each rule of the rules view is plain and each of its formulas is accepted;
and the one formula of each other view is accepted. This is what the
extractor checks of a statement before it writes its renderings. -/
def AcceptsAll (S : L.Stmt) : Prop :=
  (∀ u, L.gather S = some u → (u.map N.print).Plain ∧ ∀ q ∈ u.parts, N.toValidator.Accepts (N.print q) q) ∧
  (∀ qs, L.ctors S = some qs →
    ∀ q ∈ qs, (q.map N.print).Plain ∧ ∀ p ∈ q.parts, N.toValidator.Accepts (N.print p) p) ∧
  (∀ v q, L.formula v S = some q → N.toValidator.Accepts (N.print q) q)

/-- The world the development presents in the notation: what the
development states and proves, rendered by the notation, where a rendering
reads back as a statement when the validator accepts everything printed of
it. -/
def world : World :=
  { Stmt := L.Stmt, kind := L.kind, stmt := L.stmt, trusted := L.trusted, hash := L.hash, sig := L.sig,
    render := L.render N, Reads := fun _ S => L.AcceptsAll N S }

/-- The anatomy of the world's statements: the development's parts, printed
by the notation, and read as a part when every reading in the grammar is
the expected one. -/
def anatomy : Anatomy (L.world N) :=
  { Part := L.Part, ReadsPart := N.toValidator.ReadsPart, print := N.print, gather := L.gather, ctors := L.ctors }

/-- **The anatomy is sound.** The world prints as the anatomy says by
definition, and what the validator accepts is plain and reads back formula
by formula: nothing is assumed. -/
theorem sound : (L.anatomy N).Sound where
  plain := fun _ _ _ hR u hu => ((hR : L.AcceptsAll N _).1 u hu).1
  prose := fun S r hr => by
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ((L.render_prose N S).symm.trans hr)
    exact ⟨u, hu, rfl⟩
  formulas := fun _ _ _ hR u hu q hq => N.toValidator.accepts_readsPart (((hR : L.AcceptsAll N _).1 u hu).2 q hq)
  rulesPlain := fun _ _ _ hR qs hqs q hq => ((hR : L.AcceptsAll N _).2.1 qs hqs q hq).1
  rules := fun S r hr => by
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp ((L.render_rules N S).symm.trans hr)
    exact ⟨qs, hqs, rfl⟩
  ruleFormulas := fun _ _ _ hR qs hqs p hp => by
    obtain ⟨ps, hps, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hps
    exact N.toValidator.accepts_readsPart (((hR : L.AcceptsAll N _).2.1 qs hqs q hq).2 p hp)

section
variable {b : Bundle} {d : Doc}

/-- **Pollack-consistency of a document, prose.** If the bundle is true of
the world, and `check` reports nothing, a prose block names a statement Lean
proved, is its rendering, and its sentence comes apart into the formulas
printed from the statement's parts, each of which reads, in the notation's
grammar, only as the reading expected of its part. -/
theorem document_pollack (hb : b.True (L.world N) id) (hc : check b d = []) {k : Key} {r : Body}
    (hp : Piece.block k "prose" r ∈ d) :
    ∃ S, (L.world N).stmt k = some S ∧ (L.world N).trusted k = true ∧
      (L.world N).render "prose" S = some r ∧ (L.anatomy N).Prose r S :=
  prose_true (L.sound N) hb hc hp

/-- **Pollack-consistency of a document, rules.** The same of a rules
block: each rule's formulas read only as the constructor's parts. -/
theorem document_pollack_rules (hb : b.True (L.world N) id) (hc : check b d = []) {k : Key} {r : Body}
    (hp : Piece.block k "rules" r ∈ d) :
    ∃ S, (L.world N).stmt k = some S ∧ (L.world N).trusted k = true ∧
      (L.world N).render "rules" S = some r ∧ (L.anatomy N).Rules r S :=
  rules_true (L.sound N) hb hc hp

/-- **Pollack-consistency of a document, formulas.** The same of a block of
any other view, which shows its statement as one formula: the formula
reads, in the notation's grammar, only as the part it was printed from. -/
theorem document_pollack_formula (hb : b.True (L.world N) id) (hc : check b d = []) {k : Key} {v : View}
    {r : Body} (hv : v ≠ "prose") (hw : v ≠ "rules") (hp : Piece.block k v r ∈ d) :
    ∃ S, (L.world N).stmt k = some S ∧ (L.world N).trusted k = true ∧ (L.world N).render v S = some r ∧
      ∀ q, L.formula v S = some q → N.toValidator.ReadsPart (Body.text r).toList q := by
  obtain ⟨S, hS, ht, hr, hR⟩ := block_rendering hb hc hp fun S r' h => by
    obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp ((L.render_other N hv hw S).symm.trans h)
    rfl
  refine ⟨S, hS, ht, hr, fun q hq => ?_⟩
  obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp ((L.render_other N hv hw S).symm.trans hr)
  rw [hq] at hq'
  cases hq'
  rw [Body.text_gen, String.toList_ofList]
  exact N.toValidator.accepts_readsPart ((hR : L.AcceptsAll N S).2.2 v q hq)

end

end Development

end SpliceModel
