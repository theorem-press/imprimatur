/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Laws

/-!
# What the prose and rules views show

Theorem 1 holds of every view alike, because a world says nothing of what a
view's rendering is: `render` and `Reads` are opaque. Here two views are
given a reading, the way the validator reads them: a rendering comes apart
into formulas, a statement into parts, and each formula is read back as its
part. A `prose` sentence is *Let* its variables, *Assume* its hypotheses,
*Then* its conclusion; a `rules` figure is a list of rules, each with
premises and a conclusion.

How a rendering comes apart, how a statement does, and when a formula reads
back as a part, are an anatomy of the world. That the world's `Reads` is
the anatomy's, for these two views, is an assumption (`Anatomy.Sound`): it
is what the extractor and the validator are trusted for. Under it, Theorem 1
says, of a prose or a rules block, what the block shows, part by part.
-/

namespace SpliceModel

open Imprimatur

/-- A proposition taken apart, as the prose view shows it. -/
structure Telescope (α : Type) where
  /-- its variables, with their types -/
  vars : List α
  /-- its hypotheses -/
  hyps : List α
  /-- its conclusion -/
  concl : α

/-- A rule, as the rules view shows it. -/
structure Rule (α : Type) where
  /-- its name -/
  name : String
  /-- its premises -/
  premises : List α
  /-- its conclusion -/
  concl : α

/-- How a world's statements, and the prose and rules views' renderings, come
apart. -/
structure Anatomy (W : World) where
  /-- a part of a statement, as the notation shows it -/
  Part : Type
  /-- when a formula reads back as a part -/
  ReadsPart : TeX → Part → Prop
  /-- a proposition, taken apart -/
  telescope : W.Stmt → Option (Telescope Part)
  /-- an inductive predicate's constructors, as rules -/
  ctors : W.Stmt → Option (List (Rule Part))
  /-- a prose sentence, taken apart: Let, Assume, Then -/
  sentence : Body → Option (Telescope TeX)
  /-- a rules figure, taken apart -/
  figure : Body → Option (List (Rule TeX))

section
variable {W : World} (A : Anatomy W)

/-- Formulas read back as parts, one by one. -/
def Anatomy.ReadsAll : List TeX → List A.Part → Prop
  | [], [] => _root_.True
  | f :: fs, q :: qs => A.ReadsPart f q ∧ Anatomy.ReadsAll fs qs
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- A sentence reads back as a proposition: Let as its variables, Assume as
its hypotheses, Then as its conclusion. -/
def Anatomy.ReadsTelescope (t : Telescope TeX) (u : Telescope A.Part) : Prop :=
  A.ReadsAll t.vars u.vars ∧ A.ReadsAll t.hyps u.hyps ∧ A.ReadsPart t.concl u.concl

/-- A rule reads back as a constructor: the same name, premises as its
hypotheses, conclusion as its conclusion. -/
def Anatomy.ReadsRule (f : Rule TeX) (q : Rule A.Part) : Prop :=
  f.name = q.name ∧ A.ReadsAll f.premises q.premises ∧ A.ReadsPart f.concl q.concl

/-- Rules read back as constructors, one by one. -/
def Anatomy.ReadsRules : List (Rule TeX) → List (Rule A.Part) → Prop
  | [], [] => _root_.True
  | f :: fs, q :: qs => A.ReadsRule f q ∧ Anatomy.ReadsRules fs qs
  | [], _ :: _ => False
  | _ :: _, [] => False

/-- A prose rendering shows a statement: the sentence and the proposition
come apart, and the one reads back as the other. -/
def Anatomy.Prose (r : Body) (S : W.Stmt) : Prop :=
  ∃ t u, A.sentence r = some t ∧ A.telescope S = some u ∧ A.ReadsTelescope t u

/-- A rules rendering shows a statement: the figure and the predicate come
apart, and each rule reads back as a constructor, in order. -/
def Anatomy.Rules (r : Body) (S : W.Stmt) : Prop :=
  ∃ fs qs, A.figure r = some fs ∧ A.ctors S = some qs ∧ A.ReadsRules fs qs

/-- The anatomy is the world's: prose and rules renderings have no slots, and
one that reads back reads back part by part. -/
structure Anatomy.Sound : Prop where
  /-- a prose rendering has no slots -/
  proseIds : ∀ S r, W.render "prose" S = some r → ids r = []
  /-- a prose rendering that reads back shows its statement -/
  prose : ∀ S r, W.render "prose" S = some r → W.Reads r S → A.Prose r S
  /-- a rules rendering has no slots -/
  rulesIds : ∀ S r, W.render "rules" S = some r → ids r = []
  /-- a rules rendering that reads back shows its statement -/
  rules : ∀ S r, W.render "rules" S = some r → W.Reads r S → A.Rules r S

end

/-- A body with no slots is its own filling. -/
theorem fill_of_ids_nil {old : List (SlotId × String)} : ∀ {r : Body}, ids r = [] → fill old r = r
  | [], _ => rfl
  | .gen _ :: r, h => by simp only [fill, fill_of_ids_nil (r := r) h]
  | .slot _ _ :: _, h => by simp [ids] at h

section
variable {W : World} {A : Anatomy W} {b : Bundle} {d : Doc}

/-- A block with no slots in its view is the rendering itself. -/
theorem block_rendering (hb : b.True W id) (hc : check b d = []) {k : Key} {v : View} {r : Body}
    (hp : Piece.block k v r ∈ d) (hids : ∀ S r', W.render v S = some r' → ids r' = []) :
    ∃ S, W.stmt k = some S ∧ W.trusted k = true ∧ W.render v S = some r ∧ W.Reads r S := by
  obtain ⟨S, r', hS, ht, hr, hf, hR⟩ := block_true hb hc hp
  rw [fill_of_ids_nil (hids S r' hr)] at hf
  subst hf
  exact ⟨S, hS, ht, hr, hR⟩

/-- **Prose shows the statement.** If `check` reports nothing against a true
bundle, a prose block names a statement Lean proved, is its rendering, and
reads back as it part by part: Let its variables, Assume its hypotheses,
Then its conclusion. -/
theorem prose_true (hA : A.Sound) (hb : b.True W id) (hc : check b d = []) {k : Key} {r : Body}
    (hp : Piece.block k "prose" r ∈ d) :
    ∃ S, W.stmt k = some S ∧ W.trusted k = true ∧ W.render "prose" S = some r ∧ A.Prose r S := by
  obtain ⟨S, hS, ht, hr, hR⟩ := block_rendering hb hc hp hA.proseIds
  exact ⟨S, hS, ht, hr, hA.prose S r hr hR⟩

/-- **Rules show the predicate.** If `check` reports nothing against a true
bundle, a rules block names a statement Lean proved, is its rendering, and
each of its rules reads back as a constructor, in order. -/
theorem rules_true (hA : A.Sound) (hb : b.True W id) (hc : check b d = []) {k : Key} {r : Body}
    (hp : Piece.block k "rules" r ∈ d) :
    ∃ S, W.stmt k = some S ∧ W.trusted k = true ∧ W.render "rules" S = some r ∧ A.Rules r S := by
  obtain ⟨S, hS, ht, hr, hR⟩ := block_rendering hb hc hp hA.rulesIds
  exact ⟨S, hS, ht, hr, hA.rules S r hr hR⟩

end

end SpliceModel
