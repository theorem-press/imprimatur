/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Laws
import SpliceModel.Prose

/-!
# What the prose and rules views show

Theorem 1 holds of every view alike, because a world says nothing of what a
view's rendering is: `render` and `Reads` are opaque. Here two views are
given a reading, the way the validator reads them: a rendering comes apart
into formulas, a statement into parts, and each formula is read back as its
part. A `prose` sentence is *Let* its variables, *Assume* its hypotheses,
*Then* its conclusion; a `rules` figure is a list of rules, each with
premises and a conclusion.

How a statement comes apart, how each part is printed as a formula, and
when a formula reads back as a part, are an anatomy of the world. For the
prose view, the anatomy's printed formulas are set out as a sentence by the
prose layout, which the prose parser undoes (`SpliceModel.Prose`). Printing
is then

  render "prose" S = proseLayout (map print (telescope S)),

and what is assumed (`Anatomy.Sound`) is that the world prints prose so,
that no printed formula has a dollar in it, and, for each formula, that it
reads back as its part, which is what the validator checks. That a prose
rendering reads back part by part is then a theorem. The rules view is still assumed to read back part by part. Under
these assumptions, Theorem 1 says, of a prose or a rules block, what the
block shows, part by part.
-/

namespace SpliceModel

open Imprimatur

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
  /-- a part printed as a formula, by the notation -/
  print : Part → TeX
  /-- a proposition, taken apart -/
  telescope : W.Stmt → Option (Telescope Part)
  /-- an inductive predicate's constructors, as rules -/
  ctors : W.Stmt → Option (List (Rule Part))
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

/-- A body is a statement printed in the prose view: the statement taken
apart, each part printed by the notation, and the formulas set out as a
sentence. -/
def Anatomy.PrintsProse (S : W.Stmt) (r : Body) : Prop :=
  ∃ u, A.telescope S = some u ∧ r = proseLayout (u.map A.print)

/-- The notation is faithful on a statement: each of its parts, printed,
reads back as itself. -/
def Anatomy.Faithful (S : W.Stmt) : Prop :=
  ∀ u, A.telescope S = some u →
    (∀ q ∈ u.vars, A.ReadsPart (A.print q) q) ∧ (∀ q ∈ u.hyps, A.ReadsPart (A.print q) q) ∧
      A.ReadsPart (A.print u.concl) u.concl

/-- A prose rendering shows a statement: the sentence and the proposition
come apart, and the one reads back as the other. -/
def Anatomy.Prose (r : Body) (S : W.Stmt) : Prop :=
  ∃ t u, proseSentence r = some t ∧ A.telescope S = some u ∧ A.ReadsTelescope t u

/-- A rules rendering shows a statement: the figure and the predicate come
apart, and each rule reads back as a constructor, in order. -/
def Anatomy.Rules (r : Body) (S : W.Stmt) : Prop :=
  ∃ fs qs, A.figure r = some fs ∧ A.ctors S = some qs ∧ A.ReadsRules fs qs

/-- The anatomy is the world's. No printed formula has a dollar in it; the
world prints prose as the anatomy does, with the prose layout; and a prose
rendering that reads back reads back formula by formula, which is what the
validator checks. Rules renderings have no slots, and one that reads back
reads back part by part. -/
structure Anatomy.Sound : Prop where
  /-- a printed formula has no dollar in it -/
  plain : ∀ q, Plain (A.print q)
  /-- the world prints prose as the anatomy does -/
  prose : ∀ S r, W.render "prose" S = some r → A.PrintsProse S r
  /-- a prose rendering that reads back reads back formula by formula -/
  formulas : ∀ S r, W.render "prose" S = some r → W.Reads r S → A.Faithful S
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

/-- Formulas each printed from a part, and reading back as it, read back as
the parts. -/
theorem Anatomy.readsAll_map {W : World} (A : Anatomy W) :
    ∀ {qs : List A.Part}, (∀ q ∈ qs, A.ReadsPart (A.print q) q) → A.ReadsAll (qs.map A.print) qs
  | [], _ => trivial
  | q :: _, h => ⟨h q (List.mem_cons_self ..), A.readsAll_map fun q' hq => h q' (List.mem_cons_of_mem _ hq)⟩

/-- A prose rendering has no slots. -/
theorem Anatomy.Sound.proseIds {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "prose" S = some r) : ids r = [] := by
  obtain ⟨u, _, rfl⟩ := hA.prose S r hr
  exact ids_proseLayout _

/-- **A prose rendering shows its statement.** When it reads back, the
sentence comes apart into the formulas printed from the statement's parts,
and each reads back as its part. -/
theorem Anatomy.Sound.proseShows {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "prose" S = some r) (hR : W.Reads r S) : A.Prose r S := by
  have hF := hA.formulas S r hr hR
  obtain ⟨u, hu, rfl⟩ := hA.prose S r hr
  obtain ⟨hv, hh, hc⟩ := hF u hu
  have hl : proseSentence (proseLayout (u.map A.print)) = some (u.map A.print) := by
    apply proseSentence_proseLayout
    intro f hf
    simp only [Telescope.map, List.mem_map] at hf
    rcases hf with ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩ | rfl <;> exact hA.plain _
  exact ⟨u.map A.print, u, hl, hu, A.readsAll_map hv, A.readsAll_map hh, hc⟩

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
  obtain ⟨S, hS, ht, hr, hR⟩ := block_rendering hb hc hp fun _ _ h => hA.proseIds h
  exact ⟨S, hS, ht, hr, hA.proseShows hr hR⟩

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
