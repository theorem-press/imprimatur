/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Laws
import SpliceModel.Prose
import SpliceModel.Rules

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
prose view, the anatomy gathers what the sentence says (`Imprimatur.Layout.Prose`,
the extractor's own data), the notation prints each part, and the
extractor's own layout sets the formulas out as the sentence; the
extractor's parser takes it apart again (`SpliceModel.Prose`). Printing is
then

  render "prose" S = proseLayout (map print (gather S)),

and what is assumed (`Anatomy.Sound`) is that the world prints prose so,
that what the notation prints is plain, and, for each formula, that it
reads back as its part, which is what the validator checks. That a prose
rendering reads back part by part is then a theorem. The rules view is
treated the same way: the anatomy says which rules a predicate's
constructors are (`Imprimatur.Layout.Rule`), the extractor's own figure
layout sets them out, and its parser takes the figure apart again
(`SpliceModel.Rules`). Under these assumptions, Theorem 1 says, of a prose
or a rules block, what the block shows, part by part.
-/

namespace Imprimatur.Layout

/-- The formula a group's kind shows: its type, if it has one. -/
def kindParts {α : Type} : VarKind α → List α
  | .ofType t => [t]
  | .type => []
  | .prop => []

/-- The formulas a group shows: its names, then its type. -/
def groupParts {α : Type} (g : VarGroup α) : List α := g.names ++ kindParts g.kind

/-- The formulas a conclusion shows, in order. -/
def Concl.parts {α : Type} : Concl α → List α
  | .formula f => [f]
  | .conjuncts fs => fs
  | .iff a b => [a, b]
  | .exists_ w c => w :: c.parts

/-- The formulas the prose view shows, in order. -/
def Prose.parts {α : Type} : Prose α → List α
  | .define f => [f]
  | .statement s => (s.vars.map groupParts).flatten ++ s.hyps.map (·.formula) ++ s.concl.parts

/-- The formulas a rule shows: its conclusion, then its premises. -/
def Rule.parts {α : Type} (r : Rule α) : List α := r.concl :: r.premises

end Imprimatur.Layout

namespace SpliceModel

open Imprimatur Imprimatur.Layout

/-- How a world's statements, and the prose and rules views' renderings, come
apart. -/
structure Anatomy (W : World) where
  /-- a part of a statement, as the notation shows it -/
  Part : Type
  /-- when a formula reads back as a part -/
  ReadsPart : List Char → Part → Prop
  /-- a part printed as a formula, by the notation -/
  print : Part → List Char
  /-- what the prose view says of a statement: its parts, in their places -/
  gather : W.Stmt → Option (Layout.Prose Part)
  /-- what the rules view says of an inductive predicate: its constructors,
  as rules -/
  ctors : W.Stmt → Option (List (Layout.Rule Part))

section
variable {W : World} (A : Anatomy W)

/-- Formulas read back as parts, one by one. -/
inductive Anatomy.ReadsAll : List (List Char) → List A.Part → Prop
  /-- none -/
  | nil : ReadsAll [] []
  /-- the first, then the rest -/
  | cons {f : List Char} {q : A.Part} {fs : List (List Char)} {qs : List A.Part} :
    A.ReadsPart f q → ReadsAll fs qs → ReadsAll (f :: fs) (q :: qs)

/-- What a group ranges over reads back. -/
inductive Anatomy.ReadsKind : VarKind (List Char) → VarKind A.Part → Prop
  /-- a type, read back -/
  | ofType {t : List Char} {q : A.Part} : A.ReadsPart t q → ReadsKind (.ofType t) (.ofType q)
  /-- *a type* -/
  | type : ReadsKind .type .type
  /-- *a proposition* -/
  | prop : ReadsKind .prop .prop

/-- A group of variables reads back: name by name, and what it ranges over. -/
inductive Anatomy.ReadsGroup : VarGroup (List Char) → VarGroup A.Part → Prop
  /-- names, and kind -/
  | mk {g : VarGroup (List Char)} {u : VarGroup A.Part} :
    A.ReadsAll g.names u.names → A.ReadsKind g.kind u.kind → ReadsGroup g u

/-- Groups read back, one by one. -/
inductive Anatomy.ReadsGroups : List (VarGroup (List Char)) → List (VarGroup A.Part) → Prop
  /-- none -/
  | nil : ReadsGroups [] []
  /-- the first, then the rest -/
  | cons {g : VarGroup (List Char)} {u : VarGroup A.Part} {gs : List (VarGroup (List Char))}
    {us : List (VarGroup A.Part)} : A.ReadsGroup g u → ReadsGroups gs us → ReadsGroups (g :: gs) (u :: us)

/-- A hypothesis reads back: the same label, and its formula. -/
inductive Anatomy.ReadsHyp : Hyp (List Char) → Hyp A.Part → Prop
  /-- label, and formula -/
  | mk {hy : Hyp (List Char)} {u : Hyp A.Part} :
    hy.label = u.label → A.ReadsPart hy.formula u.formula → ReadsHyp hy u

/-- Hypotheses read back, one by one. -/
inductive Anatomy.ReadsHyps : List (Hyp (List Char)) → List (Hyp A.Part) → Prop
  /-- none -/
  | nil : ReadsHyps [] []
  /-- the first, then the rest -/
  | cons {hy : Hyp (List Char)} {u : Hyp A.Part} {hs : List (Hyp (List Char))} {us : List (Hyp A.Part)} :
    A.ReadsHyp hy u → ReadsHyps hs us → ReadsHyps (hy :: hs) (u :: us)

/-- A conclusion reads back, in its shape. -/
inductive Anatomy.ReadsConcl : Concl (List Char) → Concl A.Part → Prop
  /-- a formula -/
  | formula {f : List Char} {q : A.Part} : A.ReadsPart f q → ReadsConcl (.formula f) (.formula q)
  /-- conjuncts, one by one -/
  | conjuncts {fs : List (List Char)} {qs : List A.Part} :
    A.ReadsAll fs qs → ReadsConcl (.conjuncts fs) (.conjuncts qs)
  /-- *if and only if*, both sides -/
  | iff {lhs rhs : List Char} {lhs' rhs' : A.Part} :
    A.ReadsPart lhs lhs' → A.ReadsPart rhs rhs' → ReadsConcl (.iff lhs rhs) (.iff lhs' rhs')
  /-- *there is*, the witness and the rest -/
  | exists_ {w : List Char} {w' : A.Part} {c : Concl (List Char)} {c' : Concl A.Part} :
    A.ReadsPart w w' → ReadsConcl c c' → ReadsConcl (.exists_ w c) (.exists_ w' c')

/-- A sentence reads back as what the view says: Let as its variables,
Assume as its hypotheses, Then as its conclusion. -/
inductive Anatomy.ReadsProse : Layout.Prose (List Char) → Layout.Prose A.Part → Prop
  /-- *We define* -/
  | define {f : List Char} {q : A.Part} : A.ReadsPart f q → ReadsProse (.define f) (.define q)
  /-- a sentence -/
  | statement {s : Statement (List Char)} {u : Statement A.Part} :
    A.ReadsGroups s.vars u.vars → A.ReadsHyps s.hyps u.hyps → A.ReadsConcl s.concl u.concl →
    ReadsProse (.statement s) (.statement u)

/-- A rule reads back as a constructor: the same mark and label, premises
as its hypotheses, conclusion as its conclusion. -/
inductive Anatomy.ReadsRule : Layout.Rule (List Char) → Layout.Rule A.Part → Prop
  /-- mark, label, premises and conclusion -/
  | mk {f : Layout.Rule (List Char)} {q : Layout.Rule A.Part} :
    f.mark = q.mark → f.label = q.label → A.ReadsAll f.premises q.premises →
    A.ReadsPart f.concl q.concl → ReadsRule f q

/-- Rules read back as constructors, one by one. -/
inductive Anatomy.ReadsRules : List (Layout.Rule (List Char)) → List (Layout.Rule A.Part) → Prop
  /-- none -/
  | nil : ReadsRules [] []
  /-- the first, then the rest -/
  | cons {f : Layout.Rule (List Char)} {q : Layout.Rule A.Part} {fs : List (Layout.Rule (List Char))}
    {qs : List (Layout.Rule A.Part)} :
    A.ReadsRule f q → ReadsRules fs qs → ReadsRules (f :: fs) (q :: qs)

/-- A body is a statement printed in the prose view: what the view says of
the statement, each part printed by the notation, and the formulas set out
as the sentence by the extractor's layout. -/
def Anatomy.PrintsProse (S : W.Stmt) (r : Body) : Prop :=
  ∃ u, A.gather S = some u ∧ r = [.gen (proseLayout (u.map A.print))]

/-- The notation is faithful on a statement: each part the prose view shows,
printed, reads back as itself. -/
def Anatomy.Faithful (S : W.Stmt) : Prop :=
  ∀ u, A.gather S = some u → ∀ q ∈ u.parts, A.ReadsPart (A.print q) q

/-- A prose rendering shows a statement: the parser takes the sentence
apart, the view says what the statement's parts are, and the one reads back
as the other. -/
def Anatomy.Prose (r : Body) (S : W.Stmt) : Prop :=
  ∃ t u, proseSentence (Body.text r).toList = some t ∧ A.gather S = some u ∧ A.ReadsProse t u

/-- A body is a statement printed in the rules view: the rules the view
says its constructors are, each formula printed by the notation, and the
rules set out as the figure by the extractor's layout. -/
def Anatomy.PrintsRules (S : W.Stmt) (r : Body) : Prop :=
  ∃ qs, A.ctors S = some qs ∧ r = [.gen (figureLayout (ruleItems (qs.map (Layout.Rule.map A.print))))]

/-- The notation is faithful on a predicate: each part its rules show,
printed, reads back as itself. -/
def Anatomy.FaithfulRules (S : W.Stmt) : Prop :=
  ∀ qs, A.ctors S = some qs → ∀ q ∈ (qs.map Layout.Rule.parts).flatten, A.ReadsPart (A.print q) q

/-- A rules rendering shows a statement: the parser takes the figure apart,
the view says what the predicate's rules are, and each rule reads back as a
constructor, in order. -/
def Anatomy.Rules (r : Body) (S : W.Stmt) : Prop :=
  ∃ fs qs, figure (Body.text r).toList = some fs ∧ A.ctors S = some qs ∧ A.ReadsRules fs qs

/-- The anatomy is the world's. What the notation prints is plain; the
world prints prose and rules as the anatomy does, with the extractor's
layouts; and a rendering that reads back reads back formula by formula,
which is what the validator checks. -/
structure Anatomy.Sound : Prop where
  /-- what the notation prints of a statement is plain: no dollar in a
  formula, and a group's names come apart from each other and their type -/
  plain : ∀ S u, A.gather S = some u → (u.map A.print).Plain
  /-- the world prints prose as the anatomy does -/
  prose : ∀ S r, W.render "prose" S = some r → A.PrintsProse S r
  /-- a prose rendering that reads back reads back formula by formula -/
  formulas : ∀ S r, W.render "prose" S = some r → W.Reads r S → A.Faithful S
  /-- what the notation prints of a predicate's rules is plain: no newline
  in a formula or a label, and a mark the lexer takes apart -/
  rulesPlain : ∀ S qs, A.ctors S = some qs → ∀ q ∈ qs, (q.map A.print).Plain
  /-- the world prints rules as the anatomy does -/
  rules : ∀ S r, W.render "rules" S = some r → A.PrintsRules S r
  /-- a rules rendering that reads back reads back formula by formula -/
  ruleFormulas : ∀ S r, W.render "rules" S = some r → W.Reads r S → A.FaithfulRules S

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
  | [], _ => .nil
  | q :: _, h => .cons (h q (List.mem_cons_self ..)) (A.readsAll_map fun q' hq => h q' (List.mem_cons_of_mem _ hq))

theorem Anatomy.readsKind_map {W : World} (A : Anatomy W) {k : VarKind A.Part}
    (h : ∀ q ∈ kindParts k, A.ReadsPart (A.print q) q) : A.ReadsKind (k.map A.print) k := by
  cases k with
  | ofType t => exact .ofType (h t (by simp [kindParts]))
  | type => exact .type
  | prop => exact .prop

theorem Anatomy.readsGroups_map {W : World} (A : Anatomy W) :
    ∀ {us : List (VarGroup A.Part)}, (∀ q ∈ (us.map groupParts).flatten, A.ReadsPart (A.print q) q) →
      A.ReadsGroups (us.map (VarGroup.map A.print)) us
  | [], _ => .nil
  | u :: us, h => by
    simp only [List.map_cons, List.flatten_cons, List.mem_append, groupParts] at h
    exact .cons (.mk (A.readsAll_map fun q hq => h q (Or.inl (Or.inl hq)))
        (A.readsKind_map fun q hq => h q (Or.inl (Or.inr hq))))
      (A.readsGroups_map fun q hq => h q (Or.inr hq))

theorem Anatomy.readsHyps_map {W : World} (A : Anatomy W) :
    ∀ {us : List (Hyp A.Part)}, (∀ q ∈ us.map (·.formula), A.ReadsPart (A.print q) q) →
      A.ReadsHyps (us.map (Hyp.map A.print)) us
  | [], _ => .nil
  | u :: us, h => by
    simp only [List.map_cons, List.mem_cons] at h
    exact .cons (.mk rfl (h _ (Or.inl rfl))) (A.readsHyps_map fun q hq => h q (Or.inr hq))

theorem Anatomy.readsConcl_map {W : World} (A : Anatomy W) :
    ∀ {c : Concl A.Part}, (∀ q ∈ c.parts, A.ReadsPart (A.print q) q) → A.ReadsConcl (c.map A.print) c
  | .formula f, h => .formula (h f (by simp [Concl.parts]))
  | .conjuncts fs, h => .conjuncts (A.readsAll_map h)
  | .iff lhs rhs, h => .iff (h lhs (by simp [Concl.parts])) (h rhs (by simp [Concl.parts]))
  | .exists_ w c, h => .exists_ (h w (by simp [Concl.parts])) (A.readsConcl_map fun q hq => h q (by
      simp only [Concl.parts, List.mem_cons]; exact Or.inr hq))

/-- What the view says, each part printed, reads back as what it says. -/
theorem Anatomy.readsProse_map {W : World} (A : Anatomy W) :
    ∀ {u : Layout.Prose A.Part}, (∀ q ∈ u.parts, A.ReadsPart (A.print q) q) → A.ReadsProse (u.map A.print) u
  | .define f, h => .define (h f (by simp [Prose.parts]))
  | .statement s, h => by
    simp only [Prose.parts, List.mem_append] at h
    exact .statement (A.readsGroups_map fun q hq => h q (Or.inl (Or.inl hq)))
      (A.readsHyps_map fun q hq => h q (Or.inl (Or.inr hq)))
      (A.readsConcl_map fun q hq => h q (Or.inr hq))

/-- A rule's formulas, each printed from a part, and reading back as it, read
back as the constructor. -/
theorem Anatomy.readsRule_map {W : World} (A : Anatomy W) {q : Layout.Rule A.Part}
    (h : ∀ p ∈ q.parts, A.ReadsPart (A.print p) p) : A.ReadsRule (q.map A.print) q := by
  simp only [Layout.Rule.parts, List.mem_cons] at h
  exact .mk rfl rfl (A.readsAll_map fun p hp => h p (Or.inr hp)) (h q.concl (Or.inl rfl))

theorem Anatomy.readsRules_map {W : World} (A : Anatomy W) :
    ∀ {qs : List (Layout.Rule A.Part)}, (∀ p ∈ (qs.map Layout.Rule.parts).flatten, A.ReadsPart (A.print p) p) →
      A.ReadsRules (qs.map (Layout.Rule.map A.print)) qs
  | [], _ => .nil
  | q :: qs, h => by
    simp only [List.map_cons, List.flatten_cons, List.mem_append] at h
    exact .cons (A.readsRule_map fun p hp => h p (Or.inl hp)) (A.readsRules_map fun p hp => h p (Or.inr hp))

/-- A prose rendering has no slots. -/
theorem Anatomy.Sound.proseIds {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "prose" S = some r) : ids r = [] := by
  obtain ⟨u, _, rfl⟩ := hA.prose S r hr
  rfl

theorem Body.text_gen (s : String) : Body.text [.gen s] = s := by
  simp [Body.text, Seg.text, String.join]

/-- **A prose rendering shows its statement.** When it reads back, the
sentence comes apart into the formulas printed from the statement's parts,
and each reads back as its part. -/
theorem Anatomy.Sound.proseShows {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "prose" S = some r) (hR : W.Reads r S) : A.Prose r S := by
  have hF := hA.formulas S r hr hR
  obtain ⟨u, hu, rfl⟩ := hA.prose S r hr
  refine ⟨u.map A.print, u, ?_, hu, A.readsProse_map (hF u hu)⟩
  rw [Body.text_gen, proseLayout, String.toList_ofList]
  exact proseSentence_proseChars (hA.plain S u hu)

/-- A rules rendering has no slots. -/
theorem Anatomy.Sound.rulesIds {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "rules" S = some r) : ids r = [] := by
  obtain ⟨qs, _, rfl⟩ := hA.rules S r hr
  rfl

/-- **A rules rendering shows its predicate.** When it reads back, the
figure comes apart into the rules printed from the constructors, and each
reads back as its constructor. -/
theorem Anatomy.Sound.rulesShow {W : World} {A : Anatomy W} (hA : A.Sound) {S : W.Stmt} {r : Body}
    (hr : W.render "rules" S = some r) (hR : W.Reads r S) : A.Rules r S := by
  have hF := hA.ruleFormulas S r hr hR
  obtain ⟨qs, hqs, rfl⟩ := hA.rules S r hr
  refine ⟨qs.map (Layout.Rule.map A.print), qs, ?_, hqs, A.readsRules_map (hF qs hqs)⟩
  rw [Body.text_gen]
  exact figure_figureLayout fun q hq => by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact hA.rulesPlain S qs hqs q' hq'

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
  obtain ⟨S, hS, ht, hr, hR⟩ := block_rendering hb hc hp fun _ _ h => hA.rulesIds h
  exact ⟨S, hS, ht, hr, hA.rulesShow hr hR⟩

end

end SpliceModel
