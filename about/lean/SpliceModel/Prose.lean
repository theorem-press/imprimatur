/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Basic

/-!
# The prose layout, and its parser

The `prose` view sets a proposition out as a sentence:

  \LeanProse{Let $x$, $y$ and $z$. Assume $h₁$ and $h₂$. Then $c$.}

*Let* its variables, *Assume* its hypotheses, *Then* its conclusion, each
formula in dollars; a part with nothing in it is left out, and *Then* with
it when nothing comes before. This is the sentence `Views.proseView` writes,
without its other words (`be a type`, hypothesis labels, numbered conjuncts,
`if and only if`, `there is`).

The parser takes the sentence apart again: it splits the text at its
dollars, pairs each formula with the text before it, and sorts the formulas
into their parts by that text. It undoes the layout whenever no formula has
a dollar in it (`proseSentence_proseLayout`).
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

/-- Print each part of a telescope. -/
def Telescope.map {α β : Type} (f : α → β) (t : Telescope α) : Telescope β :=
  ⟨t.vars.map f, t.hyps.map f, f t.concl⟩

/-- The dollar sign, which opens and closes a formula. -/
def dollar : Char := '$'

/-- A formula is plain when it has no dollar in it. -/
abbrev Plain (f : TeX) : Prop := dollar ∉ f.toList

/-! ## The layout -/

/-- The formulas of a part after its first, each with the text before it: a
comma, and `and` before the last. -/
def andRest : List TeX → List (String × TeX)
  | [] => []
  | f :: fs => ((if fs = [] then " and " else ", "), f) :: andRest fs

/-- The formulas of a part, each with the text before it. -/
def andList (first : String) : List TeX → List (String × TeX)
  | [] => []
  | f :: fs => (first, f) :: andRest fs

theorem andList_nil (first : String) : andList first [] = [] := rfl

/-- A sentence's formulas, each with the text before it. -/
def proseParts (t : Telescope TeX) : List (String × TeX) :=
  andList "\\LeanProse{Let " t.vars ++
    andList (if t.vars = [] then "\\LeanProse{Assume " else ". Assume ") t.hyps ++
    [(if t.vars = [] ∧ t.hyps = [] then "\\LeanProse{" else ". Then ", t.concl)]

/-- Text and formulas, the formulas in dollars, and the sentence's end. -/
def joinParts : List (String × TeX) → String
  | [] => ".}"
  | (s, f) :: ps => s ++ "$" ++ f ++ "$" ++ joinParts ps

/-- **The prose layout.** Formulas set out as a sentence. -/
def proseLayout (t : Telescope TeX) : Body := [.gen (joinParts (proseParts t))]

/-! ## The parser

The parser is lenient: it need only undo the layout, not reject what the
layout cannot make. Text that neither starts nor continues a part starts
the conclusion, and a piece of text with no formula after it is dropped. -/

/-- Put a character at the front of the first piece. -/
def pushChar (c : Char) : List (List Char) → List (List Char)
  | [] => [[c]]
  | w :: ws => (c :: w) :: ws

/-- Split text at each dollar. -/
def splitDollar : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => if c = dollar then [] :: splitDollar cs else pushChar c (splitDollar cs)

/-- Pair each formula with the text before it, from the pieces between
dollars. -/
def unjoin : List (List Char) → List (String × TeX)
  | [] => []
  | [_] => []
  | s :: f :: rest => (String.ofList s, String.ofList f) :: unjoin rest

/-- A part of a sentence. -/
inductive Sec where
  /-- Let -/
  | vars
  /-- Assume -/
  | hyps
  /-- Then -/
  | concl
  deriving DecidableEq

/-- The part that a text starts: `Let` the variables, `Assume` the
hypotheses, and otherwise the conclusion. -/
def opener (s : String) : Sec :=
  if s = "\\LeanProse{Let " then .vars
  else if s = "\\LeanProse{Assume " ∨ s = ". Assume " then .hyps
  else .concl

/-- The text between formulas of one part. -/
def IsSep (s : String) : Prop := s = ", " ∨ s = " and "

instance (s : String) : Decidable (IsSep s) := inferInstanceAs (Decidable (_ ∨ _))

/-- The part of a formula, from the part before it and the text before it:
a separator continues the part, and other text starts one. -/
def nextSec (sec : Sec) (s : String) : Sec := if IsSep s then sec else opener s

/-- Add a formula to a part. -/
def Sec.add (f : TeX) : Sec → List TeX × List TeX × List TeX → List TeX × List TeX × List TeX
  | .vars, (vs, hs, cs) => (f :: vs, hs, cs)
  | .hyps, (vs, hs, cs) => (vs, f :: hs, cs)
  | .concl, (vs, hs, cs) => (vs, hs, f :: cs)

/-- Sort formulas into parts, by the text before each. -/
def sortParts (sec : Sec) : List (String × TeX) → List TeX × List TeX × List TeX
  | [] => ([], [], [])
  | (s, f) :: ps => (nextSec sec s).add f (sortParts (nextSec sec s) ps)

/-- A sentence whose conclusion is one formula. -/
def ofParts : List TeX × List TeX × List TeX → Option (Telescope TeX)
  | (vs, hs, [c]) => some ⟨vs, hs, c⟩
  | (_, _, []) => none
  | (_, _, _ :: _ :: _) => none

/-- **The prose parser.** A sentence taken apart. -/
def proseSentence : Body → Option (Telescope TeX)
  | [.gen s] => ofParts (sortParts .concl (unjoin (splitDollar s.toList)))
  | _ => none

/-! ## The parser undoes the layout -/

theorem splitDollar_of_not_mem : ∀ {a : List Char}, dollar ∉ a → splitDollar a = [a]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ dollar := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : dollar ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitDollar, hc, splitDollar_of_not_mem hcs, pushChar]

theorem splitDollar_append : ∀ {a : List Char} (b : List Char), dollar ∉ a →
    splitDollar (a ++ dollar :: b) = a :: splitDollar b
  | [], b, _ => by simp [splitDollar]
  | c :: cs, b, h => by
    have hc : c ≠ dollar := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : dollar ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitDollar, hc, splitDollar_append b hcs, pushChar]

/-- Text and formulas with no dollars in them. -/
def NoDollar (ps : List (String × TeX)) : Prop :=
  ∀ p ∈ ps, Plain p.1 ∧ Plain p.2

theorem unjoin_joinParts : ∀ {ps : List (String × TeX)}, NoDollar ps →
    unjoin (splitDollar (joinParts ps).toList) = ps
  | [], _ => by
    rw [joinParts, splitDollar_of_not_mem (by decide)]
    rfl
  | (s, f) :: ps, h => by
    have h₀ := h (s, f) (List.mem_cons_self ..)
    have hps : NoDollar ps := fun p hp => h p (List.mem_cons_of_mem _ hp)
    have : (joinParts ((s, f) :: ps)).toList =
        s.toList ++ dollar :: (f.toList ++ dollar :: (joinParts ps).toList) := by
      simp [joinParts, dollar]
    rw [this, splitDollar_append _ h₀.1, splitDollar_append _ h₀.2, unjoin, unjoin_joinParts hps]
    simp

theorem sortParts_andRest (sec : Sec) : ∀ (fs : List TeX) (rest : List (String × TeX)),
    sortParts sec (andRest fs ++ rest) = fs.foldr sec.add (sortParts sec rest)
  | [], rest => by simp [andRest]
  | f :: fs, rest => by
    have hs : nextSec sec (if fs = [] then " and " else ", ") = sec := by
      split <;> simp [nextSec, IsSep]
    simp only [andRest, List.cons_append, sortParts, hs, sortParts_andRest sec fs rest,
      List.foldr_cons]

theorem sortParts_andList {sec : Sec} {first : String} (hs : ¬ IsSep first) (f : TeX)
    (fs : List TeX) (rest : List (String × TeX)) :
    sortParts sec (andList first (f :: fs) ++ rest) =
      (f :: fs).foldr (opener first).add (sortParts (opener first) rest) := by
  simp only [andList, List.cons_append, sortParts, nextSec, hs, ite_false,
    sortParts_andRest (opener first) fs rest, List.foldr_cons]

theorem foldr_vars (fs : List TeX) (vs hs cs : List TeX) :
    fs.foldr Sec.vars.add (vs, hs, cs) = (fs ++ vs, hs, cs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [ih, Sec.add]

theorem foldr_hyps (fs : List TeX) (vs hs cs : List TeX) :
    fs.foldr Sec.hyps.add (vs, hs, cs) = (vs, fs ++ hs, cs) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [ih, Sec.add]

theorem sortParts_concl {sec : Sec} {s : String} (h : opener s = .concl) (hs : ¬ IsSep s)
    (c : TeX) : sortParts sec [(s, c)] = ([], [], [c]) := by
  simp [sortParts, nextSec, hs, h, Sec.add]

/-- **The parser undoes the layout**, when no formula has a dollar in it. -/
theorem proseSentence_proseLayout (t : Telescope TeX)
    (h : ∀ f, (f ∈ t.vars ∨ f ∈ t.hyps ∨ f = t.concl) → Plain f) :
    proseSentence (proseLayout t) = some t := by
  obtain ⟨vars, hyps, c⟩ := t
  have hnd : NoDollar (proseParts ⟨vars, hyps, c⟩) := by
    intro p hp
    simp only [proseParts, List.mem_append, List.mem_singleton] at hp
    have andRest_mem : ∀ fs : List TeX, ∀ p ∈ andRest fs, (Plain p.1) ∧ p.2 ∈ fs := by
      intro fs
      induction fs with
      | nil => simp [andRest]
      | cons f fs ih =>
        intro p hp
        simp only [andRest, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨by split <;> simp [Plain, dollar], List.mem_cons_self ..⟩
        · exact ⟨(ih p hp).1, List.mem_cons_of_mem _ (ih p hp).2⟩
    have andList_mem : ∀ (first : String), Plain first → ∀ fs : List TeX,
        ∀ p ∈ andList first fs, (Plain p.1) ∧ p.2 ∈ fs := by
      intro first hf fs p hp
      cases fs with
      | nil => simp [andList] at hp
      | cons f fs =>
        simp only [andList, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨hf, List.mem_cons_self ..⟩
        · exact ⟨(andRest_mem fs p hp).1, List.mem_cons_of_mem _ (andRest_mem fs p hp).2⟩
    rcases hp with (hp | hp) | rfl
    · obtain ⟨h₁, h₂⟩ := andList_mem _ (by simp [Plain, dollar]) vars p hp
      exact ⟨h₁, h p.2 (Or.inl h₂)⟩
    · obtain ⟨h₁, h₂⟩ := andList_mem _ (by split <;> simp [Plain, dollar]) hyps p hp
      exact ⟨h₁, h p.2 (Or.inr (Or.inl h₂))⟩
    · exact ⟨by split <;> simp [Plain, dollar], h c (Or.inr (Or.inr rfl))⟩
  simp only [proseSentence, proseLayout, unjoin_joinParts hnd]
  have hLet : opener "\\LeanProse{Let " = .vars := by decide
  have hAssume₀ : opener "\\LeanProse{Assume " = .hyps := by decide
  have hAssume : opener ". Assume " = .hyps := by decide
  cases vars with
  | nil =>
    cases hyps with
    | nil =>
      simp only [proseParts, andList_nil, List.nil_append, ite_true, and_self]
      rw [sortParts_concl (by decide) (by decide)]
      rfl
    | cons h₁ hs =>
      simp only [proseParts, andList_nil, List.nil_append, ite_true, reduceCtorEq, and_false,
        ite_false]
      rw [sortParts_andList (by decide), sortParts_concl (by decide) (by decide), hAssume₀]
      simp [foldr_hyps, Sec.add, ofParts]
  | cons v vs =>
    cases hyps with
    | nil =>
      simp only [proseParts, reduceCtorEq, ite_false, false_and, andList_nil, List.append_nil]
      rw [sortParts_andList (by decide), sortParts_concl (by decide) (by decide), hLet]
      simp [foldr_vars, Sec.add, ofParts]
    | cons h₁ hs =>
      simp only [proseParts, reduceCtorEq, ite_false, false_and, List.append_assoc]
      rw [sortParts_andList (by decide), sortParts_andList (by decide),
        sortParts_concl (by decide) (by decide), hLet, hAssume]
      simp [foldr_vars, foldr_hyps, Sec.add, ofParts]

/-- A laid-out sentence has no slots. -/
theorem ids_proseLayout (t : Telescope TeX) : ids (proseLayout t) = [] := rfl

end SpliceModel
