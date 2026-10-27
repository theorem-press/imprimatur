/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Validator

/-!
# The results, at the top level

The paper's introduction states its results in terms of three functions:
the extractor's (`Validated.extract`, the bundle it writes of a
development), the splicer's `apply` (which regenerates a document's blocks
from a bundle) and its `check` (what is wrong with a document, against a
bundle). This module gives the extractor's function and the two properties
the results are about, `Validated.Prints` (what the extractor is trusted
for) and `Validated.Pollack` (every formula of a document reads only as what
it was printed from), and composes the paper's theorems into the
introduction's:

- `extract_true`: the bundle the extractor writes is true;
- `apply_laws`: building changes the document's blocks only, at once, and
  leaves nothing stale;
- `paper_true`: a document that checks clean against the bundle the
  extractor writes is true of the development, and Pollack-consistent.
-/

namespace SpliceModel

open Imprimatur

/-- **Building regenerates blocks, once.** On a well-formed bundle, `apply` changes nothing but the
blocks' bodies, changes nothing a second time, and leaves no block stale. -/
theorem apply_laws {b : Bundle} (hb : WF b) (d : Doc) :
    (apply b d).map outline = d.map outline ∧ apply b (apply b d) = apply b d ∧
      ∀ k, Diag.stale k ∉ check b (apply b d) :=
  ⟨apply_outline b d, apply_apply hb d, not_stale_after_apply hb d⟩

namespace Validated

variable (X : Validated)

open Classical in
/-- What the validator reports of a statement, in any view: nothing when it
accepts every formula printed of the statement, else that it does not. -/
noncomputable def problems (_ : View) (S : X.base.Stmt) : Array String :=
  if X.AcceptsAll S then #[] else #["not validated"]

/-- The bundle the extractor writes of the development: each of the keys
`ks` hashed and rendered in the views `vs`, with what the validator reports
of it. -/
noncomputable def extract (vs : List View) (ks : List Key) : Bundle :=
  bundleOf X.world vs X.problems ks

/-- The extractor prints as the anatomy says, which is what it is trusted
for: what the notation prints of a statement is plain, and the extractor
sets prose and rules out with its layouts. -/
structure Prints : Prop where
  /-- what the notation prints of a statement is plain -/
  plain : ∀ S u, X.gather S = some u → (u.map X.print).Plain
  /-- the world prints prose as the anatomy does -/
  prose : ∀ S r, X.world.render "prose" S = some r → X.anatomy.PrintsProse S r
  /-- what the notation prints of a predicate's rules is plain -/
  rulesPlain : ∀ S qs, X.ctors S = some qs → ∀ q ∈ qs, (q.map X.print).Plain
  /-- the world prints rules as the anatomy does -/
  rules : ∀ S r, X.world.render "rules" S = some r → X.anatomy.PrintsRules S r

/-- A block of view `v` reads as its key's statement, formula by formula. A
prose sentence, or a rules figure, comes apart into formulas, each of which
reads, in the notation's grammar, only as the part of the statement it was
printed from; the other views say nothing here. -/
def ReadsAs : View → Body → Key → Prop
  | "prose", r, k => ∀ S, X.world.stmt k = some S → X.anatomy.Prose r S
  | "rules", r, k => ∀ S, X.world.stmt k = some S → X.anatomy.Rules r S
  | _, _, _ => True

/-- A document is Pollack-consistent: each of its blocks reads only as its
key's statement. -/
def Pollack (d : Doc) : Prop :=
  ∀ k v r, Piece.block k v r ∈ d → X.ReadsAs v r k

/-- **Extraction is true.** The bundle the extractor writes is true of the
development, as the validator sees it. -/
theorem extract_true (vs : List View) (ks : List Key) : (X.extract vs ks).True X.world id :=
  bundleOf_true fun _ S _ h _ => by
    unfold problems at h
    split at h
    · assumption
    · simp at h

/-- A document that checks clean against a true bundle is Pollack-consistent. -/
theorem pollack_of_check (hX : X.Prints) {b : Bundle} {d : Doc} (hb : b.True X.world id)
    (hc : check b d = []) : X.Pollack d := by
  intro k v r hp
  by_cases hv : v = "prose"
  · subst hv
    intro S hS
    obtain ⟨S', hS', -, -, hP⟩ := X.document_pollack hX.plain hX.prose hX.rulesPlain hX.rules hb hc hp
    rw [hS] at hS'
    cases hS'
    exact hP
  by_cases hw : v = "rules"
  · subst hw
    intro S hS
    obtain ⟨S', hS', -, -, hP⟩ := X.document_pollack_rules hX.plain hX.prose hX.rulesPlain hX.rules hb hc hp
    rw [hS] at hS'
    cases hS'
    exact hP
  · unfold ReadsAs
    split <;> simp_all

/-- **A paper that checks clean is true, and reads only as Lean's.** If the
extractor prints as it is trusted to and `check` reports nothing against the
bundle it writes, the document is true of the development, and each of its
formulas reads only as the part of the statement it was printed from. -/
theorem paper_true (hX : X.Prints) {vs : List View} {ks : List Key} {b : Bundle} {d : Doc}
    (hb : X.extract vs ks = b) (hc : check b d = []) : d.True X.world ∧ X.Pollack d := by
  subst hb
  exact ⟨document_true (X.extract_true vs ks) hc, X.pollack_of_check hX (X.extract_true vs ks) hc⟩

end Validated

end SpliceModel
