/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Validator

/-!
# The results, at the top level

The paper's introduction states its results in terms of two inputs, the
development `L` and the notation `N` (`SpliceModel.Validator`), and three
functions: the extractor's (`Development.extract`, the bundle it writes of
the development in the notation), the splicer's `apply` (which regenerates a
document's blocks from a bundle) and its `check` (what is wrong with a
document, against a bundle). This module gives the extractor's function and
the property the results are about, `Development.Pollack` (every formula of
a document reads only as what it was printed from), and composes the
paper's theorems into the introduction's:

- `extract_true`: the bundle the extractor writes is true;
- `clean_true`: a document that checks clean against a true bundle is true
  of the development;
- `check_sound`: and reads only as Lean's: the second arrow of the
  introduction's diagram, of a true bundle;
- `apply_laws`: building changes the document's blocks only, at once, and
  leaves nothing stale;
- `paper_true`: a document that checks clean against the bundle the
  extractor writes is true of the development, and Pollack-consistent.

Nothing is assumed of the extractor beyond the model itself: that it
renders as `Development.render` says, and that it reports a rendering it
does not accept.
-/

namespace SpliceModel

open Imprimatur

/-- **Building regenerates blocks, once.** On a well-formed bundle, `apply` changes nothing but the
blocks' bodies, changes nothing a second time, and leaves no block stale. -/
theorem apply_laws {b : Bundle} (hb : WF b) (d : Doc) :
    (apply b d).map outline = d.map outline ∧ apply b (apply b d) = apply b d ∧
      ∀ k, Diag.stale k ∉ check b (apply b d) :=
  ⟨apply_outline b d, apply_apply hb d, not_stale_after_apply hb d⟩

/-- **Building settles.** On a well-formed bundle, `apply` keeps the document's
outline; what `check` then reports is what it reported before, less *stale*,
so a build answers exactly the stale blocks and leaves what is the bundle's or
the authors' to answer; and a document `check` passes is one `apply` leaves
alone. -/
theorem build_settles {b : Bundle} (hb : WF b) (d : Doc) :
    (apply b d).map outline = d.map outline ∧ check b (apply b d) = unstale (check b d) ∧
      (check b d = [] → apply b d = d) :=
  ⟨apply_outline b d, check_apply hb d, apply_of_check_nil⟩

namespace Development

variable (L : Development) (N : Notation L.Part)

open Classical in
/-- What the validator reports of a statement, in any view: nothing when it
accepts everything printed of the statement, else that it does not. -/
noncomputable def problems (_ : View) (S : L.Stmt) : Array String :=
  if L.AcceptsAll N S then #[] else #["not validated"]

/-- The bundle the extractor writes of the development in the notation, for
the requests `rs`: each key a document cites, its statement hashed and
rendered in the views the document shows it in, with what the validator
reports of it. -/
noncomputable def extract (rs : List (Key × List View)) : Bundle :=
  bundleOf (L.world N) (L.problems N) rs

/-- A block of view `v` reads as its key's statement, formula by formula. A
prose sentence, or a rules figure, comes apart into formulas, each of which
reads, in the notation's grammar, only as the part of the statement it was
printed from; a block of any other view is one formula, which reads only as
the part the view shows. -/
def ReadsAs (v : View) (r : Body) (k : Key) : Prop :=
  match v with
  | "prose" => ∀ S, L.stmt k = some S → (L.anatomy N).Prose r S
  | "rules" => ∀ S, L.stmt k = some S → (L.anatomy N).Rules r S
  | _ => ∀ S, L.stmt k = some S → ∀ q, L.formula v S = some q → N.toValidator.ReadsPart (Body.text r).toList q

theorem readsAs_other {v : View} (hv : v ≠ "prose") (hw : v ≠ "rules") (r : Body) (k : Key) :
    L.ReadsAs N v r k =
      ∀ S, L.stmt k = some S → ∀ q, L.formula v S = some q → N.toValidator.ReadsPart (Body.text r).toList q := by
  unfold ReadsAs
  split <;> simp_all

/-- A document is Pollack-consistent: each of its blocks reads only as its
key's statement. -/
def Pollack (d : Doc) : Prop :=
  ∀ k v r, Piece.block k v r ∈ d → L.ReadsAs N v r k

/-- **Extraction is true.** The bundle the extractor writes is true of the
world the development presents in the notation. -/
theorem extract_true {rs : List (Key × List View)} {b : Bundle} (hb : b = L.extract N rs) :
    b.True (L.world N) id :=
  hb ▸ bundleOf_true fun _ S _ h _ => by
    unfold problems at h
    split at h
    · assumption
    · simp at h

/-- **A paper that checks clean is true.** If `check` reports nothing against a
bundle that is true of the world, the document is true of it: the splicer's
main theorem (`document_true`), for the world of a development. -/
theorem clean_true {b : Bundle} {d : Doc} (hb : b.True (L.world N) id) (hc : check b d = []) :
    d.True (L.world N) :=
  document_true hb hc

/-- A document that checks clean against a true bundle is Pollack-consistent. -/
theorem pollack_of_check {b : Bundle} {d : Doc} (hb : b.True (L.world N) id)
    (hc : check b d = []) : L.Pollack N d := by
  intro k v r hp
  by_cases hv : v = "prose"
  · subst hv
    intro S hS
    obtain ⟨S', hS', -, -, hP⟩ := L.document_pollack N hb hc hp
    rw [show (L.world N).stmt k = L.stmt k from rfl, hS] at hS'
    cases hS'
    exact hP
  by_cases hw : v = "rules"
  · subst hw
    intro S hS
    obtain ⟨S', hS', -, -, hP⟩ := L.document_pollack_rules N hb hc hp
    rw [show (L.world N).stmt k = L.stmt k from rfl, hS] at hS'
    cases hS'
    exact hP
  · rw [L.readsAs_other N hv hw]
    intro S hS q hq
    obtain ⟨S', hS', -, -, hP⟩ := L.document_pollack_formula N hb hc hv hw hp
    rw [show (L.world N).stmt k = L.stmt k from rfl, hS] at hS'
    cases hS'
    exact hP q hq

/-- **Checking is sound.** If `check` reports nothing against a bundle that
is true of the world the development presents in the notation, the document
is true of it, and each of its formulas reads only as the part of the
statement it was printed from: what the second arrow of the introduction's
diagram claims, given the first. -/
theorem check_sound {b : Bundle} {d : Doc} (hb : b.True (L.world N) id)
    (hc : check b d = []) : d.True (L.world N) ∧ L.Pollack N d :=
  ⟨L.clean_true N hb hc, L.pollack_of_check N hb hc⟩

/-- **A paper that checks clean is true, and reads only as Lean's.** If
`check` reports nothing against the bundle the extractor writes, the
document is true of the development, and each of its formulas reads only as
the part of the statement it was printed from: the two arrows of the
introduction's diagram, composed. -/
theorem paper_true {rs : List (Key × List View)} {b : Bundle} {d : Doc}
    (hb : b = L.extract N rs) (hc : check b d = []) : d.True (L.world N) ∧ L.Pollack N d :=
  L.check_sound N (L.extract_true N hb) hc

end Development

end SpliceModel
