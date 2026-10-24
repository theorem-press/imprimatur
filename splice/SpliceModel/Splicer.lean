/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice

/-!
# Theorems about the splicer that runs

These are about the functions the `imprimatur` binary executes, not about a
model of them (docs/verified-splicer.md). `Splice.plan` is what `apply`,
`check` and `migrate-slots` call; `apply` writes its `outputs` only when it
reports no error.

- **Text outside items never changes:** a file `apply` would write is its
  chunks, with each text chunk as it was, and each item the same item
  (`planOnce_text`, `planOnce_items`).
- **Idempotence and the fixed point:** when `apply` would write something
  and reports no error, applying the bundle again to what it wrote finds
  nothing to write, nothing to change and no error (`plan_fixed_point`).
  This holds because `plan` checks it of its own output before anything is
  written; the theorem says the check means what it says.

The scanner is lossless (`Splice.Core.Scan.print_scan`), and an ordinary
slot merge keeps the authors' text (`Splice.Core.Slots.mergeBody_keeps`).
-/

namespace SpliceModel.Splicer

open Splice

/-! ## Text outside items never changes -/

/-- What a chunk holds if it is text. -/
def textOf : Core.Scan.Chunk → Option (List Char)
  | .text r => some r
  | .item _ _ => none

/-- What a chunk holds if it is an item: the item, without its characters. -/
def itemOf : Core.Scan.Chunk → Option Item
  | .text _ => none
  | .item it _ => some it

theorem rewriteChunks_text (edits : List (Nat × Array Edit)) (cs : List Core.Scan.Chunk) :
    (rewriteChunks edits cs).map textOf = cs.map textOf := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [rewriteChunks, List.map_cons] at *
    rw [ih]
    cases c with
    | text r => rfl
    | item it raw => dsimp only; split <;> rfl

theorem rewriteChunks_items (edits : List (Nat × Array Edit)) (cs : List Core.Scan.Chunk) :
    (rewriteChunks edits cs).map itemOf = cs.map itemOf := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [rewriteChunks, List.map_cons] at *
    rw [ih]
    cases c with
    | text r => rfl
    | item it raw => dsimp only; split <;> rfl

/-- The chunks `apply` would write for a file are that file's chunks,
rewritten. -/
theorem planOnce_rewritten {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts}
    {fi : Nat} {cs : List Core.Scan.Chunk} (h : (fi, cs) ∈ (planOnce doc b o).rewritten) :
    ∃ f edits, doc.files.toList[fi]? = some f ∧ cs = rewriteChunks edits f.chunks := by
  simp only [planOnce, List.mem_toArray, List.mem_filterMap, List.mem_map, Option.map_eq_some_iff,
    Prod.mk.injEq] at h
  obtain ⟨⟨f, fi', r⟩, ⟨⟨f', fi''⟩, hmem, heq⟩, cs', hr, rfl, rfl⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hf := List.mem_zipIdx_iff_getElem?.mp hmem
  simp only [planFile] at hr
  split at hr
  · cases hr
  · cases hr
    exact ⟨f', _, hf, rfl⟩

/-- **Text outside items never changes:** the text chunks of a file `apply`
would write are the file's, in order. -/
theorem planOnce_text {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts}
    {fi : Nat} {cs : List Core.Scan.Chunk} (h : (fi, cs) ∈ (planOnce doc b o).rewritten) :
    ∃ f, doc.files.toList[fi]? = some f ∧ cs.map textOf = f.chunks.map textOf := by
  obtain ⟨f, edits, hf, rfl⟩ := planOnce_rewritten h
  exact ⟨f, hf, rewriteChunks_text _ _⟩

/-- **Items stay where they are:** a file `apply` would write has the same
items as before, in order; only their characters may change. -/
theorem planOnce_items {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts}
    {fi : Nat} {cs : List Core.Scan.Chunk} (h : (fi, cs) ∈ (planOnce doc b o).rewritten) :
    ∃ f, doc.files.toList[fi]? = some f ∧ cs.map itemOf = f.chunks.map itemOf := by
  obtain ⟨f, edits, hf, rfl⟩ := planOnce_rewritten h
  exact ⟨f, hf, rewriteChunks_items _ _⟩

/-! ## Idempotence and the fixed point -/

theorem hasErrors_append (a b : Array Splice.Diag) : hasErrors (a ++ b) = (hasErrors a || hasErrors b) := by
  simp only [hasErrors, Array.any_append]

/-- When there is nothing to write, `plan` is `planOnce`. -/
theorem plan_of_quiet {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts}
    (h : (planOnce doc b o).outputs = #[]) : plan doc b o = planOnce doc b o := by
  simp [plan, h]

/-- `plan` writes what `planOnce` would. -/
theorem plan_outputs (doc : Splice.Doc) (b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict) (o : ApplyOpts) :
    (plan doc b o).outputs = (planOnce doc b o).outputs := by
  unfold plan; dsimp only; split <;> rfl

/-- `plan` reports the changes `planOnce` finds. -/
theorem plan_changes (doc : Splice.Doc) (b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict) (o : ApplyOpts) :
    (plan doc b o).changes = (planOnce doc b o).changes := by
  unfold plan; dsimp only; split <;> rfl

/-- Every diagnostic `fixedPointDiag` gives is an error. -/
theorem fixedPointDiag_error {again : Outcome} {d : Splice.Diag} (h : fixedPointDiag again = some d) :
    d.severity = .error := by
  unfold fixedPointDiag at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

/-- Every diagnostic `rescanDiag` gives is an error. -/
theorem rescanDiag_error {doc : Splice.Doc} {fi : Nat} {cs : List Core.Scan.Chunk} {d : Splice.Diag}
    (h : rescanDiag doc fi cs = some d) : d.severity = .error := by
  unfold rescanDiag at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

theorem hasErrors_of_error {ds : Array Splice.Diag} (h : ∀ d ∈ ds, Splice.Diag.severity d = .error)
    (hne : ds ≠ #[]) : hasErrors ds = true := by
  obtain ⟨d, hd⟩ : ∃ d, d ∈ ds := by
    cases ds with
    | mk l => cases l with
      | nil => exact absurd rfl hne
      | cons d _ => exact ⟨d, by simp⟩
  simp only [hasErrors, Array.any_eq_true]
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hd
  exact ⟨i, hi, by rw [h _ hd]; rfl⟩

/-- When the checks of what `apply` would write find no error, it scans
again as built, and planning again finds nothing to do. -/
theorem checkDiags_ok {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts} {out : Outcome}
    (h : hasErrors (checkDiags doc b o out) = false) :
    rescanDiags doc out = #[] ∧ fixedPointDiag (planOnce (rewrittenDoc doc out) b o) = none := by
  unfold checkDiags at h
  dsimp only at h
  by_cases hr : rescanDiags doc out = #[]
  · refine ⟨hr, ?_⟩
    rw [hr] at h
    simp only [Array.isEmpty_empty, ite_true] at h
    cases hf : fixedPointDiag (planOnce (rewrittenDoc doc out) b o) with
    | none => rfl
    | some d =>
      rw [hf] at h
      have := fixedPointDiag_error hf
      change hasErrors #[d] = false at h
      have he : hasErrors #[d] = true :=
        hasErrors_of_error (by intro x hx; simp at hx; subst hx; exact this) (by simp)
      rw [he] at h; cases h
  · exfalso
    have hne : (rescanDiags doc out).isEmpty = false := by simpa [Array.isEmpty_iff] using hr
    rw [hne] at h
    simp only [Bool.false_eq_true, ite_false] at h
    have : hasErrors (rescanDiags doc out) = true := by
      apply hasErrors_of_error _ hr
      intro d hd
      simp only [rescanDiags, List.mem_toArray, List.mem_filterMap] at hd
      obtain ⟨p, _, hd⟩ := hd
      exact rescanDiag_error hd
    rw [this] at h; cases h

/-- **Idempotence and the fixed point.** If `apply` would write something
and reports no error, then applying the same bundle with the same options to
what it would write finds nothing to write, nothing to change (so `check`
reports nothing stale) and no error. -/
theorem plan_fixed_point {doc : Splice.Doc} {b : Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict} {o : ApplyOpts}
    (hok : hasErrors (plan doc b o).diags = false) (hout : (plan doc b o).outputs ≠ #[]) :
    let again := plan (rewrittenDoc doc (planOnce doc b o)) b o
    again.outputs = #[] ∧ again.changes = #[] ∧ hasErrors again.diags = false := by
  intro again
  rw [plan_outputs] at hout
  unfold plan at hok
  dsimp only at hok
  split at hok
  · rename_i hc
    simp only [Bool.or_eq_true, Array.isEmpty_iff] at hc
    rcases hc with hc | hc
    · rw [hc] at hok; cases hok
    · exact absurd hc hout
  · simp only [hasErrors_append, Bool.or_eq_false_iff] at hok
    obtain ⟨_, hfix⟩ := checkDiags_ok hok.2
    unfold fixedPointDiag at hfix
    split at hfix
    · cases hfix
    · rename_i herr
      split at hfix
      · cases hfix
      · rename_i hch
        split at hfix
        · rename_i houts
          have hq : (planOnce (rewrittenDoc doc (planOnce doc b o)) b o).outputs = #[] := by
            simpa [Array.isEmpty_iff] using houts
          show (plan _ b o).outputs = #[] ∧ (plan _ b o).changes = #[] ∧ hasErrors (plan _ b o).diags = false
          rw [plan_of_quiet hq]
          refine ⟨hq, ?_, by simpa using herr⟩
          cases hc : (planOnce (rewrittenDoc doc (planOnce doc b o)) b o).changes with
          | mk l => cases l with
            | nil => rfl
            | cons ch _ => simp [hc] at hch
        · cases hfix

end SpliceModel.Splicer
