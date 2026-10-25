/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBackSound

/-!
# Pruning keeps everything, or says so

The parser keeps at most two readings of each question, and of each reading
only one of each variant (`Imprimatur.Validate.keep`;
docs/pollack-consistency.md, layer 3). These are the two facts the proofs
use about it: what it keeps is among what it was given (`keep_subset`, in
`ReadBackSound`), and unless it says it dropped a reading, it keeps
everything it was given (`keep_mem`).
-/

namespace SpliceModel

open Imprimatur.Validate

section
variable {α : Type} [BEq α] (key : α → String)

/-- Once `keepGo` has dropped a reading, it says so to the end. -/
theorem keepGo_pruned_true : ∀ (xs : List α) (out : Array α) (keys : Array String),
    (keepGo key xs out keys true).2 = true
  | [], out, keys => rfl
  | y :: ys, out, keys => by
    simp only [keepGo]
    split
    · exact keepGo_pruned_true ys _ _
    · split
      · exact keepGo_pruned_true ys _ _
      · split
        · exact keepGo_pruned_true ys _ _
        · exact keepGo_pruned_true ys _ _

variable [LawfulBEq α]

/-- Unless it dropped a reading, `keepGo` keeps every reading it was given,
and every reading already kept. -/
theorem keepGo_mem : ∀ (xs : List α) (out : Array α) (keys : Array String) (res : Array α),
    keepGo key xs out keys false = (res, false) → (∀ x ∈ out, x ∈ res) ∧ (∀ x ∈ xs, x ∈ res)
  | [], out, keys, res, h => by
    simp only [keepGo, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨fun x hx => hx, fun x hx => by simp at hx⟩
  | y :: ys, out, keys, res, h => by
    simp only [keepGo] at h
    split at h
    · exact absurd (congrArg Prod.snd h) (by simp [keepGo_pruned_true])
    · split at h
      · rename_i hin
        obtain ⟨hout, hys⟩ := keepGo_mem ys out _ res h
        refine ⟨hout, fun x hx => ?_⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hout x (Array.contains_iff_mem.mp hin)
        · exact hys x hx
      · split at h
        · exact absurd (congrArg Prod.snd h) (by simp [keepGo_pruned_true])
        · obtain ⟨hout, hys⟩ := keepGo_mem ys (out.push y) _ res h
          refine ⟨fun x hx => hout x (Array.mem_push.mpr (Or.inl hx)), fun x hx => ?_⟩
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hout x (Array.mem_push.mpr (Or.inr rfl))
          · exact hys x hx

/-- Unless it dropped a reading, `keep` keeps everything. -/
theorem keep_mem (xs : Array α) (res : Array α) (h : keep key xs = (res, false)) : ∀ x ∈ xs, x ∈ res :=
  fun x hx => (keepGo_mem key xs.toList #[] #[] res h).2 x (Array.mem_def.mp hx)

end

end SpliceModel
