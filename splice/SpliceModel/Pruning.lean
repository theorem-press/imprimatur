/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBackSound

/-!
# Pruning keeps a variant of everything, or says so

The parser keeps at most two readings of each question, and of each reading
only one of each variant (`Imprimatur.Validate.keep`;
docs/pollack-consistency.md, layer 3). These are the two facts the proofs
use about it: what it keeps is among what it was given (`keep_subset`, in
`ReadBackSound`), and unless it says it dropped a reading, everything it was
given has a variant kept (`keep_dominates`).
-/

namespace SpliceModel

open Imprimatur.Validate

section
variable {α : Type} (key : α → String) (same : α → α → Bool)

/-- Once `keepGo` has dropped a reading, it says so to the end. -/
theorem keepGo_pruned_true : ∀ (xs : List α) (out : Array α) (keys : Array String),
    (keepGo key same xs out keys true).2 = true
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

/-- `x` has a variant among `res`: one with its key, the same. -/
def Dominated (res : Array α) (x : α) : Prop := ∃ y ∈ res, key x = key y ∧ same x y = true

variable (hrefl : ∀ x, same x x = true)
  (htrans : ∀ x y z, same x y = true → same y z = true → same x z = true)
include hrefl htrans

/-- Unless it dropped a reading, `keepGo` keeps a variant of every reading
it was given, and of every reading already kept. -/
theorem keepGo_dominates : ∀ (xs : List α) (out : Array α) (keys : Array String) (res : Array α),
    keepGo key same xs out keys false = (res, false) →
    (∀ x ∈ out, Dominated key same res x) ∧ (∀ x ∈ xs, Dominated key same res x)
  | [], out, keys, res, h => by
    simp only [keepGo, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨fun x hx => ⟨x, hx, rfl, hrefl x⟩, fun x hx => by simp at hx⟩
  | y :: ys, out, keys, res, h => by
    simp only [keepGo] at h
    split at h
    · exact absurd (congrArg Prod.snd h) (by simp [keepGo_pruned_true])
    · split at h
      · rename_i hany
        obtain ⟨hout, hys⟩ := keepGo_dominates ys out _ res h
        refine ⟨hout, fun x hx => ?_⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp only [Array.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hany
          obtain ⟨n, hn, hkz, hsz⟩ := hany
          obtain ⟨w, hw, hkw, hsw⟩ := hout out[n] (Array.getElem_mem hn)
          exact ⟨w, hw, hkz.symm.trans hkw, htrans _ _ _ hsz hsw⟩
        · exact hys x hx
      · split at h
        · exact absurd (congrArg Prod.snd h) (by simp [keepGo_pruned_true])
        · obtain ⟨hout, hys⟩ := keepGo_dominates ys (out.push y) _ res h
          refine ⟨fun x hx => hout x (Array.mem_push.mpr (Or.inl hx)), fun x hx => ?_⟩
          rw [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hout x (Array.mem_push.mpr (Or.inr rfl))
          · exact hys x hx

/-- Unless it dropped a reading, `keep` keeps a variant of everything. -/
theorem keep_dominates (xs : Array α) (res : Array α) (h : keep key same xs = (res, false)) :
    ∀ x ∈ xs, Dominated key same res x :=
  fun x hx => (keepGo_dominates key same hrefl htrans xs.toList #[] #[] res h).2 x (Array.mem_def.mp hx)

end

/-- Variants are the same by their second parts: reflexively. -/
theorem same_snd_refl {α β : Type} [BEq β] [LawfulBEq β] (x : α × β) : (x.2 == x.2) = true :=
  beq_self_eq_true _

/-- Variants are the same by their second parts: transitively. -/
theorem same_snd_trans {α β : Type} [BEq β] [LawfulBEq β] (x y z : α × β)
    (h₁ : (x.2 == y.2) = true) (h₂ : (y.2 == z.2) = true) : (x.2 == z.2) = true := by
  rw [beq_iff_eq] at h₁ h₂ ⊢
  exact h₁.trans h₂

end SpliceModel
