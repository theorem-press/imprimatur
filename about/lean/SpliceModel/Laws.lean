/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Basic

/-!
# The splicer's laws, and what `check` guarantees

DESIGN §18.2: locality, idempotence, the fixed point and slot preservation;
then Theorem 1, in two stages. First the generated mathematics: a block that
checks clean against a true bundle shows a statement Lean proved, rendered,
and reads back as it. Then the attested prose: a check that checks clean
names, by its hash, a statement Lean proved, and, when hashes do not
collide, the statement the prose was checked against. Together: a document
that checks clean against a true bundle is true. Last, the bundle of a
world is true of it.
-/

namespace SpliceModel

open Imprimatur

/-! ## Slots -/

theorem lookup_cons_ne {i j : SlotId} {v : String} {l : List (SlotId × String)} (h : i ≠ j) :
    lookup i ((j, v) :: l) = lookup i l := by
  simp [lookup, h]

/-- Text for a slot the rendering does not have changes nothing. -/
theorem fill_cons_of_not_mem {i : SlotId} {v : String} {S : List (SlotId × String)} :
    ∀ {r : Body}, i ∉ ids r → fill ((i, v) :: S) r = fill S r
  | [], _ => rfl
  | .gen s :: r, h => by
    simp only [fill]
    rw [fill_cons_of_not_mem (by simpa [ids] using h)]
  | .slot j t :: r, h => by
    simp only [ids, List.mem_cons, not_or] at h
    simp only [fill]
    rw [lookup_cons_ne (Ne.symm h.1), fill_cons_of_not_mem h.2]

/-- Filling twice is filling once, when the rendering's slots are distinct. -/
theorem fill_fill {old : List (SlotId × String)} :
    ∀ {r : Body}, (ids r).Nodup → fill (slots (fill old r)) r = fill old r
  | [], _ => rfl
  | .gen s :: r, h => by
    simp only [fill, slots]
    rw [fill_fill (by simpa [ids] using h)]
  | .slot i t :: r, h => by
    simp only [ids, List.nodup_cons] at h
    have e : lookup i ((i, (lookup i old).getD t) :: slots (fill old r)) =
        some ((lookup i old).getD t) := by simp [lookup]
    simp only [fill, slots]
    rw [e, Option.getD_some, fill_cons_of_not_mem h.1, fill_fill h.2]

/-- **Slot preservation.** A slot the rendering has keeps the authors' text. -/
theorem slot_kept {i : SlotId} {t : String} {old : List (SlotId × String)} :
    ∀ {r : Body}, i ∈ ids r → lookup i old = some t → lookup i (slots (fill old r)) = some t
  | [], hi, _ => by simp [ids] at hi
  | .gen s :: r, hi, ho => by
    simp only [fill, slots]
    exact slot_kept (by simpa [ids] using hi) ho
  | .slot j d :: r, hi, ho => by
    simp only [fill, slots, lookup]
    by_cases hij : i = j
    · subst hij
      simp [ho]
    · simp only [hij, ↓reduceIte]
      simp only [ids, List.mem_cons, hij, false_or] at hi
      exact slot_kept hi ho

/-! ## `apply` -/

/-- **Locality.** `apply` changes nothing outside generated blocks: the
document's outline (its text, checks, and blocks without their bodies) is
the same. -/
theorem apply_outline (b : Bundle) (d : Doc) : (apply b d).map outline = d.map outline := by
  induction d with
  | nil => rfl
  | cons p d ih =>
    simp only [apply, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    cases p with
    | block k v body =>
      simp only [regen]
      split <;> rfl
    | text _ => rfl
    | check _ _ => rfl

/-- A bundle is well formed when no rendering has two slots with the same
identifier. -/
def WF (b : Bundle) : Prop := ∀ k v r, rendering b k v = some r → (ids r).Nodup

theorem regen_regen {b : Bundle} (hb : WF b) (p : Piece) : regen b (regen b p) = regen b p := by
  cases p with
  | block k v body =>
    cases h : rendering b k v with
    | none => simp [regen, h]
    | some r => simp [regen, h, fill_fill (hb k v r h)]
  | text _ => rfl
  | check _ _ => rfl

/-- **Idempotence.** Applying a bundle twice is applying it once. -/
theorem apply_apply {b : Bundle} (hb : WF b) (d : Doc) : apply b (apply b d) = apply b d := by
  simp only [apply, List.map_map]
  exact List.map_congr_left fun p _ => regen_regen hb p

/-! ## `check` -/

theorem check_append (b : Bundle) (d₁ d₂ : Doc) : check b (d₁ ++ d₂) = check b d₁ ++ check b d₂ := by
  induction d₁ with
  | nil => rfl
  | cons p d ih => simp [check, ih]

theorem mem_check {b : Bundle} {x : Diag} : ∀ {d : Doc}, x ∈ check b d ↔ ∃ p ∈ d, x ∈ diags b p
  | [] => by simp [check]
  | p :: d => by simp [check, mem_check]

/-- `check` reports nothing exactly when it reports nothing about each piece. -/
theorem check_eq_nil {b : Bundle} {d : Doc} : check b d = [] ↔ ∀ p ∈ d, diags b p = [] := by
  constructor
  · intro h p hp
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have : x ∈ check b d := mem_check.mpr ⟨p, hp, hx⟩
    simp [h] at this
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨p, hp, hx⟩ := mem_check.mp hx
    simp [h p hp] at hx

/-- **The fixed point.** After `apply`, `check` reports no block as stale. -/
theorem not_stale_after_apply {b : Bundle} (hb : WF b) (d : Doc) (k : Key) :
    Diag.stale k ∉ check b (apply b d) := by
  intro h
  obtain ⟨p, hp, hx⟩ := mem_check.mp h
  simp only [apply, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  cases q with
  | block k' v body =>
    cases he : b.find? k' with
    | none => simp [regen, rendering, diags, he] at hx
    | some e =>
      cases hv : e.statement.view? v with
      | none => simp [regen, rendering, diags, he, hv] at hx
      | some r =>
        have hr : rendering b k' v = some r := by simp [rendering, he, hv]
        simp only [regen, hr, diags, he, hv, fill_fill (hb k' v r hr)] at hx
        cases ht : e.verdict <;> simp [ht] at hx <;> (try split at hx) <;> simp at hx
  | text _ => simp [regen, diags] at hx
  | check k' h =>
    cases he : b.find? k' with
    | none => simp [regen, diags, he] at hx
    | some e =>
      simp only [regen, diags, he] at hx
      cases ht : e.verdict <;> cases hh : e.statement.stmtHash <;> simp [ht, hh] at hx <;>
        (try split at hx) <;> simp at hx

/-- After `accept`, `check` reports no drift. -/
theorem not_drift_after_accept (b : Bundle) (d : Doc) (k : Key) :
    Diag.drift k ∉ check b (accept b d) := by
  intro h
  obtain ⟨p, hp, hx⟩ := mem_check.mp h
  simp only [accept, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  cases q with
  | check k' h =>
    cases he : b.find? k' with
    | none => simp [diags, he] at hx
    | some e =>
      simp only [he, Option.bind, diags] at hx
      cases ht : e.verdict <;> cases hh : e.statement.stmtHash <;> simp [ht, hh] at hx
  | text _ => simp [diags] at hx
  | block k' v body =>
    simp only [diags] at hx
    cases he : b.find? k' with
    | none => simp [he] at hx
    | some e =>
      simp only [he] at hx
      cases ht : e.verdict <;> cases hr : e.statement.view? v <;> simp [ht, hr] at hx <;>
        (try split at hx) <;> (try split at hx) <;> simp at hx

/-! ## What `check` guarantees (Theorem 1)

First the generated mathematics, which needs no hashes; then the attested
prose, which does. -/

section
variable {W : World} {b : Bundle} {d : Doc}

/-- A block that checks clean: the bundle has the key, its verdict is true,
it renders the view, the body is the rendering with the authors' slot text,
and the rendering has no problems. -/
theorem block_clean (hc : check b d = []) {k : Key} {v : View} {body : Body}
    (hp : Piece.block k v body ∈ d) :
    ∃ e r, b.find? k = some e ∧ e.verdict = true ∧ e.statement.view? v = some r ∧
      body = fill (slots body) r ∧ e.statement.problems v = #[] := by
  have h := check_eq_nil.mp hc _ hp
  simp only [diags] at h
  cases he : b.find? k with
  | none => simp [he] at h
  | some e =>
    simp only [he] at h
    cases hv : e.statement.view? v with
    | none => simp [hv] at h
    | some r =>
      simp only [hv] at h
      refine ⟨e, r, rfl, ?_, hv, ?_, ?_⟩
      · cases ht : e.verdict <;> simp_all
      · by_cases hf : body = fill (slots body) r
        · exact hf
        · simp [hf] at h
      · by_cases hq : e.statement.problems v = #[]
        · exact hq
        · simp [hq] at h

/-- **Theorem 1, generated mathematics.** If `check` reports nothing against
a true bundle, every block shows a statement Lean proved, rendered in its
view with the authors' slot text, and the rendering reads back as the
statement. -/
theorem block_true (hb : b.True W id) (hc : check b d = []) {k : Key} {v : View} {body : Body}
    (hp : Piece.block k v body ∈ d) : (Piece.block k v body).True W := by
  obtain ⟨e, r, he, ht, hv, hf, hq⟩ := block_clean hc hp
  obtain ⟨S, hS, hi⟩ := (hb k e he).statement
  have hm := Image.view?_mem hv
  refine ⟨S, r, hS, ?_, hi.views v r hm, hf, hi.faithful v r hm hq⟩
  rw [← (hb k e he).verdict]
  exact ht

/-- A check that checks clean: the bundle has the key, its verdict is true,
and its statement hash is the recorded one. -/
theorem check_clean (hc : check b d = []) {k : Key} {h : Hash} (hp : Piece.check k h ∈ d) :
    ∃ e, b.find? k = some e ∧ e.verdict = true ∧ e.statement.stmtHash = some h := by
  have h' := check_eq_nil.mp hc _ hp
  simp only [diags] at h'
  cases he : b.find? k with
  | none => simp [he] at h'
  | some e =>
    simp only [he] at h'
    cases hh : e.statement.stmtHash with
    | none => simp [hh] at h'
    | some h₀ =>
      simp only [hh] at h'
      refine ⟨e, rfl, ?_, ?_⟩
      · cases ht : e.verdict <;> simp_all
      · by_cases heq : h₀ = h
        · rw [hh, heq]
        · simp [heq] at h'

/-- **Theorem 1, attested prose.** If `check` reports nothing against a true
bundle, every check names, by its hash, a statement Lean proved. -/
theorem check_true (hb : b.True W id) (hc : check b d = []) {k : Key} {h : Hash}
    (hp : Piece.check k h ∈ d) : (Piece.check k h).True W := by
  obtain ⟨e, he, ht, hh⟩ := check_clean hc hp
  obtain ⟨S, hS, hi⟩ := (hb k e he).statement
  refine ⟨S, hS, ?_, hi.stmtHash h hh ▸ rfl⟩
  rw [← (hb k e he).verdict]
  exact ht

/-- **The typeset mathematics is true.** A document that checks clean against
a true bundle is true of the world. -/
theorem document_true (hb : b.True W id) (hc : check b d = []) : d.True W := by
  intro p hp
  cases p with
  | text _ => trivial
  | block k v body => exact block_true hb hc hp
  | check k h => exact check_true hb hc hp

/-- **Attested prose faces its statement.** When hashes do not collide, prose
checked against statement `T₀`, and carrying its hash, still faces `T₀`: if
`check` reports nothing against a true bundle, the key's statement is `T₀`. -/
theorem attested (hinj : ∀ S S', W.hash S = W.hash S' → S = S') (hb : b.True W id)
    (hc : check b d = []) {k : Key} {T₀ : W.Stmt} (hp : Piece.check k (W.hash T₀) ∈ d) :
    W.stmt k = some T₀ := by
  obtain ⟨S, hS, _, hh⟩ := check_true hb hc hp
  rw [hS, hinj S T₀ hh]

end

/-! ## The bundle of a world is true of it -/

section
variable {W : World} {views : List View} {problems : View → W.Stmt → Array String} {keys : List Key}

/-- The problems an honest entry records for a view are the validator's. -/
theorem entryOf_problems {k : Key} {S : W.Stmt} {v : View} (hv : v ∈ views) :
    (entryOf W views problems k S).statement.problems v = problems v S := by
  simp only [entryOf, Image.problems, List.find?_toArray]
  cases hf : (views.map fun v => (v, problems v S)).find? (·.1 == v) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf (v, problems v S) (List.mem_map_of_mem hv)
    simp at this
  | some p =>
    have hp := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    simp only [beq_iff_eq] at hp
    obtain ⟨v', _, hv'⟩ := List.mem_map.mp hm
    simp only [Option.map_some, Option.getD_some]
    rw [← hv'] at hp ⊢
    simp only at hp
    rw [hp]

/-- **An honest extractor's bundle is true.** When a rendering the validator
finds no problem in reads back as its statement, the bundle of a world is
true of it. -/
theorem bundleOf_true
    (hval : ∀ v S r, problems v S = #[] → W.render v S = some r → W.Reads r S) :
    (bundleOf W views problems keys).True W id := by
  intro k e he
  simp only [Imprimatur.Bundle.find?, bundleOf, List.find?_toArray, Option.map_eq_some_iff] at he
  obtain ⟨⟨k', e'⟩, hf, rfl⟩ := he
  have hk := List.find?_some hf
  have hm := List.mem_of_find?_eq_some hf
  simp only [beq_iff_eq] at hk
  subst hk
  obtain ⟨k₀, _, hk₀⟩ := List.mem_filterMap.mp hm
  obtain ⟨S, hS, hpair⟩ := Option.map_eq_some_iff.mp hk₀
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, rfl⟩ := hpair
  refine ⟨rfl, ⟨S, hS, ?_⟩, rfl⟩
  refine ⟨fun h hh => ?_, fun h hh => ?_, fun v t ht => ?_, fun v t ht hq => ?_⟩
  · simpa [entryOf] using hh.symm
  · simpa [entryOf] using hh.symm
  · simp only [entryOf, List.mem_toArray, List.mem_filterMap, Option.map_eq_some_iff,
      Prod.mk.injEq] at ht
    obtain ⟨v', _, r, hr, rfl, rfl⟩ := ht
    exact hr
  · dsimp only at hq
    simp only [entryOf, List.mem_toArray, List.mem_filterMap, Option.map_eq_some_iff,
      Prod.mk.injEq] at ht
    obtain ⟨v', hv', r, hr, rfl, rfl⟩ := ht
    rw [entryOf_problems hv'] at hq
    exact hval v' S r hq hr

end

end SpliceModel
