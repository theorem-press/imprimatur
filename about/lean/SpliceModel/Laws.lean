import SpliceModel.Basic

/-!
# The splicer's laws, and what `check` guarantees

DESIGN §18.2: locality, idempotence, the fixed point and slot preservation;
then Theorem 1, the soundness of `check` against an environment, and what an
attested check means when hashes do not collide.
-/

namespace SpliceModel

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
    | block k body =>
      simp only [regen]
      cases b k <;> rfl
    | text _ => rfl
    | check _ _ => rfl

/-- A bundle is well formed when no rendering has two slots with the same
identifier. -/
def WF (b : Bundle) : Prop := ∀ k e, b k = some e → (ids e.render).Nodup

theorem regen_regen {b : Bundle} (hb : WF b) (p : Piece) : regen b (regen b p) = regen b p := by
  cases p with
  | block k body =>
    cases h : b k with
    | none => simp [regen, h]
    | some e => simp [regen, h, fill_fill (hb k e h)]
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
  | block k' body =>
    cases he : b k' with
    | none => simp [regen, diags, he] at hx
    | some e =>
      simp only [regen, he, diags, fill_fill (hb k' e he)] at hx
      cases e.trusted <;> simp at hx
  | text _ => simp [regen, diags] at hx
  | check k' h =>
    cases he : b k' with
    | none => simp [regen, diags, he] at hx
    | some e =>
      simp only [regen, diags, he] at hx
      cases e.trusted <;> split at hx <;> simp at hx

/-- After `accept`, `check` reports no drift. -/
theorem not_drift_after_accept (b : Bundle) (d : Doc) (k : Key) :
    Diag.drift k ∉ check b (accept b d) := by
  intro h
  obtain ⟨p, hp, hx⟩ := mem_check.mp h
  simp only [accept, List.mem_map] at hp
  obtain ⟨q, _, rfl⟩ := hp
  cases q with
  | check k' h =>
    cases he : b k' with
    | none => simp [diags, he] at hx
    | some e =>
      simp only [he, diags, Option.map_some, Option.getD_some] at hx
      cases e.trusted <;> simp at hx
  | text _ => simp [diags] at hx
  | block k' body =>
    simp only [diags] at hx
    cases he : b k' with
    | none => simp [he] at hx
    | some e => simp only [he] at hx; cases e.trusted <;> split at hx <;> simp at hx

/-! ## What `check` guarantees (Theorem 1) -/

section
variable {Stmt : Type} {render : Stmt → Body} {hash : Stmt → Nat} {E : Env Stmt} {d : Doc}

/-- **Theorem 1, blocks.** If `check` reports nothing, every block's key is
a constant whose proof is trusted, and the block is the rendering of its
statement, with the authors' slot text. -/
theorem block_sound (hc : check (extract render hash E) d = []) {k : Key} {body : Body}
    (hp : Piece.block k body ∈ d) :
    ∃ T, E.stmt k = some T ∧ E.trusted k = true ∧ body = fill (slots body) (render T) := by
  have h := check_eq_nil.mp hc _ hp
  simp only [diags, extract] at h
  cases hs : E.stmt k with
  | none => simp [hs] at h
  | some T =>
    simp only [hs, Option.map_some] at h
    refine ⟨T, rfl, ?_, ?_⟩
    · cases ht : E.trusted k <;> simp_all
    · by_cases hf : body = fill (slots body) (render T)
      · exact hf
      · simp [hf] at h

/-- **Theorem 1, checked prose.** If `check` reports nothing, every
`\leancheck`'s key is a constant whose proof is trusted, and whose
statement has the recorded hash. -/
theorem check_sound (hc : check (extract render hash E) d = []) {k : Key} {h : Nat}
    (hp : Piece.check k h ∈ d) :
    ∃ T, E.stmt k = some T ∧ E.trusted k = true ∧ hash T = h := by
  have h' := check_eq_nil.mp hc _ hp
  simp only [diags, extract] at h'
  cases hs : E.stmt k with
  | none => simp [hs] at h'
  | some T =>
    simp only [hs, Option.map_some] at h'
    refine ⟨T, rfl, ?_, ?_⟩
    · cases ht : E.trusted k <;> simp_all
    · by_cases hf : hash T = h
      · exact hf
      · simp [hf] at h'

/-- **Attested prose.** When hashes do not collide, prose checked against
statement `T₀` and accepted still faces `T₀`: if `check` reports nothing,
the key's statement is `T₀`. -/
theorem attested (hinj : ∀ T T', hash T = hash T' → T = T') (hc : check (extract render hash E) d = [])
    {k : Key} {T₀ : Stmt} (hp : Piece.check k (hash T₀) ∈ d) : E.stmt k = some T₀ := by
  obtain ⟨T, hs, _, hh⟩ := check_sound hc hp
  rw [hs, hinj T T₀ hh]

end

end SpliceModel
