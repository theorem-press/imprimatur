import Stlc.Lang

/-! Type safety: preservation and progress.

The substitution lemma is proved as Pitts's paper suggests: typing is
*equivariant* (swapping two names in a term and its context preserves its
type), and depends on the context only at the term's free names. At an
abstraction, substitution renames the binder to a fresh name by swapping,
and equivariance carries the typing across the renaming. -/

namespace Stlc

/-! ## Free names -/

/-- The free names of a term. -/
def Tm.fv : Tm → List Atom
  | .var x => [x]
  | .lam x _ e => e.fv.filter (· != x)
  | .app e₁ e₂ => e₁.fv ++ e₂.fv
  | .unit => []

theorem mem_fv_lam {y x : Atom} {t : Ty} {e : Tm} :
    y ∈ (Tm.lam x t e).fv ↔ y ∈ e.fv ∧ y ≠ x := by
  simp [Tm.fv]

theorem fv_sub_atoms {y : Atom} : ∀ {e : Tm}, y ∈ e.fv → y ∈ e.atoms
  | .var _, h => by simpa [Tm.fv, Tm.atoms] using h
  | .lam _ _ e, h => by
    simp only [Tm.atoms, List.mem_cons]
    exact Or.inr (fv_sub_atoms (mem_fv_lam.mp h).1)
  | .app e₁ e₂, h => by
    simp only [Tm.fv, List.mem_append] at h
    simp only [Tm.atoms, List.mem_append]
    exact h.imp fv_sub_atoms fv_sub_atoms
  | .unit, h => by simp [Tm.fv] at h

theorem swapAtom_inj {a b x y : Atom} : swapAtom a b x = swapAtom a b y ↔ x = y := by
  constructor
  · intro h
    have := congrArg (swapAtom a b) h
    simpa [swapAtom_swapAtom] using this
  · intro h; rw [h]

/-- Swapping acts on free names pointwise. -/
theorem mem_fv_swap {a b y : Atom} : ∀ {e : Tm}, y ∈ (e.swap a b).fv ↔ swapAtom a b y ∈ e.fv
  | .var x => by
    simp only [Tm.swap, Tm.fv, List.mem_singleton]
    constructor
    · intro h; rw [h, swapAtom_swapAtom]
    · intro h; rw [← h, swapAtom_swapAtom]
  | .lam x t e => by
    simp only [Tm.swap]
    rw [mem_fv_lam, mem_fv_lam, mem_fv_swap]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun h => h₂ ?_⟩
      rw [← h, swapAtom_swapAtom]
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, fun h => h₂ ?_⟩
      rw [h, swapAtom_swapAtom]
  | .app e₁ e₂ => by
    simp only [Tm.swap, Tm.fv, List.mem_append]
    rw [mem_fv_swap, mem_fv_swap]
  | .unit => by simp [Tm.swap, Tm.fv]

theorem le_foldr_max {y : Nat} : ∀ {l : List Nat}, y ∈ l → y ≤ l.foldr max 0
  | _ :: _, .head _ => by simp only [List.foldr_cons]; omega
  | _ :: _, .tail _ h => by
    simp only [List.foldr_cons]
    have := le_foldr_max h
    omega

/-- A fresh name is not in the list it is fresh for. -/
theorem fresh_not_mem (l : List Nat) : fresh l ∉ l := by
  intro h
  have : l.foldr max 0 + 1 ≤ l.foldr max 0 := le_foldr_max h
  omega

/-! ## Typing is equivariant, and depends only on free names -/

/-- Swapping two names in a context. -/
def Ctx.swap (a b : Atom) (Γ : Ctx) : Ctx := Γ.map fun p => (swapAtom a b p.1, p.2)

theorem lookup_cons (Γ : Ctx) (z w : Atom) (t : Ty) :
    lookup ((z, t) :: Γ) w = if z = w then some t else lookup Γ w := by
  by_cases h : z = w
  · subst h; simp [lookup]
  · simp [lookup, h]

theorem lookup_swap (a b y : Atom) : ∀ Γ : Ctx,
    lookup (Ctx.swap a b Γ) y = lookup Γ (swapAtom a b y)
  | [] => rfl
  | (z, t) :: Γ => by
    show lookup ((swapAtom a b z, t) :: Ctx.swap a b Γ) y = _
    rw [lookup_cons, lookup_cons, lookup_swap a b y Γ]
    by_cases h : swapAtom a b z = y
    · have h' : z = swapAtom a b y := by rw [← h, swapAtom_swapAtom]
      simp [h', swapAtom_swapAtom]
    · have h' : z ≠ swapAtom a b y := fun e => h (by rw [e, swapAtom_swapAtom])
      simp [h, h']

/-- Typing is equivariant: swapping two names throughout a term and its
context preserves its type. -/
theorem HasType.swap (a b : Atom) {Γ : Ctx} {e : Tm} {t : Ty} (h : HasType Γ e t) :
    HasType (Ctx.swap a b Γ) (e.swap a b) t := by
  induction h with
  | var wf h =>
    refine .var trivial ?_
    rw [lookup_swap, swapAtom_swapAtom]; exact h
  | lam _ ih => exact .lam ih
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | unit => exact .unit trivial

/-- Typing depends on the context only at the term's free names. -/
theorem HasType.agree {Γ : Ctx} {e : Tm} {t : Ty} (h : HasType Γ e t) :
    ∀ {Δ : Ctx}, (∀ y ∈ e.fv, lookup Γ y = lookup Δ y) → HasType Δ e t := by
  induction h with
  | var _ h =>
    intro Δ hΔ
    refine .var trivial ?_
    rw [← hΔ _ (by simp [Tm.fv])]; exact h
  | @lam Γ x t₁ t₂ e _ ih =>
    intro Δ hΔ
    refine .lam (ih fun y hy => ?_)
    by_cases hyx : y = x
    · subst hyx; rw [lookup_cons, lookup_cons]; simp
    · rw [lookup_cons, lookup_cons]
      simp only [Ne.symm hyx, ite_false]
      exact hΔ y (mem_fv_lam.mpr ⟨hy, hyx⟩)
  | app _ _ ih₁ ih₂ =>
    intro Δ hΔ
    exact .app (ih₁ fun y hy => hΔ y (by simp [Tm.fv, hy]))
      (ih₂ fun y hy => hΔ y (by simp [Tm.fv, hy]))
  | unit => intro _ _; exact .unit trivial

/-! ## The substitution lemma -/

theorem lookup_cons_ne {Γ : Ctx} {x y : Atom} {t : Ty} (h : y ≠ x) :
    lookup ((x, t) :: Γ) y = lookup Γ y := by
  rw [lookup_cons]; simp [Ne.symm h]

theorem lookup_cons_self {Γ : Ctx} {x : Atom} {t : Ty} : lookup ((x, t) :: Γ) x = some t := by
  rw [lookup_cons]; simp

/-- Substitution preserves types. Γ' is the context `e` is typed in; it
gives `x` the type of `u`, and agrees with Γ at every other free name. -/
theorem subst_typing : ∀ (e : Tm) {Γ Γ' : Ctx} {x : Atom} {u : Tm} {t₁ t : Ty},
    HasType Γ' e t → (x ∈ e.fv → lookup Γ' x = some t₁) →
    (∀ y ∈ e.fv, y ≠ x → lookup Γ' y = lookup Γ y) →
    HasType Γ u t₁ → HasType Γ (subst x u e) t
  | .var y, Γ, Γ', x, u, t₁, t, he, hx, hΓ, hu => by
    cases he with
    | var _ h =>
      unfold subst
      by_cases hyx : y = x
      · subst hyx
        rw [hx (by simp [Tm.fv])] at h
        cases h
        simpa using hu
      · simp only [hyx, ite_false]
        refine .var trivial ?_
        rw [← hΓ y (by simp [Tm.fv]) hyx]; exact h
  | .app e₁ e₂, Γ, Γ', x, u, t₁, t, he, hx, hΓ, hu => by
    cases he with
    | app h₁ h₂ =>
      unfold subst
      exact .app
        (subst_typing e₁ h₁ (fun h => hx (by simp [Tm.fv, h]))
          (fun y hy => hΓ y (by simp [Tm.fv, hy])) hu)
        (subst_typing e₂ h₂ (fun h => hx (by simp [Tm.fv, h]))
          (fun y hy => hΓ y (by simp [Tm.fv, hy])) hu)
  | .unit, Γ, Γ', x, u, t₁, t, he, _, _, _ => by
    cases he with
    | unit _ => unfold subst; exact .unit trivial
  | .lam a ta e, Γ, Γ', x, u, t₁, t, he, hx, hΓ, hu => by
    cases he with
    | @lam _ _ _ t₂ _ hbody =>
      unfold subst
      simp only
      -- The fresh name the binder is renamed to.
      generalize hc : fresh (x :: a :: e.atoms ++ u.atoms) = c
      have hcf := fresh_not_mem (x :: a :: e.atoms ++ u.atoms)
      rw [hc] at hcf
      simp only [List.cons_append, List.mem_cons, List.mem_append, not_or] at hcf
      obtain ⟨hcx, hca, hce, hcu⟩ := hcf
      have hcfv : c ∉ e.fv := fun h => hce (fv_sub_atoms h)
      -- The body, renamed, typed in the renamed context.
      have hsw := hbody.swap a c
      simp only [Ctx.swap, List.map_cons] at hsw
      rw [show swapAtom a c a = c by simp [swapAtom]] at hsw
      refine .lam (subst_typing (e.swap a c) (t₁ := t₁) hsw ?_ ?_ ?_)
      · -- x, if free in the renamed body, has the type of u.
        intro hxfv
        have hx' := mem_fv_swap.mp hxfv
        have hxa : x ≠ a := by
          intro h; subst h; simp [swapAtom] at hx'; exact hcfv hx'
        have hxs : swapAtom a c x = x := by simp [swapAtom, hxa, Ne.symm hcx]
        rw [hxs] at hx'
        rw [lookup_cons_ne (Ne.symm hcx)]
        show lookup (Ctx.swap a c Γ') x = some t₁
        rw [lookup_swap, hxs]
        exact hx (mem_fv_lam.mpr ⟨hx', hxa⟩)
      · -- Elsewhere, the renamed context agrees with c : ta, Γ.
        intro y hy hyx
        by_cases hyc : y = c
        · subst hyc; simp [lookup]
        · rw [lookup_cons_ne hyc, lookup_cons_ne hyc]
          show lookup (Ctx.swap a c Γ') y = lookup Γ y
          rw [lookup_swap]
          have hy' := mem_fv_swap.mp hy
          have hya : y ≠ a := by
            intro h; subst h; simp [swapAtom] at hy'; exact hcfv hy'
          have hys : swapAtom a c y = y := by simp [swapAtom, hya, hyc]
          rw [hys] at hy' ⊢
          exact hΓ y (mem_fv_lam.mpr ⟨hy', hya⟩) hyx
      · -- u is still well typed with c bound: c is not free in it.
        exact hu.agree fun y hy => by
          have hyc : y ≠ c := fun h => hcu (h ▸ fv_sub_atoms hy)
          rw [lookup_cons_ne hyc]
termination_by e => e.size
decreasing_by
  all_goals simp_wf
  all_goals simp only [Tm.size, Tm.size_swap]
  all_goals omega

/-! ## Preservation and progress -/

/-- **Preservation.** Reduction preserves types. -/
theorem preservation {e e' : Tm} (hs : Step e e') :
    ∀ {Γ : Ctx} {t : Ty}, HasType Γ e t → HasType Γ e' t := by
  induction hs with
  | @beta x ta e v _ =>
    intro Γ t h
    cases h with
    | app h₁ h₂ =>
      cases h₁ with
      | lam hbody =>
        exact subst_typing e hbody (fun _ => lookup_cons_self)
          (fun y _ hyx => lookup_cons_ne hyx) h₂
  | app_left _ ih =>
    intro Γ t h
    cases h with
    | app h₁ h₂ => exact .app (ih h₁) h₂
  | app_right _ _ ih =>
    intro Γ t h
    cases h with
    | app h₁ h₂ => exact .app h₁ (ih h₂)

/-- A value of function type is an abstraction. -/
theorem canonical_arrow {Γ : Ctx} {v : Tm} {t₁ t₂ : Ty} (hv : IsValue v)
    (h : HasType Γ v (.arrow t₁ t₂)) : ∃ x e, v = .lam x t₁ e := by
  cases hv with
  | lam => cases h; exact ⟨_, _, rfl⟩
  | unit => cases h

/-- **Progress.** A closed, well-typed term is a value or reduces. -/
theorem progress {e : Tm} {t : Ty} (h : HasType [] e t) : IsValue e ∨ ∃ e', Step e e' := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h with
  | var _ h => subst hΓ; simp [lookup] at h
  | lam _ _ => exact .inl .lam
  | unit _ => exact .inl .unit
  | app h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ hΓ with hv₁ | ⟨e₁', hs₁⟩
    · rcases ih₂ hΓ with hv₂ | ⟨e₂', hs₂⟩
      · obtain ⟨x, e, rfl⟩ := canonical_arrow hv₁ h₁
        exact .inr ⟨_, .beta hv₂⟩
      · exact .inr ⟨_, .app_right hv₁ hs₂⟩
    · exact .inr ⟨_, .app_left hs₁⟩

end Stlc
