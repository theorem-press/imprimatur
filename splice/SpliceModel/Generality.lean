/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBack

/-!
# Generality, and the laws of sorts

The parser prunes the sorts a reading can have, by the rule that a reading
of unknown sort stands for all its other sorts (docs/pollack-consistency.md,
layer 2). What makes that sound is *generality*: a preorder on sorts, `*`
at the top, under which the algebra of sorts is monotone (`Lawful`), and
under which the grammar's readings are monotone too (`Reads.mono`): a more
general question admits the same answer, more generally. The laws are what
the extractor's algebra of Lean's types must satisfy; until proved of it,
the theorems that use them are conditional on it.
-/

namespace SpliceModel

open Imprimatur.Validate

/-- Bindings `env'` are at least as general as `env`: they bind a subset of
the type variables, each to a sort at least as general. -/
def EnvLe (le : String → String → Prop) (env env' : Env) : Prop :=
  ∀ x ∈ env', ∃ s, (x.1, s) ∈ env ∧ le s x.2

/-- The laws of a sort algebra: a preorder of generality with `*` at the
top, under which compatibility, a hole's expected sort and binding are
monotone. -/
structure Lawful (A : SortAlgebra) where
  /-- `le s s'`: `s'` is at least as general as `s`. -/
  le : String → String → Prop
  /-- reflexive -/
  refl : ∀ s, le s s
  /-- transitive -/
  trans : ∀ {s t u}, le s t → le t u → le s u
  /-- the unknown sort is the most general -/
  top : ∀ s, le s "*"
  /-- a more general reading is accepted wherever a less general one is,
  and a more general question accepts whatever a less general one does -/
  accept : ∀ {f f' e e'}, le f f' → le e e' → A.compat f e = true → A.compat f' e' = true
  /-- more general bindings make a hole's sort more general -/
  expected_mono : ∀ {env env'} (s : String), EnvLe le env env' → le (A.expected env s) (A.expected env' s)
  /-- more general bindings, bound to a more general sort, stay more general -/
  bind_mono : ∀ {env env'} (s : String) {f f'}, EnvLe le env env' → le f f' →
    EnvLe le (A.bind env s f) (A.bind env' s f')

namespace Lawful

variable {A : SortAlgebra} (L : Lawful A)

theorem envLe_refl (env : Env) : EnvLe L.le env env :=
  fun x hx => ⟨x.2, hx, L.refl x.2⟩

theorem envLe_trans {e₁ e₂ e₃ : Env} (h₁ : EnvLe L.le e₁ e₂) (h₂ : EnvLe L.le e₂ e₃) : EnvLe L.le e₁ e₃ := by
  intro x hx
  obtain ⟨s, hs, hle⟩ := h₂ x hx
  obtain ⟨s', hs', hle'⟩ := h₁ (x.1, s) hs
  exact ⟨s', hs', L.trans hle' hle⟩

/-- The empty bindings are the most general. -/
theorem envLe_empty (env : Env) : EnvLe L.le env #[] :=
  fun x hx => by simp at hx

/-- A more general question: the same span, precedence and exclusion, a
more general sort or bindings. -/
def QuestionLe : Question → Question → Prop
  | .expr s p x i j, .expr s' p' x' i' j' => L.le s s' ∧ p = p' ∧ x = x' ∧ i = i' ∧ j = j'
  | .body b pos env i j, .body b' pos' env' i' j' => b = b' ∧ pos = pos' ∧ EnvLe L.le env env' ∧ i = i' ∧ j = j'
  | .rest l n env i j, .rest l' n' env' i' j' => l = l' ∧ n = n' ∧ EnvLe L.le env env' ∧ i = i' ∧ j = j'
  | _, _ => False

/-- A more general answer: the same reading or children, a more general
sort or bindings. -/
def AnswerLe : Answer → Answer → Prop
  | .one r σ, .one r' σ' => r = r' ∧ L.le σ σ'
  | .many cs env, .many cs' env' => cs = cs' ∧ EnvLe L.le env env'
  | _, _ => False

theorem questionLe_expr {s p x i j s' p' x' i' j'} :
    L.QuestionLe (.expr s p x i j) (.expr s' p' x' i' j') ↔ L.le s s' ∧ p = p' ∧ x = x' ∧ i = i' ∧ j = j' := Iff.rfl
theorem questionLe_body {b pos env i j b' pos' env' i' j'} :
    L.QuestionLe (.body b pos env i j) (.body b' pos' env' i' j') ↔
      b = b' ∧ pos = pos' ∧ EnvLe L.le env env' ∧ i = i' ∧ j = j' := Iff.rfl
theorem questionLe_rest {l n env i j l' n' env' i' j'} :
    L.QuestionLe (.rest l n env i j) (.rest l' n' env' i' j') ↔
      l = l' ∧ n = n' ∧ EnvLe L.le env env' ∧ i = i' ∧ j = j' := Iff.rfl
theorem answerLe_one {r σ r' σ'} : L.AnswerLe (.one r σ) (.one r' σ') ↔ r = r' ∧ L.le σ σ' := Iff.rfl
theorem answerLe_many {cs env cs' env'} :
    L.AnswerLe (.many cs env) (.many cs' env') ↔ cs = cs' ∧ EnvLe L.le env env' := Iff.rfl

theorem answerLe_refl (a : Answer) : L.AnswerLe a a := by
  cases a with
  | one r σ => exact L.answerLe_one.mpr ⟨rfl, L.refl σ⟩
  | many cs env => exact L.answerLe_many.mpr ⟨rfl, L.envLe_refl env⟩

end Lawful

section
variable {A : SortAlgebra} {g : Grammar} {ts : Array String} (L : Lawful A)

/-- **Monotonicity.** A more general question admits the same answer, more
generally: the laws, applied along the derivation. -/
theorem Reads.mono {q : Question} {a : Answer} (h : Reads A g ts q a) :
    ∀ q', L.QuestionLe q q' → ∃ a', L.AnswerLe a a' ∧ Reads A g ts q' a' := by
  induction h with
  | @prod s p excl i j k pr body cs env hk hvar hcompat hex hcoe hprec hij hbody hc _ =>
    intro q' hq
    cases q' with
    | expr s' p' x' i' j' =>
      obtain ⟨hs, rfl, rfl, rfl, rfl⟩ := L.questionLe_expr.mp hq
      exact ⟨_, L.answerLe_one.mpr ⟨rfl, L.refl _⟩,
        Reads.prod hk hvar (L.accept (L.refl _) hs hcompat) hex hcoe hprec hij hbody (L.accept (L.refl _) hs hc)⟩
    | body _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @coe s p excl i j k pr body s' pc x r so hk hvar hcompat hcoe hb harg hc _ =>
    intro q' hq
    cases q' with
    | expr s'' p' x' i' j' =>
      obtain ⟨hs, rfl, rfl, rfl, rfl⟩ := L.questionLe_expr.mp hq
      exact ⟨_, L.answerLe_one.mpr ⟨rfl, L.refl _⟩,
        Reads.coe hk hvar (L.accept (L.refl _) hs hcompat) hcoe hb harg (L.accept (L.refl _) hs hc)⟩
    | body _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @paren s p excl i j r σ hlen hl hr _ ih =>
    intro q' hq
    cases q' with
    | expr s' p' x' i' j' =>
      obtain ⟨hs, rfl, rfl, rfl, rfl⟩ := L.questionLe_expr.mp hq
      obtain ⟨a', ha', hr'⟩ := ih (.expr s' 0 none (i + 1) (j - 1)) (L.questionLe_expr.mpr ⟨hs, rfl, rfl, rfl, rfl⟩)
      cases a' with
      | one r' σ' =>
        obtain ⟨rfl, hle⟩ := L.answerLe_one.mp ha'
        exact ⟨.one r σ', L.answerLe_one.mpr ⟨rfl, hle⟩, Reads.paren hlen hl hr hr'⟩
      | many _ _ => cases ha'
    | body _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @group s p excl i j r σ hlen hl hr _ ih =>
    intro q' hq
    cases q' with
    | expr s' p' x' i' j' =>
      obtain ⟨hs, rfl, rfl, rfl, rfl⟩ := L.questionLe_expr.mp hq
      obtain ⟨a', ha', hr'⟩ := ih (.expr s' p none (i + 1) (j - 1)) (L.questionLe_expr.mpr ⟨hs, rfl, rfl, rfl, rfl⟩)
      cases a' with
      | one r' σ' =>
        obtain ⟨rfl, hle⟩ := L.answerLe_one.mp ha'
        exact ⟨.one r σ', L.answerLe_one.mpr ⟨rfl, hle⟩, Reads.group hlen hl hr hr'⟩
      | many _ _ => cases ha'
    | body _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @done body pos env i hend =>
    intro q' hq
    cases q' with
    | body b' pos' env' i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_body.mp hq
      exact ⟨.many #[] env', L.answerLe_many.mpr ⟨rfl, henv⟩, Reads.done hend⟩
    | expr _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @tok body pos env i j t cs env' hb hij ht _ ih =>
    intro q' hq
    cases q' with
    | body b' pos' env₁ i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_body.mp hq
      obtain ⟨a', ha', hr'⟩ := ih (.body body (pos + 1) env₁ (i + 1) j) (L.questionLe_body.mpr ⟨rfl, rfl, henv, rfl, rfl⟩)
      cases a' with
      | many cs' env'' =>
        obtain ⟨rfl, hle⟩ := L.answerLe_many.mp ha'
        exact ⟨.many cs env'', L.answerLe_many.mpr ⟨rfl, hle⟩, Reads.tok hb hij ht hr'⟩
      | one _ _ => cases ha'
    | expr _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @hole body pos env i j s p x m r so cs env' hb hlt hle _ _ ihh ihr =>
    intro q' hq
    cases q' with
    | body b' pos' env₁ i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_body.mp hq
      obtain ⟨a₁, ha₁, hh'⟩ := ihh (.expr (A.expected env₁ s) p x i m)
        (L.questionLe_expr.mpr ⟨L.expected_mono s henv, rfl, rfl, rfl, rfl⟩)
      cases a₁ with
      | one r' so' =>
        obtain ⟨rfl, hso⟩ := L.answerLe_one.mp ha₁
        obtain ⟨a₂, ha₂, hr'⟩ := ihr (.body body (pos + 1) (A.bind env₁ s so') m j)
          (L.questionLe_body.mpr ⟨rfl, rfl, L.bind_mono s henv hso, rfl, rfl⟩)
        cases a₂ with
        | many cs' env'' =>
          obtain ⟨rfl, hle'⟩ := L.answerLe_many.mp ha₂
          exact ⟨.many (#[r] ++ cs) env'', L.answerLe_many.mpr ⟨rfl, hle'⟩, Reads.hole hb hlt hle hh' hr'⟩
        | one _ _ => cases ha₂
      | many _ _ => cases ha₁
    | expr _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @var body pos env i j m v cs env' hb hlt hle hv _ ih =>
    intro q' hq
    cases q' with
    | body b' pos' env₁ i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_body.mp hq
      obtain ⟨a', ha', hr'⟩ := ih (.body body (pos + 1) env₁ m j) (L.questionLe_body.mpr ⟨rfl, rfl, henv, rfl, rfl⟩)
      cases a' with
      | many cs' env'' =>
        obtain ⟨rfl, hle'⟩ := L.answerLe_many.mp ha'
        exact ⟨.many (#[v] ++ cs) env'', L.answerLe_many.mpr ⟨rfl, hle'⟩, Reads.var hb hlt hle hv hr'⟩
      | one _ _ => cases ha'
    | expr _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @tail body pos env i j l n m as env₁ cs env' hb hle hm _ _ iht ihr =>
    intro q' hq
    cases q' with
    | body b' pos' env₂ i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_body.mp hq
      obtain ⟨a₁, ha₁, ht'⟩ := iht (.rest l n env₂ i m) (L.questionLe_rest.mpr ⟨rfl, rfl, henv, rfl, rfl⟩)
      cases a₁ with
      | many as' env₃ =>
        obtain ⟨rfl, hle₁⟩ := L.answerLe_many.mp ha₁
        obtain ⟨a₂, ha₂, hr'⟩ := ihr (.body body (pos + 1) env₃ m j) (L.questionLe_body.mpr ⟨rfl, rfl, hle₁, rfl, rfl⟩)
        cases a₂ with
        | many cs' env'' =>
          obtain ⟨rfl, hle'⟩ := L.answerLe_many.mp ha₂
          exact ⟨.many (as ++ cs) env'', L.answerLe_many.mpr ⟨rfl, hle'⟩, Reads.tail hb hle hm ht' hr'⟩
        | one _ _ => cases ha₂
      | one _ _ => cases ha₁
    | expr _ _ _ _ _ => cases hq
    | rest _ _ _ _ _ => cases hq
  | @nil l env i =>
    intro q' hq
    cases q' with
    | rest l' n' env' i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_rest.mp hq
      exact ⟨.many #[] env', L.answerLe_many.mpr ⟨rfl, henv⟩, Reads.nil⟩
    | expr _ _ _ _ _ => cases hq
    | body _ _ _ _ _ => cases hq
  | @more l n env i j elem sep cs env' hl hij _ ih =>
    intro q' hq
    cases q' with
    | rest l' n' env₁ i' j' =>
      obtain ⟨rfl, rfl, henv, rfl, rfl⟩ := L.questionLe_rest.mp hq
      obtain ⟨a', ha', hr'⟩ := ih (.body (sep ++ elem ++ #[ASym.tail l (n - 1)]) 0 env₁ i j)
        (L.questionLe_body.mpr ⟨rfl, rfl, henv, rfl, rfl⟩)
      cases a' with
      | many cs' env'' =>
        obtain ⟨rfl, hle'⟩ := L.answerLe_many.mp ha'
        exact ⟨.many cs env'', L.answerLe_many.mpr ⟨rfl, hle'⟩, Reads.more hl hij hr'⟩
      | one _ _ => cases ha'
    | expr _ _ _ _ _ => cases hq
    | body _ _ _ _ _ => cases hq

end

end SpliceModel
