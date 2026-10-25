/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBack

/-!
# The parser is sound

Every reading `Imprimatur.Validate.readBackWith` returns is a reading in
the grammar (`SpliceModel.Exp`), with the sort it is given
(`readBack_sound`). The proof is an induction on the parser's fuel, with an
invariant on what it remembers: every reading in a memo table is a reading.
The reasoning is in Hoare triples over the parser's state monad.
-/

namespace SpliceModel

open Imprimatur.Validate

/-! ## Triples over the parser's state -/

section
variable (A : SortAlgebra) (g : Grammar) (ts : Array String)

/-- What the parser remembers is sound: every memoised reading is one, and
the productions remembered for a sort are the reachable ones. -/
def Inv (st : CState) : Prop :=
  (∀ s p excl ch i j out, st.memo[(s, p, excl, ch, i, j)]? = some out →
    ∀ x ∈ out, i < j ∧ Exp A g ts s p excl ch i j x.1 x.2) ∧
  (∀ body pos env i j n, st.memoSeq[(body, pos, env, i, j)]? = some n →
    ∀ x ∈ n, Seq A g ts body pos env i j x.1 x.2) ∧
  (∀ s r, st.reach[s]? = some r → r = reachSplit A g s) ∧
  (∀ s p excl i j out, st.memoD[(s, p, excl, i, j)]? = some out →
    ∀ x ∈ out, i < j ∧ ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)

/-- From a sound state, the computation ends in a sound state with a result
that satisfies `Q`. -/
def Triple {α : Type} (m : CountM α) (Q : α → Prop) : Prop :=
  ∀ st, Inv A g ts st → Inv A g ts (m.run st).2 ∧ Q (m.run st).1

variable {A g ts}

theorem Inv.empty : Inv A g ts {} := by
  refine ⟨fun s p excl ch i j out h => ?_, fun body pos env i j n h => ?_, fun s r h => ?_,
    fun s p excl i j out h => ?_⟩ <;> simp at h

theorem triple_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Triple A g ts (pure a) Q :=
  fun _ hst => ⟨hst, h⟩

theorem triple_bind {α β : Type} {m : CountM α} {f : α → CountM β} {Q : α → Prop} {R : β → Prop}
    (hm : Triple A g ts m Q) (hf : ∀ a, Q a → Triple A g ts (f a) R) : Triple A g ts (m >>= f) R := by
  intro st hst
  obtain ⟨h1, h2⟩ := hm st hst
  exact hf _ h2 _ h1

theorem triple_mono {α : Type} {m : CountM α} {Q R : α → Prop} (hm : Triple A g ts m Q)
    (h : ∀ a, Q a → R a) : Triple A g ts m R :=
  fun st hst => ⟨(hm st hst).1, h _ (hm st hst).2⟩

theorem triple_get : Triple A g ts get (fun st => Inv A g ts st) :=
  fun _ hst => ⟨hst, hst⟩

theorem triple_modify {f : CState → CState} (h : ∀ st, Inv A g ts st → Inv A g ts (f st)) :
    Triple A g ts (modify f) (fun _ => True) :=
  fun st hst => ⟨h st hst, trivial⟩

/-- Changing anything but the memo tables keeps the invariant. -/
theorem Inv.congr {st st' : CState} (h : Inv A g ts st) (hm : st'.memo = st.memo)
    (hs : st'.memoSeq = st.memoSeq) (hr : st'.reach = st.reach) (hd : st'.memoD = st.memoD) : Inv A g ts st' := by
  refine ⟨fun s p excl ch i j out e => h.1 s p excl ch i j out ?_,
    fun body pos env i j n e => h.2.1 body pos env i j n ?_, fun s r e => h.2.2.1 s r ?_,
    fun s p excl i j out e => h.2.2.2 s p excl i j out ?_⟩
  · rwa [hm] at e
  · rwa [hs] at e
  · rwa [hr] at e
  · rwa [hd] at e

/-- A triple whose program does not look at the state beyond the memo. -/
theorem triple_of_run {α : Type} {m : CountM α} {Q : α → Prop}
    (h : ∀ st, (m.run st).2.memo = st.memo ∧ (m.run st).2.memoSeq = st.memoSeq ∧
      (m.run st).2.reach = st.reach ∧ (m.run st).2.memoD = st.memoD ∧ Q (m.run st).1) :
    Triple A g ts m Q :=
  fun st hst => ⟨hst.congr (h st).1 (h st).2.1 (h st).2.2.1 (h st).2.2.2.1, (h st).2.2.2.2⟩

/-- Remembering sound readings keeps the invariant. -/
theorem Inv.insertExp {st : CState} (h : Inv A g ts st) {s p excl ch i j out} (active : Std.HashMap _ Unit)
    (hout : ∀ x ∈ out, i < j ∧ Exp A g ts s p excl ch i j x.1 x.2) :
    Inv A g ts { st with active := active, memo := st.memo.insert (s, p, excl, ch, i, j) out } := by
  refine ⟨fun s' p' excl' ch' i' j' out' e => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  simp only [Std.HashMap.getElem?_insert] at e
  split at e
  · rename_i heq
    simp only [beq_iff_eq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
    simp only [Option.some.injEq] at e
    subst e
    exact hout
  · exact h.1 s' p' excl' ch' i' j' out' e

/-- Remembering sound readings of a body keeps the invariant. -/
theorem Inv.insertSeq {st : CState} (h : Inv A g ts st) {body pos env i j n}
    (hn : ∀ x ∈ n, Seq A g ts body pos env i j x.1 x.2) :
    Inv A g ts { st with memoSeq := st.memoSeq.insert (body, pos, env, i, j) n } := by
  refine ⟨h.1, fun body' pos' env' i' j' n' e => ?_, h.2.2.1, h.2.2.2⟩
  simp only [Std.HashMap.getElem?_insert] at e
  split at e
  · rename_i heq
    simp only [beq_iff_eq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    simp only [Option.some.injEq] at e
    subst e
    exact hn
  · exact h.2.1 body' pos' env' i' j' n' e

/-- Remembering the reachable productions keeps the invariant. -/
theorem Inv.insertReach {st : CState} (h : Inv A g ts st) (s : String) :
    Inv A g ts { st with reach := st.reach.insert s (reachSplit A g s) } := by
  refine ⟨h.1, h.2.1, fun s' r e => ?_, h.2.2.2⟩
  simp only [Std.HashMap.getElem?_insert] at e
  split at e
  · rename_i heq
    simp only [beq_iff_eq] at heq
    subst heq
    simp only [Option.some.injEq] at e
    exact e.symm
  · exact h.2.2.1 s' r e

/-- Remembering sound readings not through a coercion keeps the invariant. -/
theorem Inv.insertD {st : CState} (h : Inv A g ts st) {s p excl i j out}
    (hout : ∀ x ∈ out, i < j ∧ ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) :
    Inv A g ts { st with memoD := st.memoD.insert (s, p, excl, i, j) out } := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun s' p' excl' i' j' out' e => ?_⟩
  simp only [Std.HashMap.getElem?_insert] at e
  split at e
  · rename_i heq
    simp only [beq_iff_eq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    simp only [Option.some.injEq] at e
    subst e
    exact hout
  · exact h.2.2.2 s' p' excl' i' j' out' e

/-! ## Keeping readings -/

theorem keepGo_subset {α : Type} [BEq α] (key : α → String) :
    ∀ (xs : List α) (out : Array α) (keys : Array String) (pruned : Bool),
      ∀ x ∈ (keepGo key xs out keys pruned).1, x ∈ xs ∨ x ∈ out
  | [], out, keys, pruned => by simp [keepGo]
  | y :: ys, out, keys, pruned => by
    intro x hx
    simp only [keepGo] at hx
    split at hx
    · rcases keepGo_subset key ys _ _ _ x hx with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
    · split at hx
      · rcases keepGo_subset key ys _ _ _ x hx with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · split at hx
        · rcases keepGo_subset key ys _ _ _ x hx with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h
        · rcases keepGo_subset key ys _ _ _ x hx with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rw [Array.mem_push] at h
            rcases h with h | rfl
            · exact Or.inr h
            · exact Or.inl (List.mem_cons_self ..)

theorem keep_subset {α : Type} [BEq α] (key : α → String) (xs : Array α) :
    ∀ x ∈ (keep key xs).1, x ∈ xs := by
  intro x hx
  rcases keepGo_subset key xs.toList #[] #[] false x hx with h | h
  · exact Array.mem_def.mpr h
  · simp at h

/-- `keepM` keeps only readings given it, and changes only `pruned`. -/
theorem triple_keepM {α : Type} [BEq α] (key : α → String) (xs : Array α)
    {P : α → Prop} (h : ∀ x ∈ xs, P x) : Triple A g ts (keepM key xs) (fun out => ∀ x ∈ out, P x) := by
  apply triple_of_run
  intro st
  simp only [keepM]
  split
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure]
    exact ⟨rfl, rfl, rfl, rfl, fun x hx => h x (keep_subset key xs x hx)⟩
  · simp only [StateT.run_pure]
    exact ⟨rfl, rfl, rfl, rfl, fun x hx => h x (keep_subset key xs x hx)⟩


/-! ## The accumulators -/

/-- `addProds` adds, to readings of production `pr`'s body, the production's
readings. -/
theorem triple_addProds (s : String) (pr : Imprimatur.Validate.Prod) {P : Reading × String → Prop}
    {R : Array Reading × Env → Prop}
    (hP : ∀ cs env, R (cs, env) → fits A g (A.expected env pr.sort) s = true →
      P (mkReading pr.name pr.order cs, A.expected env pr.sort)) :
    ∀ (rs : List (Array Reading × Env)) (out : Array (Reading × String)), (∀ x ∈ rs, R x) →
      (∀ x ∈ out, P x) → Triple A g ts (addProds A g s pr rs out) (fun res => ∀ x ∈ res, P x)
  | [], out, _, hout => by simp only [addProds]; exact triple_pure hout
  | (cs, env) :: rest, out, hrs, hout => by
    simp only [addProds]
    split
    · exact triple_addProds s pr hP rest out (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) hout
    · rename_i hc
      refine triple_bind (triple_keepM _ _ (P := P) ?_) fun out' hout' =>
        triple_addProds s pr hP rest out' (fun x hx => hrs x (List.mem_cons_of_mem _ hx)) hout'
      intro x hx
      rw [Array.mem_push] at hx
      rcases hx with hx | rfl
      · exact hout x hx
      · exact hP cs env (hrs _ (List.mem_cons_self ..)) (by simpa using hc)

/-- `addCoes` adds, to readings of a coercion's argument, the readings
through it. -/
theorem triple_addCoes (s : String) (pr : Imprimatur.Validate.Prod) (s' : String)
    {P : Reading × String → Prop} {R : Reading × String → Prop}
    (hP : ∀ r so, R (r, so) → fits A g (A.expected (A.bind #[] s' so) pr.sort) s = true →
      P (r, A.expected (A.bind #[] s' so) pr.sort)) :
    ∀ (args : List (Reading × String)) (out : Array (Reading × String)), (∀ x ∈ args, R x) →
      (∀ x ∈ out, P x) → Triple A g ts (addCoes A g s pr s' args out) (fun res => ∀ x ∈ res, P x)
  | [], out, _, hout => by simp only [addCoes]; exact triple_pure hout
  | (r, so) :: rest, out, hargs, hout => by
    simp only [addCoes]
    split
    · exact triple_addCoes s pr s' hP rest out (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hout
    · rename_i hc
      refine triple_bind (triple_keepM _ _ (P := P) ?_) fun out' hout' =>
        triple_addCoes s pr s' hP rest out' (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hout'
      intro x hx
      rw [Array.mem_push] at hx
      rcases hx with hx | rfl
      · exact hout x hx
      · exact hP r so (hargs _ (List.mem_cons_self ..)) (by simpa using hc)

/-- `joinRests` joins a reading of a nonterminal with each reading of the rest. -/
theorem triple_joinRests (a : Array Reading × Env) {P : Array Reading × Env → Prop}
    {R : Array Reading × Env → Prop} (hR : ∀ rest env₂, R (rest, env₂) → P (a.1 ++ rest, env₂)) :
    ∀ (rests : List (Array Reading × Env)) (out : Array (Array Reading × Env)),
      (∀ x ∈ rests, R x) → (∀ x ∈ out, P x) → Triple A g ts (joinRests a rests out) (fun res => ∀ x ∈ res, P x)
  | [], out, _, hout => by simp only [joinRests]; exact triple_pure hout
  | (rest, env₂) :: more, out, hrests, hout => by
    simp only [joinRests]
    refine triple_bind (triple_keepM _ _ (P := P) ?_) fun out' hout' =>
      triple_joinRests a hR more out' (fun x hx => hrests x (List.mem_cons_of_mem _ hx)) hout'
    intro x hx
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact hout x hx
    · exact hR rest env₂ (hrests _ (List.mem_cons_self ..))

/-! ## Facts about the pieces -/

/-- A variable's name spans at least one token. -/
theorem varOf_lt {i j : Nat} : ∀ (l : List (Imprimatur.Validate.Prod × Array ASym)) {v : Reading},
    varOf g ts i j l = some v → i < j
  | [], _, h => by simp [varOf] at h
  | (pr, body) :: rest, v, h => by
    simp only [varOf] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      omega
    · exact varOf_lt rest h

/-- `reachable`'s step: the productions it keeps are not variables' names,
and of a compatible sort. -/
theorem mem_reachable_foldl (s : String) : ∀ (l : List Nat) (init : Array Nat) (k : Nat),
    k ∈ l.foldl (fun out i => match g.prods[i]? with
      | some (p, _) => if !p.isVar && A.compat p.sort s then out.push i else out
      | none => out) init →
    k ∈ init ∨ ∃ pr body, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true
  | [], init, k, h => Or.inl h
  | i :: l, init, k, h => by
    simp only [List.foldl_cons] at h
    rcases mem_reachable_foldl s l _ k h with h | h
    · split at h
      · rename_i p b hp
        split at h
        · rename_i hc
          rw [Array.mem_push] at h
          rcases h with h | rfl
          · exact Or.inl h
          · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
            exact Or.inr ⟨p, b, hp, hc.1, hc.2⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr h

theorem mem_reachable {s : String} {k : Nat} (h : k ∈ reachable A g s) :
    ∃ pr body, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true := by
  rcases mem_reachable_foldl s _ #[] k h with h | h
  · simp at h
  · exact h

/-! ### The step of `reachSplit` -/

theorem reachStep_cks (acc : Reach) (k : Nat) :
    (reachStep g acc k).2.2 = if isCoe g k then acc.2.2.push k else acc.2.2 := by
  simp only [reachStep]
  split <;> rfl

theorem reachStep_others_tok (acc : Reach) (k : Nat) {t : String} (h : headSym g k = some (ASym.tok t)) :
    (reachStep g acc k).2.1 = acc.2.1 := by
  simp only [reachStep]
  try (split <;> first | rfl | (rename_i hno; exact absurd h (hno t)))

theorem reachStep_others_not (acc : Reach) (k : Nat) (h : ∀ t, headSym g k ≠ some (ASym.tok t)) :
    (reachStep g acc k).2.1 = acc.2.1.push k := by
  simp only [reachStep]

theorem reachStep_byTok (acc : Reach) (k : Nat) (t : String) :
    (reachStep g acc k).1.getD t #[] = acc.1.getD t #[] ∨
      (headSym g k = some (ASym.tok t) ∧ (reachStep g acc k).1.getD t #[] = (acc.1.getD t #[]).push k) := by
  simp only [reachStep]
  split
  · rename_i t' heq
    simp only []
    rw [Std.HashMap.getD_insert]
    split
    · rename_i ht
      rw [beq_iff_eq] at ht
      subst ht
      exact Or.inr ⟨heq, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- What a step adds is the production stepped. -/
theorem mem_reachStep (acc : Reach) (k : Nat) :
    (∀ t x, x ∈ (reachStep g acc k).1.getD t #[] → x ∈ acc.1.getD t #[] ∨ x = k) ∧
    (∀ x ∈ (reachStep g acc k).2.1, x ∈ acc.2.1 ∨ x = k) ∧
    (∀ x ∈ (reachStep g acc k).2.2, x ∈ acc.2.2 ∨ x = k) := by
  refine ⟨fun t x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rcases reachStep_byTok (g := g) acc k t with h | ⟨_, h⟩
    · rw [h] at hx; exact Or.inl hx
    · rw [h, Array.mem_push] at hx; exact hx
  · by_cases ht : ∃ t, headSym g k = some (ASym.tok t)
    · obtain ⟨t, ht⟩ := ht
      rw [reachStep_others_tok acc k ht] at hx
      exact Or.inl hx
    · rw [reachStep_others_not acc k fun t h => ht ⟨t, h⟩, Array.mem_push] at hx
      exact hx
  · rw [reachStep_cks] at hx
    split at hx
    · rw [Array.mem_push] at hx; exact hx
    · exact Or.inl hx

/-- What `reachSplit` sorts into its parts was reachable. -/
theorem mem_reachSplit (s : String) :
    (∀ t k, k ∈ (reachSplit A g s).1.getD t #[] → k ∈ reachable A g s) ∧
    (∀ k ∈ (reachSplit A g s).2.1, k ∈ reachable A g s) ∧
    (∀ k ∈ (reachSplit A g s).2.2, k ∈ reachable A g s) := by
  unfold reachSplit
  refine Array.foldl_induction (motive := fun (_ : Nat) (acc : Reach) =>
    (∀ t k, k ∈ acc.1.getD t #[] → k ∈ reachable A g s) ∧ (∀ k ∈ acc.2.1, k ∈ reachable A g s) ∧
      (∀ k ∈ acc.2.2, k ∈ reachable A g s)) ?_ ?_
  · exact ⟨fun t k h => by simp at h, fun k h => by simp at h, fun k h => by simp at h⟩
  · intro n acc hacc
    have hmem : (reachable A g s)[n] ∈ reachable A g s := Array.getElem_mem _
    obtain ⟨h1, h2, h3⟩ := mem_reachStep (g := g) acc (reachable A g s)[n]
    refine ⟨fun t k h => ?_, fun k h => ?_, fun k h => ?_⟩
    · rcases h1 t k h with h | rfl
      · exact hacc.1 t k h
      · exact hmem
    · rcases h2 k h with h | rfl
      · exact hacc.2.1 k h
      · exact hmem
    · rcases h3 k h with h | rfl
      · exact hacc.2.2 k h
      · exact hmem

/-- A production tried is not the excluded one, not a coercion, and at or
above the precedence. -/
theorem tried_spec {p : Nat} {excl : Option Nat} {i j k : Nat} (h : tried g ts p excl i j k = true) :
    ∃ pr body, g.prods[k]? = some (pr, body) ∧ excl ≠ some k ∧ pr.coercion = false ∧ p ≤ pr.prec := by
  unfold tried at h
  split at h
  · simp at h
  · rename_i pr body hk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_true_eq] at h
    exact ⟨pr, body, hk, h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

/-! ## The parser -/

/-- The readings of a nonterminal: a hole's, a variable's, a list's, each
with its span not empty (or, for a list, not reversed). -/
def SplitSpec (N : Env → Nat → Nat → Array Reading × Env → Prop) (body : Array ASym) (pos : Nat)
    (env : Env) (i j : Nat) (x : Array Reading × Env) : Prop :=
  ∃ m as env₁ rest, m ≤ j ∧ N env i m (as, env₁) ∧ Seq A g ts body (pos + 1) env₁ m j rest x.2 ∧
    x.1 = as ++ rest

/-- Every candidate production is reachable: not a variable's name, of a
compatible sort. -/
def Cands (s : String) (ks : List Nat) : Prop :=
  ∀ k ∈ ks, ∃ pr body, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true

/-- The statements proved together, for one amount of fuel. -/
def SoundAll (fuel : Nat) : Prop :=
  (∀ s p excl ch i j, Triple A g ts (expr A g ts fuel s p excl ch i j)
    (fun res => ∀ x ∈ res, i < j ∧ Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl ch i j, i < j → Triple A g ts (exprFresh A g ts fuel s p excl ch i j)
    (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl ch i j r, i < j → r = reachSplit A g s →
    Triple A g ts (exprRead A g ts fuel s p excl ch i j r)
      (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl i j ks out, i < j → Cands (A := A) (g := g) s ks →
    (∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) →
    Triple A g ts (prods A g ts fuel s p excl i j ks out)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl ch i j ks out, i < j → Cands (A := A) (g := g) s ks →
    (∀ x ∈ out, Exp A g ts s p excl ch i j x.1 x.2) →
    Triple A g ts (coes A g ts fuel s p excl ch i j ks out)
      (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ body pos env i j, Triple A g ts (seq A g ts fuel body pos env i j)
    (fun res => ∀ x ∈ res, Seq A g ts body pos env i j x.1 x.2)) ∧
  (∀ body pos env i j, Triple A g ts (seqFresh A g ts fuel body pos env i j)
    (fun res => ∀ x ∈ res, Seq A g ts body pos env i j x.1 x.2)) ∧
  (∀ (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env))) (N : Env → Nat → Nat → Array Reading × Env → Prop),
    (∀ env a b, Triple A g ts (nt env a b) (fun res => ∀ x ∈ res, N env a b x)) →
    ∀ body pos env i j, Triple A g ts (split A g ts fuel nt body pos env i j)
      (fun res => ∀ x ∈ res, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x)) ∧
  (∀ (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env))) (N : Env → Nat → Nat → Array Reading × Env → Prop),
    (∀ env a b, Triple A g ts (nt env a b) (fun res => ∀ x ∈ res, N env a b x)) →
    ∀ body pos env i j next ms out, (∀ m ∈ ms, m ≤ j) →
      (∀ x ∈ out, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x) →
      Triple A g ts (splitAt A g ts fuel nt body pos env i j next ms out)
        (fun res => ∀ x ∈ res, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x)) ∧
  (∀ body pos m j (as : List (Array Reading × Env)) out (P : Array Reading × Env → Prop),
    (∀ a ∈ as, ∀ rest env₂, Seq A g ts body (pos + 1) a.2 m j rest env₂ → P (a.1 ++ rest, env₂)) →
    (∀ x ∈ out, P x) →
    Triple A g ts (splitRests A g ts fuel body pos m j as out) (fun res => ∀ x ∈ res, P x)) ∧
  (∀ l r env i j, Triple A g ts (tail A g ts fuel l r env i j)
    (fun res => ∀ x ∈ res, i ≤ j ∧ Tail A g ts l r env i j x.1 x.2)) ∧
  (∀ s p excl i j out, i < j → (∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) →
    Triple A g ts (parens A g ts fuel s p excl i j out)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl i j out, i < j → (∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) →
    Triple A g ts (groups A g ts fuel s p excl i j out)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)) ∧
  (∀ s p excl i j r, i < j → r = reachSplit A g s →
    Triple A g ts (exprDirect A g ts fuel s p excl i j r)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2))

/-- The candidates of a question are reachable. -/
theorem cands_reachable (s : String) (t : String) :
    Cands (A := A) (g := g) s ((reachSplit A g s).1.getD t #[] ++ (reachSplit A g s).2.1).toList := by
  intro k hk
  rw [Array.toList_append, List.mem_append, ← Array.mem_def, ← Array.mem_def] at hk
  rcases hk with hk | hk
  · exact mem_reachable ((mem_reachSplit s).1 t k hk)
  · exact mem_reachable ((mem_reachSplit s).2.1 k hk)

/-- The coercions of a question are reachable. -/
theorem coes_reachable (s : String) : Cands (A := A) (g := g) s (reachSplit A g s).2.2.toList :=
  fun k hk => mem_reachable ((mem_reachSplit s).2.2 k (Array.mem_def.mpr hk))

/-- A computation that only sets `over` is sound, with no readings. -/
theorem triple_over {α : Type} {Q : Array α → Prop} (h : Q #[]) :
    Triple A g ts (do modify fun st => { st with over := true }; return (#[] : Array α)) Q := by
  apply triple_of_run
  intro st
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure]
  exact ⟨rfl, rfl, rfl, rfl, h⟩

theorem soundAll_zero : SoundAll (A := A) (g := g) (ts := ts) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s p excl ch i j; simp only [expr]; exact triple_over (by simp)
  · intro s p excl ch i j _; simp only [exprFresh]; exact triple_over (by simp)
  · intro s p excl ch i j r _ _; simp only [exprRead]; exact triple_over (by simp)
  · intro s p excl i j ks out _ _ _; simp only [prods]; exact triple_over (by simp)
  · intro s p excl ch i j ks out _ _ _; simp only [coes]; exact triple_over (by simp)
  · intro body pos env i j; simp only [seq]; exact triple_over (by simp)
  · intro body pos env i j; simp only [seqFresh]; exact triple_over (by simp)
  · intro nt N _ body pos env i j; simp only [split]; exact triple_over (by simp)
  · intro nt N _ body pos env i j next ms out _ _; simp only [splitAt]; exact triple_over (by simp)
  · intro body pos m j as out P _ _; simp only [splitRests]; exact triple_over (by simp)
  · intro l r env i j; simp only [tail]; exact triple_over (by simp)
  · intro s p excl i j out _ _; simp only [parens]; exact triple_over (by simp)
  · intro s p excl i j out _ _; simp only [groups]; exact triple_over (by simp)
  · intro s p excl i j r _ _; simp only [exprDirect]; exact triple_over (by simp)


/-- A computation that changes the state, then returns, keeps the
invariant when the change does. -/
theorem triple_modify_pure {α : Type} {f : CState → CState} {a : α} {Q : α → Prop}
    (hf : ∀ st, Inv A g ts st → Inv A g ts (f st)) (h : Q a) :
    Triple A g ts (do modify f; return a) Q :=
  triple_bind (triple_modify hf) fun _ _ => triple_pure h

/-- Remembering readings of a body, then returning them. -/
theorem triple_remember {body pos env i j} {n : Array (Array Reading × Env)}
    (hn : ∀ x ∈ n, Seq A g ts body pos env i j x.1 x.2) :
    Triple A g ts (do
      modify fun st => { st with memoSeq := st.memoSeq.insert (body, pos, env, i, j) n }
      pure n) (fun res => ∀ x ∈ res, Seq A g ts body pos env i j x.1 x.2) :=
  triple_bind (triple_modify fun _ h => h.insertSeq hn) fun _ _ => triple_pure hn

/-! ## The inductive step -/

section Step
variable {fuel : Nat} (ih : SoundAll (A := A) (g := g) (ts := ts) fuel)
include ih

theorem tail_step (l r : Nat) (env : Env) (i j : Nat) :
    Triple A g ts (tail A g ts (fuel + 1) l r env i j)
      (fun res => ∀ x ∈ res, i ≤ j ∧ Tail A g ts l r env i j x.1 x.2) := by
  obtain ⟨_, _, _, _, _, ihS, _⟩ := ih
  simp only [tail]
  split
  · rename_i elem sep hl
    split
    · rename_i hij
      refine triple_bind (ihS _ 0 env i j) fun rs hrs => triple_keepM _ _ ?_
      intro x hx
      rw [Array.mem_append] at hx
      rcases hx with hx | hx
      · split at hx
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          simp only [Array.mem_singleton] at hx
          subst hx
          exact ⟨Nat.le_refl _, Reads.nil⟩
        · simp at hx
      · exact ⟨Nat.le_of_lt hij, Reads.more hl hij (hrs x hx)⟩
    · apply triple_pure
      intro x hx
      split at hx
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp only [Array.mem_singleton] at hx
        subst hx
        exact ⟨Nat.le_refl _, Reads.nil⟩
      · simp at hx
  · apply triple_pure
    intro x hx
    split at hx
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Array.mem_singleton] at hx
      subst hx
      exact ⟨Nat.le_refl _, Reads.nil⟩
    · simp at hx

theorem splitRests_step (body : Array ASym) (pos m j : Nat) :
    ∀ (as : List (Array Reading × Env)) (out : Array (Array Reading × Env)) (P : Array Reading × Env → Prop),
      (∀ a ∈ as, ∀ rest env₂, Seq A g ts body (pos + 1) a.2 m j rest env₂ → P (a.1 ++ rest, env₂)) →
      (∀ x ∈ out, P x) →
      Triple A g ts (splitRests A g ts (fuel + 1) body pos m j as out) (fun res => ∀ x ∈ res, P x)
  | [], out, P, _, hout => by simp only [splitRests]; exact triple_pure hout
  | a :: more, out, P, has, hout => by
    obtain ⟨_, _, _, _, _, ihS, _, _, _, ihSr, _, _, _, _⟩ := ih
    simp only [splitRests]
    refine triple_bind (ihS body (pos + 1) a.2 m j) fun rests hrests => ?_
    refine triple_bind (triple_joinRests a (R := fun x => Seq A g ts body (pos + 1) a.2 m j x.1 x.2)
      (fun rest env₂ h => has a (List.mem_cons_self ..) rest env₂ h) rests.toList out
      (fun x hx => hrests x (Array.mem_def.mpr hx)) hout) fun out' hout' => ?_
    exact ihSr body pos m j more out' P (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) hout'

theorem splitAt_step (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env)))
    (N : Env → Nat → Nat → Array Reading × Env → Prop)
    (hnt : ∀ env a b, Triple A g ts (nt env a b) (fun res => ∀ x ∈ res, N env a b x))
    (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) (nx : Option String) :
    ∀ (ms : List Nat) (out : Array (Array Reading × Env)), (∀ m ∈ ms, m ≤ j) →
      (∀ x ∈ out, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x) →
      Triple A g ts (splitAt A g ts (fuel + 1) nt body pos env i j nx ms out)
        (fun res => ∀ x ∈ res, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x)
  | [], out, _, hout => by simp only [splitAt]; exact triple_pure hout
  | m :: ms, out, hms, hout => by
    obtain ⟨_, _, _, _, _, _, _, _, ihSa, ihSr, _, _, _, _⟩ := ih
    rw [splitAt.eq_def]
    dsimp only
    split
    · split
      · exact ihSa nt N hnt body pos env i j _ ms out (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hout
      · refine triple_bind (hnt env i m) fun as has => ?_
        refine triple_bind (ihSr body pos m j as.toList out (SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j)
          ?_ hout) fun out' hout' => ?_
        · intro a ha rest env₂ hseq
          exact ⟨m, a.1, a.2, rest, hms m (List.mem_cons_self ..), has a (Array.mem_def.mpr ha), hseq, rfl⟩
        · exact ihSa nt N hnt body pos env i j _ ms out' (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hout'
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine triple_bind (hnt env i m) fun as has => ?_
      refine triple_bind (ihSr body pos m j as.toList out (SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j)
        ?_ hout) fun out' hout' => ?_
      · intro a ha rest env₂ hseq
        exact ⟨m, a.1, a.2, rest, hms m (List.mem_cons_self ..), has a (Array.mem_def.mpr ha), hseq, rfl⟩
      · exact ihSa nt N hnt body pos env i j _ ms out' (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) hout'

theorem split_step (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env)))
    (N : Env → Nat → Nat → Array Reading × Env → Prop)
    (hnt : ∀ env a b, Triple A g ts (nt env a b) (fun res => ∀ x ∈ res, N env a b x))
    (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    Triple A g ts (split A g ts (fuel + 1) nt body pos env i j)
      (fun res => ∀ x ∈ res, SplitSpec (A := A) (g := g) (ts := ts) N body pos env i j x) := by
  obtain ⟨_, _, _, _, _, _, _, _, ihSa, _, _, _, _, _⟩ := ih
  simp only [split]
  split
  · rename_i hend
    have hend' : pos + 1 = body.size := by revert hend; simp
    refine triple_mono (hnt env i j) fun res hres x hx => ⟨j, x.1, x.2, #[], Nat.le_refl j, hres x hx, Reads.done hend', by simp⟩
  · refine ihSa nt N hnt body pos env i j _ _ #[] ?_ (by simp)
    intro m hm
    rw [List.mem_range'_1] at hm
    omega

theorem seq_step (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    Triple A g ts (seq A g ts (fuel + 1) body pos env i j)
      (fun res => ∀ x ∈ res, Seq A g ts body pos env i j x.1 x.2) := by
  obtain ⟨_, _, _, _, _, _, ihSF, _, _, _, _, _, _, _⟩ := ih
  simp only [seq]
  refine triple_bind triple_get fun st₀ _ => ?_
  split
  · exact triple_modify_pure (fun st h => h.congr rfl rfl rfl rfl) (by simp)
  · split
    · rename_i hend
      have hend' : pos = body.size := by revert hend; simp
      apply triple_pure
      intro x hx
      split at hx
      · rename_i hij
        have hij' : i = j := by revert hij; simp
        subst hij'
        simp only [Array.mem_singleton] at hx
        subst hx
        exact Reads.done hend'
      · simp at hx
    · refine triple_bind triple_get fun st hst => ?_
      split
      · rename_i n hmemo
        exact triple_pure (hst.2.1 body pos env i j n hmemo)
      · exact ihSF body pos env i j

theorem seqFresh_step (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    Triple A g ts (seqFresh A g ts (fuel + 1) body pos env i j)
      (fun res => ∀ x ∈ res, Seq A g ts body pos env i j x.1 x.2) := by
  obtain ⟨ihE, _, _, _, _, ihS, _, ihSp, _, _, ihT, _, _, _⟩ := ih
  simp only [seqFresh]
  refine triple_bind (triple_modify fun st h => h.congr rfl rfl rfl rfl) fun _ _ => ?_
  split
  · rename_i t hb
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      refine triple_bind (ihS body (pos + 1) env (i + 1) j) fun n hn => triple_remember ?_
      exact fun x hx => Reads.tok hb hc.1 hc.2 (hn x hx)
    · exact triple_bind (triple_pure (by simp)) fun n hn => triple_remember hn
  · rename_i s' p' x' hb
    refine triple_bind (ihSp _ (fun env a b y => a < b ∧ ∃ r so, y = (#[r], A.bind env s' so) ∧
      Exp A g ts (A.expected env s') p' x' g.chain0 a b r so) ?_ body pos env i j) fun n hn => triple_remember ?_
    · intro env a b
      refine triple_bind (ihE (A.expected env s') p' x' g.chain0 a b) fun rs hrs => triple_pure ?_
      intro y hy
      rw [Array.mem_map] at hy
      obtain ⟨⟨r, so⟩, hmem, rfl⟩ := hy
      exact ⟨(hrs _ hmem).1, r, so, rfl, (hrs _ hmem).2⟩
    · intro x hx
      obtain ⟨m, as, env₁, rest, hm, ⟨hlt, r, so, heq, hexp⟩, hseq, hx1⟩ := hn x hx
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hx1]
      exact Reads.hole hb hlt hm hexp hseq
  · rename_i hb
    refine triple_bind (ihSp _ (fun env a b y => a < b ∧ ∃ v, y = (#[v], env) ∧ VarReads g ts a b v)
      ?_ body pos env i j) fun n hn => triple_remember ?_
    · intro env a b
      apply triple_pure
      intro y hy
      rw [Array.mem_map] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      have hvo : varOf g ts a b g.prods.toList = some v := by
        cases h : varOf g ts a b g.prods.toList with
        | none => simp [h] at hv
        | some w => simp [h] at hv; subst hv; rfl
      exact ⟨varOf_lt _ hvo, v, rfl, hvo⟩
    · intro x hx
      obtain ⟨m, as, env₁, rest, hm, ⟨hlt, v, heq, hvr⟩, hseq, hx1⟩ := hn x hx
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hx1]
      exact Reads.var hb hlt hm hvr hseq
  · rename_i l n' hb
    refine triple_bind (ihSp _ (fun env a b y => a ≤ b ∧ Tail A g ts l n' env a b y.1 y.2)
      (fun env a b => ihT l n' env a b) body pos env i j) fun n hn => triple_remember ?_
    intro x hx
    obtain ⟨m, as, env₁, rest, hm, ⟨hle, ht⟩, hseq, hx1⟩ := hn x hx
    rw [hx1]
    exact Reads.tail hb hle hm ht hseq
  · exact triple_bind (triple_pure (by simp)) fun n hn => triple_remember hn

theorem prods_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) :
    ∀ (ks : List Nat) (out : Array (Reading × String)), i < j → Cands (A := A) (g := g) s ks →
      (∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) →
      Triple A g ts (prods A g ts (fuel + 1) s p excl i j ks out)
        (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)
  | [], out, _, _, hout => by simp only [prods]; exact triple_pure hout
  | k :: ks, out, hij, hks, hout => by
    obtain ⟨_, _, _, ihP, _, ihS, _, _, _, _, _, _, _, _⟩ := ih
    rw [prods.eq_def]
    dsimp only
    split
    · exact ihP s p excl i j ks out hij (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hout
    · rename_i htried
      have ht : tried g ts p excl i j k = true := by revert htried; simp
      obtain ⟨pr, body, hk, hex, hcoe, hprec⟩ := tried_spec ht
      obtain ⟨pr', body', hk', hvar, hcompat⟩ := hks k (List.mem_cons_self ..)
      rw [hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      split
      · rename_i pr'' body'' hk''
        rw [hk] at hk''
        simp only [Option.some.injEq, Prod.mk.injEq] at hk''
        obtain ⟨rfl, rfl⟩ := hk''
        refine triple_bind (ihS body 0 #[] i j) fun rs hrs => ?_
        refine triple_bind (triple_addProds s pr (P := fun x => ∀ ch, Exp A g ts s p excl ch i j x.1 x.2)
          (R := fun x => Seq A g ts body 0 #[] i j x.1 x.2) ?_ rs.toList out
          (fun x hx => hrs x (Array.mem_def.mpr hx)) hout) fun out' hout' =>
          ihP s p excl i j ks out' hij (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hout'
        intro cs env hseq hc ch
        exact Reads.prod hk hvar hcompat hex hcoe hprec hij hseq hc
      · rename_i hnone
        exact absurd hk (hnone pr body)

theorem coes_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) :
    ∀ (ks : List Nat) (out : Array (Reading × String)), i < j → Cands (A := A) (g := g) s ks →
      (∀ x ∈ out, Exp A g ts s p excl ch i j x.1 x.2) →
      Triple A g ts (coes A g ts (fuel + 1) s p excl ch i j ks out)
        (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2)
  | [], out, _, _, hout => by simp only [coes]; exact triple_pure hout
  | kk :: ks, out, hij, hks, hout => by
    obtain ⟨ihE, _, _, _, ihC, _⟩ := ih
    rw [coes.eq_def]
    dsimp only
    have hrest := ihC s p excl ch i j ks out hij (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hout
    split
    · rename_i pr body hk
      split
      · exact hrest
      · rename_i hcoe
        have hcoe' : pr.coercion = true := by cases h : pr.coercion <;> simp_all
        obtain ⟨pr', body', hk', hvar, hcompat⟩ := hks kk (List.mem_cons_self ..)
        rw [hk] at hk'
        simp only [Option.some.injEq, Prod.mk.injEq] at hk'
        obtain ⟨rfl, rfl⟩ := hk'
        split
        · rename_i s' pc x hb
          split
          · exact hrest
          · rename_i hallow
            have hallow' : ch.allows A pr s' = true := by cases h : ch.allows A pr s' <;> simp_all
            refine triple_bind (triple_mono (ihE (A.expected #[] s') p excl (ch.push A pr s' s) i j)
              fun res hres x hx => (hres x hx).2) fun args hargs => ?_
            refine triple_bind (triple_addCoes s pr s'
              (P := fun x => Exp A g ts s p excl ch i j x.1 x.2)
              (R := fun x => Exp A g ts (A.expected #[] s') p excl (ch.push A pr s' s) i j x.1 x.2)
              ?_ args.toList out
              (fun x hx => hargs x (Array.mem_def.mpr hx)) hout) fun out' hout' =>
              ihC s p excl ch i j ks out' hij (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hout'
            intro r so h hc
            exact Reads.coe hk hvar hcompat hcoe' hallow' hb h hc
        · exact hrest
    · exact hrest

theorem expr_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) :
    Triple A g ts (expr A g ts (fuel + 1) s p excl ch i j)
      (fun res => ∀ x ∈ res, i < j ∧ Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨_, ihEF, _⟩ := ih
  simp only [expr]
  split
  · exact triple_pure (by simp)
  · rename_i hij
    have hij' : i < j := by omega
    refine triple_bind triple_get fun st hst => ?_
    split
    · rename_i n hmemo
      exact triple_pure (hst.1 s p excl ch i j n hmemo)
    · exact triple_mono (ihEF s p excl ch i j hij') fun res hres x hx => ⟨hij', hres x hx⟩

theorem exprFresh_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) (hij : i < j) :
    Triple A g ts (exprFresh A g ts (fuel + 1) s p excl ch i j)
      (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨_, _, ihER, _⟩ := ih
  simp only [exprFresh]
  refine triple_bind triple_get fun st hst => ?_
  split
  · exact triple_modify_pure (fun st h => h.congr rfl rfl rfl rfl) (by simp)
  · refine triple_bind (triple_modify fun st h => h.congr rfl rfl rfl rfl) fun _ _ => ?_
    refine triple_bind triple_get fun st₂ hst₂ => ?_
    split
    · rename_i r' hr'
      exact triple_bind (triple_pure (Q := fun r => r = reachSplit A g s) (hst₂.2.2.1 s r' hr')) fun r hr =>
        ihER s p excl ch i j r hij hr
    · exact triple_bind (triple_modify fun st h => h.insertReach s) fun _ _ =>
        triple_bind (triple_pure (Q := fun r => r = reachSplit A g s) rfl) fun r hr =>
          ihER s p excl ch i j r hij hr

theorem exprDirect_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat)
    (r : Reach) (hij : i < j) (hr : r = reachSplit A g s) :
    Triple A g ts (exprDirect A g ts (fuel + 1) s p excl i j r)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨_, _, _, ihP, _, _, _, _, _, _, _, ihPa, ihG, _⟩ := ih
  obtain ⟨byTok, others, cks⟩ := r
  have hcands : Cands (A := A) (g := g) s (byTok.getD (ts.getD i "") #[] ++ others).toList := by
    have h1 : byTok = (reachSplit A g s).1 := congrArg Prod.fst hr
    have h2 : others = (reachSplit A g s).2.1 := congrArg (fun x => x.2.1) hr
    rw [h1, h2]
    exact cands_reachable s _
  simp only [exprDirect]
  refine triple_bind triple_get fun st hst => ?_
  split
  · rename_i n hmemo
    exact triple_pure fun x hx => (hst.2.2.2 s p excl i j n hmemo x hx).2
  · refine triple_bind (ihP s p excl i j _ #[] hij hcands (by simp)) fun out₁ hout₁ => ?_
    refine triple_bind (ihPa s p excl i j out₁ hij hout₁) fun out₂ hout₂ => ?_
    refine triple_bind (ihG s p excl i j out₂ hij hout₂) fun out₃ hout₃ => ?_
    exact triple_bind (triple_modify fun st h => h.insertD (fun x hx => ⟨hij, hout₃ x hx⟩)) fun _ _ =>
      triple_pure hout₃

theorem exprRead_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat)
    (r : Reach) (hij : i < j) (hr : r = reachSplit A g s) :
    Triple A g ts (exprRead A g ts (fuel + 1) s p excl ch i j r)
      (fun res => ∀ x ∈ res, Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨_, _, _, _, ihC, _, _, _, _, _, _, _, _, ihD⟩ := ih
  obtain ⟨byTok, others, cks⟩ := r
  have hcands : Cands (A := A) (g := g) s cks.toList := by
    have h3 : cks = (reachSplit A g s).2.2 := congrArg (fun x => x.2.2) hr
    rw [h3]
    exact coes_reachable s
  simp only [exprRead]
  refine triple_bind (ihD s p excl i j _ hij hr) fun direct hdirect => ?_
  refine triple_bind (ihC s p excl ch i j _ direct hij hcands fun x hx => hdirect x hx ch) fun out hout => ?_
  refine triple_bind (triple_modify fun st h => h.insertExp _ (fun x hx => ⟨hij, hout x hx⟩)) fun _ _ => ?_
  refine triple_bind triple_get fun st₄ _ => ?_
  split
  · exact triple_bind (triple_modify fun st h => h.congr rfl rfl rfl rfl) fun _ _ => triple_pure hout
  · exact triple_pure hout

theorem parens_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat)
    (out : Array (Reading × String)) (_hij : i < j) (hout : ∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) :
    Triple A g ts (parens A g ts (fuel + 1) s p excl i j out)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨ihE, _⟩ := ih
  simp only [parens]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    refine triple_bind (ihE s 0 none g.chain0 (i + 1) (j - 1)) fun rs hrs => triple_keepM _ _ ?_
    intro x hx
    rw [Array.mem_append] at hx
    rcases hx with hx | hx
    · exact hout x hx
    · exact fun ch => Reads.paren hc.1.1 hc.1.2 hc.2 (hrs x hx).2
  · exact triple_pure hout

theorem groups_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat)
    (out : Array (Reading × String)) (_hij : i < j) (hout : ∀ x ∈ out, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) :
    Triple A g ts (groups A g ts (fuel + 1) s p excl i j out)
      (fun res => ∀ x ∈ res, ∀ ch, Exp A g ts s p excl ch i j x.1 x.2) := by
  obtain ⟨ihE, _⟩ := ih
  simp only [groups]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    refine triple_bind (ihE s p none g.chain0 (i + 1) (j - 1)) fun rs hrs => triple_keepM _ _ ?_
    intro x hx
    rw [Array.mem_append] at hx
    rcases hx with hx | hx
    · exact hout x hx
    · exact fun ch => Reads.group hc.1.1 hc.1.2 hc.2 (hrs x hx).2
  · exact triple_pure hout

end Step

/-- The step. -/
theorem soundAll_succ {fuel : Nat} (ih : SoundAll (A := A) (g := g) (ts := ts) fuel) :
    SoundAll (A := A) (g := g) (ts := ts) (fuel + 1) :=
  ⟨expr_step ih, exprFresh_step ih, exprRead_step ih, prods_step ih, coes_step ih, seq_step ih,
    seqFresh_step ih, split_step ih, splitAt_step ih, splitRests_step ih, tail_step ih, parens_step ih,
    groups_step ih, exprDirect_step ih⟩

/-- The parser is sound, for any fuel. -/
theorem soundAll : ∀ fuel, SoundAll (A := A) (g := g) (ts := ts) fuel
  | 0 => soundAll_zero
  | fuel + 1 => soundAll_succ (soundAll fuel)

/-- The readings, with repeats dropped, are among the readings. -/
theorem mem_dedup (rs : Array Reading) (acc : Array Reading) :
    ∀ r ∈ rs.foldl (fun acc r => if acc.any (· == r) then acc else acc.push r) acc, r ∈ acc ∨ r ∈ rs := by
  refine Array.foldl_induction (motive := fun (_ : Nat) (acc' : Array Reading) => ∀ r ∈ acc', r ∈ acc ∨ r ∈ rs)
    (fun r hr => Or.inl hr) ?_
  intro n acc' hacc' r hr
  split at hr
  · exact hacc' r hr
  · rw [Array.mem_push] at hr
    rcases hr with hr | rfl
    · exact hacc' r hr
    · exact Or.inr (Array.getElem_mem _)

/-- A reading returned came from the parser's search, with some sort. -/
theorem mem_readings {s : String} {st : CState} {r : Reading}
    (h : r ∈ ((readings A g ts s).run st).1) :
    ∃ σ, (r, σ) ∈ ((expr A g ts (fuelFor g ts) s 0 none g.chain0 0 ts.size).run st).1 := by
  simp only [readings, StateT.run_bind, StateT.run_pure] at h
  rcases mem_dedup _ _ r h with h | h
  · simp at h
  · rw [Array.mem_map] at h
    obtain ⟨⟨r', σ⟩, hmem, rfl⟩ := h
    exact ⟨σ, hmem⟩

/-- **Soundness.** Every reading the parser returns is a reading in the
grammar, as an expression of the sort asked for, over the whole text. -/
theorem readBack_sound (s : String) {rd : Reading} (h : rd ∈ (readBackWith A g ts s).1) :
    ∃ σ, Exp A g ts s 0 none g.chain0 0 ts.size rd σ := by
  obtain ⟨σ, hmem⟩ := mem_readings (st := {}) h
  have hT := (soundAll (A := A) (g := g) (ts := ts) (fuelFor g ts)).1 s 0 none g.chain0 0 ts.size {} Inv.empty
  exact ⟨σ, (hT.2 _ hmem).2⟩

/-- **A validated formula reads as what it was rendered from.** When the
parser returns one reading, and it matches the expected reading, that
reading is a reading in the grammar, and it is the expected reading
wherever the expected one is definite. -/
theorem validated_sound (s : String) (ex rd : Reading) (h : (readBackWith A g ts s).1 = #[rd])
    (hm : ex.matches rd = true) : (∃ σ, Exp A g ts s 0 none g.chain0 0 ts.size rd σ) ∧ Matches ex rd :=
  ⟨readBack_sound s (by simp [h]), (matches_iff ex rd).mp hm⟩
end

end SpliceModel
