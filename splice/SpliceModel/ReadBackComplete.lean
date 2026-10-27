/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Pruning

/-!
# The parser is complete

Every reading in the grammar (`SpliceModel.Exp`) of a formula the parser
reads back with no flag set is among the readings it returns
(`readBack_complete`); with soundness, a formula read back as one reading
has exactly that reading (`readBack_unique`). The proof is the soundness
proof's induction on fuel, with an invariant on what the parser remembers
(every remembered answer holds every reading of its question), in triples
that hold when the flags end clear: a flag, once set, stays set, so no step
set one.
-/

namespace SpliceModel

open Imprimatur.Validate

/-! ## Triples that hold when the flags end clear -/

/-- No flag set. -/
def Clear (st : CState) : Prop := st.over = false ∧ st.pruned = false ∧ st.cut = false

section
variable (A : SortAlgebra) (g : Grammar) (ts : Array String)

/-- A reading by production `k`, as the `prod` rule gives it. -/
def ExpProd (k : Nat) (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) (r : Reading) (σ : String) : Prop :=
  ∃ pr body cs env, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true ∧
    excl ≠ some k ∧ pr.coercion = false ∧ p ≤ pr.prec ∧ i < j ∧ Seq A g ts body 0 #[] i j cs env ∧
    A.compat (A.expected env pr.sort) s = true ∧ r = mkReading pr.name pr.order cs ∧ σ = A.expected env pr.sort

/-- A reading through coercion `k`, as the `coe` rule gives it. -/
def ExpCoe (k : Nat) (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) (r : Reading)
    (σ : String) : Prop :=
  ∃ pr body s' pc x so, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true ∧
    pr.coercion = true ∧ ch.allows A pr s' = true ∧ body[0]? = some (ASym.hole s' pc x) ∧
    Exp A g ts (A.expected #[] s') p excl (ch.push A pr s') i j r so ∧
    A.compat (A.expected (A.bind #[] s' so) pr.sort) s = true ∧
    σ = A.expected (A.bind #[] s' so) pr.sort

/-- A reading not through a coercion of the question's own: by a
production, in the emitter's parentheses, or in a TeX group. -/
def Direct (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) (r : Reading) (σ : String) : Prop :=
  (∃ k, ExpProd A g ts k s p excl i j r σ) ∨
  (3 ≤ j - i ∧ ts[i]? = some "(" ∧ ts[j - 1]? = some ")" ∧ Exp A g ts s 0 none g.chain0 (i + 1) (j - 1) r σ) ∨
  (3 ≤ j - i ∧ ts[i]? = some "{" ∧ ts[j - 1]? = some "}" ∧ Exp A g ts s p none g.chain0 (i + 1) (j - 1) r σ)

/-- What the parser remembers is complete: every memoised answer holds
every reading of its question, and the productions remembered for a sort
are the reachable ones. -/
def CInv (st : CState) : Prop :=
  (∀ s p excl ch i j out, st.memo[(s, p, excl, ch, i, j)]? = some out →
    ∀ r σ, Exp A g ts s p excl ch i j r σ → (r, σ) ∈ out) ∧
  (∀ body pos env i j n, st.memoSeq[(body, pos, env, i, j)]? = some n →
    ∀ cs env', Seq A g ts body pos env i j cs env' → (cs, env') ∈ n) ∧
  (∀ s r, st.reach[s]? = some r → r = reachSplit A g s) ∧
  (∀ s p excl i j out, st.memoD[(s, p, excl, i, j)]? = some out →
    ∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ out)

/-- The flags only rise through the computation; and from a complete
state, when the flags end clear and `P` holds, the computation ends in a
complete state with a result that satisfies `Q`. -/
def CTriple {α : Type} (m : CountM α) (P : Prop) (Q : α → Prop) : Prop :=
  ∀ st, (Clear (m.run st).2 → Clear st) ∧
    (P → CInv A g ts st → Clear (m.run st).2 → CInv A g ts (m.run st).2 ∧ Q (m.run st).1)

variable {A g ts}

theorem CInv.empty : CInv A g ts {} := by
  refine ⟨fun s p excl ch i j out h => ?_, fun body pos env i j n h => ?_, fun s r h => ?_,
    fun s p excl i j out h => ?_⟩ <;> simp at h

theorem ctriple_pure {α : Type} {a : α} {P : Prop} {Q : α → Prop} (h : P → Q a) : CTriple A g ts (pure a) P Q :=
  fun _ => ⟨id, fun hP hinv _ => ⟨hinv, h hP⟩⟩

theorem ctriple_bind {α β : Type} {m : CountM α} {f : α → CountM β} {P : Prop} {Q : α → Prop} {R : β → Prop}
    (hm : CTriple A g ts m P Q) (hf : ∀ a, CTriple A g ts (f a) (P ∧ Q a) R) : CTriple A g ts (m >>= f) P R := by
  intro st
  obtain ⟨hm1, hm2⟩ := hm st
  obtain ⟨hf1, hf2⟩ := hf (m.run st).1 (m.run st).2
  refine ⟨fun hc => hm1 (hf1 hc), fun hP hinv hc => ?_⟩
  obtain ⟨hinv', hq⟩ := hm2 hP hinv (hf1 hc)
  exact hf2 ⟨hP, hq⟩ hinv' hc

theorem ctriple_mono {α : Type} {m : CountM α} {P : Prop} {Q R : α → Prop} (hm : CTriple A g ts m P Q)
    (h : P → ∀ a, Q a → R a) : CTriple A g ts m P R :=
  fun st => ⟨(hm st).1, fun hP hinv hc => ⟨((hm st).2 hP hinv hc).1, h hP _ ((hm st).2 hP hinv hc).2⟩⟩

theorem ctriple_weaken {α : Type} {m : CountM α} {P P' : Prop} {Q : α → Prop} (hP : P' → P)
    (hm : CTriple A g ts m P Q) : CTriple A g ts m P' Q :=
  fun st => ⟨(hm st).1, fun hP' => (hm st).2 (hP hP')⟩

/-- A triple with no precondition, under any. -/
theorem CTriple.ofTrue {α : Type} {m : CountM α} {P : Prop} {Q : α → Prop} (hm : CTriple A g ts m True Q) :
    CTriple A g ts m P Q :=
  ctriple_weaken (fun _ => trivial) hm

theorem ctriple_get {P : Prop} : CTriple A g ts get P (fun st => CInv A g ts st ∧ Clear st) :=
  fun _ => ⟨id, fun _ hinv hc => ⟨hinv, hinv, hc⟩⟩

/-- A change of state that leaves the flags as they are, and keeps the
invariant when the flags are clear and `P` holds. -/
theorem ctriple_modify {f : CState → CState} {P : Prop} (hC : ∀ st, Clear (f st) → Clear st)
    (hI : P → ∀ st, CInv A g ts st → Clear (f st) → CInv A g ts (f st)) :
    CTriple A g ts (modify f) P (fun _ => True) :=
  fun st => ⟨hC st, fun hP hinv hc => ⟨hI hP st hinv hc, trivial⟩⟩

/-- A computation that sets a flag: the flags do not end clear. -/
theorem ctriple_flag {α : Type} {f : CState → CState} {a : α} {P : Prop} {Q : α → Prop}
    (h : ∀ st, ¬ Clear (f st)) : CTriple A g ts (do modify f; return a) P Q :=
  fun st => ⟨fun hc => absurd hc (h st), fun _ _ hc => absurd hc (h st)⟩

theorem ctriple_over {α : Type} {P : Prop} {Q : Array α → Prop} :
    CTriple A g ts (do modify fun st => { st with over := true }; return (#[] : Array α)) P Q :=
  ctriple_flag fun _ hc => by simp [Clear] at hc

theorem ctriple_cut {α : Type} {P : Prop} {Q : Array α → Prop} :
    CTriple A g ts (do modify fun st => { st with cut := true }; return (#[] : Array α)) P Q :=
  ctriple_flag fun _ hc => by simp [Clear] at hc

/-- Changing anything but the memo tables keeps the invariant. -/
theorem CInv.congr {st st' : CState} (h : CInv A g ts st) (hm : st'.memo = st.memo)
    (hs : st'.memoSeq = st.memoSeq) (hr : st'.reach = st.reach) (hd : st'.memoD = st.memoD) : CInv A g ts st' := by
  refine ⟨fun s p excl ch i j out e => h.1 s p excl ch i j out ?_,
    fun body pos env i j n e => h.2.1 body pos env i j n ?_, fun s r e => h.2.2.1 s r ?_,
    fun s p excl i j out e => h.2.2.2 s p excl i j out ?_⟩
  · rwa [hm] at e
  · rwa [hs] at e
  · rwa [hr] at e
  · rwa [hd] at e

/-- Remembering a complete answer keeps the invariant. -/
theorem CInv.insertExp {st : CState} (h : CInv A g ts st) {s p excl ch i j out} (active : Std.HashMap _ Unit)
    (hout : ∀ r σ, Exp A g ts s p excl ch i j r σ → (r, σ) ∈ out) :
    CInv A g ts { st with active := active, memo := st.memo.insert (s, p, excl, ch, i, j) out } := by
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

/-- Remembering a complete answer of a body keeps the invariant. -/
theorem CInv.insertSeq {st : CState} (h : CInv A g ts st) {body pos env i j n}
    (hn : ∀ cs env', Seq A g ts body pos env i j cs env' → (cs, env') ∈ n) :
    CInv A g ts { st with memoSeq := st.memoSeq.insert (body, pos, env, i, j) n } := by
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
theorem CInv.insertReach {st : CState} (h : CInv A g ts st) (s : String) :
    CInv A g ts { st with reach := st.reach.insert s (reachSplit A g s) } := by
  refine ⟨h.1, h.2.1, fun s' r e => ?_, h.2.2.2⟩
  simp only [Std.HashMap.getElem?_insert] at e
  split at e
  · rename_i heq
    simp only [beq_iff_eq] at heq
    subst heq
    simp only [Option.some.injEq] at e
    exact e.symm
  · exact h.2.2.1 s' r e

/-- Remembering a complete answer not through a coercion keeps the
invariant. -/
theorem CInv.insertD {st : CState} (h : CInv A g ts st) {s p excl i j out}
    (hout : ∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ out) :
    CInv A g ts { st with memoD := st.memoD.insert (s, p, excl, i, j) out } := by
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

/-- `keepM` keeps everything, when the flags end clear. -/
theorem ctriple_keepM {α : Type} [BEq α] [LawfulBEq α] (key : α → String) (xs : Array α) {P : Prop} :
    CTriple A g ts (keepM key xs) P (fun out => ∀ x ∈ xs, x ∈ out) := by
  intro st
  simp only [keepM]
  split
  · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure]
    exact ⟨fun hc => absurd hc.2.1 (by simp), fun _ _ hc => absurd hc.2.1 (by simp)⟩
  · rename_i hp
    simp only [StateT.run_pure]
    refine ⟨id, fun _ hinv _ => ⟨hinv, keep_mem key xs (keep key xs).1 ?_⟩⟩
    rw [Bool.not_eq_true] at hp
    exact Prod.ext rfl hp

/-! ## The accumulators -/

/-- `addProds` adds every reading of the production, when the flags end
clear. -/
theorem ctriple_addProds (s : String) (pr : Imprimatur.Validate.Prod) :
    ∀ (rs : List (Array Reading × Env)) (out : Array (Reading × String)),
      CTriple A g ts (addProds A s pr rs out) True (fun res => (∀ x ∈ out, x ∈ res) ∧
        ∀ cs env, (cs, env) ∈ rs → A.compat (A.expected env pr.sort) s = true →
          (mkReading pr.name pr.order cs, A.expected env pr.sort) ∈ res)
  | [], out => by
    simp only [addProds]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun cs env h => by simp at h⟩
  | (cs, env) :: rest, out => by
    simp only [addProds]
    split
    · rename_i hc
      refine ctriple_mono (ctriple_addProds s pr rest out) fun _ res ⟨hsub, hrest⟩ => ⟨hsub, ?_⟩
      intro cs' env' hmem hc'
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact absurd hc' (by simpa using hc)
      · exact hrest cs' env' hmem hc'
    · refine ctriple_bind (ctriple_keepM _ _) fun out' => ?_
      refine ctriple_mono (ctriple_addProds s pr rest out').ofTrue fun ⟨_, hkeep⟩ res ⟨hsub, hrest⟩ => ?_
      refine ⟨fun x hx => hsub x (hkeep x (Array.mem_push.mpr (Or.inl hx))), ?_⟩
      intro cs' env' hmem hc'
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hsub _ (hkeep _ (Array.mem_push.mpr (Or.inr rfl)))
      · exact hrest cs' env' hmem hc'

/-- `addCoes` adds every reading through the coercion, when the flags end
clear. -/
theorem ctriple_addCoes (s : String) (pr : Imprimatur.Validate.Prod) (s' : String) :
    ∀ (args : List (Reading × String)) (out : Array (Reading × String)),
      CTriple A g ts (addCoes A s pr s' args out) True (fun res => (∀ x ∈ out, x ∈ res) ∧
        ∀ r so, (r, so) ∈ args → A.compat (A.expected (A.bind #[] s' so) pr.sort) s = true →
          (r, A.expected (A.bind #[] s' so) pr.sort) ∈ res)
  | [], out => by
    simp only [addCoes]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun r so h => by simp at h⟩
  | (r, so) :: rest, out => by
    simp only [addCoes]
    split
    · rename_i hc
      refine ctriple_mono (ctriple_addCoes s pr s' rest out) fun _ res ⟨hsub, hrest⟩ => ⟨hsub, ?_⟩
      intro r' so' hmem hc'
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact absurd hc' (by simpa using hc)
      · exact hrest r' so' hmem hc'
    · refine ctriple_bind (ctriple_keepM _ _) fun out' => ?_
      refine ctriple_mono (ctriple_addCoes s pr s' rest out').ofTrue fun ⟨_, hkeep⟩ res ⟨hsub, hrest⟩ => ?_
      refine ⟨fun x hx => hsub x (hkeep x (Array.mem_push.mpr (Or.inl hx))), ?_⟩
      intro r' so' hmem hc'
      rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hsub _ (hkeep _ (Array.mem_push.mpr (Or.inr rfl)))
      · exact hrest r' so' hmem hc'

/-- `joinRests` joins the reading with every reading of the rest, when the
flags end clear. -/
theorem ctriple_joinRests (a : Array Reading × Env) :
    ∀ (rests : List (Array Reading × Env)) (out : Array (Array Reading × Env)),
      CTriple A g ts (joinRests a rests out) True (fun res => (∀ x ∈ out, x ∈ res) ∧
        ∀ rest env₂, (rest, env₂) ∈ rests → (a.1 ++ rest, env₂) ∈ res)
  | [], out => by
    simp only [joinRests]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun rest env₂ h => by simp at h⟩
  | (rest, env₂) :: more, out => by
    simp only [joinRests]
    refine ctriple_bind (ctriple_keepM _ _) fun out' => ?_
    refine ctriple_mono (ctriple_joinRests a more out').ofTrue fun ⟨_, hkeep⟩ res ⟨hsub, hmore⟩ => ?_
    refine ⟨fun x hx => hsub x (hkeep x (Array.mem_push.mpr (Or.inl hx))), ?_⟩
    intro rest' env₂' hmem
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact hsub _ (hkeep _ (Array.mem_push.mpr (Or.inr rfl)))
    · exact hmore rest' env₂' hmem

/-! ## Facts about derivations -/

/-- Lists whose elements take at least a token: every notation's
(`Validate.ofRule` makes each element a hole). -/
abbrev ListsWF (g : Grammar) : Prop :=
  ∀ (l : Nat) elem sep, g.lists[l]? = some (elem, sep) → 1 ≤ minLenFrom (sep ++ elem) 0

theorem foldl_minLen (l : List ASym) (a : Nat) :
    l.foldl (fun n s => n + minLen s) a = a + l.foldl (fun n s => n + minLen s) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons s l ih =>
    simp only [List.foldl_cons]
    rw [ih (a + minLen s), ih (0 + minLen s)]
    omega

theorem minLenFrom_succ {body : Array ASym} {pos : Nat} {sym : ASym} (h : body[pos]? = some sym) :
    minLenFrom body pos = minLen sym + minLenFrom body (pos + 1) := by
  unfold minLenFrom
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  have hlt' : pos < body.toList.length := by simpa using hlt
  rw [List.drop_eq_getElem_cons hlt', List.foldl_cons, foldl_minLen, Nat.zero_add]
  rfl

theorem minLenFrom_end {body : Array ASym} {pos : Nat} (h : body.size ≤ pos) : minLenFrom body pos = 0 := by
  unfold minLenFrom
  rw [List.drop_of_length_le (by simpa using h)]
  rfl

theorem minLenFrom_append (xs ys : Array ASym) :
    minLenFrom (xs ++ ys) 0 = minLenFrom xs 0 + minLenFrom ys 0 := by
  unfold minLenFrom
  simp only [List.drop_zero, Array.toList_append, List.foldl_append]
  rw [foldl_minLen]

theorem minLenFrom_singleton (sym : ASym) : minLenFrom #[sym] 0 = minLen sym := by
  rw [minLenFrom_succ (body := #[sym]) (pos := 0) (sym := sym) (by simp), minLenFrom_end (by simp)]
  omega

/-- What a question spans: an expression at least a token, a body at least
what its symbols need, a list's rest at least a token per element
required. -/
abbrev Spans : Question → Prop
  | .expr _ _ _ _ i j => i < j
  | .body body pos _ i j => i + minLenFrom body pos ≤ j
  | .rest _ n _ i j => i + n ≤ j

theorem Reads.spans (hg : ListsWF g) {q : Question} {a : Answer} (h : Reads A g ts false q a) : Spans q := by
  induction h with
  | prod _ _ _ _ _ _ hij _ _ => exact hij
  | coe _ _ _ _ _ _ _ _ ih => exact ih
  | paren h3 _ _ _ => simp only [Spans]; omega
  | group h3 _ _ _ => simp only [Spans]; omega
  | done hend => simp only [Spans]; rw [minLenFrom_end (Nat.le_of_eq hend.symm)]; omega
  | tok hb _ _ _ ih => simp only [Spans] at ih ⊢; rw [minLenFrom_succ hb]; simp only [minLen]; omega
  | hole hb hlt hle _ _ _ ih => simp only [Spans] at ih ⊢; rw [minLenFrom_succ hb]; simp only [minLen]; omega
  | var hb hlt hle _ _ ih => simp only [Spans] at ih ⊢; rw [minLenFrom_succ hb]; simp only [minLen]; omega
  | tail hb hle hle' _ _ ih₁ ih₂ =>
    simp only [Spans] at ih₁ ih₂ ⊢; rw [minLenFrom_succ hb]; simp only [minLen]; omega
  | nil => simp only [Spans]; omega
  | more hl hij _ ih =>
    simp only [Spans] at ih ⊢
    rw [minLenFrom_append, minLenFrom_singleton] at ih
    simp only [minLen] at ih
    have := hg _ _ _ hl
    omega

/-- An expression spans at least a token. -/
theorem exp_lt (hg : ListsWF g) {s p excl ch i j r σ} (h : Exp A g ts s p excl ch i j r σ) : i < j :=
  Reads.spans hg h

/-- A body that starts with a token starts where it stands. -/
theorem seq_tok_head {body pos env i j cs env' t} (h : Seq A g ts body pos env i j cs env')
    (hb : body[pos]? = some (ASym.tok t)) : ts[i]? = some t := by
  cases h with
  | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
  | tok hb' _ hts _ => rw [hb'] at hb; cases hb; exact hts
  | hole hb' _ _ _ _ => rw [hb'] at hb; cases hb
  | var hb' _ _ _ _ => rw [hb'] at hb; cases hb
  | tail hb' _ _ _ _ => rw [hb'] at hb; cases hb

/-- A body that ends with a token, read from before its end, ends where it
stands. -/
abbrev LastTok (t : String) : Question → Prop
  | .body body pos _ _ j => pos < body.size → body[body.size - 1]? = some (ASym.tok t) → ts[j - 1]? = some t
  | _ => True

theorem Reads.lastTok {t : String} {q : Question} {a : Answer} (h : Reads A g ts false q a) : LastTok (ts := ts) t q := by
  induction h with
  | prod => trivial
  | coe => trivial
  | paren => trivial
  | group => trivial
  | nil => trivial
  | more => trivial
  | done hend => intro hpos _; omega
  | @tok body pos env i j t' cs env' hb hij hts hcont ih =>
    intro hpos hlast
    rcases Nat.lt_or_ge (pos + 1) body.size with hlt | hge
    · exact ih hlt hlast
    · have hsz : body.size - 1 = pos := by omega
      rw [hsz, hb] at hlast
      cases hlast
      cases hcont with
      | done hend => simpa using hts
      | tok hb' _ _ _ => rw [Array.getElem?_eq_none (by omega)] at hb'; cases hb'
      | hole hb' _ _ _ _ => rw [Array.getElem?_eq_none (by omega)] at hb'; cases hb'
      | var hb' _ _ _ _ => rw [Array.getElem?_eq_none (by omega)] at hb'; cases hb'
      | tail hb' _ _ _ _ => rw [Array.getElem?_eq_none (by omega)] at hb'; cases hb'
  | @hole body pos env i j s p x m r so cs env' hb hlt hle _ _ _ ih =>
    intro hpos hlast
    rcases Nat.lt_or_ge (pos + 1) body.size with hlt' | hge
    · exact ih hlt' hlast
    · have hsz : body.size - 1 = pos := by omega
      rw [hsz, hb] at hlast
      cases hlast
  | @var body pos env i j m v cs env' hb hlt hle _ _ ih =>
    intro hpos hlast
    rcases Nat.lt_or_ge (pos + 1) body.size with hlt' | hge
    · exact ih hlt' hlast
    · have hsz : body.size - 1 = pos := by omega
      rw [hsz, hb] at hlast
      cases hlast
  | @tail body pos env i j l n m as env₁ cs env' hb hle hle' _ _ _ ih =>
    intro hpos hlast
    rcases Nat.lt_or_ge (pos + 1) body.size with hlt' | hge
    · exact ih hlt' hlast
    · have hsz : body.size - 1 = pos := by omega
      rw [hsz, hb] at hlast
      cases hlast

theorem seq_last_tok {t : String} {body pos env i j cs env'} (h : Seq A g ts body pos env i j cs env')
    (hpos : pos < body.size) (hlast : body[body.size - 1]? = some (ASym.tok t)) : ts[j - 1]? = some t :=
  Reads.lastTok h hpos hlast

/-- A reading by a production is by a production tried. -/
theorem tried_complete {k s p excl i j r σ} (h : ExpProd A g ts k s p excl i j r σ) :
    tried g ts p excl i j k = true := by
  obtain ⟨pr, body, cs, env, hk, hvar, hcompat, hex, hcoe, hprec, hij, hseq, hc, rfl, rfl⟩ := h
  unfold tried
  rw [hk]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hex, hcoe⟩, hprec⟩, ?_⟩, ?_⟩
  · split
    · rename_i t hb
      simp only [beq_iff_eq]
      exact seq_tok_head hseq hb
    · rfl
  · split
    · rename_i t hb
      simp only [beq_iff_eq]
      have hb' : body[body.size - 1]? = some (ASym.tok t) := by simpa [Array.back?] using hb
      have hpos : 0 < body.size := by
        rcases Nat.eq_zero_or_pos body.size with h0 | h0
        · rw [h0] at hb'
          simp [h0] at hb'
        · exact h0
      exact seq_last_tok hseq hpos hb'
    · rfl

/-! ## The candidates are complete -/

theorem mem_reachable_foldl_of (s : String) : ∀ (l : List Nat) (init : Array Nat) (k : Nat),
    (k ∈ init ∨ (k ∈ l ∧ ∃ pr body, g.prods[k]? = some (pr, body) ∧ pr.isVar = false ∧ A.compat pr.sort s = true)) →
    k ∈ l.foldl (fun out i => match g.prods[i]? with
      | some (p, _) => if !p.isVar && A.compat p.sort s then out.push i else out
      | none => out) init
  | [], init, k, h => by
    simp only [List.foldl_nil]
    rcases h with h | ⟨h, _⟩
    · exact h
    · simp at h
  | i :: l, init, k, h => by
    simp only [List.foldl_cons]
    apply mem_reachable_foldl_of s l
    rcases h with h | ⟨hmem, pr, body, hk, hvar, hc⟩
    · left
      split
      · split
        · exact Array.mem_push.mpr (Or.inl h)
        · exact h
      · exact h
    · rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · left
        rw [hk]
        simp only [hvar, hc, Bool.not_false, Bool.and_self, ↓reduceIte]
        exact Array.mem_push.mpr (Or.inr rfl)
      · exact Or.inr ⟨hmem, pr, body, hk, hvar, hc⟩

/-- A production of a compatible sort, not a variable's name, is reachable. -/
theorem mem_reachable_of {s : String} {k : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym}
    (hk : g.prods[k]? = some (pr, body)) (hvar : pr.isVar = false) (hc : A.compat pr.sort s = true) :
    k ∈ reachable A g s := by
  unfold reachable
  apply mem_reachable_foldl_of s
  exact Or.inr ⟨List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hk).1, pr, body, hk, hvar, hc⟩

/-- A step keeps what was sorted in before. -/
theorem reachStep_mono (acc : Reach) (k : Nat) :
    (∀ t x, x ∈ acc.1.getD t #[] → x ∈ (reachStep g acc k).1.getD t #[]) ∧
    (∀ x ∈ acc.2.1, x ∈ (reachStep g acc k).2.1) ∧ (∀ x ∈ acc.2.2, x ∈ (reachStep g acc k).2.2) := by
  refine ⟨fun t x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rcases reachStep_byTok (g := g) acc k t with h | ⟨_, h⟩
    · rw [h]; exact hx
    · rw [h]; exact Array.mem_push.mpr (Or.inl hx)
  · by_cases ht : ∃ t, headSym g k = some (ASym.tok t)
    · obtain ⟨t, ht⟩ := ht
      rw [reachStep_others_tok acc k ht]
      exact hx
    · rw [reachStep_others_not acc k fun t h => ht ⟨t, h⟩]
      exact Array.mem_push.mpr (Or.inl hx)
  · rw [reachStep_cks]
    split
    · exact Array.mem_push.mpr (Or.inl hx)
    · exact hx

/-- A step sorts the production in: by its first token, among the others,
and among the coercions if it is one. -/
theorem mem_reachStep_self (acc : Reach) (k : Nat) :
    (∀ t, headSym g k = some (ASym.tok t) → k ∈ (reachStep g acc k).1.getD t #[]) ∧
    ((∀ t, headSym g k ≠ some (ASym.tok t)) → k ∈ (reachStep g acc k).2.1) ∧
    (isCoe g k = true → k ∈ (reachStep g acc k).2.2) := by
  refine ⟨fun t ht => ?_, fun hnt => ?_, fun hc => ?_⟩
  · rcases reachStep_byTok (g := g) acc k t with h | ⟨_, h⟩
    · exfalso
      simp only [reachStep] at h
      split at h
      · rename_i t' heq
        rw [heq] at ht
        cases ht
        simp only [Std.HashMap.getD_insert_self] at h
        exact absurd h (by simp)
      · rename_i hno
        exact hno t ht
    · rw [h]; exact Array.mem_push.mpr (Or.inr rfl)
  · rw [reachStep_others_not acc k hnt]
    exact Array.mem_push.mpr (Or.inr rfl)
  · rw [reachStep_cks, hc]
    simp

/-- A reachable production is sorted into `reachSplit`: by its first token,
or among the others; and among the coercions if it is one. -/
theorem mem_reachSplit_of {s : String} {k : Nat} (hk : k ∈ reachable A g s) :
    (∀ t, headSym g k = some (ASym.tok t) → k ∈ (reachSplit A g s).1.getD t #[]) ∧
    ((∀ t, headSym g k ≠ some (ASym.tok t)) → k ∈ (reachSplit A g s).2.1) ∧
    (isCoe g k = true → k ∈ (reachSplit A g s).2.2) := by
  obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem hk
  unfold reachSplit
  refine Array.foldl_induction (motive := fun n (acc : Reach) =>
    ∀ idx' (hs : idx' < (reachable A g s).size), idx' < n →
      (∀ t, headSym g (reachable A g s)[idx'] = some (ASym.tok t) →
        (reachable A g s)[idx'] ∈ acc.1.getD t #[]) ∧
      ((∀ t, headSym g (reachable A g s)[idx'] ≠ some (ASym.tok t)) → (reachable A g s)[idx'] ∈ acc.2.1) ∧
      (isCoe g (reachable A g s)[idx'] = true → (reachable A g s)[idx'] ∈ acc.2.2))
    ?_ ?_ idx hidx hidx
  · intro idx' _ h'
    exact absurd h' (Nat.not_lt_zero _)
  · intro n acc hacc idx' hs h'
    simp only [Fin.getElem_fin]
    rcases Nat.lt_or_ge idx' n with hlt | hge
    · obtain ⟨h1, h2, h3⟩ := hacc idx' hs hlt
      obtain ⟨m1, m2, m3⟩ := reachStep_mono (g := g) acc (reachable A g s)[n.1]
      exact ⟨fun t ht => m1 t _ (h1 t ht), fun hnt => m2 _ (h2 hnt), fun hc => m3 _ (h3 hc)⟩
    · have hidx' : idx' = n.1 := by omega
      subst hidx'
      exact mem_reachStep_self acc _

/-- A production that can read the span is among the candidates. -/
theorem mem_cands_of {s : String} {k i : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym}
    (hk : g.prods[k]? = some (pr, body)) (hvar : pr.isVar = false) (hc : A.compat pr.sort s = true)
    (hhead : ∀ t, body[0]? = some (ASym.tok t) → ts[i]? = some t) :
    k ∈ ((reachSplit A g s).1.getD (ts.getD i "") #[] ++ (reachSplit A g s).2.1).toList := by
  rw [Array.toList_append, List.mem_append, ← Array.mem_def, ← Array.mem_def]
  have hr := mem_reachSplit_of (A := A) (mem_reachable_of hk hvar hc)
  have hhd : headSym g k = body[0]? := by unfold headSym; rw [hk]; rfl
  by_cases ht : ∃ t, body[0]? = some (ASym.tok t)
  · obtain ⟨t, hb⟩ := ht
    left
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp (hhead t hb)
    have : ts.getD i "" = ts[i] := by simp [Array.getD, hlt]
    rw [this]
    exact hr.1 _ (by rw [hhd, hb])
  · right
    exact hr.2.1 fun t h => ht ⟨t, by rw [← hhd]; exact h⟩

/-- A coercion that can read the span is among the question's coercions. -/
theorem mem_coes_of {s : String} {k : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym}
    (hk : g.prods[k]? = some (pr, body)) (hvar : pr.isVar = false) (hc : A.compat pr.sort s = true)
    (hcoe : pr.coercion = true) : k ∈ (reachSplit A g s).2.2.toList := by
  rw [← Array.mem_def]
  refine (mem_reachSplit_of (A := A) (mem_reachable_of hk hvar hc)).2.2 ?_
  unfold isCoe
  rw [hk]
  exact hcoe

end

/-! ## The parser -/

section Complete
variable (A : SortAlgebra) (g : Grammar) (ts : Array String)

/-- Every reading of the expression question is among the answers. -/
def DomE (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) (res : Array (Reading × String)) :
    Prop :=
  ∀ r σ, Exp A g ts s p excl ch i j r σ → (r, σ) ∈ res

/-- Every reading of the body question is among the answers. -/
def DomS (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) (res : Array (Array Reading × Env)) : Prop :=
  ∀ cs env', Seq A g ts body pos env i j cs env' → (cs, env') ∈ res

/-- Every reading of the list's rest is among the answers. -/
def DomT (l n : Nat) (env : Env) (i j : Nat) (res : Array (Array Reading × Env)) : Prop :=
  ∀ cs env', Tail A g ts l n env i j cs env' → (cs, env') ∈ res

/-- Every reading of a nonterminal (by `N`) then the rest of the body, the
nonterminal ending where it may (at its start only for the rest of a
list), is among the answers. -/
def SplitDom (N : Env → Nat → Nat → Array Reading × Env → Prop) (body : Array ASym) (pos : Nat) (env : Env)
    (i j : Nat) (res : Array (Array Reading × Env)) : Prop :=
  ∀ m as env₁ rest env', (match body[pos]? with | some (ASym.tail _ _) => i ≤ m | _ => i < m) → m ≤ j →
    N env i m (as, env₁) → Seq A g ts body (pos + 1) env₁ m j rest env' → (as ++ rest, env') ∈ res

/-- The same, for the nonterminal ending at one of `ms`, where the token
that follows, if one does, stands. -/
def SplitAtDom (N : Env → Nat → Nat → Array Reading × Env → Prop) (body : Array ASym) (pos : Nat) (env : Env)
    (i j : Nat) (next : Option String) (ms : List Nat) (res : Array (Array Reading × Env)) : Prop :=
  ∀ m ∈ ms, (match next with | some t => ts[m]? = some t | none => True) →
    ∀ as env₁ rest env', N env i m (as, env₁) → Seq A g ts body (pos + 1) env₁ m j rest env' →
      (as ++ rest, env') ∈ res

/-- The statements proved together, for one amount of fuel. -/
def CompleteAll (fuel : Nat) : Prop :=
  (∀ s p excl ch i j, CTriple A g ts (expr A g ts fuel s p excl ch i j) True (DomE A g ts s p excl ch i j)) ∧
  (∀ s p excl ch i j, CTriple A g ts (exprFresh A g ts fuel s p excl ch i j) True (DomE A g ts s p excl ch i j)) ∧
  (∀ s p excl ch i j r, CTriple A g ts (exprRead A g ts fuel s p excl ch i j r) (r = reachSplit A g s)
    (DomE A g ts s p excl ch i j)) ∧
  (∀ s p excl i j ks out, CTriple A g ts (prods A g ts fuel s p excl i j ks out) True
    (fun res => (∀ x ∈ out, x ∈ res) ∧
      ∀ k ∈ ks, ∀ r σ, ExpProd A g ts k s p excl i j r σ → (r, σ) ∈ res)) ∧
  (∀ s p excl ch i j ks out, CTriple A g ts (coes A g ts fuel s p excl ch i j ks out) True
    (fun res => (∀ x ∈ out, x ∈ res) ∧
      ∀ k ∈ ks, ∀ r σ, ExpCoe A g ts k s p excl ch i j r σ → (r, σ) ∈ res)) ∧
  (∀ body pos env i j, CTriple A g ts (seq A g ts fuel body pos env i j) True (DomS A g ts body pos env i j)) ∧
  (∀ body pos env i j, CTriple A g ts (seqFresh A g ts fuel body pos env i j) (pos ≠ body.size)
    (DomS A g ts body pos env i j)) ∧
  (∀ (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env))) (N : Env → Nat → Nat → Array Reading × Env → Prop),
    (∀ env a b, CTriple A g ts (nt env a b) True (fun res => ∀ x, N env a b x → x ∈ res)) →
    ∀ body pos env i j, CTriple A g ts (split A g ts fuel nt body pos env i j) True
      (SplitDom A g ts N body pos env i j)) ∧
  (∀ (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env))) (N : Env → Nat → Nat → Array Reading × Env → Prop),
    (∀ env a b, CTriple A g ts (nt env a b) True (fun res => ∀ x, N env a b x → x ∈ res)) →
    ∀ body pos env i j next ms out, CTriple A g ts (splitAt A g ts fuel nt body pos env i j next ms out) True
      (fun res => (∀ x ∈ out, x ∈ res) ∧ SplitAtDom A g ts N body pos env i j next ms res)) ∧
  (∀ body pos m j (as : List (Array Reading × Env)) out,
    CTriple A g ts (splitRests A g ts fuel body pos m j as out) True
      (fun res => (∀ x ∈ out, x ∈ res) ∧
        ∀ a ∈ as, ∀ rest env', Seq A g ts body (pos + 1) a.2 m j rest env' → (a.1 ++ rest, env') ∈ res)) ∧
  (∀ l n env i j, CTriple A g ts (tail A g ts fuel l n env i j) True (DomT A g ts l n env i j)) ∧
  (∀ s p excl i j out, CTriple A g ts (parens A g ts fuel s p excl i j out) True
    (fun res => (∀ x ∈ out, x ∈ res) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "(" → ts[j - 1]? = some ")" →
      Exp A g ts s 0 none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ res)) ∧
  (∀ s p excl i j out, CTriple A g ts (groups A g ts fuel s p excl i j out) True
    (fun res => (∀ x ∈ out, x ∈ res) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "{" → ts[j - 1]? = some "}" →
      Exp A g ts s p none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ res)) ∧
  (∀ s p excl i j r, CTriple A g ts (exprDirect A g ts fuel s p excl i j r) (r = reachSplit A g s)
    (fun res => ∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ res))

variable {A g ts}

theorem completeAll_zero : CompleteAll A g ts 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s p excl ch i j; simp only [expr]; exact ctriple_over
  · intro s p excl ch i j; simp only [exprFresh]; exact ctriple_over
  · intro s p excl ch i j r; simp only [exprRead]; exact ctriple_over
  · intro s p excl i j ks out; simp only [prods]; exact ctriple_over
  · intro s p excl ch i j ks out; simp only [coes]; exact ctriple_over
  · intro body pos env i j; simp only [seq]; exact ctriple_over
  · intro body pos env i j; simp only [seqFresh]; exact ctriple_over
  · intro nt N _ body pos env i j; simp only [split]; exact ctriple_over
  · intro nt N _ body pos env i j next ms out; simp only [splitAt]; exact ctriple_over
  · intro body pos m j as out; simp only [splitRests]; exact ctriple_over
  · intro l n env i j; simp only [tail]; exact ctriple_over
  · intro s p excl i j out; simp only [parens]; exact ctriple_over
  · intro s p excl i j out; simp only [groups]; exact ctriple_over
  · intro s p excl i j r; simp only [exprDirect]; exact ctriple_over

/-- Remembering the readings of a body, then returning them. -/
theorem ctriple_remember {body pos env i j} {n : Array (Array Reading × Env)} {P : Prop}
    (hn : P → DomS A g ts body pos env i j n) :
    CTriple A g ts (do
      modify fun st => { st with memoSeq := st.memoSeq.insert (body, pos, env, i, j) n }
      pure n) P (DomS A g ts body pos env i j) :=
  ctriple_bind (ctriple_modify (fun _ h => h) fun hP _ hinv _ => hinv.insertSeq (hn hP)) fun _ =>
    ctriple_pure fun ⟨hP, _⟩ => hn hP

/-- The token a body's next symbol is, if it is one. -/
theorem next_some {body : Array ASym} {pos : Nat} {t : String}
    (h : (match body[pos + 1]? with | some (ASym.tok t) => some t | _ => none) = some t) :
    body[pos + 1]? = some (ASym.tok t) := by
  split at h
  · rename_i heq
    cases h
    exact heq
  · cases h

/-! ## The inductive step -/

namespace Complete

section Step
variable {fuel : Nat} (ih : CompleteAll A g ts fuel)
include ih

theorem tail_step (l r : Nat) (env : Env) (i j : Nat) :
    CTriple A g ts (tail A g ts (fuel + 1) l r env i j) True (DomT A g ts l r env i j) := by
  obtain ⟨_, _, _, _, _, ihS, _⟩ := ih
  simp only [tail]
  split
  · rename_i elem sep hl
    split
    · rename_i hij
      refine ctriple_bind (ihS _ 0 env i j).ofTrue fun rs => ?_
      refine ctriple_mono (ctriple_keepM _ _) fun ⟨_, hrs⟩ res hkeep cs env' hd => ?_
      cases hd with
      | nil => exact hkeep _ (Array.mem_append.mpr (Or.inl (by simp)))
      | more hl' _ hseq =>
        rw [hl] at hl'
        cases hl'
        exact hkeep _ (Array.mem_append.mpr (Or.inr (hrs cs env' hseq)))
    · rename_i hnij
      refine ctriple_pure fun _ cs env' hd => ?_
      cases hd with
      | nil => simp
      | more _ hij' _ => exact absurd hij' hnij
  · rename_i hnone
    refine ctriple_pure fun _ cs env' hd => ?_
    cases hd with
    | nil => simp
    | more hl' _ _ => exact absurd hl' (hnone _ _)

theorem splitRests_step (body : Array ASym) (pos m j : Nat) :
    ∀ (as : List (Array Reading × Env)) (out : Array (Array Reading × Env)),
      CTriple A g ts (splitRests A g ts (fuel + 1) body pos m j as out) True
        (fun res => (∀ x ∈ out, x ∈ res) ∧
          ∀ a ∈ as, ∀ rest env', Seq A g ts body (pos + 1) a.2 m j rest env' → (a.1 ++ rest, env') ∈ res)
  | [], out => by
    simp only [splitRests]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun a ha => by simp at ha⟩
  | a :: more, out => by
    obtain ⟨_, _, _, _, _, ihS, _, _, _, ihSr, _⟩ := ih
    simp only [splitRests]
    refine ctriple_bind (ihS body (pos + 1) a.2 m j).ofTrue fun rests => ?_
    refine ctriple_bind (ctriple_joinRests a rests.toList out).ofTrue fun out' => ?_
    refine ctriple_mono (ihSr body pos m j more out').ofTrue fun ⟨⟨_, hrests⟩, hsub', hjoin⟩ res ⟨hsub, hmore⟩ => ?_
    refine ⟨fun x hx => hsub x (hsub' x hx), ?_⟩
    intro a' ha' rest env' hseq
    rw [List.mem_cons] at ha'
    rcases ha' with rfl | ha'
    · exact hsub _ (hjoin rest env' (Array.mem_def.mp (hrests rest env' hseq)))
    · exact hmore a' ha' rest env' hseq

theorem splitAt_step (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env)))
    (N : Env → Nat → Nat → Array Reading × Env → Prop)
    (hnt : ∀ env a b, CTriple A g ts (nt env a b) True (fun res => ∀ x, N env a b x → x ∈ res))
    (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) (nx : Option String) :
    ∀ (ms : List Nat) (out : Array (Array Reading × Env)),
      CTriple A g ts (splitAt A g ts (fuel + 1) nt body pos env i j nx ms out) True
        (fun res => (∀ x ∈ out, x ∈ res) ∧ SplitAtDom A g ts N body pos env i j nx ms res)
  | [], out => by
    simp only [splitAt]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun m hm => by simp at hm⟩
  | m :: ms, out => by
    obtain ⟨_, _, _, _, _, _, _, _, ihSa, ihSr, _⟩ := ih
    have hgo : CTriple A g ts (do
        let as ← nt env i m
        let out ← splitRests A g ts fuel body pos m j as.toList out
        splitAt A g ts fuel nt body pos env i j nx ms out) True
        (fun res => (∀ x ∈ out, x ∈ res) ∧ SplitAtDom A g ts N body pos env i j nx (m :: ms) res) := by
      refine ctriple_bind (hnt env i m).ofTrue fun as => ?_
      refine ctriple_bind (ihSr body pos m j as.toList out).ofTrue fun out' => ?_
      refine ctriple_mono (ihSa nt N hnt body pos env i j nx ms out').ofTrue
        fun ⟨⟨_, has⟩, hsub', hdom'⟩ res ⟨hsub, hdom⟩ => ?_
      refine ⟨fun x hx => hsub x (hsub' x hx), ?_⟩
      intro m' hm' hok as' env₁ rest env' hN hseq
      rw [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · exact hsub _ (hdom' (as', env₁) (Array.mem_def.mp (has _ hN)) rest env' hseq)
      · exact hdom m' hm' hok as' env₁ rest env' hN hseq
    cases nx with
    | none =>
      rw [splitAt.eq_def]
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hgo
    | some t =>
      rw [splitAt.eq_def]
      dsimp only
      split
      · rename_i hne
        refine ctriple_mono (ihSa nt N hnt body pos env i j _ ms out) fun _ res ⟨hsub, hdom⟩ => ⟨hsub, ?_⟩
        intro m' hm' hok
        rw [List.mem_cons] at hm'
        rcases hm' with rfl | hm'
        · simp only [bne_iff_ne, ne_eq] at hne
          exact absurd hok hne
        · exact hdom m' hm' hok
      · exact hgo

theorem split_step (hg : ListsWF g) (nt : Env → Nat → Nat → CountM (Array (Array Reading × Env)))
    (N : Env → Nat → Nat → Array Reading × Env → Prop)
    (hnt : ∀ env a b, CTriple A g ts (nt env a b) True (fun res => ∀ x, N env a b x → x ∈ res))
    (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    CTriple A g ts (split A g ts (fuel + 1) nt body pos env i j) True (SplitDom A g ts N body pos env i j) := by
  obtain ⟨_, _, _, _, _, _, _, _, ihSa, _⟩ := ih
  simp only [split]
  split
  · rename_i hend
    have hend' : pos + 1 = body.size := by simpa using hend
    refine ctriple_mono (hnt env i j) fun _ res hres m as env₁ rest env' _ _ hN hseq => ?_
    cases hseq with
    | done _ => simpa using hres _ hN
    | tok hb _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
    | hole hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
    | var hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
    | tail hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
  · refine ctriple_mono (ihSa nt N hnt body pos env i j _ _ #[]) fun _ res ⟨_, hdom⟩ m as env₁ rest env' hstart hmj hN hseq => ?_
    have hspan := Reads.spans hg hseq
    simp only [Spans] at hspan
    refine hdom m ?_ ?_ as env₁ rest env' hN hseq
    · rw [List.mem_range'_1]
      split at hstart
      · rename_i heq
        simp only [heq]
        omega
      · rename_i hno
        split
        · rename_i heq
          exact absurd heq (hno _ _)
        · show i + 1 ≤ m ∧ m < i + 1 + (j - minLenFrom body (pos + 1) + 1 - (i + 1))
          omega
    · split
      · exact seq_tok_head hseq (next_some ‹_›)
      · trivial

theorem seq_step (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    CTriple A g ts (seq A g ts (fuel + 1) body pos env i j) True (DomS A g ts body pos env i j) := by
  obtain ⟨_, _, _, _, _, _, ihSF, _⟩ := ih
  simp only [seq]
  refine ctriple_bind ctriple_get fun st₀ => ?_
  split
  · exact ctriple_over
  · split
    · rename_i hend
      have hend' : pos = body.size := by simpa using hend
      refine ctriple_pure fun _ cs env' hd => ?_
      cases hd with
      | done _ => simp
      | tok hb _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
      | hole hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
      | var hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
      | tail hb _ _ _ _ => rw [Array.getElem?_eq_none (Nat.le_of_eq hend'.symm)] at hb; cases hb
    · rename_i hend
      refine ctriple_bind ctriple_get fun st => ?_
      split
      · rename_i n hmemo
        exact ctriple_pure fun ⟨_, hinv, _⟩ => hinv.2.1 body pos env i j n hmemo
      · exact ctriple_weaken (fun _ => by simpa using hend) (ihSF body pos env i j)

theorem seqFresh_step (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
    CTriple A g ts (seqFresh A g ts (fuel + 1) body pos env i j) (pos ≠ body.size)
      (DomS A g ts body pos env i j) := by
  obtain ⟨ihE, _, _, _, _, ihS, _, ihSp, _, _, ihT, _, _, _⟩ := ih
  simp only [seqFresh]
  refine ctriple_bind (ctriple_modify (fun _ h => h) fun _ _ hinv _ => hinv.congr rfl rfl rfl rfl) fun _ => ?_
  split
  · rename_i t hb
    split
    · rename_i hc
      refine ctriple_bind (ihS body (pos + 1) env (i + 1) j).ofTrue fun n => ctriple_remember fun ⟨_, hn⟩ cs env' hd => ?_
      cases hd with
      | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
      | tok hb' _ _ hcont => rw [hb] at hb'; cases hb'; exact hn cs env' hcont
      | hole hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | var hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | tail hb' _ _ _ _ => rw [hb] at hb'; cases hb'
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
      refine ctriple_bind (ctriple_pure (Q := fun (_ : Array (Array Reading × Env)) => True) fun _ => trivial)
        fun n => ctriple_remember fun _ cs env' hd => ?_
      cases hd with
      | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
      | tok hb' hij hts _ => rw [hb] at hb'; cases hb'; exact absurd hts (hc hij)
      | hole hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | var hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | tail hb' _ _ _ _ => rw [hb] at hb'; cases hb'
  · rename_i s' p' x' hb
    refine ctriple_bind (ihSp _ (fun env a b y => ∃ r so, y = (#[r], A.bind env s' so) ∧
      Exp A g ts (A.expected env s') p' x' g.chain0 a b r so) ?_ body pos env i j).ofTrue
      fun n => ctriple_remember fun ⟨_, hn⟩ cs env' hd => ?_
    · intro env a b
      refine ctriple_bind (ihE (A.expected env s') p' x' g.chain0 a b) fun rs => ctriple_pure fun ⟨_, hrs⟩ y hy => ?_
      obtain ⟨r, so, rfl, hexp⟩ := hy
      exact Array.mem_map.mpr ⟨(r, so), hrs r so hexp, rfl⟩
    · cases hd with
      | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
      | tok hb' _ _ _ => rw [hb] at hb'; cases hb'
      | hole hb' hlt hle hexp hseq =>
        rw [hb] at hb'
        cases hb'
        exact hn _ _ _ _ _ (by simp only [hb]; exact hlt) hle ⟨_, _, rfl, hexp⟩ hseq
      | var hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | tail hb' _ _ _ _ => rw [hb] at hb'; cases hb'
  · rename_i hb
    refine ctriple_bind (ihSp _ (fun env a b y => ∃ v, y = (#[v], env) ∧ VarReads g ts a b v) ?_ body pos env i j).ofTrue
      fun n => ctriple_remember fun ⟨_, hn⟩ cs env' hd => ?_
    · intro env a b
      refine ctriple_pure fun _ y hy => ?_
      obtain ⟨v, rfl, hv⟩ := hy
      unfold VarReads at hv
      rw [hv]
      simp
    · cases hd with
      | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
      | tok hb' _ _ _ => rw [hb] at hb'; cases hb'
      | hole hb' _ _ _ _ => rw [hb] at hb'; cases hb'
      | var hb' hlt hle hv hseq =>
        rw [hb] at hb'
        cases hb'
        exact hn _ _ _ _ _ (by simp only [hb]; exact hlt) hle ⟨_, rfl, hv⟩ hseq
      | tail hb' _ _ _ _ => rw [hb] at hb'; cases hb'
  · rename_i l n' hb
    refine ctriple_bind (ihSp _ (fun env a b y => Tail A g ts l n' env a b y.1 y.2)
      (fun env a b => ctriple_mono (ihT l n' env a b) fun _ res hres y hy => hres y.1 y.2 hy) body pos env i j).ofTrue
      fun n => ctriple_remember fun ⟨_, hn⟩ cs env' hd => ?_
    cases hd with
    | done hend => rw [Array.getElem?_eq_none (Nat.le_of_eq hend.symm)] at hb; cases hb
    | tok hb' _ _ _ => rw [hb] at hb'; cases hb'
    | hole hb' _ _ _ _ => rw [hb] at hb'; cases hb'
    | var hb' _ _ _ _ => rw [hb] at hb'; cases hb'
    | tail hb' hle hle' ht hseq =>
      rw [hb] at hb'
      cases hb'
      exact hn _ _ _ _ _ (by simp only [hb]; exact hle) hle' ht hseq
  · rename_i hb
    refine ctriple_bind (ctriple_pure (Q := fun (_ : Array (Array Reading × Env)) => True) fun _ => trivial)
      fun n => ctriple_remember fun ⟨⟨hpos, _⟩, _⟩ cs env' hd => ?_
    cases hd with
    | done hend => exact absurd hend hpos
    | tok hb' _ _ _ => rw [hb] at hb'; cases hb'
    | hole hb' _ _ _ _ => rw [hb] at hb'; cases hb'
    | var hb' _ _ _ _ => rw [hb] at hb'; cases hb'
    | tail hb' _ _ _ _ => rw [hb] at hb'; cases hb'

theorem prods_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) :
    ∀ (ks : List Nat) (out : Array (Reading × String)),
      CTriple A g ts (prods A g ts (fuel + 1) s p excl i j ks out) True
        (fun res => (∀ x ∈ out, x ∈ res) ∧
          ∀ k ∈ ks, ∀ r σ, ExpProd A g ts k s p excl i j r σ → (r, σ) ∈ res)
  | [], out => by
    simp only [prods]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun k hk => by simp at hk⟩
  | k :: ks, out => by
    obtain ⟨_, _, _, ihP, _, ihS, _⟩ := ih
    rw [prods.eq_def]
    dsimp only
    split
    · rename_i hnt
      refine ctriple_mono (ihP s p excl i j ks out) fun _ res ⟨hsub, hks⟩ => ⟨hsub, fun k' hk' r σ he => ?_⟩
      rw [List.mem_cons] at hk'
      rcases hk' with rfl | hk'
      · have := tried_complete he
        simp [this] at hnt
      · exact hks k' hk' r σ he
    · split
      · rename_i pr body hk
        refine ctriple_bind (ihS body 0 #[] i j).ofTrue fun rs => ?_
        refine ctriple_bind (ctriple_addProds s pr rs.toList out).ofTrue fun out' => ?_
        refine ctriple_mono (ihP s p excl i j ks out').ofTrue fun ⟨⟨_, hrs⟩, hsub', hadd⟩ res ⟨hsub, hks⟩ => ?_
        refine ⟨fun x hx => hsub x (hsub' x hx), fun k' hk' r σ he => ?_⟩
        rw [List.mem_cons] at hk'
        rcases hk' with rfl | hk'
        · obtain ⟨pr', body', cs, env, hk', _, _, _, _, _, _, hseq, hc, rfl, rfl⟩ := he
          rw [hk] at hk'
          simp only [Option.some.injEq, Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          exact hsub _ (hadd cs env (Array.mem_def.mp (hrs cs env hseq)) hc)
        · exact hks k' hk' r σ he
      · rename_i hnone
        refine ctriple_mono (ihP s p excl i j ks out) fun _ res ⟨hsub, hks⟩ => ⟨hsub, fun k' hk' r σ he => ?_⟩
        rw [List.mem_cons] at hk'
        rcases hk' with rfl | hk'
        · obtain ⟨pr', body', _, _, hk', _⟩ := he
          exact absurd hk' (hnone pr' body')
        · exact hks k' hk' r σ he

theorem coes_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) :
    ∀ (ks : List Nat) (out : Array (Reading × String)),
      CTriple A g ts (coes A g ts (fuel + 1) s p excl ch i j ks out) True
        (fun res => (∀ x ∈ out, x ∈ res) ∧
          ∀ k ∈ ks, ∀ r σ, ExpCoe A g ts k s p excl ch i j r σ → (r, σ) ∈ res)
  | [], out => by
    simp only [coes]
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun k hk => by simp at hk⟩
  | kk :: ks, out => by
    obtain ⟨ihE, _, _, _, ihC, _⟩ := ih
    rw [coes.eq_def]
    dsimp only
    have hrest : ∀ (P : ∀ k' ∈ kk :: ks, ∀ r σ, ExpCoe A g ts k' s p excl ch i j r σ → ∀ pr body,
        g.prods[kk]? = some (pr, body) → k' = kk → False),
        CTriple A g ts (coes A g ts fuel s p excl ch i j ks out) True
          (fun res => (∀ x ∈ out, x ∈ res) ∧
            ∀ k' ∈ kk :: ks, ∀ r σ, ExpCoe A g ts k' s p excl ch i j r σ → (r, σ) ∈ res) := by
      intro hP
      refine ctriple_mono (ihC s p excl ch i j ks out) fun _ res ⟨hsub, hks⟩ => ⟨hsub, fun k' hk' r σ he => ?_⟩
      rw [List.mem_cons] at hk'
      rcases hk' with rfl | hk'
      · have ⟨pr', body', _, _, _, _, hk', _⟩ := he
        exact absurd rfl (hP k' (List.mem_cons_self ..) r σ he pr' body' hk')
      · exact hks k' hk' r σ he
    split
    · rename_i pr body hk
      split
      · rename_i hskip
        refine hrest fun k' _ r σ he pr' body' hk' hkk => ?_
        subst hkk
        obtain ⟨pr'', body'', _, _, _, _, hk'', _, _, hcoe, _⟩ := he
        rw [hk] at hk''
        simp only [Option.some.injEq, Prod.mk.injEq] at hk''
        obtain ⟨rfl, rfl⟩ := hk''
        rw [hcoe] at hskip
        simp at hskip
      · split
        · rename_i s' pc x hb
          split
          · rename_i hskip
            refine hrest fun k' _ r σ he pr' body' hk' hkk => ?_
            subst hkk
            obtain ⟨pr'', body'', s'', pc', x', so, hk'', _, _, _, hallow, hb', _⟩ := he
            rw [hk] at hk''
            simp only [Option.some.injEq, Prod.mk.injEq] at hk''
            obtain ⟨rfl, rfl⟩ := hk''
            rw [hb] at hb'
            cases hb'
            rw [hallow] at hskip
            simp at hskip
          · refine ctriple_bind (ihE (A.expected #[] s') p excl (ch.push A pr s') i j).ofTrue fun args => ?_
            refine ctriple_bind (ctriple_addCoes s pr s' args.toList out).ofTrue fun out' => ?_
            refine ctriple_mono (ihC s p excl ch i j ks out').ofTrue
              fun ⟨⟨_, hargs⟩, hsub', hadd⟩ res ⟨hsub, hks⟩ => ?_
            refine ⟨fun x hx => hsub x (hsub' x hx), fun k' hk' r σ he => ?_⟩
            rw [List.mem_cons] at hk'
            rcases hk' with rfl | hk'
            · obtain ⟨pr', body', s'', pc', x', so, hk', _, _, _, _, hb', hexp, hc', rfl⟩ := he
              rw [hk] at hk'
              simp only [Option.some.injEq, Prod.mk.injEq] at hk'
              obtain ⟨rfl, rfl⟩ := hk'
              rw [hb] at hb'
              cases hb'
              exact hsub _ (hadd r so (Array.mem_def.mp (hargs r so hexp)) hc')
            · exact hks k' hk' r σ he
        · rename_i hno
          refine hrest fun k' _ r σ he pr' body' hk' hkk => ?_
          subst hkk
          obtain ⟨pr'', body'', s', pc, x, _, hk'', _, _, _, _, hb, _⟩ := he
          rw [hk] at hk''
          simp only [Option.some.injEq, Prod.mk.injEq] at hk''
          obtain ⟨rfl, rfl⟩ := hk''
          exact hno s' pc x hb
    · rename_i hnone
      refine ctriple_mono (ihC s p excl ch i j ks out) fun _ res ⟨hsub, hks⟩ => ⟨hsub, fun k' hk' r σ he => ?_⟩
      rw [List.mem_cons] at hk'
      rcases hk' with rfl | hk'
      · obtain ⟨pr', body', _, _, _, _, hk', _⟩ := he
        exact absurd hk' (hnone pr' body')
      · exact hks k' hk' r σ he

theorem parens_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) (out : Array (Reading × String)) :
    CTriple A g ts (parens A g ts (fuel + 1) s p excl i j out) True
      (fun res => (∀ x ∈ out, x ∈ res) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "(" → ts[j - 1]? = some ")" →
        Exp A g ts s 0 none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ res) := by
  obtain ⟨ihE, _⟩ := ih
  simp only [parens]
  split
  · refine ctriple_bind (ihE s 0 none g.chain0 (i + 1) (j - 1)).ofTrue fun rs => ?_
    refine ctriple_mono (ctriple_keepM _ _) fun ⟨_, hrs⟩ res hkeep => ?_
    exact ⟨fun x hx => hkeep x (Array.mem_append.mpr (Or.inl hx)),
      fun r σ _ _ _ hd => hkeep _ (Array.mem_append.mpr (Or.inr (hrs r σ hd)))⟩
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun r σ h3 hl hr _ => absurd hr (hc ⟨h3, hl⟩)⟩

theorem groups_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) (out : Array (Reading × String)) :
    CTriple A g ts (groups A g ts (fuel + 1) s p excl i j out) True
      (fun res => (∀ x ∈ out, x ∈ res) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "{" → ts[j - 1]? = some "}" →
        Exp A g ts s p none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ res) := by
  obtain ⟨ihE, _⟩ := ih
  simp only [groups]
  split
  · refine ctriple_bind (ihE s p none g.chain0 (i + 1) (j - 1)).ofTrue fun rs => ?_
    refine ctriple_mono (ctriple_keepM _ _) fun ⟨_, hrs⟩ res hkeep => ?_
    exact ⟨fun x hx => hkeep x (Array.mem_append.mpr (Or.inl hx)),
      fun r σ _ _ _ hd => hkeep _ (Array.mem_append.mpr (Or.inr (hrs r σ hd)))⟩
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
    exact ctriple_pure fun _ => ⟨fun x hx => hx, fun r σ h3 hl hr _ => absurd hr (hc ⟨h3, hl⟩)⟩

theorem exprDirect_step (s : String) (p : Nat) (excl : Option Nat) (i j : Nat)
    (r : Reach) :
    CTriple A g ts (exprDirect A g ts (fuel + 1) s p excl i j r) (r = reachSplit A g s)
      (fun res => ∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ res) := by
  obtain ⟨_, _, _, ihP, _, _, _, _, _, _, _, ihPa, ihG, _⟩ := ih
  obtain ⟨byTok, others, cks⟩ := r
  simp only [exprDirect]
  refine ctriple_bind ctriple_get fun st => ?_
  split
  · rename_i n hmemo
    exact ctriple_pure fun ⟨_, hinv, _⟩ => hinv.2.2.2 s p excl i j n hmemo
  · refine ctriple_bind (ihP s p excl i j _ #[]).ofTrue fun out₁ => ?_
    refine ctriple_bind (ihPa s p excl i j out₁).ofTrue fun out₂ => ?_
    refine ctriple_bind (ihG s p excl i j out₂).ofTrue fun out₃ => ?_
    have hdom : ((((byTok, others, cks) = reachSplit A g s ∧ (CInv A g ts st ∧ Clear st)) ∧
        ((∀ x ∈ (#[] : Array (Reading × String)), x ∈ out₁) ∧
          ∀ k ∈ (byTok.getD (ts.getD i "") #[] ++ others).toList, ∀ r σ,
            ExpProd A g ts k s p excl i j r σ → (r, σ) ∈ out₁)) ∧
        ((∀ x ∈ out₁, x ∈ out₂) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "(" → ts[j - 1]? = some ")" →
          Exp A g ts s 0 none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ out₂)) ∧
        ((∀ x ∈ out₂, x ∈ out₃) ∧ ∀ r σ, 3 ≤ j - i → ts[i]? = some "{" → ts[j - 1]? = some "}" →
          Exp A g ts s p none g.chain0 (i + 1) (j - 1) r σ → (r, σ) ∈ out₃) →
        ∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ out₃ := by
      intro hP r σ hd
      obtain ⟨⟨⟨⟨hr, _⟩, _, hP₁⟩, hsub₂, hPa⟩, hsub₃, hG⟩ := hP
      have h1 : byTok = (reachSplit A g s).1 := congrArg Prod.fst hr
      have h2 : others = (reachSplit A g s).2.1 := congrArg (fun x => x.2.1) hr
      subst h1 h2
      rcases hd with ⟨k, he⟩ | ⟨h3, hl, hr', hin⟩ | ⟨h3, hl, hr', hin⟩
      · have he' := he
        obtain ⟨pr, body, cs, env, hk, hvar, hc, _, _, _, _, hseq, _⟩ := he'
        exact hsub₃ _ (hsub₂ _ (hP₁ k (mem_cands_of hk hvar hc fun t hb => seq_tok_head hseq hb) r σ he))
      · exact hsub₃ _ (hPa r σ h3 hl hr' hin)
      · exact hG r σ h3 hl hr' hin
    exact ctriple_bind (ctriple_modify (fun _ h => h) fun hP _ hinv _ => hinv.insertD (hdom hP)) fun _ =>
      ctriple_pure fun ⟨hP, _⟩ => hdom hP

theorem exprRead_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat)
    (r : Reach) :
    CTriple A g ts (exprRead A g ts (fuel + 1) s p excl ch i j r) (r = reachSplit A g s)
      (DomE A g ts s p excl ch i j) := by
  obtain ⟨_, _, _, _, ihC, _, _, _, _, _, _, _, _, ihD⟩ := ih
  obtain ⟨byTok, others, cks⟩ := r
  simp only [exprRead]
  refine ctriple_bind (ihD s p excl i j (byTok, others, cks)) fun direct => ?_
  have hdom : ∀ out, (((byTok, others, cks) = reachSplit A g s ∧
      (∀ r σ, Direct A g ts s p excl i j r σ → (r, σ) ∈ direct)) ∧
      ((∀ x ∈ direct, x ∈ out) ∧ ∀ k ∈ cks.toList, ∀ r σ,
        ExpCoe A g ts k s p excl ch i j r σ → (r, σ) ∈ out)) →
      DomE A g ts s p excl ch i j out := by
    intro out hP r σ hd
    obtain ⟨⟨hr, hD⟩, hsub, hC⟩ := hP
    have h3 : cks = (reachSplit A g s).2.2 := congrArg (fun x => x.2.2) hr
    subst h3
    cases hd with
    | prod hk hvar hcompat hex hcoe hprec hij hseq hc =>
      exact hsub _ (hD _ _ (Or.inl ⟨_, _, _, _, _, hk, hvar, hcompat, hex, hcoe, hprec, hij, hseq, hc, rfl, rfl⟩))
    | coe hk hvar hcompat hcoe hallow hb hexp hc =>
      exact hC _ (mem_coes_of hk hvar hcompat hcoe) _ _
        ⟨_, _, _, _, _, _, hk, hvar, hcompat, hcoe, hallow.resolve_left Bool.false_ne_true, hb, hexp, hc, rfl⟩
    | paren h3 hl hr' hinner => exact hsub _ (hD _ _ (Or.inr (Or.inl ⟨h3, hl, hr', hinner⟩)))
    | group h3 hl hr' hinner => exact hsub _ (hD _ _ (Or.inr (Or.inr ⟨h3, hl, hr', hinner⟩)))
  refine ctriple_bind (ihC s p excl ch i j _ direct).ofTrue fun out => ?_
  refine ctriple_bind (ctriple_modify (fun _ h => h) fun hP _ hinv _ => hinv.insertExp _ (hdom out hP)) fun _ => ?_
  refine ctriple_bind ctriple_get fun _ => ?_
  split
  · exact ctriple_bind (ctriple_modify (fun _ h => h) fun _ _ hinv _ => hinv.congr rfl rfl rfl rfl) fun _ =>
      ctriple_pure fun ⟨⟨⟨hP, _⟩, _⟩, _⟩ => hdom out hP
  · exact ctriple_pure fun ⟨⟨hP, _⟩, _⟩ => hdom out hP

theorem exprFresh_step (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) :
    CTriple A g ts (exprFresh A g ts (fuel + 1) s p excl ch i j) True (DomE A g ts s p excl ch i j) := by
  obtain ⟨_, _, ihER, _⟩ := ih
  simp only [exprFresh]
  refine ctriple_bind ctriple_get fun _ => ?_
  split
  · exact ctriple_cut
  · refine ctriple_bind (ctriple_modify (fun _ h => h) fun _ _ hinv _ => hinv.congr rfl rfl rfl rfl) fun _ => ?_
    refine ctriple_bind ctriple_get fun _ => ?_
    split
    · rename_i r' hr'
      refine ctriple_bind (ctriple_pure (Q := fun r => r = reachSplit A g s) fun ⟨_, hinv, _⟩ => hinv.2.2.1 s r' hr')
        fun r => ?_
      exact ctriple_weaken (fun hP => hP.2) (ihER s p excl ch i j r)
    · refine ctriple_bind (ctriple_modify (fun _ h => h) fun _ _ hinv _ => hinv.insertReach s) fun _ => ?_
      refine ctriple_bind (ctriple_pure (Q := fun r => r = reachSplit A g s) fun _ => rfl) fun r => ?_
      exact ctriple_weaken (fun hP => hP.2) (ihER s p excl ch i j r)

theorem expr_step (hg : ListsWF g) (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) :
    CTriple A g ts (expr A g ts (fuel + 1) s p excl ch i j) True (DomE A g ts s p excl ch i j) := by
  obtain ⟨_, ihEF, _⟩ := ih
  simp only [expr]
  split
  · rename_i hij
    exact ctriple_pure fun _ r σ hd => absurd (exp_lt hg hd) (Nat.not_lt.mpr hij)
  · refine ctriple_bind ctriple_get fun _ => ?_
    split
    · rename_i n hmemo
      exact ctriple_pure fun ⟨_, hinv, _⟩ => hinv.1 s p excl ch i j n hmemo
    · exact (ihEF s p excl ch i j).ofTrue

end Step

end Complete

/-- The step. -/
theorem completeAll_succ (hg : ListsWF g) {fuel : Nat} (ih : CompleteAll A g ts fuel) :
    CompleteAll A g ts (fuel + 1) :=
  ⟨Complete.expr_step ih hg, Complete.exprFresh_step ih, Complete.exprRead_step ih,
    Complete.prods_step ih, Complete.coes_step ih, Complete.seq_step ih, Complete.seqFresh_step ih,
    Complete.split_step ih hg, Complete.splitAt_step ih, Complete.splitRests_step ih,
    Complete.tail_step ih, Complete.parens_step ih, Complete.groups_step ih, Complete.exprDirect_step ih⟩

/-- The parser is complete, for any fuel. -/
theorem completeAll (hg : ListsWF g) : ∀ fuel, CompleteAll A g ts fuel
  | 0 => completeAll_zero
  | fuel + 1 => completeAll_succ hg (completeAll hg fuel)

/-! ## The theorems -/

/-- Dropping repeats keeps every reading. -/
theorem mem_dedup_of : ∀ (l : List Reading) (acc : Array Reading) (r : Reading), r ∈ acc ∨ r ∈ l →
    r ∈ l.foldl (fun acc r => if acc.any (· == r) then acc else acc.push r) acc
  | [], acc, r, h => by
    simp only [List.foldl_nil]
    rcases h with h | h
    · exact h
    · simp at h
  | x :: l, acc, r, h => by
    simp only [List.foldl_cons]
    apply mem_dedup_of l
    rcases h with h | h
    · left
      split
      · exact h
      · exact Array.mem_push.mpr (Or.inl h)
    · rw [List.mem_cons] at h
      rcases h with rfl | h
      · left
        split
        · rename_i hany
          simp only [Array.any_eq_true, beq_iff_eq] at hany
          obtain ⟨n, hn, rfl⟩ := hany
          exact Array.getElem_mem hn
        · exact Array.mem_push.mpr (Or.inr rfl)
      · exact Or.inr h

/-- `readings` runs the parser on the whole text, and drops repeats. -/
theorem readings_run (s : String) (st : CState) :
    (readings A g ts s).run st =
      ((((expr A g ts (fuelFor g ts) s 0 none g.chain0 0 ts.size).run st).1.map (·.1)).foldl
        (fun acc r => if acc.any (· == r) then acc else acc.push r) #[],
       ((expr A g ts (fuelFor g ts) s 0 none g.chain0 0 ts.size).run st).2) := rfl

/-- Flags clear at the end: the state is clear, and the grammar's lists
take tokens. -/
theorem clear_of_flags {st : CState} (h : (st.flags g).any = false) : Clear st ∧ listsWF g = true := by
  simp only [Flags.any, CState.flags, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at h
  exact ⟨⟨h.1.1.1.1, h.1.1.2, h.1.2⟩, h.2⟩

/-- `listsWF` decides `ListsWF`. -/
theorem listsWF_spec (h : listsWF g = true) : ListsWF g := by
  intro l elem sep hl
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hl
  have := Array.all_eq_true_iff_forall_mem.mp h _ (hget ▸ Array.getElem_mem hlt)
  simpa using this

/-- **Completeness.** When no flag is set, every reading in the grammar of
the whole text as sort `s` is among the readings the parser returns. -/
theorem readBack_complete (s : String) (hf : (readBackWith A g ts s).2.any = false)
    {rd : Reading} {σ : String} (h : Exp A g ts s 0 none g.chain0 0 ts.size rd σ) : rd ∈ (readBackWith A g ts s).1 := by
  have hrun := readings_run (A := A) (g := g) (ts := ts) s {}
  have hf' : (((readings A g ts s).run {}).2.flags g).any = false := hf
  rw [hrun] at hf'
  obtain ⟨hclear, hwf⟩ := clear_of_flags hf'
  have hT := (completeAll (A := A) (ts := ts) (listsWF_spec hwf) (fuelFor g ts)).1 s 0 none g.chain0 0 ts.size
    ({} : CState)
  obtain ⟨_, hdom⟩ := hT.2 trivial CInv.empty hclear
  show rd ∈ ((readings A g ts s).run {}).1
  rw [hrun]
  dsimp only
  rw [← Array.foldl_toList]
  apply mem_dedup_of
  right
  rw [← Array.mem_def, Array.mem_map]
  exact ⟨(rd, σ), hdom rd σ h, rfl⟩

/-- **Uniqueness.** When the parser returns one reading with no flag set,
every reading in the grammar is that one. -/
theorem readBack_unique (s : String) {rd : Reading} (h : (readBackWith A g ts s).1 = #[rd])
    (hf : (readBackWith A g ts s).2.any = false) {rd' : Reading} {σ : String}
    (h' : Exp A g ts s 0 none g.chain0 0 ts.size rd' σ) : rd' = rd := by
  have := readBack_complete s hf h'
  rw [h] at this
  simpa using this

/-- **Pollack-consistency of a formula.** When the parser returns one
reading with no flag set, and it matches the expected reading: the
formula has a reading in the grammar, and every reading it has in the
grammar matches the expected one. -/
theorem pollack (s : String) (ex rd : Reading) (h : (readBackWith A g ts s).1 = #[rd])
    (hf : (readBackWith A g ts s).2.any = false) (hm : ex.matches rd = true) :
    (∃ σ, Exp A g ts s 0 none g.chain0 0 ts.size rd σ) ∧
      ∀ rd' σ, Exp A g ts s 0 none g.chain0 0 ts.size rd' σ → Matches ex rd' :=
  ⟨readBack_sound s (by simp [h]), fun rd' σ h' => by
    rw [readBack_unique s h hf h']
    exact (matches_iff ex rd).mp hm⟩

end Complete

end SpliceModel
