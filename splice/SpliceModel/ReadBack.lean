/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.ReadBack

/-!
# Reading back, specified and proved sound

The extractor reads every formula it renders back in the notation's
grammar (`Imprimatur.ReadBack`, docs/verified-validator.md). Here is what
"reads back as" means, as inductive relations (`Exp`, `Seq`, `Tail`) that
say the parser's search declaratively, and the theorems about the parser
that runs:

- **Soundness** (`expr_sound`): every reading the parser returns is a
  reading in the grammar, with the sort it is given.
- **Matching** (`matches_iff`): `Reading.matches` decides `Matches`, the
  structural relation in which `any` stands for any reading.

Sorts are the parser's parameter (`SortAlgebra`), so these hold for every
algebra of sorts. Completeness is `SpliceModel.ReadBackComplete`.
-/

namespace SpliceModel

open Imprimatur.Validate

/-! ## Matching -/

mutual
/-- A reading matches the expected one: `any` matches any reading, and a
node matches a node of the same name whose children match, pairwise. -/
inductive Matches : Reading → Reading → Prop
  /-- `any` -/
  | any (r : Reading) : Matches .any r
  /-- the same name, and matching children -/
  | node (n : String) {ks ks' : List Reading} : MatchesList ks ks' → Matches (.node n ks) (.node n ks')

/-- Children match, pairwise. -/
inductive MatchesList : List Reading → List Reading → Prop
  /-- none -/
  | nil : MatchesList [] []
  /-- the first, then the rest -/
  | cons {k k' : Reading} {ks ks' : List Reading} : Matches k k' → MatchesList ks ks' → MatchesList (k :: ks) (k' :: ks')
end

mutual
theorem matches_iff : ∀ (e r : Reading), Reading.matches e r = true ↔ Matches e r
  | .any, r => by simp [Reading.matches, Matches.any]
  | .node n ks, .any => by
    simp only [Reading.matches, Bool.false_eq_true, false_iff]
    intro h; cases h
  | .node n ks, .node n' ks' => by
    simp only [Reading.matches, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨rfl, h⟩
      exact .node n ((matchesList_iff ks ks').mp h)
    · intro h
      cases h with
      | node _ h => exact ⟨rfl, (matchesList_iff ks ks').mpr h⟩
termination_by e _ => sizeOf e

theorem matchesList_iff : ∀ (ks ks' : List Reading), Reading.matchesList ks ks' = true ↔ MatchesList ks ks'
  | [], [] => by simp [Reading.matchesList, MatchesList.nil]
  | [], _ :: _ => by
    simp only [Reading.matchesList, Bool.false_eq_true, false_iff]
    intro h; cases h
  | _ :: _, [] => by
    simp only [Reading.matchesList, Bool.false_eq_true, false_iff]
    intro h; cases h
  | k :: ks, k' :: ks' => by
    simp only [Reading.matchesList, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      exact .cons ((matches_iff k k').mp h1) ((matchesList_iff ks ks').mp h2)
    · intro h
      cases h with
      | cons h1 h2 => exact ⟨(matches_iff k k').mpr h1, (matchesList_iff ks ks').mpr h2⟩
termination_by ks _ => sizeOf ks
end

mutual
/-- A reading with no `any` in it: what the parser finds. -/
inductive Definite : Reading → Prop
  /-- a node whose children are definite -/
  | node (n : String) {ks : List Reading} : DefiniteList ks → Definite (.node n ks)

/-- Readings each definite. -/
inductive DefiniteList : List Reading → Prop
  /-- none -/
  | nil : DefiniteList []
  /-- the first, then the rest -/
  | cons {k : Reading} {ks : List Reading} : Definite k → DefiniteList ks → DefiniteList (k :: ks)
end

mutual
/-- A definite reading matches an expected reading with no `any` only if it
is that reading. -/
theorem matches_definite_eq : ∀ {e r : Reading}, Definite e → Matches e r → e = r
  | .node n ks, .node _ ks', .node _ hd, .node _ hm => by
    rw [matchesList_definite_eq hd hm]
  | .node _ _, .any, _, h => by cases h
termination_by e _ _ _ => sizeOf e

theorem matchesList_definite_eq : ∀ {ks ks' : List Reading}, DefiniteList ks → MatchesList ks ks' → ks = ks'
  | [], [], _, _ => rfl
  | k :: ks, k' :: ks', .cons hd hds, .cons hm hms => by
    rw [matches_definite_eq hd hm, matchesList_definite_eq hds hms]
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
termination_by ks _ _ _ => sizeOf ks
end

/-! ## Readings equal -/

mutual
/-- `Reading.beq` decides equality. -/
theorem Reading.beq_iff : ∀ (a b : Reading), Reading.beq a b = true ↔ a = b
  | .any, .any => by simp [Reading.beq]
  | .any, .node _ _ => by simp [Reading.beq]
  | .node _ _, .any => by simp [Reading.beq]
  | .node n ks, .node n' ks' => by
    simp only [Reading.beq, Bool.and_eq_true, beq_iff_eq, Reading.node.injEq]
    exact and_congr Iff.rfl (Reading.beqList_iff ks ks')
termination_by a _ => sizeOf a

theorem Reading.beqList_iff : ∀ (ks ks' : List Reading), Reading.beqList ks ks' = true ↔ ks = ks'
  | [], [] => by simp [Reading.beqList]
  | [], _ :: _ => by simp [Reading.beqList]
  | _ :: _, [] => by simp [Reading.beqList]
  | k :: ks, k' :: ks' => by
    simp only [Reading.beqList, Bool.and_eq_true, List.cons.injEq]
    exact and_congr (Reading.beq_iff k k') (Reading.beqList_iff ks ks')
termination_by ks _ => sizeOf ks
end

instance : LawfulBEq Reading where
  eq_of_beq h := (Reading.beq_iff _ _).mp h
  rfl := (Reading.beq_iff _ _).mpr rfl

/-! ## The grammar's readings -/

section
variable (A : SortAlgebra) (g : Grammar) (ts : Array String)

/-- A bound variable's name, by the grammar's atoms. -/
def VarReads (i j : Nat) (v : Reading) : Prop := varOf g ts i j g.prods.toList = some v

end

/-- A question the parser asks of a span of the text. -/
inductive Question where
  /-- an expression of sort `s`, at precedence `p`, not by production
  `excl`, through the invisible coercions the chain `ch` allows -/
  | expr (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat)
  /-- the rest of a body, `body[pos:]`, under bindings `env` -/
  | body (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat)
  /-- the rest of list `l`, `n` more elements required, under bindings `env` -/
  | rest (l n : Nat) (env : Env) (i j : Nat)

/-- An answer: a reading with its sort, or children with the bindings after
them. -/
inductive Answer where
  /-- a reading, of a sort -/
  | one (r : Reading) (σ : String)
  /-- children, and the bindings after them -/
  | many (cs : Array Reading) (env : Env)

section
variable (A : SortAlgebra) (g : Grammar) (ts : Array String) (free : Bool)

/-- `ts[i:j]` reads back (DESIGN §18.4): a question of the span, and an
answer to it. An expression question is answered by a production of a
compatible sort at or above the precedence, its body read left to right,
or through a coercion not on the chain already, or inside the emitter's
parentheses or a TeX group; a body question by its symbols in turn, a hole
read at the sort the bindings so far give it and binding its type
variables; a list's rest by nothing, when none is required, or a
separator, an element and the rest. A reading's sort is its own: the
production's under its bindings, or the coercion's.

With `free` set, a coercion is applied whatever the chain above it: this
is the unrestricted grammar, whose chains of coercions are of any length,
against which the chain rule is measured (`ExpFree`,
`SpliceModel.ReadBackChains`). -/
inductive Reads : Question → Answer → Prop
  /-- By a production of a compatible sort, at or above the precedence, not
  the excluded one and not a coercion: its body read, its sort under the
  bindings compatible with the sort asked for. -/
  | prod {s : String} {p : Nat} {excl : Option Nat} {ch : Chain} {i j kp : Nat} {pr : Imprimatur.Validate.Prod}
      {body : Array ASym} {cs : Array Reading} {env : Env} :
    g.prods[kp]? = some (pr, body) → pr.isVar = false → A.compat pr.sort s = true →
    excl ≠ some kp → pr.coercion = false → p ≤ pr.prec → i < j →
    Reads (.body body 0 #[] i j) (.many cs env) → A.compat (A.expected env pr.sort) s = true →
    Reads (.expr s p excl ch i j) (.one (mkReading pr.name pr.order cs) (A.expected env pr.sort))
  /-- Through a coercion of a compatible sort that the chain allows (any,
  if `free`): its
  argument read at the sort of the coercion's hole, under the same
  exclusion (an operand of a chain is never the chain, through a coercion
  either), below the coercion on the chain; and the coercion's sort with
  the argument's bound compatible. -/
  | coe {s : String} {p : Nat} {excl : Option Nat} {ch : Chain} {i j kp : Nat} {pr : Imprimatur.Validate.Prod}
      {body : Array ASym} {s' : String} {pc : Nat} {x : Option Nat} {r : Reading} {so : String} :
    g.prods[kp]? = some (pr, body) → pr.isVar = false → A.compat pr.sort s = true →
    pr.coercion = true → (free ∨ ch.allows A pr s' = true) → body[0]? = some (ASym.hole s' pc x) →
    Reads (.expr (A.expected #[] s') p excl (ch.push A pr s') i j) (.one r so) →
    A.compat (A.expected (A.bind #[] s' so) pr.sort) s = true →
    Reads (.expr s p excl ch i j) (.one r (A.expected (A.bind #[] s' so) pr.sort))
  /-- In the emitter's parentheses: read inside them, at any precedence. -/
  | paren {s : String} {p : Nat} {excl : Option Nat} {ch : Chain} {i j : Nat} {r : Reading} {σ : String} :
    3 ≤ j - i → ts[i]? = some "(" → ts[j - 1]? = some ")" →
    Reads (.expr s 0 none g.chain0 (i + 1) (j - 1)) (.one r σ) → Reads (.expr s p excl ch i j) (.one r σ)
  /-- In a TeX group: read inside it. -/
  | group {s : String} {p : Nat} {excl : Option Nat} {ch : Chain} {i j : Nat} {r : Reading} {σ : String} :
    3 ≤ j - i → ts[i]? = some "{" → ts[j - 1]? = some "}" →
    Reads (.expr s p none g.chain0 (i + 1) (j - 1)) (.one r σ) → Reads (.expr s p excl ch i j) (.one r σ)
  /-- The end of the body, with nothing left. -/
  | done {body : Array ASym} {pos : Nat} {env : Env} {i : Nat} :
    pos = body.size → Reads (.body body pos env i i) (.many #[] env)
  /-- A token, where it stands. -/
  | tok {body : Array ASym} {pos : Nat} {env : Env} {i j : Nat} {t : String} {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.tok t) → i < j → ts[i]? = some t →
    Reads (.body body (pos + 1) env (i + 1) j) (.many cs env') → Reads (.body body pos env i j) (.many cs env')
  /-- A hole: an expression of its sort under the bindings, which then binds
  its type variables. -/
  | hole {body : Array ASym} {pos : Nat} {env : Env} {i j : Nat} {s : String} {p : Nat} {x : Option Nat}
      {m : Nat} {r : Reading} {so : String} {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.hole s p x) → i < m → m ≤ j →
    Reads (.expr (A.expected env s) p x g.chain0 i m) (.one r so) →
    Reads (.body body (pos + 1) (A.bind env s so) m j) (.many cs env') →
    Reads (.body body pos env i j) (.many (#[r] ++ cs) env')
  /-- A bound variable's name. -/
  | var {body : Array ASym} {pos : Nat} {env : Env} {i j m : Nat} {v : Reading} {cs : Array Reading} {env' : Env} :
    body[pos]? = some ASym.var → i < m → m ≤ j → VarReads g ts i m v →
    Reads (.body body (pos + 1) env m j) (.many cs env') → Reads (.body body pos env i j) (.many (#[v] ++ cs) env')
  /-- The rest of a list, which may be empty. -/
  | tail {body : Array ASym} {pos : Nat} {env : Env} {i j l n m : Nat} {as : Array Reading} {env₁ : Env}
      {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.tail l n) → i ≤ m → m ≤ j →
    Reads (.rest l n env i m) (.many as env₁) → Reads (.body body (pos + 1) env₁ m j) (.many cs env') →
    Reads (.body body pos env i j) (.many (as ++ cs) env')
  /-- Nothing more, when none is required. -/
  | nil {l : Nat} {env : Env} {i : Nat} : Reads (.rest l 0 env i i) (.many #[] env)
  /-- The separator, an element, and the rest. -/
  | more {l n : Nat} {env : Env} {i j : Nat} {elem sep : Array ASym} {cs : Array Reading} {env' : Env} :
    g.lists[l]? = some (elem, sep) → i < j →
    Reads (.body (sep ++ elem ++ #[ASym.tail l (n - 1)]) 0 env i j) (.many cs env') →
    Reads (.rest l n env i j) (.many cs env')

/-- `ts[i:j]` reads as `r`, of sort `σ`, as an expression of sort `s` at
precedence `p` not made by production `excl`, through the coercions the
chain `ch` allows. -/
abbrev Exp (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) (r : Reading) (σ : String) :
    Prop :=
  Reads A g ts false (.expr s p excl ch i j) (.one r σ)

/-- `Exp` in the unrestricted grammar: through chains of coercions of any
length, whatever the chain rule allows. -/
abbrev ExpFree (s : String) (p : Nat) (excl : Option Nat) (ch : Chain) (i j : Nat) (r : Reading) (σ : String) :
    Prop :=
  Reads A g ts true (.expr s p excl ch i j) (.one r σ)

/-- `ts[i:j]` reads as `body[pos:]` under bindings `env`, with the readings
of its holes, variables and lists `cs`, and the bindings after them. -/
abbrev Seq (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) (cs : Array Reading) (env' : Env) : Prop :=
  Reads A g ts false (.body body pos env i j) (.many cs env')

/-- `ts[i:j]` reads as the rest of list `l`, `n` more elements required. -/
abbrev Tail (l n : Nat) (env : Env) (i j : Nat) (cs : Array Reading) (env' : Env) : Prop :=
  Reads A g ts false (.rest l n env i j) (.many cs env')

end

end SpliceModel
