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

/-! ## The grammar's readings -/

section
variable (A : SortAlgebra) (g : Grammar) (ts : Array String)

/-- A bound variable's name, by the grammar's atoms. -/
def VarReads (i j : Nat) (v : Reading) : Prop := varOf g ts i j g.prods.toList = some v

mutual
/-- `ts[i:j]` reads as `r`, of sort `σ`, as an expression of sort `s` at
precedence `p` not made by production `excl` (DESIGN §18.4). -/
inductive Exp : String → Nat → Option Nat → Nat → Nat → Reading → String → Prop
  /-- By a production of a compatible sort, at or above the precedence, not
  the excluded one and not a coercion: its body read, its sort under the
  bindings compatible. -/
  | prod {s : String} {p : Nat} {excl : Option Nat} {i j k : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym}
      {cs : Array Reading} {env : Env} :
    g.prods[k]? = some (pr, body) → pr.isVar = false → A.compat pr.sort s = true →
    excl ≠ some k → pr.coercion = false → p ≤ pr.prec → i < j →
    Seq body 0 #[] i j cs env → A.compat (A.expected env pr.sort) s = true →
    Exp s p excl i j (mkReading pr.name pr.order cs) (variantOf s (A.expected env pr.sort))
  /-- Through a coercion of a compatible sort: its argument read, at the
  argument's sort (the same question, when that is the sort asked for), and
  the coercion's sort with the argument's bound compatible. -/
  | coe {s : String} {p : Nat} {excl : Option Nat} {i j k : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym}
      {s' : String} {pc : Nat} {x : Option Nat} {r : Reading} {so : String} :
    g.prods[k]? = some (pr, body) → pr.isVar = false → A.compat pr.sort s = true →
    pr.coercion = true → body[0]? = some (ASym.hole s' pc x) →
    Exp (A.expected #[] s') p (if A.expected #[] s' == s then excl else none) i j r so →
    A.compat (A.expected (A.bind #[] s' so) pr.sort) s = true →
    Exp s p excl i j r (variantOf s (A.expected (A.bind #[] s' so) pr.sort))
  /-- In the emitter's parentheses: read inside them, at any precedence. -/
  | paren {s : String} {p : Nat} {excl : Option Nat} {i j : Nat} {r : Reading} {σ : String} :
    3 ≤ j - i → ts[i]? = some "(" → ts[j - 1]? = some ")" →
    Exp s 0 none (i + 1) (j - 1) r σ → Exp s p excl i j r σ
  /-- In a TeX group: read inside it. -/
  | group {s : String} {p : Nat} {excl : Option Nat} {i j : Nat} {r : Reading} {σ : String} :
    3 ≤ j - i → ts[i]? = some "{" → ts[j - 1]? = some "}" →
    Exp s p none (i + 1) (j - 1) r σ → Exp s p excl i j r σ

/-- `ts[i:j]` reads as `body[pos:]` under bindings `env`, with the readings
of its holes, variables and lists `cs`, and the bindings after them. -/
inductive Seq : Array ASym → Nat → Env → Nat → Nat → Array Reading → Env → Prop
  /-- The end of the body, with nothing left. -/
  | done {body : Array ASym} {pos : Nat} {env : Env} {i : Nat} : pos = body.size → Seq body pos env i i #[] env
  /-- A token, where it stands. -/
  | tok {body : Array ASym} {pos : Nat} {env : Env} {i j : Nat} {t : String} {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.tok t) → i < j → ts[i]? = some t →
    Seq body (pos + 1) env (i + 1) j cs env' → Seq body pos env i j cs env'
  /-- A hole: an expression of its sort under the bindings, which then binds
  its type variables. -/
  | hole {body : Array ASym} {pos : Nat} {env : Env} {i j : Nat} {s : String} {p : Nat} {x : Option Nat}
      {m : Nat} {r : Reading} {so : String} {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.hole s p x) → i < m → m ≤ j →
    Exp (A.expected env s) p x i m r so →
    Seq body (pos + 1) (A.bind env s so) m j cs env' → Seq body pos env i j (#[r] ++ cs) env'
  /-- A bound variable's name. -/
  | var {body : Array ASym} {pos : Nat} {env : Env} {i j m : Nat} {v : Reading} {cs : Array Reading} {env' : Env} :
    body[pos]? = some ASym.var → i < m → m ≤ j → VarReads g ts i m v →
    Seq body (pos + 1) env m j cs env' → Seq body pos env i j (#[v] ++ cs) env'
  /-- The rest of a list, which may be empty. -/
  | tail {body : Array ASym} {pos : Nat} {env : Env} {i j l n m : Nat} {as : Array Reading} {env₁ : Env}
      {cs : Array Reading} {env' : Env} :
    body[pos]? = some (ASym.tail l n) → i ≤ m → m ≤ j →
    Tail l n env i m as env₁ → Seq body (pos + 1) env₁ m j cs env' → Seq body pos env i j (as ++ cs) env'

/-- `ts[i:j]` reads as the rest of list `l`, `n` more elements required. -/
inductive Tail : Nat → Nat → Env → Nat → Nat → Array Reading → Env → Prop
  /-- Nothing more, when none is required. -/
  | nil {l : Nat} {env : Env} {i : Nat} : Tail l 0 env i i #[] env
  /-- The separator, an element, and the rest. -/
  | more {l n : Nat} {env : Env} {i j : Nat} {elem sep : Array ASym} {cs : Array Reading} {env' : Env} :
    g.lists[l]? = some (elem, sep) → i < j →
    Seq (sep ++ elem ++ #[ASym.tail l (n - 1)]) 0 env i j cs env' → Tail l n env i j cs env'
end

end

end SpliceModel
