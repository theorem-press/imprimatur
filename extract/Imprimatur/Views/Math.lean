/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render

/-!
# The `math` and `prose` views

DESIGN §7.3.

**`math`: a declaration as a formula.**

- *A theorem or axiom.* The statement, with its outer variables left out (as
  a paper states a result) and its hypotheses as premises:
  `P \wedge Q \implies C`.
- *A non-recursive definition.* `f\,x \mathrel{:=} body`.
- *Anything else.* `name : type`.

It is wrapped in `\LeanMath{…}`, broken into lines with `\LeanBreak` when
wider than the width limit.

**`prose`: a theorem as a sentence.**

```
Let x, y ∈ T. Assume (h₁) P and (h₂) Q. Then (1) A and (2) B.
```

- *Variables.* Grouped when they have the same type; a type of types reads
  "be a type".
- *Hypotheses.* Labelled with their names.
- *The conclusion.* Split at `∧`, and read as "if and only if" for `↔`.

It is wrapped in `\LeanProse{…}`, with its formulas in `$…$`.
-/

namespace Imprimatur.Views

open Lean Meta Render

/-- The outer binders of a statement, sorted into variables, hypotheses and
the conclusion, inside a telescope. -/
partial def statementParts {α : Type} (type : Expr)
    (k : Array (Name × Expr × Expr) → Array (Name × Expr) → Expr → RenderM α) : RenderM α :=
  go type #[] #[]
where
  go (e : Expr) (vars : Array (Name × Expr × Expr)) (hyps : Array (Name × Expr)) : RenderM α := do
    match e with
    | .forallE n t b bi =>
      withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        if bi.isInstImplicit then go body vars hyps
        else if (← isProp t) then go body vars (hyps.push (n, t))
        else go body (vars.push (n, x, t)) hyps
    | _ => k vars hyps e

/-- The conjuncts of `a ∧ (b ∧ c)`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then #[e.appFn!.appArg!] ++ conjuncts e.appArg! else #[e]

/-- Render inside `$…$`, on one line. -/
def inline (e : Expr) : RenderM String := do
  return "$" ++ (← render e).render 100000 ++ "$"

/-- `name : type`. -/
def typedDoc (c : ConstantInfo) : RenderM Doc := do
  return .node 0 #[.tex (constTeX (← read).strip c.name), .tex " : ", .child 0 (← render c.type)]

/-- A constant as a formula (see the module docs). -/
def mathDoc (c : ConstantInfo) : RenderM Doc := do
  let env ← getEnv
  match c with
  | .thmInfo _ | .axiomInfo _ =>
    statementParts c.type fun _ hyps concl => do
      let concl ← render concl
      if hyps.isEmpty then return concl
      let mut parts : Array Doc := #[]
      for (h, i) in hyps.toList.zip (List.range hyps.size) do
        if i > 0 then
          parts := parts.push .brk
          parts := parts.push (.tex " \\wedge ")
        parts := parts.push (.child 36 (← render h.2))
      return .node 25 #[.child 26 (.node 35 parts), .brk, .tex " \\implies ", .child 25 concl]
  | .defnInfo d =>
    if Trust.isRecursive env c.name || Trust.isAux env c.name then typedDoc c
    else
      lambdaTelescope d.value fun xs v => do
        let lhs ← apply (.tex (constTeX (← read).strip c.name)) xs
        let rhs ← render v
        return .node 0 #[.child 0 lhs, .brk, .tex " \\mathrel{:=} ", .child 0 rhs]
  | _ => typedDoc c

/-- The `math` view of a constant. Typeset mathematics is wider than the
`\\footnotesize` monospace that `width` is measured in, so lines break at
three quarters of it (60 characters by default). -/
def mathView (c : ConstantInfo) (width : Nat) : RenderM String := do
  return s!"\\LeanMath\{{(← mathDoc c).render (width * 3 / 4)}}"

/-- The `prose` view of a constant. -/
partial def proseView (c : ConstantInfo) (width : Nat) : RenderM String := do
  unless c matches .thmInfo _ | .axiomInfo _ do
    let formula := (← mathDoc c).render 100000
    return s!"\\LeanProse\{We define ${formula}$.}"
  statementParts c.type fun vars hyps concl => do
    let mut sentences : Array String := #[]
    -- Variables, grouped by type.
    let mut groups : Array (Array Name × Expr) := #[]
    for (n, _, t) in vars do
      match groups.back? with
      | some (ns, t') =>
        if t' == t then groups := groups.pop.push (ns.push n, t) else groups := groups.push (#[n], t)
      | none => groups := groups.push (#[n], t)
    let mut phrases : Array String := #[]
    for (ns, t) in groups do
      let names := ", ".intercalate (ns.map (varTeX (← read).metavars ·)).toList
      if t.isProp then
        phrases := phrases.push s!"${names}$ be {if ns.size == 1 then "a proposition" else "propositions"}"
      else if t.isSort then
        phrases := phrases.push s!"${names}$ be {if ns.size == 1 then "a type" else "types"}"
      else
        phrases := phrases.push s!"${names} \\in {(← render t).render 100000}$"
    unless phrases.isEmpty do sentences := sentences.push s!"Let {andList phrases}."
    -- Hypotheses, labelled.
    let mut hs : Array String := #[]
    for (n, h) in hyps do
      let label := if n.hasMacroScopes || n.isAnonymous then "" else
        s!"\\LeanHyp\{{TeX.escape n.eraseMacroScopes.toString}} "
      hs := hs.push s!"{label}{← inline h}"
    unless hs.isEmpty do sentences := sentences.push s!"Assume {andList hs}."
    -- The conclusion.
    let thenPart ← conclusion concl
    sentences := sentences.push ((if sentences.isEmpty then "" else "Then ") ++ thenPart ++ ".")
    let _ := width
    return s!"\\LeanProse\{{" ".intercalate sentences.toList}}"
where
  /-- A conclusion in words: conjuncts are numbered, `↔` reads "if and only
  if", and `∃ x, p` reads "there is x such that p". -/
  conclusion (concl : Expr) : RenderM String := do
    if concl.isAppOfArity ``Exists 2 then
      if let .lam n t b bi := concl.appArg! then
        return ← withLocalDecl n bi t fun x => do
          let body := b.instantiate1 x
          return s!"there is ${varTeX (← read).metavars n}$ such that {← conclusion body}"
    let cs := conjuncts concl
    if cs.size > 1 then
      let items ← (cs.toList.zip (List.range cs.size)).mapM fun (x, i) => do
        return s!"({i + 1})~{← inline x}"
      return andList items.toArray
    if concl.isAppOfArity ``Iff 2 then
      return s!"{← inline concl.appFn!.appArg!} if and only if {← inline concl.appArg!}"
    inline concl
  /-- `a`, `a and b`, `a, b and c`. -/
  andList (xs : Array String) : String :=
    match xs.size with
    | 0 => ""
    | 1 => xs[0]!
    | n => ", ".intercalate (xs.extract 0 (n - 1)).toList ++ " and " ++ xs[n - 1]!

end Imprimatur.Views
