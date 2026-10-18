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

/-- Apply the premise conventions (DESIGN §7.6) to hypotheses: those a
convention hides are dropped, and variables a metavariable convention names
get its rendering. Then continue with the remaining hypotheses. -/
def withConventions {α : Type} (hyps : Array (Name × Expr))
    (k : Array (Name × Expr) → RenderM α) : RenderM α := do
  let conventions := projectConventions (← getEnv)
  let mut kept : Array (Name × Expr) := #[]
  let mut overrides : Array (FVarId × String) := #[]
  for (n, h) in hyps do
    let mut hidden := false
    for cv in conventions do
      if let some bs ← cv.pat.matchExpr h then
        hidden := true
        if let some (v, tex) := cv.metavar then
          if let some (_, .fvar f) := bs.find? (·.1 == v) then
            let plain := varTeX #[] (← f.getUserName)
            let sub := match plain.splitOn "_" with
              | _ :: rest@(_ :: _) => "_" ++ "_".intercalate rest
              | _ => ""
            overrides := overrides.push (f, tex ++ sub)
    unless hidden do kept := kept.push (n, h)
  withReader (fun ctx => { ctx with overrides := ctx.overrides ++ overrides }) (k kept)

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

/-- The binders of an equation lemma, with the names the definition used:
Lean names the matched argument `x` and renames a pattern variable `x` to
`x_1`, so `x_1` is shown as `x` when no other binder is called `x`. -/
def restoreEqnNames (e : Expr) : Expr :=
  let names := collect e #[]
  rename names e
where
  collect : Expr → Array Name → Array Name
    | .forallE n _ b _, acc => collect b (acc.push n)
    | _, acc => acc
  base? (n : Name) : Option Name :=
    match n with
    | .str p s =>
      match s.splitOn "_" with
      | [] | [_] => none
      | parts =>
        if (parts.getLast!.toNat?).isSome then some (.str p ("_".intercalate parts.dropLast)) else none
    | _ => none
  rename (names : Array Name) : Expr → Expr
    | .forallE n t b bi =>
      let n' := match base? n with
        | some m => if names.contains m || names.contains n == false then n
                    else if (names.filter (base? · == some m)).size == 1 then m else n
        | none => n
      .forallE n' t (rename names b) bi
    | e => e

/-- `lhs = rhs` of an equation statement, with its variables introduced. -/
def equationRow (eqn : Expr) : RenderM String :=
  statementParts eqn fun _ _ concl => do
    if concl.isAppOfArity ``Eq 3 then
      let lhs := (← render concl.appFn!.appArg!).render 100000
      let rhs := (← render concl.appArg!).render 100000
      return s!"{lhs} &= {rhs}"
    return (← render concl).render 100000

/-- The `math` view with theorem modifiers (DESIGN §9.1):

- `rule`: a theorem's hypotheses over its conclusion, as an inference rule;
- `forall`: the statement with its outer quantifiers;
- `def`: a definition as its equations, aligned;
- `names=full`: no namespaces are left out. -/
def mathViewWith (c : ConstantInfo) (width : Nat) (opts : Array (String × String)) :
    RenderM String := do
  let has (k : String) := opts.any (·.1 == k)
  let full := opts.any (· == ("names", "full"))
  let isThm := c matches .thmInfo _ | .axiomInfo _
  let isDef := c matches .defnInfo _
  let wrap (body : String) : String := "\\LeanMath{" ++ body ++ "}"
  withReader (fun ctx => if full then { ctx with strip := #[] } else ctx) do
    if has "rule" && isThm then
      statementParts c.type fun _ hyps concl => withConventions hyps fun hyps => do
        let ps ← hyps.mapM fun (_, h) => do return (← render h).render 100000
        let cs := (← render concl).render 100000
        return wrap ("\\inferrule{" ++ " \\\\ ".intercalate ps.toList ++ "}{" ++ cs ++ "}")
    else if has "forall" then
      return wrap ((← render c.type).render (width * 3 / 4))
    else if has "def" && isDef then
      match ← getEqnsFor? c.name with
      | some es =>
        let rows ← es.mapM fun e => do equationRow (restoreEqnNames (← getConstInfo e).type)
        return wrap ("\\begin{aligned}" ++ " \\\\ ".intercalate rows.toList ++ "\\end{aligned}")
      | none => mathView c width
    else mathView c width

/-- The `prose` view of a constant. -/
partial def proseView (c : ConstantInfo) (width : Nat) : RenderM String := do
  unless c matches .thmInfo _ | .axiomInfo _ do
    let formula := (← mathDoc c).render 100000
    return s!"\\LeanProse\{We define ${formula}$.}"
  statementParts c.type fun vars hyps concl => withConventions hyps fun hyps => do
    let mut sentences : Array String := #[]
    -- Variables, grouped by type. Each is rendered as a variable, so a
    -- metavariable convention (`\val`) applies to it here too.
    let mut groups : Array (Array Expr × Expr) := #[]
    for (_, x, t) in vars do
      match groups.back? with
      | some (xs, t') =>
        if t' == t then groups := groups.pop.push (xs.push x, t) else groups := groups.push (#[x], t)
      | none => groups := groups.push (#[x], t)
    let mut phrases : Array String := #[]
    for (xs, t) in groups do
      let ns := xs
      let names := ", ".intercalate (← xs.toList.mapM fun x => do return (← render x).render 100000)
      if t.isProp then
        phrases := phrases.push s!"${names}$ be {if ns.size == 1 then "a proposition" else "propositions"}"
      else if t.isSort then
        phrases := phrases.push s!"${names}$ be {if ns.size == 1 then "a type" else "types"}"
      else
        phrases := phrases.push s!"${names} \\in {(← render t).render 100000}$"
    unless phrases.isEmpty do sentences := sentences.push s!"Let {andList phrases}."
    -- Hypotheses, labelled with their names where the paper refers to them
    -- (`\leanhypref{key}{h}`).
    let ctx ← read
    let mut hs : Array String := #[]
    for (n, h) in hyps do
      let name := n.eraseMacroScopes.toString
      let referred := ctx.document.hypRefs.contains (ctx.key, name)
      let label := if n.hasMacroScopes || n.isAnonymous || !referred then "" else
        s!"\\LeanHyp\{{TeX.escape name}} "
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
          return s!"there is ${← varName n}$ such that {← conclusion body}"
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
