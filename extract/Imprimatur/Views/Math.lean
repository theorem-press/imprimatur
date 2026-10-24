/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render
import Imprimatur.Layout

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

/-- The names the author gave binders in a definition: those of its type and
value without macro scopes. Lean's own names (`x✝`) have them. -/
partial def authorNames (c : ConstantInfo) : Array Name :=
  go (go #[] c.type) (c.value?.getD (.sort .zero))
where
  go (acc : Array Name) : Expr → Array Name
    | .forallE n t b _ | .lam n t b _ => go (go (keep acc n) t) b
    | .letE n t v b _ => go (go (go (keep acc n) t) v) b
    | .app f a => go (go acc f) a
    | .mdata _ e | .proj _ _ e => go acc e
    | _ => acc
  keep (acc : Array Name) (n : Name) : Array Name :=
    if n.hasMacroScopes || n.isAnonymous || acc.contains n then acc else acc.push n

/-- Name the binders Lean gave generic names (`a`, `a_1`, `x✝`) in an
equation lemma after their types' grammar categories, as BNF does
(`latex_category Shape => "c"`): a `Shape` is `c`, two are `c₁` and `c₂`.
A type is `T`, a function `f`, a number `n`, a list `l` and a Boolean `b`;
binders of other types keep their names, as do binders the definition `defn`
names itself (an author's `a` is not generic). -/
def nameEqnBinders (e : Expr) (defn : Option Name := none) : MetaM Expr := do
  let cats := projectCategories (← getEnv)
  let (own, params) ← match defn with
    | some d => do
      let c ← getConstInfo d
      -- The compiled value may have lost the patterns' names (structural
      -- recursion uses the recursor), but the matchers' types keep them.
      let mut own := authorNames c
      let env ← getEnv
      for i in [1:100] do
        let some m := env.find? (d ++ Name.mkSimple s!"match_{i}") | break
        own := (authorNames m).foldl (fun a n => if a.contains n then a else a.push n) own
      pure (own, c.type.getForallBinderNames.toArray)
    | none => pure (#[], #[])
  -- A category's letter as a name: an ASCII letter, or a Greek macro's letter.
  let letterName (tex : String) : Option String :=
    if tex.length == 1 && tex.toList.all Char.isAlpha then some tex
    else (Render.greek.find? (·.2 == tex)).map (·.1)
  let base (n : Name) : String :=
    ((n.eraseMacroScopes.toString.replace "✝" "").splitOn "_")[0]!
  let generic (n : Name) : Bool := base n == "a" || base n == "x"
  forallTelescope e fun xs body => do
    -- A binder that is an argument of the definition on the left-hand side
    -- (`@labels R C ι k (leaf spec)`, its first four binders) takes the name
    -- the definition gives that argument, if no other binder has it.
    let lhsArgs := match body.eq? with
      | some (_, l, _) => l.getAppArgs
      | none => #[]
    let taken ← xs.mapM fun x => do return (← x.fvarId!.getDecl).userName
    let param? (x : Expr) : Option Name := do
      let i ← lhsArgs.findIdx? (· == x)
      let n ← params[i]?
      if n.hasMacroScopes || taken.contains n then none else some n
    -- The letter for each binder, if it is to be renamed.
    let letters ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      -- Lean's `x_1` for the author's second `x` is the author's.
      if !generic d.userName || own.contains (Name.mkSimple (base d.userName)) then return none
      if param? x |>.isSome then return none
      let t ← whnfR (← instantiateMVars d.type)
      -- A type is `T`, and a function `f`.
      if t.isSort then return some "T"
      if t.isForall then return some "f"
      match t.getAppFn with
      | .const c _ =>
        if let some l := (cats.find? (·.1 == c)).bind fun (_, m) => letterName m then return some l
        -- Otherwise a conventional letter for a few common types.
        return match c with
          | ``Nat => some "n"
          | ``List => some "l"
          | ``Bool => some "b"
          | _ => none
      | _ => return none
    let subs := ["₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"]
    let mut names : Array (Option Name) := #[]
    for l in letters do
      match l with
      | none => names := names.push none
      | some l =>
        let total := (letters.filter (· == some l)).size
        let idx := (names.filter fun n => n.isSome && (n.get!.toString.startsWith l)).size
        names := names.push (some (if total == 1 then Name.mkSimple l
          else Name.mkSimple (l ++ subs.getD idx s!"_{idx + 1}")))
    -- A pattern variable Lean named (`val`, for the author's `_`) that the
    -- right-hand side does not use is `_`.
    let rhs := match body.eq? with
      | some (_, _, r) => some r
      | none => none
    let mut lctx ← getLCtx
    for (x, n) in xs.zip names do
      let d ← x.fvarId!.getDecl
      if (d.userName.hasMacroScopes || !own.contains d.userName.eraseMacroScopes) &&
          n.isNone && (param? x).isNone then
        if let some r := rhs then
          let inTypes ← xs.anyM fun (y : Expr) => do
            return (← y.fvarId!.getDecl).type.containsFVar x.fvarId!
          if !r.containsFVar x.fvarId! && !inTypes then
            lctx := lctx.setUserName x.fvarId! `_
            continue
      if let some n := n then lctx := lctx.setUserName x.fvarId! n
      else if generic (← x.fvarId!.getDecl).userName then
        if let some p := param? x then lctx := lctx.setUserName x.fvarId! p
    withLCtx lctx (← getLocalInstances) do
      mkForallFVars xs body

/-- `lhs = rhs` of an equation statement, with its variables introduced. A
right-hand side wider than `width` is broken, its lines aligned after the
`=`. -/
def equationRow (eqn : Expr) (width : Nat := 100000) : RenderM String :=
  statementParts eqn fun _ _ concl => do
    if concl.isAppOfArity ``Eq 3 then
      -- The arguments on the left are patterns: an injection a rule writes as
      -- its argument is shown (`Render.Ctx.inPattern`).
      let lhs := (← withReader (fun c => { c with inPattern := true })
        (render concl.appFn!.appArg!)).render 100000
      let rhs := (← render concl.appArg!).render width
      let rhs := rhs.replace " \\LeanBreak " " \\\\ &\\qquad "
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
  -- A definition's equations display it.
  if has "def" then noteShown c.name
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
        let rows ← es.mapM fun e => do
          equationRow (← nameEqnBinders (restoreEqnNames (← getConstInfo e).type) c.name) (width * 3 / 4)
        return wrap ("\\begin{aligned}" ++ " \\\\ ".intercalate rows.toList ++ "\\end{aligned}")
      | none => mathView c width
    else mathView c width

/-- A formula on one line, as the prose view sets it in `$…$`. -/
def formulaChars (e : Expr) : RenderM (List Char) := do
  return ((← render e).render 100000).toList

/-- A conclusion in words (`Layout.Concl`): conjuncts are numbered, `↔`
reads "if and only if", and `∃ x, p` reads "there is x such that p". -/
partial def gatherConcl (concl : Expr) : RenderM (Layout.Concl (List Char)) := do
  if concl.isAppOfArity ``Exists 2 then
    if let .lam n t b bi := concl.appArg! then
      return ← withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        return .exists_ (← varNameT n t).toList (← gatherConcl body)
  let cs := conjuncts concl
  if cs.size > 1 then
    return .conjuncts (← cs.toList.mapM formulaChars)
  if concl.isAppOfArity ``Iff 2 then
    return .iff (← formulaChars concl.appFn!.appArg!) (← formulaChars concl.appArg!)
  return .formula (← formulaChars concl)

/-- What the `prose` view of a constant says (`Layout.Prose`): the formulas
of its sentence, each rendered, and which part each plays. The layout,
`Layout.proseLayout`, sets them out; `proseView` is the two together. -/
def gatherProse (c : ConstantInfo) : RenderM (Layout.Prose (List Char)) := do
  unless c matches .thmInfo _ | .axiomInfo _ do
    return .define ((← mathDoc c).render 100000).toList
  statementParts c.type fun vars hyps concl => withConventions hyps fun hyps => do
    -- Variables, grouped by type. Each is rendered as a variable, so a
    -- metavariable convention (`\val`) applies to it here too.
    let mut groups : Array (Array Expr × Expr) := #[]
    for (_, x, t) in vars do
      match groups.back? with
      | some (xs, t') =>
        if t' == t then groups := groups.pop.push (xs.push x, t) else groups := groups.push (#[x], t)
      | none => groups := groups.push (#[x], t)
    let mut gs : Array (Layout.VarGroup (List Char)) := #[]
    for (xs, t) in groups do
      let names ← xs.toList.mapM formulaChars
      let kind ← if t.isProp then pure .prop
        else if t.isSort then pure .type
        else pure (.ofType (← formulaChars t))
      gs := gs.push { names, kind }
    -- Hypotheses, labelled with their names where the paper refers to them
    -- (`\leanhypref{key}{h}`).
    let ctx ← read
    let mut hs : Array (Layout.Hyp (List Char)) := #[]
    for (n, h) in hyps do
      let name := n.eraseMacroScopes.toString
      let referred := ctx.document.hypRefs.contains (ctx.key, name)
      let label := if n.hasMacroScopes || n.isAnonymous || !referred then none else
        some (TeX.escape name).toList
      hs := hs.push { label, formula := ← formulaChars h }
    return .statement { vars := gs.toList, hyps := hs.toList, concl := ← gatherConcl concl }

/-- The `prose` view of a constant: what it says, laid out. -/
def proseView (c : ConstantInfo) (width : Nat) : RenderM String := do
  let _ := width
  return Layout.proseLayout (← gatherProse c)

end Imprimatur.Views
