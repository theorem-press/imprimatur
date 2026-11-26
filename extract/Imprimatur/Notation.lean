/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Notation rules

A notation rule (DESIGN §7.5) maps a pattern over Lean expressions to a TeX
template:

```lean
latex_notation SetRealization.Realize U φ ρ => r"#U \models #φ"  hide ρ := Fin.elim0
latex_notation Label.lub a b                => r"\lub{#a, #b}"   flatten
```

**Patterns.** A pattern's head is a constant. Its explicit arguments are
pattern variables, wildcards, constants or nested patterns. Implicit and
instance arguments are not part of the pattern: they are found from the head's
type and skipped.

**Where rules come from.** Rules come from the project, through the
`latex_notation` command, which stores them in an environment extension. Packs
shipped with imprimatur (`Imprimatur.Packs`) supply more. Packs name their
constants rather than elaborate them, so imprimatur doesn't depend on Mathlib.
-/

namespace Imprimatur

open Lean Meta

/-- A pattern over an expression. -/
inductive Pat where
  /-- A pattern variable, referred to as `#name` in the template. -/
  | var (n : Name)
  /-- Matches anything. -/
  | wild
  /-- A constant applied to patterns for its explicit arguments. -/
  | app (head : Name) (args : Array Pat)
  /-- A closed expression the subterm must be definitionally equal to. -/
  | lit (e : Expr)
  /-- A pattern whose implicit arguments are also constrained: argument `i`
  (counting every argument) must match the given pattern. This is how
  `(a : Set α) ≤ b` differs from `a ≤ b`. -/
  | constrained (p : Pat) (cs : Array (Nat × Pat))
  /-- `fun x => body`: a λ, binding the variable `x` to its bound variable. -/
  | lam (x : Name) (body : Pat)
  /-- `∀ x, body`: a dependent ∀ (one whose body mentions its variable). -/
  | pi (x : Name) (dom : Pat) (body : Pat)
  /-- `p → q`: a non-dependent ∀, an implication or a function type. -/
  | arrow (dom cod : Pat)
  deriving Inhabited, Repr, BEq

/-- How specific a pattern is: the number of constant and binder nodes. More
specific patterns are tried first (DESIGN §7.5). -/
partial def Pat.specificity : Pat → Nat
  | .app _ args => 1 + args.foldl (· + ·.specificity) 0
  | .lit _ => 1
  | .constrained p cs => p.specificity + cs.foldl (· + ·.2.specificity) 0
  | .lam _ b => 1 + b.specificity
  | .pi _ d b => 1 + d.specificity + b.specificity
  | .arrow d c => 1 + d.specificity + c.specificity
  | _ => 0

/-- The variables of a pattern, in order, each once: a bound variable
(`∃ n, s = f n`) is listed where its binder is, not again where it is used,
since a rule's parts are one per variable. -/
partial def Pat.vars (p : Pat) : Array Name :=
  go p |>.foldl (fun acc v => if acc.contains v then acc else acc.push v) #[]
where
  go : Pat → Array Name
    | .var n => #[n]
    | .app _ args => args.foldl (· ++ go ·) #[]
    | .constrained p _ => go p
    | .lam x b => #[x] ++ go b
    | .pi x d b => #[x] ++ go d ++ go b
    | .arrow d c => go d ++ go c
    | _ => #[]

/-- The variable a binder pattern binds, and the variable its body is, when
the pattern is `fun x => p`, `∀ x, p` or a constant applied to one of them
(`∃ x, p`). Such rules can fold a chain of binders (`flatten`). -/
partial def Pat.binder? : Pat → Option (Name × Name)
  | .lam x (.var p) | .pi x _ (.var p) => some (x, p)
  | .app _ args => args.findSome? Pat.binder?
  | .constrained p _ => p.binder?
  | _ => none

/-- The variables a pattern binds (`fun x => p`, `∀ x, p`): in a template
they stand for a bound variable's name, not an expression. -/
partial def Pat.binderVars : Pat → Array Name
  | .app _ args => args.foldl (· ++ ·.binderVars) #[]
  | .constrained p _ => p.binderVars
  | .lam x b => #[x] ++ b.binderVars
  | .pi x d b => #[x] ++ d.binderVars ++ b.binderVars
  | .arrow d c => d.binderVars ++ c.binderVars
  | _ => #[]

/-- The head a rule is indexed by: `_forall`, `_arrow` and `_lam` stand for
the binders. -/
def Pat.head : Pat → Name
  | .app h _ | .constrained (.app h _) _ => h
  | .pi .. => `_forall
  | .arrow .. => `_arrow
  | .lam .. => `_lam
  | _ => .anonymous

/-- A notation rule. -/
structure NotationRule where
  /-- The pattern; its head is a constant. -/
  pat : Pat
  /-- The TeX template; `#x` inserts the rendering of variable `x`. -/
  template : String
  /-- The precedence of the result (DESIGN §7.5 `prec`); 1024 is atomic. -/
  prec : Nat := 1024
  /-- The rendered width in characters, if not estimated from the template. -/
  width : Option Nat := none
  /-- Variables that must match a pattern (such as a constant), and are hidden. -/
  hides : Array (Name × Pat) := #[]
  /-- Variables that must match a pattern, and are shown (`when x := p`). -/
  guards : Array (Name × Pat) := #[]
  /-- The variant this rule belongs to; `none` is the default notation. -/
  variant : Option String := none
  /-- Render nested applications of the same head as one n-ary chain. -/
  flatten : Bool := false
  /-- How operands at the rule's own precedence group: `left`, `right` or
  `none` (both sides parenthesised). -/
  assoc : String := "left"
  /-- Allow a line break before each operator between operands. -/
  breakBefore : Bool := false
  /-- For a flattened binder rule, the text between the bound variables. -/
  sep : String := ", "
  /-- The sort of what the rule renders (its type's head, `Prop`, `Sort`, or
  `*` when unknown), for reading renderings back (DESIGN §18.3). -/
  sort : String := "*"
  /-- The sorts of its variables. -/
  holeSorts : Array (Name × String) := #[]
  /-- A synonym writes a constant as what it is by definition (`Nat.succ n`
  as `n + 1`), so reading it back as that is right: it adds no reading of
  its own (DESIGN §18.3). -/
  synonym : Bool := false
  /-- Where the rule came from, for messages: a module or a pack. -/
  origin : String := ""
  deriving Inhabited

/-- The sort of an expression of type `t`, as the validator compares sorts
(DESIGN §18.3):

- `Prop`, and `Sort` for types;
- the head constant of a type, after unfolding reducible definitions, with
  its type arguments: `Option(Label)`;
- `(A → B)` for a function type;
- `?m`, a type variable, for a type a notation pattern leaves open
  (`a ⊔ b` for any `a b : α`): the holes of that sort must agree;
- `'x` for a type parameter `x` of the statement;
- `*` when unknown (a dependent function type, a universe that may be zero). -/
partial def sortKey (t : Expr) : MetaM String := do
  let t ← whnfR (← instantiateMVars t)
  match t with
  | .sort .zero => return "Prop"
  -- A universe that may be zero (`Sort u`) is either: `Sort*`, which is a
  -- type or a proposition, but not a value of a datatype.
  | .sort u => return if u.isNeverZero then "Sort" else "Sort*"
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return "*"
    let d ← sortKey d
    let b ← sortKey b
    return if d == "*" && b == "*" then "*" else s!"({d} → {b})"
  | _ =>
    -- A type that is a function type by definition (`Matrix R C α`, `Set α`)
    -- is written as one: the reader's algebra does not let a named type
    -- stand for a function (`STerm.compat`).
    if let .const .. := t.getAppFn then
      if let some f ← (try some <$> whnf t catch _ => pure none) then
        if f.isForall then return ← sortKey f
    match t.getAppFn with
    | .const n _ =>
      -- With its type arguments (`Option(Label)`); other arguments, such as
      -- `n` in `Fin n`, are left out.
      let mut args : Array String := #[]
      for x in t.getAppArgs do
        let isType ← try (do return (← whnfR (← inferType x)).isSort) catch _ => pure false
        if isType then args := args.push (← sortKey x)
      return if args.isEmpty then n.toString else s!"{n}({", ".intercalate args.toList})"
    | .mvar m => return s!"?{m.name}"
    | .fvar f => return s!"'{f.name}"
    | _ => return "*"

/-- The head constant of a rule. -/
def NotationRule.head (r : NotationRule) : Name := r.pat.head

/-- How specific a rule is: its pattern's, and its guards'. -/
def NotationRule.specificity (r : NotationRule) : Nat :=
  r.pat.specificity + r.guards.foldl (· + ·.2.specificity) 0

/-- A binder name rendered as a metavariable (DESIGN §7.5 `latex_metavar`). -/
structure MetavarRule where
  /-- The binder name, as written in Lean. -/
  name : Name
  /-- Its TeX. -/
  tex : String
  /-- Also rename the name when it has a subscript or primes (`idx₁` as
  `i_{1}`), not only the name itself. -/
  decorated : Bool := false
  deriving Inhabited

/-- A named group of constructors, rendered together by the `rules` view
(DESIGN §6.2 `latex_group`). Its key in the TeX is its title. -/
structure RuleGroup where
  /-- The title, which is also the key. -/
  title : String
  /-- The constructors, in order. -/
  ctors : Array Name
  deriving Inhabited

/-- How the rules of one inductive predicate are labelled and marked
(`latex_rules`). -/
structure RulesStyle where
  /-- The inductive. -/
  induct : Name
  /-- The label template: `#` is the rule's name. -/
  label : String := "#"
  /-- A macro written before each rule as `\macro{Key}{label}%`, so prose
  can refer to rules; `Key` is the name without spaces. -/
  labelMacro : Option String := none
  /-- The text between the words of a label made from a name. -/
  sep : String := "-"
  /-- Whether a docstring starting `Label:` gives the label. -/
  docLabels : Bool := true
  deriving Inhabited

/-- A premise convention (DESIGN §7.6). -/
structure PremiseConvention where
  /-- The pattern of premises to hide. -/
  pat : Pat
  /-- With `latex_metavar_convention`: the variable whose premise is hidden,
  and how it is rendered (`\val`). -/
  metavar : Option (Name × String) := none
  deriving Inhabited

/-- What a notation module declares. -/
inductive NotationEntry where
  /-- A notation rule. -/
  | rule (r : NotationRule)
  /-- A metavariable name. -/
  | metavar (m : MetavarRule)
  /-- A group of rules. -/
  | group (g : RuleGroup)
  /-- A display: definitions (or types) shown together by the `clauses` (or
  `grammar|display`) view, as the block with key `title` (`latex_display`). -/
  | display (title : String) (decls : Array Name)
  /-- A rule's label. -/
  | ruleLabel (ctor : Name) (label : String)
  /-- How an inductive's rules are labelled. -/
  | rulesStyle (s : RulesStyle)
  /-- A premise convention. -/
  | convention (c : PremiseConvention)
  /-- The metavariable of a grammar category (`latex_category`). -/
  | category (ty : Name) (tex : String)
  /-- The type of a category declared with arguments (`latex_category T A … =>
  "m"`): `T A …`, which its metavariable ranges over, and which the table of
  conventions writes. -/
  | categoryType (ty : Name) (tex : String) (type : Expr)
  /-- A custom view (`@[latex_view "name"]`) and the function that renders it. -/
  | view (name : String) (fn : Name)
  /-- A key of the document and the declaration it names (`latex_entry`),
  with options every view of it renders with. -/
  | entry (key : String) (decl : Name) (opts : Array (String × String))
  /-- A style setting (`latex_style`). -/
  | style (key value : String)
  deriving Inhabited

/-- The notation declared by every imported notation module, and the current
one. -/
initialize notationExt : SimplePersistentEnvExtension NotationEntry (Array NotationEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[] }

/-- The project's notation rules, in declaration order. -/
def projectRules (env : Environment) : Array NotationRule :=
  (notationExt.getState env).filterMap fun
    | .rule r => some r
    | _ => none

/-- The project's metavariable names. -/
def projectMetavars (env : Environment) : Array MetavarRule :=
  (notationExt.getState env).filterMap fun
    | .metavar m => some m
    | _ => none

/-- The project's rule groups. -/
def projectGroups (env : Environment) : Array RuleGroup :=
  (notationExt.getState env).filterMap fun
    | .group g => some g
    | _ => none

/-- The project's displays (`latex_display`): titles and their declarations. -/
def projectDisplays (env : Environment) : Array (String × Array Name) :=
  (notationExt.getState env).filterMap fun
    | .display t ds => some (t, ds)
    | _ => none

/-- Explicit rule labels. -/
def projectRuleLabels (env : Environment) : Array (Name × String) :=
  (notationExt.getState env).filterMap fun
    | .ruleLabel c l => some (c, l)
    | _ => none

/-- Rule styles, by inductive. -/
def projectRulesStyles (env : Environment) : Array RulesStyle :=
  (notationExt.getState env).filterMap fun
    | .rulesStyle st => some st
    | _ => none

/-- Premise conventions. -/
def projectConventions (env : Environment) : Array PremiseConvention :=
  (notationExt.getState env).filterMap fun
    | .convention c => some c
    | _ => none

/-- Custom views, by name. -/
def projectViews (env : Environment) : Array (String × Name) :=
  (notationExt.getState env).filterMap fun
    | .view n f => some (n, f)
    | _ => none

/-- Entries: keys, their declarations and their options. -/
def projectEntries (env : Environment) : Array (String × Name × Array (String × String)) :=
  (notationExt.getState env).filterMap fun
    | .entry k d o => some (k, d, o)
    | _ => none

/-- The style settings, last declaration first. -/
def projectStyles (env : Environment) : Array (String × String) :=
  ((notationExt.getState env).filterMap fun
    | .style k v => some (k, v)
    | _ => none).reverse

/-- Grammar categories' metavariables. -/
def projectCategories (env : Environment) : Array (Name × String) :=
  (notationExt.getState env).filterMap fun
    | .category t m => some (t, m)
    | _ => none

/-- The types of the categories declared with arguments (`latex_category List
Prog => "p"`), each with its head and metavariable. -/
def projectCategoryTypes (env : Environment) : Array (Name × String × Expr) :=
  (notationExt.getState env).filterMap fun
    | .categoryType t m ty => some (t, m, ty)
    | _ => none

/-- The explicit arguments of an application, given the head's type: implicit
and instance arguments are left out. `none` if the head is not a constant or
is under-applied. -/
def explicitArgs (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let .const h _ := e.getAppFn | return none
  let some ci := (← getEnv).find? h | return none
  let args := e.getAppArgs
  let mut ty := ci.type
  let mut out := #[]
  for a in args do
    match ty with
    | .forallE _ _ b bi =>
      if bi.isExplicit then out := out.push a
      ty := b
    | _ =>
      -- More arguments than the type shows (the result is a function type
      -- after unfolding): count them as explicit.
      out := out.push a
  -- Under-applied: some explicit binders remain.
  let rec remaining : Expr → Bool
    | .forallE _ _ b bi => bi.isExplicit || remaining b
    | _ => false
  if remaining ty then return none
  return some (h, out)

/-- The explicit arguments of an application, whether or not it is fully
applied; `none` if its head is not a constant. -/
def explicitArgsLoose (e : Expr) : MetaM (Option (Name × Array Expr)) := do
  let .const h _ := e.getAppFn | return none
  let some ci := (← getEnv).find? h | return none
  let mut ty := ci.type
  let mut out := #[]
  for a in e.getAppArgs do
    match ty with
    | .forallE _ _ b bi =>
      if bi.isExplicit then out := out.push a
      ty := b
    | _ => out := out.push a
  return some (h, out)

/-- Split an application after its `k`-th explicit argument: the application
up to there, and the arguments after it. `none` if it has fewer. -/
def splitAfterExplicit (e : Expr) (k : Nat) : MetaM (Option (Expr × Array Expr)) := do
  let .const h _ := e.getAppFn | return none
  let some ci := (← getEnv).find? h | return none
  let args := e.getAppArgs
  let mut ty := ci.type
  let mut seen := 0
  for i in [0:args.size] do
    let explicit := match ty with
      | .forallE _ _ _ bi => bi.isExplicit
      | _ => true
    if let .forallE _ _ b _ := ty then ty := b
    if explicit then
      seen := seen + 1
      if seen == k then
        return some (mkAppN e.getAppFn (args.extract 0 (i + 1)), args.extract (i + 1) args.size)
  return none

/-- The number of explicit arguments a pattern takes. -/
def Pat.arity : Pat → Nat
  | .app _ args | .constrained (.app _ args) _ => args.size
  | _ => 0

/-- The local context with each pattern variable `xs[i]` named as the
alternative `alt` names its `i`th binder, unless that name is inaccessible,
and renamed when another variable in scope has the name already. -/
partial def patternNames (alt : Expr) (xs : Array Expr) : MetaM LocalContext := do
  let mut lctx ← getLCtx
  let mut body := alt
  for x in xs do
    let suggested := if body.isLambda then body.bindingName! else .anonymous
    let unused := body.isLambda && !body.bindingBody!.hasLooseBVar 0
    if body.isLambda then body := body.bindingBody!
    let .fvar id := x | continue
    let some decl := lctx.find? id | continue
    -- A variable the branch does not use is written `_`, as in the source.
    if unused then
      lctx := lctx.setUserName id `_
      continue
    let base :=
      if suggested.isAnonymous || suggested.hasMacroScopes || suggested.isInaccessibleUserName
      then decl.userName.eraseMacroScopes else suggested
    let clash (n : Name) (l : LocalContext) : Bool :=
      l.decls.toList.any fun
        | some d => d.fvarId != id && d.userName == n
        | none => false
    let mut name := base
    let mut i := 1
    while clash name lctx do
      name := base.appendAfter s!"_{i}"
      i := i + 1
    lctx := lctx.setUserName id name
  return lctx

/-- `match y with | pat => rhs`: a matcher applied to the variable `y` alone,
with one alternative, `y` nowhere else. Runs `k` on the pattern and the
right-hand side, with the pattern's variables in scope, named as the
alternative names them; `none` for any other expression. So `fun p => match
p with | (a, b) => e` is a λ that binds the pattern `(a, b)`. -/
def withDestructuring {α : Type} (y e : Expr) (k : Expr → Expr → MetaM (Option α)) :
    MetaM (Option α) := do
  unless ← isMatcherApp e do return none
  let some app ← matchMatcherApp? e | return none
  let .fvar yid := y | return none
  unless app.discrs == #[y] && app.alts.size == 1 && app.remaining.isEmpty do return none
  if (app.alts[0]!).containsFVar yid || app.params.any (·.containsFVar yid) then return none
  let some eqns ← (try some <$> Match.getEquationsFor app.matcherName catch _ => pure none)
    | return none
  let some eqn := eqns.eqnNames[0]? | return none
  let nParams := app.params.size
  forallTelescope (← getConstInfo eqn).type fun _ body => do
    let some (_, lhs, rhs) := body.eq? | return none
    let args := lhs.getAppArgs
    let some pat := args[nParams + 1]? | return none
    unless rhs.getAppFn == args[nParams + 2]! do return none
    let rhsBody := (app.alts[0]!).beta rhs.getAppArgs
    let lctx ← patternNames (app.alts[0]!) rhs.getAppArgs
    withLCtx lctx (← getLocalInstances) do k pat rhsBody

/-- Match a pattern, and continue with the bindings of its variables. The
continuation runs inside the scope of the locals that binder patterns
introduce: a bound variable is bound to its local, and a body to the
expression under the binder, so that both render in scope. `none` if the
pattern doesn't match (or the continuation returns `none`). -/
partial def Pat.matchExprK {α : Type} (p : Pat) (e : Expr) (acc : Array (Name × Expr))
    (k : Array (Name × Expr) → MetaM (Option α)) : MetaM (Option α) := do
  match p with
  | .wild => k acc
  | .var n => k (acc.push (n, e))
  | .lit v =>
    if ← withNewMCtxDepth (isDefEq e v) then k acc else return none
  | .constrained q cs =>
    let args := e.consumeMData.getAppArgs
    let rec goCs (i : Nat) : MetaM (Option α) := do
      if h : i < cs.size then
        let (j, c) := cs[i]
        let some a := args[j]? | return none
        c.matchExprK a #[] fun _ => goCs (i + 1)
      else q.matchExprK e acc k
    goCs 0
  | .app h ps =>
    let e := e.consumeMData
    -- A constant pattern with no arguments matches the constant, whatever
    -- its implicit arguments.
    if ps.isEmpty && e.getAppFn.isConstOf h then
      if let some (_, #[]) ← explicitArgsLoose e then return ← k acc
    -- The pattern names the first explicit arguments; an application with
    -- more is over-applied, and handled by the renderer.
    let some (h', args) ← explicitArgsLoose e | return none
    if h' != h || args.size != ps.size then return none
    let rec goArgs (i : Nat) (acc : Array (Name × Expr)) : MetaM (Option α) := do
      if h : i < ps.size then
        ps[i].matchExprK args[i]! acc fun acc' => goArgs (i + 1) acc'
      else k acc
    goArgs 0 acc
  | .lam x body =>
    let .lam n t b bi := e.consumeMData | return none
    withLocalDecl n bi t fun y => do
      let b := b.instantiate1 y
      -- `fun p => match p with | (a, b) => e` binds a pattern: `x` stands for
      -- the pattern `(a, b)`, and the body is `e`, with `a` and `b` in scope.
      match ← withDestructuring y b (fun pat rhs => body.matchExprK rhs (acc.push (x, pat)) k) with
      | some r => return some r
      | none => body.matchExprK b (acc.push (x, y)) k
  | .pi x dom body =>
    let .forallE n t b bi := e.consumeMData | return none
    unless b.hasLooseBVar 0 do return none
    dom.matchExprK t acc fun acc =>
      withLocalDecl n bi t fun y => body.matchExprK (b.instantiate1 y) (acc.push (x, y)) k
  | .arrow dom cod =>
    let .forallE _ t b _ := e.consumeMData | return none
    if b.hasLooseBVar 0 then return none
    dom.matchExprK t acc fun acc => cod.matchExprK b acc k

/-- Match a pattern without binders; on success, the bindings of its
variables. (With binder patterns, use `matchExprK`: their locals go out of
scope here.) -/
def Pat.matchExpr (p : Pat) (e : Expr) (acc : Array (Name × Expr) := #[]) :
    MetaM (Option (Array (Name × Expr))) :=
  p.matchExprK e acc fun bs => pure (some bs)

/-- Try a rule on an expression, and continue with the bindings if it matches
and every hidden variable has its value (see `Pat.matchExprK`). -/
def NotationRule.tryMatchK {α : Type} (r : NotationRule) (e : Expr)
    (k : Array (Name × Expr) → MetaM (Option α)) : MetaM (Option α) :=
  r.pat.matchExprK e #[] fun bs => do
    for (x, p) in r.hides ++ r.guards do
      match bs.find? (·.1 == x) with
      | some (_, a) =>
        if (← p.matchExpr a).isNone then return none
      | none => return none
    k bs

/-- Try a rule without binders on an expression: the bindings, if it matches. -/
def NotationRule.tryMatch (r : NotationRule) (e : Expr) : MetaM (Option (Array (Name × Expr))) :=
  r.tryMatchK e fun bs => pure (some bs)

end Imprimatur
