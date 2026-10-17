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
  deriving Inhabited, Repr, BEq

/-- How specific a pattern is: the number of constant nodes. More specific
patterns are tried first (DESIGN §7.5). -/
partial def Pat.specificity : Pat → Nat
  | .app _ args => 1 + args.foldl (· + ·.specificity) 0
  | .lit _ => 1
  | .constrained p cs => p.specificity + cs.foldl (· + ·.2.specificity) 0
  | _ => 0

/-- The variables of a pattern, in order. -/
partial def Pat.vars : Pat → Array Name
  | .var n => #[n]
  | .app _ args => args.foldl (· ++ ·.vars) #[]
  | .constrained p _ => p.vars
  | _ => #[]

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
  /-- The variant this rule belongs to; `none` is the default notation. -/
  variant : Option String := none
  /-- Render nested applications of the same head as one n-ary chain. -/
  flatten : Bool := false
  /-- How operands at the rule's own precedence group: `left`, `right` or
  `none` (both sides parenthesised). -/
  assoc : String := "left"
  /-- Allow a line break before each operator between operands. -/
  breakBefore : Bool := false
  /-- Where the rule came from, for messages: a module or a pack. -/
  origin : String := ""
  deriving Inhabited

/-- The head constant of a rule. -/
def NotationRule.head (r : NotationRule) : Name :=
  match r.pat with
  | .app h _ | .constrained (.app h _) _ => h
  | _ => .anonymous

/-- A binder name rendered as a metavariable (DESIGN §7.5 `latex_metavar`). -/
structure MetavarRule where
  /-- The binder name, as written in Lean. -/
  name : Name
  /-- Its TeX. -/
  tex : String
  deriving Inhabited

/-- What a notation module declares. -/
inductive NotationEntry where
  /-- A notation rule. -/
  | rule (r : NotationRule)
  /-- A metavariable name. -/
  | metavar (m : MetavarRule)
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

/-- Match a pattern; on success, the bindings of its variables. -/
partial def Pat.matchExpr (p : Pat) (e : Expr) (acc : Array (Name × Expr) := #[]) :
    MetaM (Option (Array (Name × Expr))) := do
  match p with
  | .wild => return some acc
  | .var n => return some (acc.push (n, e))
  | .lit v =>
    if ← withNewMCtxDepth (isDefEq e v) then return some acc else return none
  | .constrained q cs =>
    let args := e.consumeMData.getAppArgs
    for (i, c) in cs do
      let some a := args[i]? | return none
      if (← c.matchExpr a).isNone then return none
    q.matchExpr e acc
  | .app h ps =>
    let e := e.consumeMData
    -- A constant pattern with no arguments matches the constant, whatever
    -- its implicit arguments.
    if ps.isEmpty && e.getAppFn.isConstOf h then
      if let some (_, #[]) ← explicitArgsLoose e then return some acc
    -- The pattern names the first explicit arguments; an application with
    -- more is over-applied, and handled by the renderer.
    let some (h', args) ← explicitArgsLoose e | return none
    if h' != h || args.size != ps.size then return none
    let mut acc := acc
    for (q, a) in ps.zip args do
      match ← q.matchExpr a acc with
      | some acc' => acc := acc'
      | none => return none
    return some acc

/-- Try a rule on an expression: the bindings, if it matches and every hidden
variable has its value. -/
def NotationRule.tryMatch (r : NotationRule) (e : Expr) : MetaM (Option (Array (Name × Expr))) := do
  let some bs ← r.pat.matchExpr e | return none
  for (x, p) in r.hides do
    match bs.find? (·.1 == x) with
    | some (_, a) =>
      if (← p.matchExpr a).isNone then return none
    | none => return none
  return some bs

end Imprimatur
