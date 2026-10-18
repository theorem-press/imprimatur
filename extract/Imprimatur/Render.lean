/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Doc
import Imprimatur.Trust
import Imprimatur.TeX
import Imprimatur.Notation
import Imprimatur.Commands
import Imprimatur.Views.Lean
import Imprimatur.Requests

/-!
# Rendering expressions as mathematics

`render` turns an expression into a `Doc` (DESIGN §7.1, §7.2):

1. **A notation rule,** if one matches. The rules tried, in order:
   - rules of the requested variant;
   - the project's rules;
   - the packs' rules.

   Within each group, the most specific pattern wins, and declaration order
   breaks ties. A rule's template is filled with the renderings of its
   variables. A variable inside braces needs no parentheses; one at the top
   level needs the rule's precedence (following its associativity).
2. **Built-in forms:**
   - `∀` (bounded `∀ x ∈ s` when it can), `∃`, implication and `λ`;
   - a constant applied to arguments, rendered as a named function of its
     explicit arguments, so notation still applies inside them;
   - variables, under the paper's metavariable names (`latex_metavar`, and
     subscripts for trailing digits);
   - literals and sorts.
3. **Lean's delaborator,** for anything else (`match`, `let`, …), in monospace.
-/

namespace Imprimatur.Render

open Lean Meta

/-- What rendering needs. -/
structure Ctx where
  /-- The rules, project first, then packs. -/
  rules : Array NotationRule
  /-- Metavariable names. -/
  metavars : Array MetavarRule
  /-- The notation variant asked for. -/
  variant : Option String := none
  /-- Namespaces left out of constant names. -/
  strip : Array Name := #[]
  /-- The rules used so far, by `origin: template` (for tests). -/
  used : IO.Ref (Array String)
  /-- Renderings of particular variables, from metavariable conventions. -/
  overrides : Array (FVarId × String) := #[]
  /-- `latex_style names := raw`: binder names are written as they are. -/
  rawVars : Bool := false
  /-- `latex_style applied_variables := call`: `f(a)(b)` for an applied variable. -/
  callVars : Bool := false
  /-- `latex_style applied_variables := subscript`: `f_{a, b}` for an applied variable. -/
  subscriptVars : Bool := false
  /-- The document's blocks and labels, for views that index it. -/
  document : DocumentInfo := {}

/-- The renderer's monad. -/
abbrev RenderM := ReaderT Ctx MetaM

/-- Unicode subscript digits, and their values. -/
def subscripts : List (Char × Char) :=
  [('₀', '0'), ('₁', '1'), ('₂', '2'), ('₃', '3'), ('₄', '4'), ('₅', '5'), ('₆', '6'), ('₇', '7'),
   ('₈', '8'), ('₉', '9')]

/-- Greek letters, and their macros. -/
def greek : List (String × String) :=
  [("α", "\\alpha"), ("β", "\\beta"), ("γ", "\\gamma"), ("δ", "\\delta"), ("ε", "\\varepsilon"),
   ("ζ", "\\zeta"), ("η", "\\eta"), ("θ", "\\theta"), ("ι", "\\iota"), ("κ", "\\kappa"),
   ("λ", "\\lambda"), ("μ", "\\mu"), ("ν", "\\nu"), ("ξ", "\\xi"), ("π", "\\pi"), ("ρ", "\\rho"),
   ("σ", "\\sigma"), ("τ", "\\tau"), ("υ", "\\upsilon"), ("φ", "\\varphi"), ("χ", "\\chi"),
   ("ψ", "\\psi"), ("ω", "\\omega"), ("Γ", "\\Gamma"), ("Δ", "\\Delta"), ("Θ", "\\Theta"),
   ("Λ", "\\Lambda"), ("Ξ", "\\Xi"), ("Π", "\\Pi"), ("Σ", "\\Sigma"), ("Φ", "\\Phi"),
   ("Ψ", "\\Psi"), ("Ω", "\\Omega"), ("ℓ", "\\ell")]

/-- The TeX of a variable named `n` (DESIGN §7.5, metavariables): a
`latex_metavar` name, or the name with trailing digits as a subscript; a
Greek letter becomes its macro; a name longer than one letter is set in
`\mathit` and escaped, unless `raw` (`latex_style variables := raw`), when
names are written as they are. -/
def varTeX (metavars : Array MetavarRule) (n : Name) (raw : Bool := false) : String :=
  let s := (n.eraseMacroScopes.toString.replace "✝" "")
  match metavars.find? (·.name.toString == s) with
  | some m => m.tex
  | none =>
    let cs := s.toList
    let primes := (cs.reverse.takeWhile (· == '\'')).length
    let cs := cs.take (cs.length - primes)
    let digitsRev := cs.reverse.takeWhile fun c => c.isDigit || subscripts.any (·.1 == c)
    let base := String.ofList (cs.take (cs.length - digitsRev.length))
    let digits := String.ofList (digitsRev.reverse.map fun c =>
      ((subscripts.find? (·.1 == c)).map (·.2)).getD c)
    let baseTeX := match metavars.find? (fun m => m.decorated && m.name.toString == base), greek.find? (·.1 == base) with
      | some m, _ => m.tex
      | none, some (_, m) => m
      | none, none =>
        if raw then base
        else if base.length ≤ 1 then TeX.escape base else s!"\\mathit\{{TeX.escape base}}"
    let sub := if digits.isEmpty then "" else s!"_\{{digits}}"
    baseTeX ++ sub ++ String.ofList (List.replicate primes '\'')

/-- The TeX of a variable, under the style in force. -/
def varName (n : Name) : RenderM String := do
  let ctx ← read
  return varTeX ctx.metavars n ctx.rawVars

/-- The TeX of a constant without notation. -/
def constTeX (strip : Array Name) (n : Name) : String :=
  s!"\\LeanMathConst\{{TeX.escape (Views.stripName strip n).toString}}"

/-- The rules that could render an application of `head`, best first. -/
def candidates (head : Name) : RenderM (Array NotationRule) := do
  let ctx ← read
  let rs := ctx.rules.filter (·.head == head)
  -- A stable sort: variant first, then project before packs (already in
  -- order), then specificity.
  let key (r : NotationRule) : Nat × Nat :=
    ((if r.variant.isSome && r.variant == ctx.variant then 0 else if r.variant.isNone then 1 else 2),
     1000 - r.specificity)
  let le (a b : NotationRule) : Bool :=
    let (x1, y1) := key a
    let (x2, y2) := key b
    x1 < x2 || (x1 == x2 && y1 ≤ y2)
  return (rs.toList.mergeSort le).toArray.filter fun r => r.variant.isNone || r.variant == ctx.variant

/-- The depth of unescaped braces after `t`, starting from `d`. -/
def braceDepth (t : String) (d : Nat) : Nat := Id.run do
  let mut d := d
  let mut esc := false
  for c in t.toList do
    if esc then esc := false; continue
    if c == '\\' then esc := true
    else if c == '{' then d := d + 1
    else if c == '}' then d := d - 1
  return d

mutual

  /-- Render an expression. -/
  partial def render (e : Expr) : RenderM Doc := do
    let e := e.consumeMData
    -- Notation rules first: those for the head constant, or for the binder.
    let head : Name := match e with
      | .forallE _ _ b _ => if b.hasLooseBVar 0 then `_forall else `_arrow
      | .lam .. => `_lam
      | _ => match e.getAppFn with
        | .const h _ => h
        | _ => .anonymous
    unless head.isAnonymous do
      for r in ← candidates head do
        let fire (e : Expr) (bs : Array (Name × Expr)) : RenderM (Option Doc) := do
          (← read).used.modify (·.push s!"{r.origin}: {r.template}")
          return some (← applyRule r bs e)
        let ctx ← read
        if let some d ← r.tryMatchK e (fun bs => (fire e bs).run ctx) then return d
        -- Over-applied, as `(f ∘ g) x`: match a prefix, then apply the rest.
        if let some (pre, rest) ← splitAfterExplicit e r.pat.arity then
          if !rest.isEmpty then
            if let some d ← r.tryMatchK pre (fun bs => (fire pre bs).run ctx) then
              return ← apply d rest
      if head == ``Exists then
        if let some d ← renderExists e then return d
    match e with
    | .fvar f =>
      match (← read).overrides.find? (·.1 == f) with
      | some (_, t) => return .tex t
      | none => return .tex (← varName (← f.getUserName))
    | .sort .zero => return .tex "\\mathrm{Prop}"
    | .sort _ => return .tex "\\mathrm{Type}"
    | .lit (.natVal n) => return .tex (toString n)
    | .lit (.strVal s) => return .tex s!"\\text\{``{TeX.escape s}''}"
    | .forallE .. => renderForall e
    | .lam n t b bi =>
      withLocalDecl n bi t fun x => do
        let body ← render (b.instantiate1 x)
        return .node 0 #[.tex s!"\\lambda {← varName n}.\\,", .child 0 body]
    | .const h _ => return .tex (constTeX (← read).strip h)
    | .app .. =>
      if ← isMatcherApp e then return ← delab e
      let f := e.getAppFn
      match f with
      | .const h _ =>
        match ← explicitArgsLoose e with
        | some (_, args) => apply (.tex (constTeX (← read).strip h)) args
        | none => delab e
      | .fvar _ =>
        if (← read).subscriptVars then
          let mut parts : Array Doc := #[.child Doc.maxPrec (← render f), .tex "_{"]
          for (a, i) in e.getAppArgs.toList.zip (List.range e.getAppNumArgs) do
            if i > 0 then parts := parts.push (.tex ", ")
            parts := parts.push (.child 0 (← render a))
          return .node Doc.maxPrec (parts.push (.tex "}"))
        if (← read).callVars then
          let mut parts : Array Doc := #[.child Doc.maxPrec (← render f)]
          for a in e.getAppArgs do
            parts := parts ++ #[.tex "(", .child 0 (← render a), .tex ")"]
          return .node Doc.maxPrec parts
        apply (← render f) e.getAppArgs
      | .lam .. => apply (← render f) e.getAppArgs
      | _ => delab e
    | _ => delab e

  /-- A function applied to arguments: `f\,a\,b`. -/
  partial def apply (f : Doc) (args : Array Expr) : RenderM Doc := do
    if args.isEmpty then return f
    let mut parts : Array Doc := #[.child Doc.maxPrec f]
    for a in args do
      -- Proofs are not shown.
      if ← isProof a then continue
      parts := parts.push (.tex "\\,")
      parts := parts.push (.child Doc.maxPrec (← render a))
    if parts.size == 1 then return f
    return .node (Doc.maxPrec - 1) parts

  /-- Fill a rule's template. A flattened binder rule (`∃ x, p` with
  `flatten`) first folds a chain of binders into one list of variables. -/
  partial def applyRule (r : NotationRule) (bs : Array (Name × Expr)) (e : Expr) : RenderM Doc := do
    if r.flatten then
      if let some (x, p) := r.pat.binder? then
        return ← foldBinders r bs x p #[] e
    fillTemplate r bs #[] e

  /-- Fold `∃ a, ∃ b, p`: while the body matches the rule again, collect the
  bound variables, then fill the template with the list. -/
  partial def foldBinders (r : NotationRule) (bs : Array (Name × Expr)) (x p : Name)
      (xs : Array Expr) (e : Expr) : RenderM Doc := do
    let (some (_, xv), some (_, body)) := (bs.find? (·.1 == x), bs.find? (·.1 == p))
      | fillTemplate r bs #[] e
    let xs := xs.push xv
    let ctx ← read
    match ← r.tryMatchK body (fun bs' => do return some (← (foldBinders r bs' x p xs body).run ctx)) with
    | some d => return d
    | none => fillTemplate r bs #[(x, xs)] e

  /-- Fill a rule's template; `multi` gives the variables that stand for a
  list, joined by the rule's `sep`. -/
  partial def fillTemplate (r : NotationRule) (bs : Array (Name × Expr))
      (multi : Array (Name × Array Expr)) (e : Expr) : RenderM Doc := do
    let vars := r.pat.vars.map (·.toString)
    let some parts := (splitTemplate r.template vars).toOption | return .tex r.template
    let hidden := r.hides.map (·.1.toString)
    let get (v : String) := (bs.find? (·.1.toString == v)).map (·.2)
    -- A template that is one variable shows that variable as it is.
    if let #[.inr v] := parts then
      if let some a := get v then return ← render a
    -- Flatten a chain: `a ∘ (b ∘ c)` becomes one n-ary node.
    let operands ← if r.flatten && r.pat.binder?.isNone then collect r e else pure #[]
    let topHoles := Id.run do
      let mut d := 0
      let mut out : Array Nat := #[]
      for p in parts do
        match p with
        | .inl t => d := braceDepth t d
        | .inr _ => out := out.push d
      return out
    let topCount := (topHoles.filter (· == 0)).size
    let mut out : Array Doc := #[]
    let mut depth := 0
    let mut holeIdx := 0
    let mut topIdx := 0
    let mut textW := r.width
    for p in parts do
      match p with
      | .inl t =>
        if r.breakBefore && holeIdx > 0 && depth == 0 then out := out.push .brk
        let mut w := texWidth t
        if let some tw := textW then
          w := tw
          textW := some 0
        out := out.push (.text t w)
        depth := braceDepth t depth
      | .inr v =>
        if hidden.contains v then
          holeIdx := holeIdx + 1
          continue
        let need :=
          -- Inside braces, or in an atomic template, which delimits its own
          -- arguments (`(#a, #b)`, `\\max(#a, #b)`), nothing is needed.
          if depth > 0 || r.prec ≥ Doc.maxPrec then 0
          else
            let first := topIdx == 0
            let last := topIdx + 1 == topCount
            match r.assoc with
            | "left" => if first then r.prec else r.prec + 1
            | "right" => if last then r.prec else r.prec + 1
            | _ => r.prec + 1
        if r.flatten && !operands.isEmpty && holeIdx == 1 then
          -- The rest of the chain, separated by the text between the holes.
          -- The separator is the text between the two holes.
          let firstHole := (parts.findIdx? (fun p => match p with | .inr _ => true | _ => false)).getD 0
          let sep : String := match (parts[firstHole + 1]? : Option (Sum String String)) with
            | some (Sum.inl t) => t
            | _ => ""
          for (o, i) in operands.toList.drop 1 |>.zip (List.range operands.size) do
            if i > 0 then
              if r.breakBefore && depth == 0 then out := out.push .brk
              out := out.push (.tex sep)
            out := out.push (.child need (← render o))
        else if r.flatten && !operands.isEmpty && holeIdx == 0 then
          out := out.push (.child need (← render operands[0]!))
        else if let some (_, xs) := multi.find? (·.1.toString == v) then
          for (a, i) in xs.toList.zip (List.range xs.size) do
            if i > 0 then out := out.push (.tex r.sep)
            out := out.push (.child need (← render a))
        else
          match get v with
          | some a => out := out.push (.child need (← render a))
          | none => out := out.push (.tex s!"?{v}")
        holeIdx := holeIdx + 1
        if depth == 0 then topIdx := topIdx + 1
    return .node r.prec out

  /-- The operands of a chain of a flattening rule. -/
  partial def collect (r : NotationRule) (e : Expr) : RenderM (Array Expr) := do
    match ← r.tryMatch e with
    | some bs =>
      let vs := r.pat.vars
      let a := (bs.find? (·.1 == vs[0]!)).map (·.2)
      let b := (bs.find? (·.1 == vs[1]!)).map (·.2)
      match a, b with
      | some a, some b => return (← collect r a) ++ (← collect r b)
      | _, _ => return #[e]
    | none => return #[e]

  /-- `∃ x, p`, and `∃ x ∈ s, p`. -/
  partial def renderExists (e : Expr) : RenderM (Option Doc) := do
    let some (_, #[.lam n t b bi]) ← explicitArgs e | return none
    withLocalDecl n bi t fun x => do
      let body := b.instantiate1 x
      let v ← varName n
      -- `∃ x, x ∈ s ∧ p` is written `∃ x ∈ s, p`.
      if body.isAppOfArity ``And 2 then
        let mem := body.appFn!.appArg!
        if mem.isAppOfArity ``Membership.mem 5 && mem.appArg! == x then
          let s ← render mem.appFn!.appArg!
          let p ← render body.appArg!
          return some (.node 0 #[.tex s!"\\exists {v} \\in ", .child 50 s, .tex ",\\ ", .child 0 p])
      return some (.node 0 #[.tex s!"\\exists {v},\\ ", .child 0 (← render body)])

  /-- `∀` and implication. -/
  partial def renderForall (e : Expr) : RenderM Doc := do
    let .forallE n t b bi := e | delab e
    let isProp ← isProp e
    if !b.hasLooseBVars then
      -- An implication or a function type.
      let arrow := if isProp then "\\implies" else "\\to"
      let lhs ← render t
      let rhs ← render b
      return .node 25 #[.child 26 lhs, .brk, .tex s!" {arrow} ", .child 25 rhs]
    withLocalDecl n bi t fun x => do
      let body := b.instantiate1 x
      -- Instance binders are not shown.
      if bi.isInstImplicit then return ← render body
      let v ← varName n
      -- `∀ x, x ∈ s → p` is written `∀ x ∈ s, p`.
      if let .forallE _ dom rest _ := body then
        if !rest.hasLooseBVars && dom.isAppOfArity ``Membership.mem 5 && dom.appArg! == x then
          let s ← render dom.appFn!.appArg!
          return .node 0 #[.tex s!"\\forall {v} \\in ", .child 50 s, .tex ",\\ ", .child 0 (← render rest)]
      let ty ← render t
      return .node 0 #[.tex s!"\\forall {v} : ", .child 1 ty, .tex ",\\ ", .child 0 (← render body)]

  /-- Lean's own rendering, in monospace, for what nothing else covers. -/
  partial def delab (e : Expr) : RenderM Doc := do
    let text := toString (← ppExpr e)
    let line := " ".intercalate ((text.splitOn "\n").map (·.trimAscii.toString))
    return .text s!"\\LeanMathCode\{{TeX.escape line}}" line.length

end

end Imprimatur.Render
