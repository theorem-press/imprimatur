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
import Imprimatur.Validate

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

When the context asks for it (`problems`), each formula a view renders is
read back (DESIGN §18.4, `Imprimatur.Validate`): the renderer logs the atoms
it writes (variables, literals, constants without notation), and the
formula must parse, in the grammar of the notation in scope, as exactly one
expression. Two variables that print alike are reported too.
-/

namespace Imprimatur.Render

open Lean Meta

/-- An atom written in a formula, for reading it back. -/
structure Atom where
  /-- Its TeX. -/
  tex : String
  /-- Its sort (`Validate`). -/
  sort : String
  /-- A bound variable's name, at its binder. -/
  isVar : Bool := false
  /-- The variable it is, if it is one. -/
  fvar : Option FVarId := none
  /-- The variable's name. -/
  name : String := ""

/-- What a view rendered, for the views that index the document: a notation
rule that fired, a category's metavariable that appeared, or a declaration a
view displayed (a grammar's type, a definition). Each is tagged with the key
of the block. -/
inductive IndexEvent where
  /-- A notation rule fired. -/
  | rule (key : String) (r : NotationRule)
  /-- A variable printed as the metavariable of the category of `ty`. -/
  | category (key : String) (ty : Name)
  /-- The block displays the declaration `n`. -/
  | shows (key : String) (n : Name)
  deriving Inhabited

/-- The events of an export, in the order the blocks were rendered. The
views that index the document are rendered after all the others. -/
initialize indexEvents : IO.Ref (Array IndexEvent) ← IO.mkRef #[]

/-- What a formula being rendered should read back as (DESIGN §18.4): the
expected readings of the subterms rendered so far, at this level, and how the
form being rendered makes its own from them. A form without a frame reads as
`Validate.anyReading`. -/
structure Expect where
  /-- The expected readings of the subterms rendered at this level. -/
  kids : Array Validate.Reading := #[]
  /-- This form's reading, from its subterms'. -/
  frame : Option (Array Validate.Reading → Validate.Reading) := none

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
  /-- `latex_style pattern_matching := cases`: a `match` as a case analysis. -/
  casesMatch : Bool := false
  /-- `latex_style lists := literal`: a list literal is written `[a, b]`. -/
  listLiterals : Bool := false
  /-- Rendering a `case`'s patterns: a constructor a rule writes as its bare
  argument (`Sum.inl i` as `i`) is shown, since it is what the case tests. -/
  inPattern : Bool := false
  /-- The document's blocks and labels, for views that index it. -/
  document : DocumentInfo := {}
  /-- The key being rendered, as the document writes it. -/
  key : String := ""
  /-- The project's root, for source locations. -/
  root : System.FilePath := "."
  /-- The modules the document imports: the project's, whose first
  components tell its constants from the library's. -/
  imports : Array Name := #[]
  /-- Where to report formulas that do not read back faithfully, when they
  are to be checked (DESIGN §18.4). -/
  problems : Option (IO.Ref (Array String)) := none
  /-- The atoms written in the formula being rendered. -/
  atoms : Option (IO.Ref (Array Atom)) := none
  /-- The expected reading of the formula being rendered. -/
  expect : Option (IO.Ref Expect) := none
  /-- The grammar of the notation in scope (`Validate.notationGrammar`),
  built once for the formulas a view renders. -/
  grammar : Option Validate.Grammar := none

/-- The renderer's monad. -/
abbrev RenderM := ReaderT Ctx MetaM

/-- Record that the block being rendered displays the declaration `n`: a
grammar's type, or a definition. The table of conventions says where each
category's type is shown. -/
def noteShown (n : Name) : RenderM Unit := do
  indexEvents.modify (·.push (.shows (← read).key n))

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
  -- `_`, a variable nothing uses, is TeX's subscript in any style.
  if s == "_" then "\\_" else
  match metavars.find? (·.name.toString == s) with
  | some m => m.tex
  | none =>
    let cs := s.toList
    let primes := (cs.reverse.takeWhile (· == '\'')).length
    let cs := cs.take (cs.length - primes)
    let digitsRev := cs.reverse.takeWhile fun c => c.isDigit || subscripts.any (·.1 == c)
    let base := String.ofList (cs.take (cs.length - digitsRev.length))
    -- Lean's `a_1`: the underscore only separates the number.
    let base := if !digitsRev.isEmpty && base.endsWith "_" && base.length > 1 then
      (base.dropEnd 1).toString else base
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

/-- How strictly the categories' metavariables are read
(`latex_style categories`): `loose`, `unique` (a metavariable stands for one
type) or `strict` (and a variable of a category's type is written with its
metavariable). -/
def categoriesStyle : MetaM String := do
  return ((projectStyles (← getEnv)).find? (·.1 == "categories")).map (·.2) |>.getD "loose"

/-- The metavariable of the category a type belongs to: its head's, or, for a
type that unfolds (`abbrev`), the head's of what it unfolds to. -/
def categoryLetter? (ty : Expr) : MetaM (Option String) := do
  let cats := projectCategories (← getEnv)
  let of (t : Expr) : Option String := match t.getAppFn with
    | .const h _ => (cats.find? (·.1 == h)).map (·.2)
    | _ => none
  let ty ← instantiateMVars ty
  if let some m := of ty then return some m
  try return of (← whnfR ty) catch _ => return none

/-- The decorations of a variable's name: its subscript (from trailing
digits) and its primes, as TeX. -/
def nameDecorations (n : Name) : String :=
  let s := n.eraseMacroScopes.toString.replace "✝" ""
  let cs := s.toList
  let primes := (cs.reverse.takeWhile (· == '\'')).length
  let cs := cs.take (cs.length - primes)
  let digitsRev := cs.reverse.takeWhile fun c => c.isDigit || subscripts.any (·.1 == c)
  let digits := String.ofList (digitsRev.reverse.map fun c =>
    ((subscripts.find? (·.1 == c)).map (·.2)).getD c)
  (if digits.isEmpty then "" else s!"_\{{digits}}") ++ String.ofList (List.replicate primes '\'')

/-- The TeX of a variable of type `ty`. With `latex_style categories :=
strict`, a variable of a category's type is written with the category's
metavariable and its own decorations (`t : Ty` as $\tau$, `t₁` as
$\tau_{1}$), so the reader knows its type from its letter. -/
def varNameT (n : Name) (ty : Expr) : RenderM String := do
  if (← categoriesStyle) == "strict" then
    if let some m ← categoryLetter? ty then
      return m ++ nameDecorations n
  varName n

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

/-- Log an atom of the formula being rendered. -/
def logAtom (tex : String) (sort : String) (isVar : Bool := false) (fvar : Option FVarId := none)
    (name : String := "") : RenderM Unit := do
  if let some r := (← read).atoms then r.modify (·.push { tex, sort, isVar, fvar, name })

/-- A metavariable's base: its TeX without trailing primes and subscript, so
`e_{1}'` is `e`. -/
def metavarBase (t : String) : String := Id.run do
  let mut t := t
  while t.endsWith "'" do t := (t.dropEnd 1).toString
  if t.endsWith "}" then
    let parts := t.splitOn "_{"
    if parts.length ≥ 2 then t := "_{".intercalate (parts.dropLast)
  return t

/-- The elements of a list literal: a chain of `List.cons` ending in
`List.nil`. -/
partial def listLiteral? (e : Expr) : Option (Array Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => some #[]
  | (``List.cons, #[_, a, l]) => (listLiteral? l).map (#[a] ++ ·)
  | _ => none

/-- The sort of an expression, for reading back. -/
def sortOf (e : Expr) : MetaM String := do
  try sortKey (← inferType e) catch _ => pure "*"

/-- Read a rendered formula back (DESIGN §18.4): it must have exactly one
reading as an expression of `e`'s sort, and its free variables must print
differently. Problems go to the context's `problems`. -/
def validate (e : Expr) (d : Doc) (atoms : Array Atom) (expected : Validate.Reading)
    (problems : IO.Ref (Array String)) : RenderM Unit := do
  let ctx ← read
  let tex := d.render 100000
  let ts := Validate.tokenize tex
  if ts.isEmpty then return
  let mut leaves : Array Validate.Prod := #[]
  for a in atoms do
    let p : Validate.Prod :=
      { name := a.tex, sort := a.sort, prec := Doc.maxPrec, isVar := a.isVar,
        syms := (Validate.tokenize a.tex).toList.map .tok }
    unless p.syms.isEmpty || leaves.any (fun q => q.name == p.name && q.sort == p.sort && q.isVar == p.isVar) do
      leaves := leaves.push p
  let base := ctx.grammar.getD
    (Validate.notationGrammar ctx.rules ctx.variant ctx.callVars ctx.subscriptVars ctx.casesMatch
      ctx.listLiterals)
  let g := base.extend leaves
  let h₀ ← IO.getNumHeartbeats
  let boundOverride := (← (IO.getEnv "IMPRIMATUR_CHAIN_DEPTH" : IO _)).bind (·.toNat?)
  let (rs, flags) := Validate.readBackBounded boundOverride g ts (← sortOf e)
  -- IMPRIMATUR_VALIDATE_STATS=1 counts the questions each formula asks, and
  -- the heartbeats (small allocations, in thousands) reading it back took.
  if (← (IO.getEnv "IMPRIMATUR_VALIDATE_STATS" : IO _)) == some "1" then
    let h₁ ← IO.getNumHeartbeats
    let log := (Validate.readBackLog g ts (← sortOf e)).2
    IO.eprintln s!"stats {ts.size} tokens {log.size} questions {(h₁ - h₀) / 1000} kbeats depth {g.depth} key {(← read).key}: {tex}"
    if log.size > 100000 then for l in log do IO.eprintln s!"  read {l}"
  -- Two readings are two readings, whatever else was dropped.
  if rs.size ≥ 2 then
    problems.modify (·.push s!"ambiguous: ${tex}$ reads as {rs[0]!.text} and as {rs[1]!.text}")
  else if flags.over then
    problems.modify (·.push s!"not validated, as reading it back took too long: ${tex}$")
  else if flags.pruned then
    -- IMPRIMATUR_VALIDATE_DEBUG=1 shows what was read where.
    if (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1" then
      IO.eprintln s!"validate: pruned {ts} as {← sortOf e}"
      for l in (Validate.readBackLog g ts (← sortOf e)).2 do IO.eprintln s!"  read {l}"
    problems.modify (·.push s!"not validated, as a reading was dropped: ${tex}$")
  else if flags.cut then
    problems.modify (·.push s!"not validated, as reading it back went round in a circle: ${tex}$")
  else if flags.lists then
    problems.modify (·.push s!"not validated, as a list of the notation takes no token: ${tex}$")
  else if rs.isEmpty then
    -- IMPRIMATUR_VALIDATE_DEBUG=1 shows the tokens and the grammar.
    if (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1" then
      IO.eprintln s!"validate: {ts} as {← sortOf e}"
      for l in (Validate.readBackLog g ts (← sortOf e)).2 do IO.eprintln s!"  read {l}"
      for (p, b) in g.prods do IO.eprintln s!"  {p.name} : {p.sort} @{p.prec} := {repr b}"
    problems.modify (·.push s!"not validated, as the notation does not read it back: ${tex}$")
  else if !expected.matches rs[0]! then
    -- The one reading is not what was rendered: the grammar does not follow
    -- the renderer here, or the emitter left out parentheses a reader needs.
    problems.modify (·.push s!"misread: ${tex}$ reads as {rs[0]!.text}, but was rendered from {expected.text}")
  -- A grammar category's metavariable stands for that category (the BNF
  -- convention: `e ::= e₁\;e₂`), so a variable of another type must not
  -- print as it.
  let cats := projectCategories (← getEnv)
  for a in atoms do
    if a.fvar.isNone || a.sort == "*" || Validate.isTyVar a.sort || a.sort.startsWith "'" then continue
    -- A letter may stand for several types (the paper's programs, and a
    -- development's representation of them); a type is compared by its head.
    let tys := (cats.filter (·.2 == metavarBase a.tex)).map (·.1)
    if let some ty := tys[0]? then
      let head (k : String) : String := (k.splitOn "(")[0]!
      -- A category's type is compared as a variable's is, after unfolding
      -- (`Decls := List (Name × List Name)` is a list).
      -- A type with parameters (`PlanMatrix Δ d`) is compared at its
      -- parameters, as a variable's type is that type applied.
      let keys ← tys.mapM fun t => do
        try
          let ci ← getConstInfo t
          let c := Expr.const t (ci.levelParams.map Level.param)
          forallTelescope ci.type fun xs _ => do pure (head (← sortKey (mkAppN c xs)))
        catch _ => pure t.toString
      -- A metavariable stands for one type (`latex_style categories := unique`
      -- or `strict`): types that unfold to the same head are one.
      let style ← categoriesStyle
      let pre := if style == "loose" then "" else "category: "
      let distinct := keys.foldl (fun a k => if a.contains k then a else a.push k) #[]
      if distinct.size > 1 then
        let p := s!"{pre}the metavariable ${metavarBase a.tex}$ stands for {", ".intercalate (tys.toList.map toString)}, \
          so a reader cannot tell which type a variable written with it has: give each type its own \
          metavariable (latex_category)"
        unless (← problems.get).contains p do problems.modify (·.push p)
      -- The categories that appear, for the table of conventions.
      for (t, k) in tys.zip keys do
        if t.toString == head a.sort || k == head a.sort then
          indexEvents.modify (·.push (.category (← read).key t))
      unless tys.any (·.toString == head a.sort) || keys.contains (head a.sort) do
        let p := s!"{pre}the variable {a.name} prints as ${a.tex}$, which stands for {ty} \
          (latex_category), but has type {a.sort}: name it differently, or change the metavariable ${metavarBase a.tex}$"
        unless (← problems.get).contains p do problems.modify (·.push p)
  -- Free variables that print alike.
  let lctx ← getLCtx
  let free := atoms.filterMap fun a => match a.fvar with
    | some f => if lctx.contains f then some (f, a.tex) else none
    | none => none
  let mut seen : Array (FVarId × String) := #[]
  for (f, t) in free do
    -- Variables nothing uses are all `_`.
    if t == "\\_" then continue
    if let some (f', _) := seen.find? fun (f', t') => t' == t && f' != f then
      let n₁ := (lctx.find? f').map (·.userName.eraseMacroScopes.toString) |>.getD "?"
      let n₂ := (lctx.find? f).map (·.userName.eraseMacroScopes.toString) |>.getD "?"
      let pre := if (← categoriesStyle) == "strict" then "category: " else ""
      let p := s!"{pre}variables {n₁} and {n₂} both print as ${t}$, in ${tex}$"
      unless (← problems.get).contains p do problems.modify (·.push p)
    unless seen.any (·.1 == f) do seen := seen.push (f, t)

/-- Set the frame of the form being rendered, if its reading is expected. -/
def expectFrame (f : Option (Array Validate.Reading → Validate.Reading)) : RenderM Unit := do
  if let some ex := (← read).expect then ex.modify ({ · with frame := f })

/-- The form being rendered is an atom, which reads as its TeX. -/
def expectLeaf (t : String) : RenderM Unit := expectFrame (some fun _ => .node t [])

/-- The form being rendered is a built-in form (`Validate.builtins`) with
these bound variables and `n` subterms. -/
def expectForm (name : String) (vars : Array String) (n : Nat) : RenderM Unit :=
  expectFrame (some fun kids =>
    if kids.size == n then Validate.mkReading name none (vars.map (.node · []) ++ kids)
    else Validate.anyReading)

/-- The form being rendered is an application of `pre` and the subterms. -/
def expectApp (pre : Array String) : RenderM Unit :=
  expectFrame (some fun kids =>
    -- A constant applied only to implicit arguments and proofs shows no
    -- argument, so it reads as an atom: `Fin.castSucc`, not an application.
    if kids.isEmpty && pre.size == 1 then .node pre[0]! []
    else Validate.mkReading "application" none (pre.map (.node · []) ++ kids))

mutual

  /-- Render an expression. A formula a view renders (not a part of one) is
  read back when the context asks for it. -/
  partial def render (e : Expr) : RenderM Doc := do
    let ctx ← read
    if let (some problems, none) := (ctx.problems, ctx.atoms) then
      let atoms ← IO.mkRef #[]
      let ex ← IO.mkRef ({} : Expect)
      let d ← withReader (fun c => { c with atoms := some atoms, expect := some ex }) (render e)
      validate e d (← atoms.get) (((← ex.get).kids[0]?).getD Validate.anyReading) problems
      return d
    let some ex := ctx.expect | renderForm e
    -- This form's subterms' readings are collected afresh, and its own is
    -- added to its parent's.
    let saved ← ex.get
    ex.set {}
    let d ← try renderForm e catch err =>
      ex.set { saved with kids := saved.kids.push Validate.anyReading }
      throw err
    let st ← ex.get
    let r := match st.frame with
      | some f => f st.kids
      | none => Validate.anyReading
    ex.set { saved with kids := saved.kids.push r }
    return d

  /-- Render an expression, without reading it back. -/
  partial def renderForm (e : Expr) : RenderM Doc := do
    let ctx ← read
    let e := e.consumeMData
    -- `latex_style lists := literal`: `[a, b]`, not `a :: b :: []`.
    if ctx.listLiterals then
      if let some xs := listLiteral? e then
        unless xs.isEmpty do
          let mut parts : Array Doc := #[.tex "["]
          for (x, i) in xs.toList.zip (List.range xs.size) do
            if i > 0 then parts := parts ++ #[.tex ",\\ ", .brk]
            parts := parts.push (.child 0 (← render x))
          return .node Doc.maxPrec (parts.push (.tex "]"))
    -- Notation rules first: those for the head constant, or for the binder.
    let head : Name := match e with
      | .forallE _ _ b _ => if b.hasLooseBVar 0 then `_forall else `_arrow
      | .lam .. => `_lam
      | _ => match e.getAppFn with
        | .const h _ => h
        | _ => .anonymous
    unless head.isAnonymous do
      let bare (r : NotationRule) : Bool :=
        r.pat.vars.any (fun v => r.template.trimAscii.toString == s!"#{v}")
      let cands ← candidates head
      -- In a pattern, a rule that writes a constructor as its bare argument
      -- gives way to one that shows it, if the paper has one.
      let shown := cands.any fun r => !bare r && r.pat.arity > 0
      for r in cands do
        if ctx.inPattern && shown && bare r then continue
        let fire (e : Expr) (bs : Array (Name × Expr)) : RenderM (Option Doc) := do
          (← read).used.modify (·.push s!"{r.origin}: {r.template}")
          indexEvents.modify (·.push (.rule (← read).key r))
          return some (← applyRule r bs e)
        let ctx ← read
        if let some d ← r.tryMatchK e (fun bs => (fire e bs).run ctx) then return d
        -- Over-applied, as `(f ∘ g) x`: match a prefix, then apply the rest.
        if let some (pre, rest) ← splitAfterExplicit e r.pat.arity then
          if !rest.isEmpty then
            if let some d ← r.tryMatchK pre (fun bs => (fire pre bs).run ctx) then
              let d ← apply d rest
              expectFrame none
              return d
      if head == ``Exists then
        if let some d ← renderExists e then return d
    match e with
    | .fvar f =>
      let t ← match (← read).overrides.find? (·.1 == f) with
        | some (_, t) => pure t
        | none => do varNameT (← f.getUserName) (← f.getType)
      logAtom t (← sortOf e) (fvar := some f) (name := (← f.getUserName).eraseMacroScopes.toString)
      expectLeaf t
      return .tex t
    | .sort .zero => logAtom "\\mathrm{Prop}" "Sort"; expectLeaf "\\mathrm{Prop}"; return .tex "\\mathrm{Prop}"
    | .sort _ => logAtom "\\mathrm{Type}" "Sort"; expectLeaf "\\mathrm{Type}"; return .tex "\\mathrm{Type}"
    | .lit (.natVal n) => logAtom (toString n) "Nat"; expectLeaf (toString n); return .tex (toString n)
    | .lit (.strVal s) =>
      let t := s!"\\text\{``{TeX.escape s}''}"
      logAtom t "String"
      expectLeaf t
      return .tex t
    | .forallE .. => renderForall e
    | .lam n t b bi =>
      -- A binder Lean named that the body does not use is `_`; one whose
      -- name is in scope already is renamed, so `λx.\,λx.` is not shown.
      let lctx ← getLCtx
      let n := if n.hasMacroScopes && !b.hasLooseBVar 0 then `_
        else Id.run do
          let base := n.eraseMacroScopes
          let mut m := base
          let mut i := 1
          while (lctx.findFromUserName? m).isSome do
            m := base.appendAfter s!"_{i}"
            i := i + 1
          return m
      withLocalDecl n bi t fun x => do
        let body ← render (b.instantiate1 x)
        -- Proofs are not shown, so neither is a λ that binds one: the
        -- branches of `if h : c then a else b` are `a` and `b`.
        if ← isProp t then
          expectFrame (some fun kids => kids[0]?.getD Validate.anyReading)
          return body
        logAtom (← varNameT n t) "*" (isVar := true)
        let v ← varNameT n t
        expectForm "λ" #[v] 1
        return .node 0 #[.tex s!"\\lambda {v}.\\,", .child 0 body]
    | .const h _ =>
      let t := constTeX (← read).strip h
      logAtom t (← sortOf e)
      expectLeaf t
      return .tex t
    | .app .. =>
      if ← isMatcherApp e then
        return ← if (← read).casesMatch then renderMatch e else delab e
      let f := e.getAppFn
      match f with
      | .const h _ =>
        match ← explicitArgsLoose e with
        | some (_, args) =>
          let t := constTeX (← read).strip h
          logAtom t "*"
          let d ← apply (.tex t) args
          expectApp #[t]
          return d
        | none => delab e
      | .fvar _ =>
        if (← read).subscriptVars then
          let fd ← render f
          -- A function that has a script already (`k_{1}`) is grouped, as
          -- `{k_{1}}_{x}`: TeX allows one subscript.
          let t := fd.render 100000
          let scripted := t.endsWith "}" || t.endsWith "'"
          let mut parts : Array Doc :=
            if scripted then #[.tex "{", .child Doc.maxPrec fd, .tex "}_{"]
            else #[.child Doc.maxPrec fd, .tex "_{"]
          for (a, i) in e.getAppArgs.toList.zip (List.range e.getAppNumArgs) do
            if i > 0 then parts := parts.push (.tex ", ")
            parts := parts.push (.child 0 (← render a))
          expectApp #[]
          return .node Doc.maxPrec (parts.push (.tex "}"))
        if (← read).callVars then
          let mut parts : Array Doc := #[.child Doc.maxPrec (← render f)]
          for a in e.getAppArgs do
            parts := parts ++ #[.tex "(", .child 0 (← render a), .tex ")"]
          expectApp #[]
          return .node Doc.maxPrec parts
        let d ← apply (← render f) e.getAppArgs
        expectApp #[]
        return d
      | .lam .. =>
        let d ← apply (← render f) e.getAppArgs
        expectApp #[]
        return d
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
      if let some a := get v then
        let d ← render a
        -- A coercion is invisible: its reading is its argument's.
        expectFrame (some fun kids => kids[0]?.getD Validate.anyReading)
        return d
    -- Flatten a chain: `a ∘ (b ∘ c)` becomes one n-ary node.
    let operands ← if r.flatten && r.pat.binder?.isNone then collect r e else pure #[]
    let topHoles := Id.run do
      let mut d := 0
      let mut out : Array Nat := #[]
      for p in parts do
        match p with
        | .inl t => d := TeX.braceDepth t d
        | .inr _ => out := out.push d
      return out
    let topCount := (topHoles.filter (· == 0)).size
    let mut out : Array Doc := #[]
    let mut depth := 0
    let mut holeIdx := 0
    let mut topIdx := 0
    let mut textW := r.width
    let mut partIdx := 0
    for p in parts do
      partIdx := partIdx + 1
      match p with
      | .inl t =>
        if r.breakBefore && holeIdx > 0 && depth == 0 then out := out.push .brk
        let mut w := texWidth t
        if let some tw := textW then
          w := tw
          textW := some 0
        out := out.push (.text t w)
        depth := TeX.braceDepth t depth
      | .inr v =>
        if hidden.contains v then
          holeIdx := holeIdx + 1
          continue
        -- The precedence the hole needs: the policy the validator's grammar
        -- shares (`Doc.holeNeeds`).
        let need := Doc.holeNeeds r.prec r.assoc depth (partIdx == 1 || partIdx == parts.size)
          (topIdx == 0) (topIdx + 1 == topCount)
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
    -- The reading: the rule's production with its holes' readings. Chains,
    -- folded binders and synonyms are left unchecked.
    match (if r.flatten || !multi.isEmpty then none else Validate.ofRule r) with
    | some p =>
      let n := (p.order.map (·.size)).getD 0
      expectFrame (some fun kids => if kids.size == n then Validate.mkReading p.name p.order kids else Validate.anyReading)
    | none => expectFrame none
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
      let v ← varNameT n t
      logAtom v "*" (isVar := true)
      -- `∃ x, x ∈ s ∧ p` is written `∃ x ∈ s, p`.
      if body.isAppOfArity ``And 2 then
        let mem := body.appFn!.appArg!
        if mem.isAppOfArity ``Membership.mem 5 && mem.appArg! == x then
          let s ← render mem.appFn!.appArg!
          let p ← render body.appArg!
          expectForm "bounded ∃" #[v] 2
          return some (.node 0 #[.tex s!"\\exists {v} \\in ", .child 50 s, .tex ",\\ ", .brk, .child 0 p])
      let p ← render body
      expectForm "∃" #[v] 1
      return some (.node 0 #[.tex s!"\\exists {v},\\ ", .brk, .child 0 p])

  /-- `∀` and implication. -/
  partial def renderForall (e : Expr) : RenderM Doc := do
    let .forallE n t b bi := e | delab e
    let isProp ← isProp e
    if !b.hasLooseBVars then
      -- An implication or a function type.
      let arrow := if isProp then "\\implies" else "\\to"
      let lhs ← render t
      let rhs ← render b
      expectForm (if isProp then "implication" else "function type") #[] 2
      return .node 25 #[.child 26 lhs, .brk, .tex s!" {arrow} ", .child 25 rhs]
    withLocalDecl n bi t fun x => do
      let body := b.instantiate1 x
      -- Instance binders are not shown.
      if bi.isInstImplicit then return ← render body
      let v ← varNameT n t
      logAtom v "*" (isVar := true)
      -- `∀ x, x ∈ s → p` is written `∀ x ∈ s, p`.
      if let .forallE _ dom rest _ := body then
        if !rest.hasLooseBVars && dom.isAppOfArity ``Membership.mem 5 && dom.appArg! == x then
          let s ← render dom.appFn!.appArg!
          return .node 0 #[.tex s!"\\forall {v} \\in ", .child 50 s, .tex ",\\ ", .brk, .child 0 (← render rest)]
      let ty ← render t
      return .node 0 #[.tex s!"\\forall {v} : ", .child 1 ty, .tex ",\\ ", .brk, .child 0 (← render body)]

  /-- A `match` as a case analysis: `\mathsf{case}\ d\ \mathsf{of}\ p_1
  \Rightarrow e_1 \mid \dots`, a branch for each equation of the matcher,
  its patterns and its right-hand side rendered in the notation in scope.
  What cannot be read so is left to Lean's printer. -/
  partial def renderMatch (e : Expr) : RenderM Doc := do
    let some app ← matchMatcherApp? e | delab e
    let some eqns ← (try some <$> Match.getEquationsFor app.matcherName catch _ => pure none)
      | delab e
    let nParams := app.params.size
    let nDiscrs := app.discrs.size
    let commaJoin (ds : Array Doc) : Array Doc := Id.run do
      let mut out : Array Doc := #[]
      for (d, i) in ds.toList.zip (List.range ds.size) do
        if i > 0 then out := out.push (.tex ",\\ ")
        out := out.push (.child 1 d)
      return out
    let discrs ← app.discrs.mapM render
    let mut parts : Array Doc :=
      #[.tex "\\mathsf{case}\\ "] ++ commaJoin discrs ++ #[.tex "\\ \\mathsf{of}\\ "]
    let mut first := true
    for eqn in eqns.eqnNames do
      let ty := (← getConstInfo eqn).type
      let branch? ← forallTelescope ty fun _ body => do
        let some (_, lhs, rhs) := body.eq? | return none
        let args := lhs.getAppArgs
        let pats := args.extract (nParams + 1) (nParams + 1 + nDiscrs)
        let alts := args.extract (nParams + 1 + nDiscrs) (nParams + 1 + nDiscrs + app.alts.size)
        let some k := alts.findIdx? (· == rhs.getAppFn) | return none
        let rhsBody := (app.alts[k]!).beta rhs.getAppArgs
        -- The pattern variables take the names the alternative gives them,
        -- made distinct from the names already in scope: a nested `case`
        -- must not show two variables as one.
        let lctx ← patternNames (app.alts[k]!) rhs.getAppArgs
        withLCtx lctx (← getLocalInstances) do
          let ps ← withReader (fun c => { c with inPattern := true }) (pats.mapM render)
          let b ← render rhsBody
          return some (commaJoin ps ++ #[.tex " \\Rightarrow ", .child 1 b])
      let some branch := branch? | return ← delab e
      unless first do parts := parts ++ #[.brk, .tex " \\mid "]
      first := false
      parts := parts ++ branch
    let d : Doc := .node 0 parts
    if app.remaining.isEmpty then return d else apply d app.remaining

  /-- The local context with each pattern variable `xs[i]` named as the
  alternative `alt` names its `i`th binder, unless that name is inaccessible,
  and renamed when another variable in scope has the name already. -/
  partial def patternNames (alt : Expr) (xs : Array Expr) : RenderM LocalContext := do
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

  /-- Lean's own rendering, in monospace, for what nothing else covers. -/
  partial def delab (e : Expr) : RenderM Doc := do
    let text := toString (← ppExpr e)
    let line := " ".intercalate ((text.splitOn "\n").map (·.trimAscii.toString))
    let t := s!"\\LeanMathCode\{{TeX.escape line}}"
    logAtom t (← sortOf e)
    return .text t line.length

end

end Imprimatur.Render
