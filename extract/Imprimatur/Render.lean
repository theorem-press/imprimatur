/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Timing
import Imprimatur.ValidationLog
import Imprimatur.Doc
import Imprimatur.Trust
import Imprimatur.TeX
import Imprimatur.Notation
import Imprimatur.Commands
import Imprimatur.Views.Lean
import Imprimatur.Requests
import Imprimatur.Validate
import Imprimatur.Denote

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
  /-- A metavariable convention hid a premise of predicate `pred`, and
  printed the variable it constrains as `tex` (DESIGN §7.6). -/
  | convention (key : String) (pred : Name) (tex : String)
  deriving Inhabited

/-- The events of an export, in the order the blocks were rendered. The
views that index the document are rendered after all the others. -/
initialize indexEvents : IO.Ref (Array IndexEvent) ← IO.mkRef #[]

/-- No invisible coercion above. -/
def noChain : Validate.Chain := { visited := [], cast := false, count := none }

/-- A rule's production as an invisible coercion, with its hole's sort:
what the reader's chain rule is decided by (`Validate.Chain.allows`). -/
def coercionOf (r : NotationRule) : Option (Validate.Prod × String) :=
  match Validate.ofRule r with
  | some p => if p.coercion then match p.syms with | [.hole s' _] => some (p, s') | _ => none else none
  | none => none

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
  /-- The variables a metavariable convention names, each with the predicate
  its hidden premise puts it in (`IsValue` for `IsValue v`): the prose view
  binds such a variable in the predicate, not in its type, so that the
  premise the convention hides is still said (DESIGN §7.6). -/
  ranges : Array (FVarId × Expr) := #[]
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
  /-- Rendering a production of a grammar (`Views.alternative`), which shows
  its variables' types only by their letters: under `latex_style categories
  := strict`, each variable's type must have a metavariable. -/
  production : Bool := false
  /-- The variables whose types the block itself states (`Let α ∈ ℝ` in
  prose, `∀ α : ℝ` in a formula): a reader sees the declaration before the
  letter, so it may bear another category's letter there. -/
  declared : Array FVarId := #[]
  /-- The view being rendered (`math`, `rules`, …), for the timing log. -/
  view : String := ""
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
  /-- The grammar of the notation in scope (`Validate.notationGrammar`),
  built once for the formulas a view renders. -/
  grammar : Option Validate.Grammar := none
  /-- The chain of invisible coercions above the term being rendered: a
  coercion is hidden only when the reader's chain rule allows it there, so
  that every chain the renderer hides is one the reader reads
  (docs/coercion-chains.md, route A). Any other form starts a new chain. -/
  chain : Validate.Chain := noChain

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

/-- The metavariables of the category a type belongs to, the category's own
first: its head's, or, for a type that unfolds (`abbrev`), the head's of what
it unfolds to. A category declared with arguments (`latex_category List Prog
=> "p"`) is the type at those arguments only, and is preferred to one
declared bare (`latex_category List => "l"`), which is the type at any. -/
def categoryLetters (ty : Expr) : MetaM (Array String) := do
  let env ← getEnv
  let cats := projectCategories env
  let types := projectCategoryTypes env
  let of (t : Expr) : MetaM (Array String) := do
    let .const h _ := t.getAppFn | return #[]
    let mut typed : Array String := #[]
    let mut bare : Array String := #[]
    for (c, m) in cats do
      if c != h then continue
      match types.find? fun (c', m', _) => c' == c && m' == m with
      | some (_, _, cty) =>
        -- Compared without assigning anything still open in the formula.
        if ← (try withNewMCtxDepth (isDefEq t cty) catch _ => pure false) then typed := typed.push m
      | none => bare := bare.push m
    return if typed.isEmpty then bare else typed
  let ty ← instantiateMVars ty
  let ms ← of ty
  unless ms.isEmpty do return ms
  try of (← whnfR ty) catch _ => return #[]

/-- The category's own metavariable of a type (`categoryLetters`). -/
def categoryLetter? (ty : Expr) : MetaM (Option String) :=
  return (← categoryLetters ty)[0]?

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

/-- A metavariable's base: its TeX without trailing primes and subscript, so
`e_{1}'` is `e`. -/
def metavarBase (t : String) : String := Id.run do
  let mut t := t
  while t.endsWith "'" do t := (t.dropEnd 1).toString
  if t.endsWith "}" then
    let parts := t.splitOn "_{"
    if parts.length ≥ 2 then t := "_{".intercalate (parts.dropLast)
  return t

/-- The TeX of a variable of type `ty`. With `latex_style categories :=
strict`, a variable of a category's type is written with the category's
metavariable and its own decorations (`t : Ty` as $\tau$, `t₁` as
$\tau_{1}$), so the reader knows its type from its letter. Several
variables in scope of one category with no decorations of their own
(`plans trials : ℕ`) are numbered in the order they are bound ($n_{1}$,
$n_{2}$), as BNF numbers them; their Lean names are the development's. -/
def varNameT (n : Name) (ty : Expr) : RenderM String := do
  -- A binder nothing uses is `_`, whatever its type.
  if (← categoriesStyle) == "strict" && n != `_ then
    let ms ← categoryLetters ty
    if let some m := ms[0]? then
      let deco := nameDecorations n
      -- A variable named by one of the category's metavariables keeps it.
      let own ← varName n
      if ms.contains (metavarBase own) then return own
      unless deco.isEmpty do return m ++ deco
      -- The undecorated variables of this category in scope that no
      -- metavariable names, in order; numbered when there are several, or
      -- when a variable in scope is named by the category's own letter.
      let (same, taken) ← (← getLCtx).foldlM (init := (#[], false))
        fun (acc : Array Name × Bool) d => do
          if d.isImplementationDetail then return acc
          unless (← categoryLetters d.type)[0]? == some m do return acc
          let t := metavarBase (← varName d.userName)
          if t == m then return (acc.1, true)
          if ms.contains t || !(nameDecorations d.userName).isEmpty then return acc
          return (acc.1.push d.userName, acc.2)
      if same.size > 1 || taken then
        if let some i := same.idxOf? n then return s!"{m}_\{{i + 1}}"
      return m
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

/-- Whether a notation rule in scope writes `e`: what earns an instance
binder a place among the hypotheses (DESIGN §7.6). -/
def hasRule (e : Expr) : RenderM Bool := do
  let .const head _ := e.getAppFn | return false
  for r in ← candidates head do
    if (← r.tryMatch e).isSome then return true
  return false

/-- Whether a rule of the project (not of a pack) writes `e`. -/
def hasProjectRule (e : Expr) : RenderM Bool := do
  let .const head _ := e.getAppFn | return false
  for r in ← candidates head do
    if r.origin.startsWith "pack " then continue
    if (← r.tryMatch e).isSome then return true
  return false

/-- The hypothesis an instance binder `[C a]` states, if any (DESIGN §7.6):
the class itself when a notation rule writes it (`[Fintype V]` as "V is
finite"); otherwise, for a class in `Prop` with one field and nothing else,
that field's statement (`[NeZero n]` as `n ≠ 0`, `[Fact p]` as `p`), since
the instance is that statement and no more. Any other instance binder,
which fixes structure a paper does not state, is `none`: left out. -/
def instanceHypothesis? (t : Expr) : RenderM (Option Expr) := do
  if ← hasRule t then return some t
  let .const c us := t.getAppFn | return none
  let env ← getEnv
  let some info := getStructureInfo? env c | return none
  let #[field] := info.fieldNames | return none
  let some proj := getProjFnForField? env c field | return none
  unless ← isProp t do return none
  let projTy ← try inferType (mkAppN (mkConst proj us) t.getAppArgs) catch _ => return none
  let .forallE _ _ body _ := (← whnf projTy) | return none
  if body.hasLooseBVars then return none
  return if ← isProp body then some body else none

/-- Log an atom of the formula being rendered. -/
def logAtom (tex : String) (sort : String) (isVar : Bool := false) (fvar : Option FVarId := none)
    (name : String := "") (expr : Option Expr := none) : RenderM Unit := do
  if let some r := (← read).atoms then r.modify (·.push { tex, sort, isVar, fvar, name, expr })

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

/-- The sort of what is shown for an argument: a λ over a proof is shown as
its body (`⋂ n ∈ s, f n` is `iInter fun n => iInter fun _ : n ∈ s => f n`),
so its sort is the body's, not the function's from the proof. -/
partial def shownSortOf (e : Expr) : MetaM String := do
  match e with
  | .lam n t b bi =>
    if ← isProp t then withLocalDecl n bi t fun x => shownSortOf (b.instantiate1 x)
    else sortOf e
  | _ => sortOf e

/-- What a `let` or `have` stands for: its body with the value put in for
the variable. A statement means the same with the definition unfolded, and
so renders in the paper's notation, where Lean's text for the `let` would
not (#135). Metadata is dropped the same way. -/
def unLet? (e : Expr) : Option Expr :=
  match e with
  | .letE _ _ v b _ => some (b.instantiate1 v)
  | .mdata _ e => some e
  | .app (.app (.app (.app (.const ``letFun _) _) _) v) f =>
    some (match f with | .lam _ _ b _ => b.instantiate1 v | _ => .app f v)
  | _ => none

/-- A synonym rule as an equation (DESIGN §18.4): a λ over the variables
its pattern shows, whose body is the denotation of its template read back
in the rest of the notation, with the metavariables of that denotation
abstracted, to be opened afresh at each use. The variables have the types
the pattern gives them, and the reading taken is the one well typed at the
pattern's type. `none` if the template does not read back as one thing. -/
def synonymEquation (g : Validate.Grammar) (r : NotationRule) : RenderM (Option AbstractMVarsResult) := do
  let ctx ← read
  let debug := (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1"
  let vars := Denote.shownVars r
  let names := vars.map (·.toString)
  let some parts := (splitTemplate r.template (r.pat.vars.map (·.toString))).toOption | return none
  let text := String.join (parts.toList.map fun | .inl t => t | .inr v => s!" {v} ")
  let ts := Validate.tokenize text
  let numerals := (ts.filter fun t => t.all Char.isDigit).toList.eraseDups.toArray
  let atomProds : Array Validate.Prod := names.map (fun n =>
    { name := n, sort := "*", prec := Doc.maxPrec, syms := (Validate.tokenize n).toList.map .tok }) ++
    numerals.map fun n => { name := n, sort := "Nat", prec := Doc.maxPrec, syms := [.tok n] }
  let (rs, flags) := Validate.readBack (g.extend atomProds) ts "*"
  if rs.isEmpty || flags.any then
    if debug then IO.eprintln s!"validate: synonym {r.pat.head}: {rs.size} readings of {text}"
    return none
  let rules := ctx.rules.filter fun r' => r'.variant.isNone || r'.variant == ctx.variant
  -- The variables' types, from the pattern: `Fintype a` makes `a` a type.
  let insts ← IO.mkRef #[]
  let coerced ← IO.mkRef #[]
  let postponed : IO.Ref (Array (Expr × Expr × Nat × Bool)) ← IO.mkRef #[]
  let dctx : Denote.Ctx := { rules, coercions := rules.filter Denote.isCoercion, atoms := #[], insts, coerced, postponed }
  let mvars ← vars.mapM fun _ => mkFreshExprMVar none
  -- The pattern's variables take the types the pattern gives them: what
  -- `ofPat` put off is resolved before they are read.
  let lhs ← try (do
      let lhs ← Denote.ofPat r.pat (vars.zip mvars)
      Denote.resolvePostponed (force := true)
      instantiateMVars lhs : Denote.DenoteM Expr).run dctx catch ex =>
    if debug then IO.eprintln s!"validate: synonym {r.pat.head}: pattern: {← ex.toMessageData.toString}"
    return none
  discard <| inferType lhs
  let decls : Array (Name × (Array Expr → RenderM Expr)) :=
    (names.zip mvars).map fun (n, m) => (Name.mkSimple n, fun _ => do instantiateMVars (← inferType m))
  withLocalDeclsD decls fun fvs => do
    let atoms : Array Atom := (names.zip fvs).map (fun (n, fv) =>
      { tex := n, sort := "*", fvar := some fv.fvarId!, name := n, expr := some fv }) ++
      numerals.map fun n => { tex := n, sort := "Nat", expr := some (mkRawNatLit n.toNat!) }
    let mut found : Array Expr := #[]
    for rd in rs do
      match ← Denote.run rules atoms rd with
      | .error msg => if debug then IO.eprintln s!"validate: synonym {r.pat.head}: {rd.text}: {msg}"
      | .ok d =>
        -- A synonym may write a class (a type) as a proposition: any type will do.
        if ← Denote.wellTyped d.term d.insts none then found := found.push d.term
    let #[rhs] := found
      | if debug then IO.eprintln s!"validate: synonym {r.pat.head}: {found.size} well-typed readings of {text}"
        return none
    -- The pattern's variables are the metavariables; the equation is over the locals.
    for (m, fv) in mvars.zip fvs do discard <| isDefEq m fv
    let lam ← mkLambdaFVars fvs (← instantiateMVars rhs)
    return some (← abstractMVars lam)

/-- A synonym rule's template read back in the rest of the notation, with
its shown variables as leaves named `?v`: the shape of text the rule
writes, for `rewriteSynonyms`. `none` if the template does not read back
as one thing. -/
def synonymTemplate (g : Validate.Grammar) (r : NotationRule) : Option Validate.Reading := Id.run do
  let names := (Denote.shownVars r).map (·.toString)
  let some parts := (splitTemplate r.template (r.pat.vars.map (·.toString))).toOption | return none
  let text := String.join (parts.toList.map fun | .inl t => t | .inr v => s!" {v} ")
  let ts := Validate.tokenize text
  let numerals := (ts.filter fun t => t.all Char.isDigit).toList.eraseDups.toArray
  let atomProds : Array Validate.Prod := names.map (fun n =>
    { name := s!"?{n}", sort := "*", prec := Doc.maxPrec, syms := (Validate.tokenize n).toList.map .tok }) ++
    numerals.map fun n => { name := n, sort := "Nat", prec := Doc.maxPrec, syms := [.tok n] }
  let (rs, flags) := Validate.readBack (g.extend atomProds) ts "*"
  if flags.any then return none
  let #[rd] := rs | return none
  return some rd

/-- A reading matched against a synonym's template reading, whose `?v`
leaves are holes: what fills each hole, by the hole's name, or nothing
where they differ. -/
partial def matchTemplate (t r : Validate.Reading) (acc : List (String × Validate.Reading) := []) :
    Option (List (String × Validate.Reading)) :=
  match t, r with
  | .node n [], r =>
    if n.startsWith "?" then some ((n, r) :: acc)
    else if r == .node n [] then some acc else none
  | .node n ks, .node n' ks' =>
    if n != n' || ks.length != ks'.length then none
    else (ks.zip ks').foldlM (init := acc) fun acc (k, k') => matchTemplate k k' acc

/-- A reading with each subtree shaped as a synonym's template rewritten to
the synonym's pattern, children in the order the pattern shows them: `v ∈
Val` read as `Membership.mem[Val; v]`, where no instance makes that well
typed, is `IsValue[v]`, which the synonym declares it to mean. -/
partial def rewriteSynonyms (syns : Array (NotationRule × Validate.Reading)) : Validate.Reading → Validate.Reading
  | .node n ks => Id.run do
    let r := Validate.Reading.node n (ks.map (rewriteSynonyms syns))
    for (rule, t) in syns do
      if let some bs := matchTemplate t r then
        let kids := (Denote.shownVars rule).toList.filterMap fun v => (bs.find? (·.1 == s!"?{v}")).map (·.2)
        return .node rule.pat.shape kids
    return r

/-- The synonym template readings computed so far, by notation variant. -/
initialize synonymTemplateCache : IO.Ref (Array (String × Array (NotationRule × Validate.Reading))) ← IO.mkRef #[]

/-- The synonym equations computed so far, by notation variant: they are
closed terms, the same for every view and entry of a run. -/
initialize synonymCache : IO.Ref (Array (String × Array (NotationRule × AbstractMVarsResult))) ← IO.mkRef #[]

/-- The synonym equations of the notation in scope, computed once per
variant (`synonymCache`). -/
def synonymEquations (g : Validate.Grammar) : RenderM (Array (NotationRule × AbstractMVarsResult)) := do
  let ctx ← read
  -- Keyed by the variant and the rules, for the tests, which run several
  -- notations in one process.
  let variant := s!"{ctx.variant.getD ""}|{ctx.rules.size}|{hash (ctx.rules.map fun r => (r.template, r.pat.head.toString))}"
  if let some (_, eqs) := (← synonymCache.get).find? (·.1 == variant) then return eqs
  let mut eqs := #[]
  let mctx ← readThe Meta.Context
  for r in ctx.rules do
    if r.synonym && (r.variant.isNone || r.variant == ctx.variant) then
      -- A synonym whose equation exhausts the budget is left out, with a
      -- note under IMPRIMATUR_VALIDATE_DEBUG; the view's formulas go on.
      let mst ← getThe Meta.State
      let r? : Except Exception (Option AbstractMVarsResult × Meta.State) ←
        (Core.tryCatchRuntimeEx (do return .ok (← ((synonymEquation g r).run ctx).run mctx mst))
          (fun ex => return .error ex) : CoreM _)
      match r? with
      | .ok (some ab, st) => set st; eqs := eqs.push (r, ab)
      | .ok (none, st) => set st
      | .error ex =>
        if (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1" then
          IO.eprintln s!"validate: synonym {r.pat.head}: {← ex.toMessageData.toString}"
  synonymCache.modify (·.push (variant, eqs))
  return eqs

/-- The synonym template readings of the notation in scope, computed once
per variant (`synonymTemplateCache`). -/
def synonymTemplates (g : Validate.Grammar) : RenderM (Array (NotationRule × Validate.Reading)) := do
  let ctx ← read
  let variant := s!"{ctx.variant.getD ""}|{ctx.rules.size}|{hash (ctx.rules.map fun r => (r.template, r.pat.head.toString))}"
  if let some (_, ts) := (← synonymTemplateCache.get).find? (·.1 == variant) then return ts
  let ts := ctx.rules.filterMap fun r =>
    if r.synonym && (r.variant.isNone || r.variant == ctx.variant) then (synonymTemplate g r).map (r, ·) else none
  synonymTemplateCache.modify (·.push (variant, ts))
  return ts

/-- An expression with the synonym equations applied: each subterm a synonym
rule matches becomes what the rule writes it as. -/
def applySynonyms (eqs : Array (NotationRule × AbstractMVarsResult)) (e : Expr) : RenderM Expr := do
  if eqs.isEmpty then return e
  -- The synonym applies where the renderer would have used it: where no
  -- rule it prefers (`candidates`) matches first.
  let eqs ← eqs.mapM fun (r, ab) => do return (r, ab, ← candidates r.head)
  Meta.transform e (pre := fun sub => do
    for (r, ab, preferred) in eqs do
      unless sub.getAppFn.isConstOf r.head do continue
      let mut taken := false
      for r' in preferred do
        if r'.pat == r.pat && r'.template == r.template && r'.variant == r.variant then break
        if (← r'.tryMatch sub).isSome then taken := true; break
      if taken then continue
      if let some bs ← r.tryMatch sub then
        let vars := Denote.shownVars r
        if vars.all fun v => bs.any (·.1 == v) then
          let args := vars.map fun v => ((bs.find? (·.1 == v)).map (·.2)).getD sub
          let (_, _, lam) ← openAbstractMVarsResult ab
          -- Once at this node, then its children: a synonym whose template
          -- reads back to its own head would otherwise rewrite for ever.
          return .continue (lam.beta args)
    return .continue)

/-- The operands of a chain of a flattening rule, as the renderer collects
them (`collect`). -/
partial def chainOperands (r : NotationRule) (e : Expr) : MetaM (Array Expr) := do
  match ← r.tryMatch e with
  | some bs =>
    let vs := r.pat.vars
    match vs[0]?.bind (fun v => bs.find? (·.1 == v)), vs[1]?.bind (fun v => bs.find? (·.1 == v)) with
    | some (_, a), some (_, b) => return (← chainOperands r a) ++ (← chainOperands r b)
    | _, _ => return #[e]
  | none => return #[e]

/-- The expression rendered, as the notation reads it (DESIGN §18.4): `let`s
unfolded, an instance binder left out or stated as the hypothesis it is
(`instanceHypothesis?`), a λ over a proof as its body, `∃ h : p, q` over a
proof as `p ∧ q`, and a chain of a flattening rule bracketed as the rule's
associativity has it, the notation having declared the operation
associative; then the synonym equations. These are what the renderer does
to the expression besides writing it in the notation. -/
partial def normalise (g : Validate.Grammar) (e : Expr) : RenderM Expr := do
  let ctx ← read
  let chains := ctx.rules.filter fun r =>
    r.flatten && r.pat.binder?.isNone && !r.synonym && (r.variant.isNone || r.variant == ctx.variant)
  let rec go (e : Expr) : RenderM Expr := do
    Denote.trace do return s!"normalise {e.getAppFn.constName?.getD `_} ({e.approxDepth})"
    if let some e' := unLet? e then return ← go e'
    match e with
    | .forallE n t b bi =>
      if bi.isInstImplicit && !b.hasLooseBVars then
        match ← instanceHypothesis? t with
        | some h => return mkForall n .default (← go h) (← go b)
        | none => return ← go b
      let t' ← go t
      withLocalDecl n bi t' fun x => do mkForallFVars #[x] (← go (b.instantiate1 x))
    | .lam n t b bi =>
      if (← isProp t) && !b.hasLooseBVar 0 then return ← go (b.lowerLooseBVars 1 1)
      let t' ← go t
      withLocalDecl n bi t' fun x => do mkLambdaFVars #[x] (← go (b.instantiate1 x))
    | .app .. =>
      if e.isAppOfArity ``Exists 2 then
        if let .lam _ t b _ := e.appArg! then
          if (← isProp t) && !b.hasLooseBVar 0 then return ← go (mkAnd t (b.lowerLooseBVars 1 1))
      -- A chain of three or more operands of one type, rebracketed: the
      -- notation declares it associative. A chain whose operands differ in
      -- type (`(a, b, c)`) is bracketed as its types demand, and left.
      for r in chains do
        if e.getAppFn.isConstOf r.head && (← r.tryMatch e).isSome then
          let ops ← chainOperands r e
          let ty ← inferType e
          let homogeneous ← ops.allM fun o => do withReducible <| isDefEq (← inferType o) ty
          if ops.size ≥ 3 && homogeneous then
            let ops ← ops.mapM go
            -- The outer application, with its two explicit arguments replaced.
            let some (_, #[_, _]) ← explicitArgsLoose e | break
            let some ci := (← getEnv).find? e.getAppFn.constName! | break
            let args := e.getAppArgs
            let mut ty := ci.type
            let mut idx : Array Nat := #[]
            for i in [0:args.size] do
              match ty with
              | .forallE _ _ b bi =>
                if bi.isExplicit then idx := idx.push i
                ty := b
              | _ => idx := idx.push i
            let some i₀ := idx[0]? | break
            let some i₁ := idx[1]? | break
            let node (x y : Expr) : Expr := mkAppN e.getAppFn ((args.set! i₀ x).set! i₁ y)
            if r.assoc == "right" then
              let rev := ops.reverse
              return rev.toList.tail!.foldl (fun acc o => node o acc) rev[0]!
            else return ops.toList.tail!.foldl node ops[0]!
      e.withApp fun f args => do return mkAppN (← go f) (← args.mapM go)
    | .mdata _ e => go e
    | _ => pure e
  let e ← go e
  applySynonyms (← synonymEquations g) e

/-- Read a rendered formula back (DESIGN §18.4): exactly one of its readings
must be well typed at the formula's type, and that reading must denote the
formula (`Denote`), up to what the notation leaves implicit and reducible
unfolding; and its free variables must print differently. Problems go to
the context's `problems`. -/
def validate (e : Expr) (d : Doc) (atoms : Array Atom)
    (problems : IO.Ref (Array String)) (renderMs : Nat := 0) : RenderM Unit := do
  let ctx ← read
  let t0 ← IO.monoMsNow
  let before := (← problems.get).size
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
  -- A production with a token the formula lacks reads none of it: this
  -- formula's grammar is the productions whose tokens all occur, and its
  -- atoms, so a large notation costs a formula only what it could read as.
  let present (p : Validate.Prod) : Bool := p.syms.all fun
    | .tok t => ts.contains t
    | .list elem _ _ => elem.all fun | .tok t => ts.contains t | _ => true
    | _ => true
  let g := Validate.Grammar.of ((base.prods.map (·.1)).filter present ++ leaves)
  let h₀ ← IO.getNumHeartbeats
  let (rs, flags, steps) := Validate.readBackSteps g ts (← sortOf e)
  let tParsed ← IO.monoMsNow
  let rules := ctx.rules.filter fun r => r.variant.isNone || r.variant == ctx.variant
  let debug := (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1"
  -- The expression as the notation reads it, and its type: what the one
  -- reading must denote, and the type it must have. Then each reading's
  -- denotation, kept if it is well typed; one whose denotation fails (a
  -- type that fits nothing) is ill typed too. Each formula has the entry's
  -- heartbeat budget afresh; one that exhausts it is not validated, as for
  -- the parser.
  let body : RenderM (Expr × Array (Validate.Reading × Denote.Denotation)) := do
    Denote.trace do return s!"formula {tex}"
    let e' ← normalise base e
    Denote.trace do return "normalised"
    let τ ← inferType e'
    Denote.trace do return s!"type {← ppExpr τ}"
    let mut typed : Array (Validate.Reading × Denote.Denotation) := #[]
    let attempt (r : Validate.Reading) : RenderM (Option Denote.Denotation) := do
      match ← Denote.run rules atoms r (some τ) with
      | .ok d =>
        Denote.trace do return "denoted; typing"
        if ← Denote.wellTyped d.term d.insts (some τ) then return some d
        if debug then
          IO.eprintln s!"validate: ill typed {r.text} = {← withOptions (pp.explicit.set · true) (ppExpr (← instantiateMVars d.term))} : {← ppExpr τ}"
        return none
      | .error msg =>
        if debug then IO.eprintln s!"validate: no denotation of {r.text}: {msg}"
        return none
    let syns ← synonymTemplates base
    for r in rs do
      match ← attempt r with
      | some d => typed := typed.push (r, d)
      | none =>
        -- Ill typed as read: as the synonyms say the text means, if that
        -- is another reading (`v ∈ Val` for `IsValue v`).
        let r' := rewriteSynonyms syns r
        if r' != r then
          if debug then IO.eprintln s!"validate: by synonym {r.text} is {r'.text}"
          if let some d ← attempt r' then typed := typed.push (r, d)
    return (e', typed)
  let mctx ← readThe Meta.Context
  let mst ← getThe Meta.State
  let denoted : Except Exception ((Expr × Array (Validate.Reading × Denote.Denotation)) × Meta.State) ←
    (Core.tryCatchRuntimeEx
      (do return .ok (← withCurrHeartbeats (Denote.withDepth (body.run ctx) |>.run mctx mst)))
      (fun ex => return .error ex) : CoreM _)
  -- IMPRIMATUR_VALIDATION_LOG: the formula, its readings, what the well-typed
  -- ones denote, the term it was rendered from, and the verdict, which is
  -- read off the problem this formula added, if any (`Imprimatur.ValidationLog`).
  let logEvent (typed : Array (Validate.Reading × Denote.Denotation)) (e' : Option Expr) (alike : Bool) :
      RenderM Unit := do
    unless ← ValidationLog.on do return
    let ps ← problems.get
    let news := ps.extract before ps.size
    let (verdict, reason) := match news[0]? with
      | some p =>
        (if p.startsWith "misread" then "misread" else if p.startsWith "ambiguous" then "ambiguous"
         else "not validated", p)
      | none => if alike then ("skipped", "two free variables print alike") else ("validated", "")
    let dens ← typed.mapM fun (_, d) => do return toJson (← ppExpr (← instantiateMVars d.term)).pretty
    let now ← IO.monoMsNow
    let mut fields : List (String × Json) :=
      [("key", toJson ctx.key), ("view", toJson ctx.view), ("tex", toJson tex), ("verdict", toJson verdict)]
    unless reason.isEmpty do fields := fields ++ [("reason", toJson reason)]
    fields := fields ++ [("readings", toJson (rs.map (·.text))), ("typed", toJson (typed.map (·.1.text))),
      ("denotes", Json.arr dens), ("rendered", toJson (← ppExpr e).pretty)]
    if let some e' := e' then
      if e' != e then fields := fields ++ [("normalised", toJson (← ppExpr e').pretty)]
    fields := fields ++ [("tokens", toJson ts.size), ("steps", toJson steps), ("ms", toJson (now - t0)),
      ("parse_ms", toJson (tParsed - t0)), ("denote_ms", toJson (now - tParsed))]
    ValidationLog.event fields
  -- IMPRIMATUR_TIMING: the formula, its sizes, and the time rendering,
  -- reading it back and denoting it took (`Imprimatur.Timing`).
  if ← Timing.on then
    Timing.event "formula" ((← IO.monoMsNow) - t0)
      [("key", toJson ctx.key), ("view", toJson ctx.view), ("render_ms", toJson renderMs),
       ("parse_ms", toJson (tParsed - t0)), ("denote_ms", toJson ((← IO.monoMsNow) - tParsed)),
       ("tokens", toJson ts.size), ("steps", toJson steps), ("readings", toJson rs.size),
       ("tex", toJson (String.ofList (tex.toList.take 120)))]
  let (e', typed) ← match denoted with
    | .ok (r, st) => set st; pure r
    | .error ex =>
      if debug then IO.eprintln s!"validate: denoting {tex} failed: {← ex.toMessageData.toString}"
      problems.modify (·.push s!"not validated, as reading it back took too long: ${tex}$")
      logEvent #[] none false
      return
  -- Free variables that print alike: the text cannot be read, and is
  -- reported below for that, not as a misread.
  let lctx ← getLCtx
  let free := atoms.filterMap fun a => match a.fvar with
    | some f => if lctx.contains f then some (f, a.tex) else none
    | none => none
  let alike := free.any fun (f, t) => free.any fun (f', t') => f != f' && t == t'
  -- IMPRIMATUR_VALIDATE_READINGS=1 prints each formula, as one tab-separated
  -- line: its key, its TeX, the readings the parser found, and what the
  -- well-typed ones denote (the about paper's example diagram draws them).
  if (← (IO.getEnv "IMPRIMATUR_VALIDATE_READINGS" : IO _)) == some "1" then
    let dens ← typed.mapM fun (r, d) => do pure s!"{r.text} = {← ppExpr (← instantiateMVars d.term)}"
    IO.eprintln s!"reading\t{ctx.key}\t{tex}\t{" | ".intercalate (rs.toList.map (·.text))}\t{" | ".intercalate dens.toList}"
  -- IMPRIMATUR_VALIDATE_STATS=1 counts the questions each formula asks, and
  -- the heartbeats (small allocations, in thousands) reading it back took.
  if (← (IO.getEnv "IMPRIMATUR_VALIDATE_STATS" : IO _)) == some "1" then
    let h₁ ← IO.getNumHeartbeats
    let log := (Validate.readBackLog g ts (← sortOf e)).2
    IO.eprintln s!"stats {ts.size} tokens {log.size} questions {(h₁ - h₀) / 1000} kbeats key {ctx.key}: {tex}"
    if log.size > 100000 then for l in log do IO.eprintln s!"  read {l}"
  -- Two well-typed readings are two readings, whatever else was dropped.
  if typed.size ≥ 2 then
    -- IMPRIMATUR_VALIDATE_DEBUG=1 shows what was read where, and the atoms'
    -- sorts, which are what tell two readings apart.
    if (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1" then
      IO.eprintln s!"validate: ambiguous {ts} as {← sortOf e}"
      for l in (Validate.readBackLog g ts (← sortOf e)).2 do IO.eprintln s!"  read {l}"
      for p in leaves do IO.eprintln s!"  atom {p.name} : {p.sort}"
    problems.modify (·.push s!"ambiguous: ${tex}$ reads as {typed[0]!.1.text} and as {typed[1]!.1.text}")
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
  else if alike then pure ()
  else if typed.isEmpty then
    -- Every reading is ill typed: the text names something else.
    problems.modify (·.push s!"misread: ${tex}$ reads as {rs[0]!.text}, which is not well typed as \
      `{← ppExpr e}` is")
  else
    let (r, d) := typed[0]!
    -- The one reading is not what was rendered: the emitter left out
    -- parentheses a reader needs, or the text says something else.
    unless ← Denote.agrees rules e' d do
      if debug then
        let coes := rules.filter Denote.isCoercion
        let chs := Denote.chainRules rules
        IO.eprintln s!"validate: misread\n  rendered  {← ppExpr e}\n  as read   {← ppExpr e'}\n  denotes   {← ppExpr (← instantiateMVars d.term)}\n  skeleton  {repr (← Denote.skeleton coes (← instantiateMVars e') #[] chs)}\n  skeleton' {repr (← Denote.skeleton coes (← instantiateMVars d.term) d.coerced chs)}"
      problems.modify (·.push s!"misread: ${tex}$ reads as {r.text}, that is \
        `{← ppExpr (← instantiateMVars d.term)}`, but was rendered from `{← ppExpr e}`")
  logEvent typed (some e') alike
  -- A grammar category's metavariable stands for that category (the BNF
  -- convention: `e ::= e₁\;e₂`), so a variable of another type must not
  -- print as it.
  let cats := projectCategories (← getEnv)
  for a in atoms do
    if a.fvar.isNone || a.sort == "*" || Validate.isTyVar a.sort || a.sort.startsWith "'" then continue
    -- A variable the block declares with its type may bear any letter there.
    if (← read).declared.contains a.fvar.get! then continue
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
  -- A production of a grammar says what a form takes only by its variables'
  -- letters (`design(n, \overline{x})`), so under `strict` every variable
  -- in one has a declared metavariable.
  if (← read).production && (← categoriesStyle) == "strict" then
    for a in atoms do
      let some f := a.fvar | continue
      if a.sort == "*" || Validate.isTyVar a.sort || a.sort.startsWith "'" then continue
      let some d := lctx.find? f | continue
      if (← categoryLetter? d.type).isNone then
        let p := s!"category: the variable {a.name} has type {← ppExpr d.type}, which has no \
          metavariable, so the production does not say what it ranges over: declare one \
          (latex_category)"
        unless (← problems.get).contains p do problems.modify (·.push p)
  -- Free variables that print alike.
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

mutual

  /-- Render an expression. A formula a view renders (not a part of one) is
  read back when the context asks for it. -/
  partial def render (e : Expr) : RenderM Doc := do
    let ctx ← read
    if let (some problems, none) := (ctx.problems, ctx.atoms) then
      let atoms ← IO.mkRef #[]
      let t0 ← IO.monoMsNow
      let d ← withReader (fun c => { c with atoms := some atoms }) (render e)
      let renderMs := (← IO.monoMsNow) - t0
      validate e d (← atoms.get) problems renderMs
      return d
    renderForm e

  /-- Render an expression, without reading it back. The chain of invisible
  coercions above it reaches only a coercion's rule; anything else is
  rendered with no chain above. -/
  partial def renderForm (e : Expr) : RenderM Doc := do
    let ch := (← read).chain
    withReader (fun c => { c with chain := noChain }) (renderFormIn ch e)

  /-- `renderForm`, below the chain of invisible coercions `ch`. -/
  partial def renderFormIn (ch : Validate.Chain) (e : Expr) : RenderM Doc := do
    let ctx ← read
    let e := e.consumeMData
    -- `latex_style lists := literal`: `[a, b]`, not `a :: b :: []`, unless
    -- the project writes this list's cons itself (`{x : a, y : b}`).
    if ctx.listLiterals && !(← hasProjectRule e) then
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
    -- `∃ h : p, q` over a proof the body does not mention is `p ∧ q`, before
    -- any rule for `∃` binds `h` as a variable and loses the hypothesis.
    if e.isAppOfArity ``Exists 2 then
      if let .lam _ t b _ := e.appArg! then
        if (← isProp t) && !b.hasLooseBVar 0 then return ← render (mkAnd t b)
    unless head.isAnonymous do
      let bare (r : NotationRule) : Bool :=
        r.pat.vars.any (fun v => r.template.trimAscii.toString == s!"#{v}")
      let cands ← candidates head
      -- In a pattern, a rule that writes a constructor as its bare argument
      -- gives way to one that shows it, if the paper has one.
      let shown := cands.any fun r => !bare r && r.pat.arity > 0
      for r in cands do
        if ctx.inPattern && shown && bare r then continue
        -- An invisible coercion is hidden only where the chain rule allows
        -- it; elsewhere it gives way, to a rule that shows it or to the
        -- constant applied (`\LeanMathConst{Option.some}\,x`).
        let coe := coercionOf r
        -- The chain below this rule: one more coercion, or a new chain.
        let below (ch : Validate.Chain) : Option Validate.Chain := match coe with
          | some (p, s') => if ch.allows Validate.algebra p s' then some (ch.push Validate.algebra p s') else none
          | none => some noChain
        let fire (ch : Validate.Chain) (e : Expr) (bs : Array (Name × Expr)) : RenderM (Option Doc) := do
          (← read).used.modify (·.push s!"{r.origin}: {r.template}")
          indexEvents.modify (·.push (.rule (← read).key r))
          return some (← withReader (fun c => { c with chain := ch }) (applyRule r bs e))
        let ctx ← read
        if let some ch' := below ch then
          if let some d ← r.tryMatchK e (fun bs => (fire ch' e bs).run ctx) then return d
        -- Over-applied, as `(f ∘ g) x`: match a prefix, then apply the rest.
        -- The prefix is the function of an application, so starts a chain.
        if let some (pre, rest) ← splitAfterExplicit e r.pat.arity then
          if let (false, some ch') := (rest.isEmpty, below noChain) then
            if let some d ← r.tryMatchK pre (fun bs => (fire ch' pre bs).run ctx) then
              let d ← apply d rest
              return d
      if head == ``Exists then
        if let some d ← renderExists e then return d
    if let some e' := unLet? e then return ← render e'
    match e with
    | .fvar f =>
      let t ← match (← read).overrides.find? (·.1 == f) with
        | some (_, t) => pure t
        | none => do varNameT (← f.getUserName) (← f.getType)
      logAtom t (← sortOf e) (fvar := some f) (name := (← f.getUserName).eraseMacroScopes.toString)
        (expr := some e)
      return .tex t
    | .sort .zero => logAtom "\\mathrm{Prop}" "Sort" (expr := some e); return .tex "\\mathrm{Prop}"
    | .sort _ => logAtom "\\mathrm{Type}" "Sort" (expr := some e); return .tex "\\mathrm{Type}"
    | .lit (.natVal n) => logAtom (toString n) "Nat" (expr := some e); return .tex (toString n)
    | .lit (.strVal s) =>
      let t := s!"\\text\{``{TeX.escape s}''}"
      logAtom t "String" (expr := some e)
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
        let e' := b.instantiate1 x
        -- Proofs are not shown, so neither is a λ that binds one: the
        -- branches of `if h : c then a else b` are `a` and `b`.
        if ← isProp t then
          let body ← render e'
          return body
        -- `fun p => match p with | (a, b) => e` destructures its argument:
        -- it is written with the pattern for its binder, `λ (a, b).\, e`.
        if let some d ← renderPatternLambda x e' then return d
        let body ← render e'
        logAtom (← varNameT n t) "*" (isVar := true)
        let v ← varNameT n t
        return .node 0 #[.tex s!"\\lambda {v}.\\,", .child 0 body]
    | .const h _ =>
      let t := constTeX (← read).strip h
      logAtom t (← sortOf e) (expr := some e)
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
          -- The constant's sort as applied here: a function from its shown
          -- arguments' sorts to the result's, so that the application reads
          -- back with a known sort, and `|f x|` is the cardinality of what
          -- `f x` is (#90). Proofs are not shown, so not counted.
          let shown ← args.filterM fun a => do return !(← isProof a)
          let sorts ← shown.mapM fun a => (shownSortOf a : MetaM String)
          let sort := sorts.foldr (fun a acc => s!"({a} → {acc})") (← sortOf e)
          logAtom t sort (expr := some f)
          let d ← apply (.tex t) args
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
          return .node Doc.maxPrec (parts.push (.tex "}"))
        if (← read).callVars then
          let mut parts : Array Doc := #[.child Doc.maxPrec (← render f)]
          for a in e.getAppArgs do
            parts := parts ++ #[.tex "(", .child 0 (← render a), .tex ")"]
          return .node Doc.maxPrec parts
        let d ← apply (← render f) e.getAppArgs
        return d
      | .lam .. =>
        let d ← apply (← render f) e.getAppArgs
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
    -- A binder over a proof is a hypothesis, not a variable (`renderExists`
    -- writes `∃ h : p, q` as `p ∧ q`): the fold stops before it.
    match ← r.tryMatchK body (fun bs' => do
        if let some (_, xv') := bs'.find? (·.1 == x) then
          if ← isProp (← inferType xv') then return none
        return some (← (foldBinders r bs' x p xs body).run ctx)) with
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
        return ← render a
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
    -- `∃ h : p, q`, over a proof the body does not mention, is `p ∧ q`: the
    -- hypothesis is stated, not a vacuous "there is h".
    if (← isProp t) && !b.hasLooseBVar 0 then return some (← render (mkAnd t b))
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
          return some (.node 0 #[.tex s!"\\exists {v} \\in ", .child 50 s, .tex ",\\ ", .brk, .child 0 p])
      let p ← render body
      return some (.node 0 #[.tex s!"\\exists {v},\\ ", .brk, .child 0 p])

  /-- `∀` and implication. -/
  partial def renderForall (e : Expr) : RenderM Doc := do
    let .forallE n t b bi := e | delab e
    let isProp ← isProp e
    if !b.hasLooseBVars then
      -- An instance binder is left out, unless it states a hypothesis
      -- (`instanceHypothesis?`): then the paper states it (DESIGN §7.6).
      let t ← if bi.isInstImplicit then
          match ← instanceHypothesis? t with
          | some h => pure h
          | none => return ← render b
        else pure t
      -- An implication or a function type.
      let arrow := if isProp then "\\implies" else "\\to"
      let lhs ← render t
      let rhs ← render b
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
      -- The binder states the variable's type, so the letter check passes it over.
      let body ← withReader (fun c => { c with declared := c.declared.push x.fvarId! }) (render body)
      return .node 0 #[.tex s!"\\forall {v} : ", .child 1 ty, .tex ",\\ ", .brk, .child 0 body]

  /-- A `match` as a case analysis: `\mathsf{case}\ d\ \mathsf{of}\ p_1
  \Rightarrow e_1 \mid \dots`, a branch for each equation of the matcher,
  its patterns and its right-hand side rendered in the notation in scope.
  What cannot be read so is left to Lean's printer. -/
  partial def renderMatch (e : Expr) : RenderM Doc := do
    let some app ← matchMatcherApp? e | delab e
    let some branches ← matchBranches app | delab e
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
    for (ps, b) in branches do
      unless first do parts := parts ++ #[.brk, .tex " \\mid "]
      first := false
      parts := parts ++ commaJoin ps ++ #[.tex " \\Rightarrow ", .child 1 b]
    let d : Doc := .node 0 parts
    if app.remaining.isEmpty then return d else apply d app.remaining

  /-- The branches of a matcher application, from the matcher's equations:
  each alternative's patterns and its right-hand side, rendered in the
  notation in scope. `none` when an equation cannot be read. -/
  partial def matchBranches (app : MatcherApp) : RenderM (Option (Array (Array Doc × Doc))) := do
    let some eqns ← (try some <$> Match.getEquationsFor app.matcherName catch _ => pure none)
      | return none
    let nParams := app.params.size
    let nDiscrs := app.discrs.size
    let mut out : Array (Array Doc × Doc) := #[]
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
          return some (ps, b)
      let some branch := branch? | return none
      out := out.push branch
    return some out

  /-- A λ whose body is a `match` on its own variable with one alternative,
  `fun p => match p with | (a, b) => e`: written with the pattern as its
  binder, `\lambda (a, b).\, e`, in the notation in scope, whatever the
  `pattern_matching` style. The pattern reads back as the term it is (a
  pair of variables), under the λ form. `none` for any other λ. -/
  partial def renderPatternLambda (x e : Expr) : RenderM (Option Doc) := do
    let ctx ← read
    withDestructuring x e fun pat rhs => (do
      let p ← withReader (fun c => { c with inPattern := true }) (render pat)
      let b ← render rhs
      return some (.node 0 #[.tex "\\lambda ", .child Doc.maxPrec p, .tex ".\\,", .child 0 b])
      : RenderM (Option Doc)).run ctx

  /-- Lean's own rendering, in monospace, for what nothing else covers. The
  text is Lean's, in which the paper's notation and metavariables do not
  apply, and the read-back takes it for any subterm (DESIGN §18.4), so a
  formula that falls back is reported as not validated (#135). -/
  partial def delab (e : Expr) : RenderM Doc := do
    let text := toString (← ppExpr e)
    let line := " ".intercalate ((text.splitOn "\n").map (·.trimAscii.toString))
    let t := s!"\\LeanMathCode\{{TeX.escape line}}"
    if let some problems := (← read).problems then
      let msg := s!"not validated: `{line}` is Lean's own text for a subterm nothing renders, \
        in which the paper's notation does not apply"
      problems.modify fun ps => if ps.contains msg then ps else ps.push msg
    logAtom t (← sortOf e) (expr := some e)
    return .text t line.length

end

end Imprimatur.Render
