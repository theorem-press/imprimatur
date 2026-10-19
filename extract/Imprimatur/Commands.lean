/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Notation

/-!
# `latex_notation` and `latex_metavar`

The commands of a notation module (DESIGN §6.2, §7.5):

```lean
latex_notation Des.nest A B => r"\nestD{#A}{#B}"  width := 5
latex_notation (variant := "named") Des.nest A B => r"\kw{nest}\;#A\;#B"
latex_notation ¬ SetRealization.Realize U φ ρ => r"#U \not\models #φ"  hide ρ := Fin.elim0  prec := 50
latex_notation Label.lub a b => r"\lub{#a, #b}"  flatten
latex_metavar spec => "L"
```

**Elaborating the pattern.** The pattern is elaborated as an ordinary term:

- every identifier that doesn't name a constant becomes a pattern variable,
  bound as a local of unknown type;
- `_` is a wildcard.

So notation such as `=`, `¬` or `+` works in patterns, and every constant is
resolved: a renamed constant is an error when the notation module is built
(DESIGN §4, constraint 3).
-/

namespace Imprimatur

open Lean Elab Command Term Meta

/-- An option after a notation rule's template. -/
declare_syntax_cat latexNotationOpt (behavior := symbol)
/-- `prec := n`: the precedence of the rendered result. -/
syntax &"prec" " := " num : latexNotationOpt
/-- `width := n`: the rendered width in characters, for line breaking. -/
syntax &"width" " := " num : latexNotationOpt
/-- `hide x := v`: apply only when `x` is `v`, and leave it out. -/
syntax &"hide" ident " := " term:max : latexNotationOpt
/-- `flatten`: render nested applications as one n-ary chain, or nested
binders as one list of variables. -/
syntax &"flatten" : latexNotationOpt
/-- `synonym`: the rule writes an expression as another rule writes one it
equals (`Nat.card R` as `|R|`, like `Fintype.card R`), so reading a formula
back identifies the two (DESIGN §18.3). -/
syntax &"synonym" : latexNotationOpt
/-- `when x := v`: apply only when `x` matches the pattern `v`, and show it. -/
syntax &"when" ident " := " term:max : latexNotationOpt
/-- `sep := ", "`: the text between the variables of a flattened binder rule. -/
syntax &"sep" " := " str : latexNotationOpt
/-- `assoc := left | right | none`: which side of a chain at the rule's own
precedence is left without parentheses. -/
syntax &"assoc" " := " (&"left" <|> &"right" <|> &"none") : latexNotationOpt

/-- `latex_notation (variant := "v")? PATTERN => "TEMPLATE" OPTIONS*` -/
syntax (name := latexNotation)
  "latex_notation " (atomic("(" &"variant" " := " str ")"))? term " => " str latexNotationOpt* : command

/-- `latex_metavar NAME => "TEX"`: render binders named `NAME` as `TEX`;
with `decorated`, also `NAME` with a subscript or primes (`NAME₁` as
`TEX_{1}`). -/
syntax (name := latexMetavar) "latex_metavar " ident " => " str (&" decorated")? : command

/-- The identifiers in a pattern that don't name constants. -/
partial def patternVars (stx : Syntax) : TermElabM (Array Name) := do
  let mut out := #[]
  match stx with
  | .ident _ _ n _ =>
    if n.isAtomic && !n.isAnonymous && (← resolveGlobalName n).isEmpty && !out.contains n then
      out := out.push n
  | .node _ _ args =>
    for a in args do
      for v in ← patternVars a do
        unless out.contains v do out := out.push v
  | _ => pure ()
  return out

/-- Turn an elaborated pattern into a `Pat`: locals are variables, holes are
wildcards, and applications of constants are matched on their explicit
arguments. -/
partial def toPat (vars : Array (Name × Expr)) (e : Expr) : MetaM Pat := do
  let e := (← instantiateMVars e).consumeMData
  -- An unknown term, possibly applied (`?k i` in the type `Fin (?k i)`).
  if e.getAppFn.isMVar then return .wild
  if let .fvar _ := e then
    match vars.find? (·.2 == e) with
    | some (n, _) => return .var n
    | none => throwError "unexpected local {e} in a notation pattern"
  if let .const h _ := e then return .app h #[]
  -- Binders written in the pattern (`fun x => p`, `∀ x, p`) bind a pattern
  -- variable of the binder's name; an arrow (`p → q`) has a binder name
  -- that is not a variable.
  match e with
  | .lam n t b _ =>
    let some (_, x) := vars.find? (·.1 == n)
      | throwError "the binder {n} must be a pattern variable (a name that isn't a constant)"
    discard <| isDefEq (← inferType x) t
    return .lam n (← toPat vars (b.instantiate1 x))
  | .forallE n t b _ =>
    match vars.find? (·.1 == n) with
    | some (_, x) =>
      discard <| isDefEq (← inferType x) t
      return .pi n (← toPat vars t) (← toPat vars (b.instantiate1 x))
    | none =>
      if b.hasLooseBVar 0 then
        throwError "the binder {n} must be a pattern variable (a name that isn't a constant)"
      return .arrow (← toPat vars t) (← toPat vars b)
  | _ => pure ()
  -- A constant applied to its explicit arguments, fully or partly (a rule
  -- for `f a` applies to the function `f a`, as in `Summable (f a)`).
  match ← explicitArgsLoose e with
  | some (h, args) =>
    let pat : Pat := .app h (← args.mapM (toPat vars))
    -- Implicit arguments the pattern fixes, such as the type `Set ?α` in
    -- `(a : Set α) ≤ b`, constrain the match. Ones it leaves open (still
    -- metavariables, or instances) don't.
    let ci ← getConstInfo h
    let mut ty := ci.type
    let mut cs : Array (Nat × Pat) := #[]
    for (a, i) in e.getAppArgs.toList.zip (List.range e.getAppNumArgs) do
      let .forallE _ _ b bi := ty | break
      ty := b
      if bi.isExplicit || bi.isInstImplicit then continue
      let a ← instantiateMVars a
      if a.isMVar then continue
      let p ← toPat vars a
      unless p matches .wild do cs := cs.push (i, p)
    return if cs.isEmpty then pat else .constrained pat cs
  | none =>
    if e.hasFVar || e.hasMVar then
      throwError "notation patterns must be applications of constants, not {e}"
    return .lit e

/-- A template split into text and variables. At each `#`, the variable is
the longest pattern variable the template continues with, so `#k'` is `k`
followed by a prime when `k` is a variable and `k'` is not. A `#` followed by
no variable is an error, reported with the name it seems to start. -/
def splitTemplate (t : String) (vars : Array String) :
    Except String (Array (Sum String String)) := Id.run do
  let cs := t.toList.toArray
  let mut out : Array (Sum String String) := #[]
  let mut text := ""
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '#' && i + 1 < cs.size && isIdFirst cs[i + 1]! then
      let rest := String.ofList (cs.extract (i + 1) cs.size).toList
      let best := vars.foldl (fun (b : Option String) v =>
        if rest.startsWith v && (b.map (fun x => decide (x.length < v.length))).getD true then some v else b) none
      match best with
      | some v =>
        unless text.isEmpty do out := out.push (.inl text)
        text := ""
        out := out.push (.inr v)
        i := i + 1 + v.length
      | none =>
        let mut j := i + 1
        while j < cs.size && isIdRest cs[j]! do j := j + 1
        return .error (String.ofList (cs.extract (i + 1) j).toList)
    else
      text := text.push cs[i]!
      i := i + 1
  unless text.isEmpty do out := out.push (.inl text)
  return .ok out

/-- Elaborate a pattern (see the module docs): its `Pat`, and its variables. -/
def elabPatternSorted (patStx : Syntax) :
    TermElabM (Pat × Array Name × Array (Name × String) × String) := do
  let vars ← patternVars patStx
  -- An unknown name at the head would be read as a pattern variable.
  if patStx.getKind == ``Lean.Parser.Term.app && patStx[0].isIdent && vars.contains patStx[0].getId then
    throwErrorAt patStx[0] "unknown constant {patStx[0].getId} at the head of the pattern \
      (a name that isn't a constant is read as a pattern variable)"
  -- Bind each pattern variable as a local whose type is unknown.
  let rec withVars (i : Nat) (acc : Array (Name × Expr)) :
      TermElabM (Pat × Array (Name × String) × String) := do
    if h : i < vars.size then
      let ty ← mkFreshTypeMVar
      withLocalDeclD vars[i] ty fun x => withVars (i + 1) (acc.push (vars[i], x))
    else
      -- Instances cannot be found for variables of unknown type
      -- (`Decidable p`), and don't matter: a pattern ignores them. No info
      -- tree: the binders of `∀ x, p` would be reported as unused.
      let e ← withReader (fun ctx => { ctx with ignoreTCFailures := true }) <|
        withEnableInfoTree false <| withoutErrToSorry do
          let e ← elabTerm patStx none
          synthesizeSyntheticMVars (postpone := .yes)
          -- Elaboration may be postponed (`binrel%` waits for its operands'
          -- types, `spec.order` for the type of `spec`): resume it with
          -- postponement off, so it completes or reports its error. Not
          -- `synthesizeSyntheticMVarsNoPostponing`: that applies default
          -- instances, which would fix the type of `OfNat.ofNat n` to `Nat`.
          withoutPostponing <| synthesizeSyntheticMVars (postpone := .yes)
          pure e
      let pat ← toPat acc e
      unless pat matches .app .. | .constrained .. | .lam .. | .pi .. | .arrow .. do
        let head := ((← instantiateMVars e).getAppFn.fvarId?.bind fun f => acc.find? (·.2 == .fvar f)).map (·.1)
        match head with
        | some h => throwErrorAt patStx "{h} is not a constant, so it was read as a pattern \
            variable; a pattern must have a constant at its head"
        | none => throwErrorAt patStx "a pattern must have a constant at its head, not {repr pat}"
      -- The sorts of the variables and of the whole, for reading back. A
      -- universe in a pattern was defaulted when it was elaborated, but the
      -- matcher ignores universes, so it stands for any (`p → q` matches
      -- implications and function types): its sort is unknown.
      -- A type that mentions the pattern's own variables (`k : ι → ℕ` in
      -- `PlanMatrix R C ι k`) stands for whatever they match: the pattern's
      -- variables are type variables there.
      let loose (k : String) : String := Id.run do
        if k == "Sort" || k == "Sort*" then return "*"
        let mut k := k
        for (_, x) in acc do
          k := k.replace s!"'{x.fvarId!.name}" s!"?{x.fvarId!.name}"
        return k
      -- But a type is known to be one when its head has no universe to
      -- default (`Fin n`), and a variable whose type is a universe is a type
      -- (or a proposition, which is read where a type is expected): `[n]`,
      -- the type `Fin n`, is then not read as a list.
      let closed ← match (← instantiateMVars e).getAppFn with
        | .const c _ => do pure ((← getConstInfo c).levelParams.isEmpty)
        | _ => pure false
      let sorts ← acc.mapM fun (n, x) => do
        let k ← sortKey (← inferType x)
        return (n, if k == "Sort" || k == "Sort*" then k else loose k)
      let sort ← try (fun k => if closed && k == "Sort" then k else loose k) <$> sortKey (← inferType e)
        catch _ => pure "*"
      return (pat, sorts, sort)
  let (pat, sorts, sort) ← withVars 0 #[]
  return (pat, vars, sorts, sort)

/-- Elaborate a pattern (see the module docs): its `Pat`, and its variables. -/
def elabPattern (patStx : Syntax) : TermElabM (Pat × Array Name) := do
  let (pat, vars, _, _) ← elabPatternSorted patStx
  return (pat, vars)

/-- The atom of an option written as one of several keywords
(`(&"left" <|> &"right")`), which the parser may wrap in a node. -/
partial def choiceAtom (stx : Syntax) : String :=
  if stx.isAtom then stx.getAtomVal
  else match stx.getArgs[0]? with
    | some a => choiceAtom a
    | none => ""

/-- Elaborate `latex_notation`. -/
@[command_elab latexNotation] def elabLatexNotation : CommandElab := fun stx => do
  let variant := if stx[1].getNumArgs == 0 then none else stx[1][3].isStrLit?
  let some template := stx[4].isStrLit? | throwErrorAt stx[4] "expected a string"
  let rule ← liftTermElabM do
    let (pat, vars, holeSorts, sort) ← elabPatternSorted stx[2]
    let mut r : NotationRule :=
      { pat, template, variant, origin := toString (← getMainModule), sort, holeSorts }
    for o in stx[5].getArgs do
      -- Each option starts with its keyword.
      match o[0].getAtomVal with
      | "prec" => r := { r with prec := o[2].isNatLit?.getD 1024 }
      | "width" => r := { r with width := o[2].isNatLit? }
      | "flatten" => r := { r with flatten := true }
      | "synonym" => r := { r with synonym := true }
      | "sep" => r := { r with sep := o[2].isStrLit?.getD ", " }
      | "assoc" => r := { r with assoc := choiceAtom o[2] }
      | "hide" | "when" =>
        let x := o[1].getId
        unless vars.contains x do
          throwErrorAt o[1] "{x} is not a variable of the pattern"
        -- The value is a pattern too, so `Fin.elim0` matches whatever its
        -- implicit arguments are, and `Exists _` any existential.
        let v ← instantiateMVars (← elabTerm o[3] none)
        synthesizeSyntheticMVars (postpone := .yes)
        let p ← toPat #[] v
        if o[0].getAtomVal == "hide" then r := { r with hides := r.hides.push (x, p) }
        else r := { r with guards := r.guards.push (x, p) }
      | _ => throwErrorAt o "unknown notation option"
    if let .error v := splitTemplate template (pat.vars.map (·.toString)) then
      throwErrorAt stx[4] "the template uses #{v}, which is not a variable of the pattern"
    if r.flatten && pat.arity != 2 && pat.binder?.isNone then
      throwErrorAt stx "flatten needs a pattern with exactly two arguments, or a binder"
    -- A variable the template neither shows nor accounts for is lost: two
    -- expressions that differ only there render alike (DESIGN §18.3).
    if let .ok parts := splitTemplate template (pat.vars.map (·.toString)) then
      let shown := parts.filterMap fun | .inr v => some v | .inl _ => none
      for x in pat.vars do
        unless shown.contains x.toString || r.hides.any (·.1 == x) || r.guards.any (·.1 == x) do
          logWarningAt stx[4] m!"the template does not show #{x}, so expressions that differ \
            only in {x} render alike; show it, or say what it must be with `when {x} := …` \
            or `hide {x} := …`"
    return r
  modifyEnv (notationExt.addEntry · (.rule rule))

/-- Elaborate `latex_metavar`. -/
@[command_elab latexMetavar] def elabLatexMetavar : CommandElab := fun stx => do
  let some tex := stx[3].isStrLit? | throwErrorAt stx[3] "expected a string"
  let decorated := stx[4].getNumArgs > 0
  modifyEnv (notationExt.addEntry · (.metavar { name := stx[1].getId, tex := tex, decorated }))

/-- `latex_group "Title" := [c₁, c₂, …]`: constructors shown together by the
`rules` view, as the block with key `Title` (DESIGN §6.2). -/
syntax (name := latexGroup) "latex_group " str " := " "[" ident,* "]" : command

/-- Elaborate `latex_group`. -/
@[command_elab latexGroup] def elabLatexGroup : CommandElab := fun stx => do
  let some title := stx[1].isStrLit? | throwErrorAt stx[1] "expected a string"
  let ctors ← stx[4].getSepArgs.mapM fun id => liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  for (c, id) in ctors.zip stx[4].getSepArgs do
    unless (← getEnv).find? c matches some (.ctorInfo _) do
      throwErrorAt id "{c} is not a constructor"
  modifyEnv (notationExt.addEntry · (.group { title, ctors }))

/-- `latex_rule_label C "T-App"`: the label of the rule for constructor `C`
(DESIGN §7.4). -/
syntax (name := latexRuleLabel) "latex_rule_label " ident ppSpace str : command

/-- Elaborate `latex_rule_label`. -/
@[command_elab latexRuleLabel] def elabLatexRuleLabel : CommandElab := fun stx => do
  let c ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some label := stx[2].isStrLit? | throwErrorAt stx[2] "expected a string"
  modifyEnv (notationExt.addEntry · (.ruleLabel c label))

/-- An option of `latex_rules`. -/
declare_syntax_cat latexRulesOpt (behavior := symbol)
/-- `label := "($\\Downarrow$\\text{-#})"`: the label template; `#` is the rule's name. -/
syntax &"label" " := " str : latexRulesOpt
/-- `label_macro := "rulelabel"`: write `\rulelabel{Key}{label}%` before each rule. -/
syntax &"label_macro" " := " str : latexRulesOpt

/-- `sep := " "`: the text between the words of a label made from a
constructor's name (`scalar_lit` gives `Scalar Lit`); `-` by default. -/
syntax &"sep" " := " str : latexRulesOpt

/-- `doc_labels := false`: don't read labels from the constructors'
docstrings (DESIGN §7.4), when they start with prose such as `Variables: …`. -/
syntax &"doc_labels" " := " (&"true" <|> &"false") : latexRulesOpt

/-- `latex_rules I OPTIONS`: how the rules of inductive `I` are labelled. -/
syntax (name := latexRules) "latex_rules " ident latexRulesOpt* : command

/-- Elaborate `latex_rules`. -/
@[command_elab latexRules] def elabLatexRules : CommandElab := fun stx => do
  let i ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  unless (← getEnv).find? i matches some (.inductInfo _) do
    throwErrorAt stx[1] "{i} is not an inductive type"
  let mut st : RulesStyle := { induct := i }
  for o in stx[2].getArgs do
    match o[0].getAtomVal, o[2].isStrLit? with
    | "label", some t => st := { st with label := t }
    | "label_macro", some m => st := { st with labelMacro := some m }
    | "sep", some t => st := { st with sep := t }
    | "doc_labels", _ => st := { st with docLabels := choiceAtom o[2] == "true" }
    | _, _ => throwErrorAt o "unknown option"
  modifyEnv (notationExt.addEntry · (.rulesStyle st))

/-- `latex_metavar_convention P v => "\\val"`: hide premises matching `P`,
and render the variable they constrain, `v`, as `\\val` (DESIGN §7.6). -/
syntax (name := latexMetavarConvention) "latex_metavar_convention " term " => " str : command

/-- Elaborate `latex_metavar_convention`. -/
@[command_elab latexMetavarConvention] def elabLatexMetavarConvention : CommandElab := fun stx => do
  let some tex := stx[3].isStrLit? | throwErrorAt stx[3] "expected a string"
  let (pat, vars) ← liftTermElabM (elabPattern stx[1])
  let [v] := vars.toList
    | throwErrorAt stx[1] "a metavariable convention's pattern must have exactly one variable"
  modifyEnv (notationExt.addEntry · (.convention { pat, metavar := some (v, tex) }))

/-- `latex_hide_premise P`: hide premises matching `P` (DESIGN §7.6). -/
syntax (name := latexHidePremise) "latex_hide_premise " term : command

/-- Elaborate `latex_hide_premise`. -/
@[command_elab latexHidePremise] def elabLatexHidePremise : CommandElab := fun stx => do
  let (pat, _) ← liftTermElabM (elabPattern stx[1])
  modifyEnv (notationExt.addEntry · (.convention { pat }))

/-- `latex_entry "Key" => decl (options := "forall, names=full")?`: the
declaration a key of the document names, when the key is a title rather than
a Lean name (DESIGN §6.2). The options are those of a block (DESIGN §9.1),
and apply to every view of the key. -/
syntax (name := latexEntry) "latex_entry " str " => " ident (&"options" " := " str)? : command

/-- Elaborate `latex_entry`. -/
@[command_elab latexEntry] def elabLatexEntry : CommandElab := fun stx => do
  let some key := stx[1].isStrLit? | throwErrorAt stx[1] "expected a string"
  let decl ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[3])
  let opts : Array (String × String) := Id.run do
    let some text := (if stx[4].getNumArgs == 0 then none else stx[4][2].isStrLit?) | return #[]
    let mut out := #[]
    for o in text.splitOn "," do
      let o := o.trimAscii.toString
      if o.isEmpty then continue
      match o.splitOn "=" with
      | [k, v] => out := out.push (k.trimAscii.toString, v.trimAscii.toString)
      | _ => out := out.push (o, "")
    return out
  if (projectEntries (← getEnv)).any (·.1 == key) then
    throwErrorAt stx[1] "the key {repr key} already has an entry"
  modifyEnv (notationExt.addEntry · (.entry key decl opts))

/-- `latex_style KEY := VALUE`: a style setting of the renderer (DESIGN §7.5):

- `names := italic` (the default) sets binder names longer than one letter
  in `\mathit`, and escapes them; `names := raw` writes them as they are, so
  a binder name is TeX (`l_c`);
- `applied_variables := juxtaposed` (the default) renders a variable applied
  to arguments as `f\,a\,b`; `applied_variables := call` as `f(a)(b)`;
  `applied_variables := subscript` as `f_{a, b}` (a family, as in `k_x`).
- `pattern_matching := code` (the default) renders a `match` with Lean's printer;
  `pattern_matching := cases` as a case analysis in the notation in scope,
  `\mathsf{case}\ d\ \mathsf{of}\ p_1 \Rightarrow e_1 \mid \dots`. -/
syntax (name := latexStyle) "latex_style " ident " := " ident : command

/-- Elaborate `latex_style`. -/
@[command_elab latexStyle] def elabLatexStyle : CommandElab := fun stx => do
  let key := stx[1].getId.toString
  let value := stx[3].getId.toString
  let known : List (String × List String) :=
    [("names", ["italic", "raw"]), ("applied_variables", ["juxtaposed", "call", "subscript"]),
     ("pattern_matching", ["code", "cases"]), ("lists", ["cons", "literal"])]
  let some (_, values) := known.find? (·.1 == key)
    | throwErrorAt stx[1] "unknown style {key}; the styles are {", ".intercalate (known.map (·.1))}"
  unless values.contains value do
    throwErrorAt stx[3] "{key} must be one of {", ".intercalate values}, not {value}"
  modifyEnv (notationExt.addEntry · (.style key value))

/-- `latex_category T => "e"`: the metavariable of grammar category `T`
(the `grammar` view). -/
syntax (name := latexCategory) "latex_category " ident " => " str : command

/-- Elaborate `latex_category`. -/
@[command_elab latexCategory] def elabLatexCategory : CommandElab := fun stx => do
  let t ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let some tex := stx[3].isStrLit? | throwErrorAt stx[3] "expected a string"
  modifyEnv (notationExt.addEntry · (.category t tex))

end Imprimatur
