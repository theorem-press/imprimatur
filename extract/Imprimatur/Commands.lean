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
latex_notation Tm.app A B => r"\app{#A}{#B}"  width := 5
latex_notation (variant := "named") Tm.app A B => r"\kw{nest}\;#A\;#B"
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
/-- `flatten`: render nested applications as one n-ary chain. -/
syntax &"flatten" : latexNotationOpt

/-- `latex_notation (variant := "v")? PATTERN => "TEMPLATE" OPTIONS*` -/
syntax (name := latexNotation)
  "latex_notation " (atomic("(" &"variant" " := " str ")"))? term " => " str latexNotationOpt* : command

/-- `latex_metavar NAME => "TEX"`: render binders named `NAME` as `TEX`. -/
syntax (name := latexMetavar) "latex_metavar " ident " => " str : command

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
  if e.isMVar then return .wild
  if let .fvar _ := e then
    match vars.find? (·.2 == e) with
    | some (n, _) => return .var n
    | none => throwError "unexpected local {e} in a notation pattern"
  if let .const h _ := e then return .app h #[]
  match ← explicitArgs e with
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
    -- A constant applied only to implicit arguments, such as `@Fin.elim0 ?α`.
    if let some (h, #[]) ← explicitArgsLoose e then return .app h #[]
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

/-- Elaborate `latex_notation`. -/
@[command_elab latexNotation] def elabLatexNotation : CommandElab := fun stx => do
  let variant := if stx[1].getNumArgs == 0 then none else stx[1][3].isStrLit?
  let patStx := stx[2]
  let some template := stx[4].isStrLit? | throwErrorAt stx[4] "expected a string"
  let rule ← liftTermElabM do
    let vars ← patternVars patStx
    -- An unknown name at the head would be read as a pattern variable.
    if patStx.getKind == ``Lean.Parser.Term.app && patStx[0].isIdent && vars.contains patStx[0].getId then
      throwErrorAt patStx[0] "unknown constant {patStx[0].getId} at the head of the pattern \
        (a name that isn't a constant is read as a pattern variable)"
    -- Bind each pattern variable as a local whose type is unknown.
    let rec withVars (i : Nat) (acc : Array (Name × Expr)) : TermElabM NotationRule := do
      if h : i < vars.size then
        let ty ← mkFreshTypeMVar
        withLocalDeclD vars[i] ty fun x => withVars (i + 1) (acc.push (vars[i], x))
      else
        let e ← withoutErrToSorry <| elabTerm patStx none
        synthesizeSyntheticMVars (postpone := .yes)
        -- Elaboration may be postponed (as for `≤` with typed operands); finish
        -- it if it can be, and otherwise keep what there is.
        try synthesizeSyntheticMVarsNoPostponing catch _ => pure ()
        let pat ← toPat acc e
        unless pat matches .app .. | .constrained .. do
          let head := ((← instantiateMVars e).getAppFn.fvarId?.bind fun f => acc.find? (·.2 == .fvar f)).map (·.1)
          match head with
          | some h => throwErrorAt patStx "{h} is not a constant, so it was read as a pattern \
              variable; a notation pattern must have a constant at its head"
          | none => throwErrorAt patStx "a notation pattern must have a constant at its head, not {repr pat}"
        let mut r : NotationRule := { pat, template, variant, origin := toString (← getMainModule) }
        for o in stx[5].getArgs do
          -- Each option starts with its keyword.
          match o[0].getAtomVal with
          | "prec" => r := { r with prec := o[2].isNatLit?.getD 1024 }
          | "width" => r := { r with width := o[2].isNatLit? }
          | "flatten" => r := { r with flatten := true }
          | "hide" =>
            let x := o[1].getId
            unless vars.contains x do
              throwErrorAt o[1] "{x} is not a variable of the pattern"
            -- The value is a pattern too, so `Fin.elim0` matches whatever its
            -- implicit arguments are.
            let v ← instantiateMVars (← elabTerm o[3] none)
            synthesizeSyntheticMVars (postpone := .yes)
            r := { r with hides := r.hides.push (x, ← toPat #[] v) }
          | _ => throwErrorAt o "unknown notation option"
        if let .error v := splitTemplate template (pat.vars.map (·.toString)) then
          throwErrorAt stx[4] "the template uses #{v}, which is not a variable of the pattern"
        if r.flatten && pat.arity != 2 then
          throwErrorAt stx "flatten needs a pattern with exactly two arguments"
        return r
    withVars 0 #[]
  modifyEnv (notationExt.addEntry · (.rule rule))

/-- Elaborate `latex_metavar`. -/
@[command_elab latexMetavar] def elabLatexMetavar : CommandElab := fun stx => do
  let some tex := stx[3].isStrLit? | throwErrorAt stx[3] "expected a string"
  modifyEnv (notationExt.addEntry · (.metavar { name := stx[1].getId, tex }))

end Imprimatur
