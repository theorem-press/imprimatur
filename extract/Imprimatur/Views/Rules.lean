/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render

/-!
# The `rules` view

Each constructor of an inductive predicate becomes a mathpartir
`\inferrule` (DESIGN §7.3).

**Premises.** A constructor's explicit binders whose type is a proposition
are its premises. They are kept in their source order, after the premise
conventions of DESIGN §7.6 hide some:

- `latex_hide_premise P` hides premises matching `P`;
- `latex_metavar_convention P v => "\val"` hides premises matching `P`, and
  renders the variable `v` they constrain as `\val` (with the variable's own
  subscript).

**Hidden binders.** Implicit and instance binders are never premises.

**The conclusion** is the constructor's result type.

**The label** is chosen in the order of DESIGN §7.4:

1. a `latex_rule_label`;
2. a docstring that starts `Label:` or `Label.`;
3. the constructor's name, prettified (`i_nest` becomes `I-Nest`).

The inductive's `latex_rules` template then places the label (`#`). With
`label_macro`, each rule is preceded by `\macro{Key}{label}%`, so prose can
refer to it.

**Layout.**

```latex
\begin{mathpar}

\inferrule[Label]
  {
    premise \\
    premise
  }
  { conclusion }

\and

…
\end{mathpar}
```
-/

namespace Imprimatur.Views

open Lean Meta Render

/-- The words of a constructor's name: its last component, split at `_`. -/
def nameWords (c : Name) : Array String :=
  let last := match c with
    | .str _ s => s
    | _ => c.toString
  (last.splitOn "_").toArray.filter (!·.isEmpty) |>.map fun w =>
    match w.toList with
    | ch :: rest => String.ofList (ch.toUpper :: rest)
    | [] => w

/-- A docstring's label: the text before a leading `:` or `.`, if it is short
and has no spaces (`/-- T-CB: … -/`). -/
def docLabel? (doc : String) : Option String :=
  let doc := doc.trimAscii.toString
  let cut := doc.takeWhile (fun c => c != ':' && c != '.' && c != ' ' && c != '\n')
  let rest := (doc.drop cut.toString.length).toString
  if !cut.isEmpty && cut.toString.length ≤ 20 && (rest.startsWith ":" || rest.startsWith ".") then
    some cut.toString
  else none

/-- A rule's label, and its key (the name without spaces). -/
def ruleLabel (c : Name) (style : Option RulesStyle) : MetaM (String × String) := do
  let env ← getEnv
  let words := nameWords c
  let key := String.join words.toList
  let sep := (style.map (·.sep)).getD "-"
  let base ← match (projectRuleLabels env).find? (·.1 == c) with
    | some (_, l) => pure l
    | none =>
      let fromName := sep.intercalate words.toList
      if (style.map (·.docLabels)).getD true then
        match ← findDocString? env c with
        | some d => pure ((docLabel? d).getD fromName)
        | none => pure fromName
      else pure fromName
  let template := (style.map (·.label)).getD "#"
  return (template.replace "#" base, key)

/-- The variable a metavariable convention renders, with its subscript:
`v₁` with `\val` gives `\val_{1}`. -/
def conventionTeX (tex : String) (name : Name) : String :=
  let plain := varTeX #[] name
  match plain.splitOn "_" with
  | _ :: sub :: rest => tex ++ "_" ++ "_".intercalate (sub :: rest)
  | _ => tex

/-- One rule. -/
partial def renderRule (c : ConstantInfo) (style : Option RulesStyle) : RenderM String := do
  let (label, key) ← ruleLabel c.name style
  go c.type #[] #[] fun premises concl overrides => do
    withReader (fun ctx => { ctx with overrides := ctx.overrides ++ overrides }) do
      let ps ← premises.mapM fun p => do return (← render p).render 100000
      let cs := (← render concl).render 100000
      let mark := match style.bind (·.labelMacro) with
        | some m => s!"\\{m}\{{key}}\{{label}}%\n"
        | none => ""
      if ps.isEmpty then
        return s!"{mark}\\inferrule[{label}]\n  \{ }\n  \{ {cs} }"
      let body := " \\\\\n".intercalate (ps.toList.map ("    " ++ ·))
      return s!"{mark}\\inferrule[{label}]\n  \{\n{body}\n  }\n  \{ {cs} }"
where
  /-- Walk the binders: premises, and variables a convention renders. -/
  go {α : Type} (e : Expr) (premises : Array Expr) (overrides : Array (FVarId × String))
      (k : Array Expr → Expr → Array (FVarId × String) → RenderM α) : RenderM α := do
    match e with
    | .forallE n t b bi =>
      withLocalDecl n bi t fun x => do
        let body := b.instantiate1 x
        if bi.isExplicit && (← isProp t) then
          -- A premise, unless a convention hides it.
          let mut hidden := false
          let mut overrides := overrides
          for cv in projectConventions (← getEnv) do
            if let some bs ← cv.pat.matchExpr t then
              hidden := true
              if let some (v, tex) := cv.metavar then
                if let some (_, .fvar f) := bs.find? (·.1 == v) then
                  overrides := overrides.push (f, conventionTeX tex (← f.getUserName))
          go body (if hidden then premises else premises.push t) overrides k
        else go body premises overrides k
    | _ => k premises e overrides

/-- The constructors a `rules` block shows: an inductive's, or a group's,
less any `exclude`d, or only the `include`d. Names match on their last
component. -/
def selectCtors (ctors : Array Name) (incl excl : Array String) : Array Name :=
  let short (c : Name) := match c with | .str _ s => s | _ => c.toString
  ctors.filter fun c =>
    (incl.isEmpty || incl.contains (short c)) && !excl.contains (short c)

/-- The `rules` view of constructors. -/
def rulesView (ctors : Array Name) : RenderM String := do
  let env ← getEnv
  let styles := projectRulesStyles env
  let mut out : Array String := #["\\begin{mathpar}"]
  for c in ctors do
    match env.find? c with
    | some ci@(.ctorInfo i) =>
      let style := styles.find? (·.induct == i.induct)
      out := out ++ #["", ← renderRule ci style, "", "\\and"]
    | _ => out := out.push s!"% {c} is not a constructor"
  if out.back? == some "\\and" then out := out.pop
  return "\n".intercalate (out.push "\\end{mathpar}").toList

end Imprimatur.Views
