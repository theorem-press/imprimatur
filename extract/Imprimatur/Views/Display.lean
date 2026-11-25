/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Views.Math
import Imprimatur.Views.Grammar
import Imprimatur.Views.Index

/-!
# Displays of definitions and grammars

Definitions and grammars set as a paper sets them in a display: a titled box
of rows, each a formula with its description flush right.

- **`clauses`**: each definition by its equations, `lhs ≜ rhs`, as
  `\LeanClause{…}{description}` rows. The definition of a type shows its
  category's metavariable (`m ∈ T ≜ …`).
- **`grammar|display`**: each inductive type as a `\LeanCategory{m ∈ T}{…}`
  row, followed by its constructors as `\LeanEntry{…}{…}` rows; a structure's
  fields are one entry, a record, three fields to a row, or, when they are
  documented, one row each with its description.

A block shows one declaration (its key), or the declarations of a display
(`latex_display "Title" := […]`, whose title is the key). Descriptions are
the docstrings' first sentences, as `\leanslot`s named after what they
describe, so an author's rewording survives regeneration. `imprimatur.sty`
sets the rows in the `LeanDisplay` environment.
-/

namespace Imprimatur.Views

open Lean Meta Render

/-- The signature of a definition as a row: the definition applied to its
binders, in the type it returns, `f(x, y) ∈ T`, with the binders' types as
the row's text, `for x ∈ A, y ∈ B`. An instance binder is left out, as the
`math` view leaves it out of a statement; a binder that is a proposition is
written as that proposition. Generic binder names (`a`, `x✝`) are named
after their categories, as in an equation. -/
def signatureRow (d : Name) : RenderM String := do
  let ci ← getConstInfo d
  let ty ← nameEqnBinders ci.type (some d)
  forallTelescope ty fun xs body => do
    let lhs ← render (mkAppN (.const d (ci.levelParams.map mkLevelParam)) xs)
    let res ← render body
    let mut binders : Array String := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit then continue
      let t := decl.type
      let tTeX := (← render t).render 100000
      if ← isProp t then binders := binders.push s!"${tTeX}$"
      else binders := binders.push s!"${← varNameT decl.userName t} \\in {tTeX}$"
    let text := if binders.isEmpty then "" else "for " ++ ", ".intercalate binders.toList
    return s!"\\LeanClause\{{lhs.render 100000} \\in {res.render 100000}}\{{text}}"

/-- Whether `types` (the `clauses` view's option) asks for the signature of
`d`: `types=` asks for every definition's, `types=f,g` for those named. -/
def wantsSignature (types : Option (Array String)) (d : Name) : Bool :=
  match types with
  | none => false
  | some #[] => true
  | some names => names.any fun n => d.toString == n || d.toString.endsWith ("." ++ n)

/-- Whether `include=` and `exclude=` select an equation, by the constants
its left-hand side mentions, named by their last component: for a definition
by cases, `include=randomized,noInterference` keeps the cases of those
constructors. -/
def selectEqn (lhs : Expr) (incl excl : Array String) : Bool :=
  let short (c : Name) := match c with | .str _ s => s | _ => c.toString
  let names := lhs.foldConsts (#[] : Array String) fun c acc => acc.push (short c)
  (incl.isEmpty || names.any incl.contains) && !names.any excl.contains

/-- The rows of definitions, `lhs ≜ rhs`: the `clauses` view. With `types`,
a definition's signature row precedes its equations (`signatureRow`); `incl`
and `excl` select the equations shown (`selectEqn`). -/
def clausesView (decls : Array Name) (types : Option (Array String) := none)
    (incl excl : Array String := #[]) : RenderM String := do
  let cats := projectCategories (← getEnv)
  let mut rows : Array String := #[]
  for d in decls do
    let some es ← getEqnsFor? d
      | throwError "{d} has no equations: the clauses view shows definitions"
    noteShown d
    let doc ← docSentence d
    if wantsSignature types d then rows := rows.push (← signatureRow d)
    -- The definition of a type shows the metavariable that ranges over it.
    let isType ← forallTelescope (← getConstInfo d).type fun _ b => return b.isSort
    let mv := if isType then (cats.find? (·.1 == d)).map (·.2) else none
    let mut n := 0
    for e in es do
      let ty := (← getConstInfo e).type
      -- `include=` and `exclude=` select equations by the constants of their
      -- left-hand sides.
      let keep ← forallTelescope ty fun _ b =>
        return !b.isAppOfArity ``Eq 3 || selectEqn b.appFn!.appArg! incl excl
      unless keep do continue
      let eqn ← nameEqnBinders (restoreEqnNames ty) d
      let row ← equationRow eqn
      let row := row.replace " &= " " \\;\\deq\\; "
      let row := match mv, n with
        | some m, 0 => s!"{m} \\in {row}"
        | _, _ => row
      -- The description goes with the first equation shown.
      let desc := if n == 0 then s!"\\leanslot\{{d}}\{{doc}}" else ""
      rows := rows.push s!"\\LeanClause\{{row}}\{{desc}}"
      n := n + 1
  return "\\begin{LeanDisplay}\n" ++ "\\\\\n".intercalate rows.toList ++ "\n\\end{LeanDisplay}"

/-- The rows of grammars: the `grammar|display` view. -/
def displayGrammarView (tys : Array Name) : RenderM String := do
  let env ← getEnv
  let cats := projectCategories env
  let mut blocks : Array String := #[]
  for ty in tys do
    let some (.inductInfo i) := env.find? ty | throwError "{ty} is not an inductive type"
    noteShown ty
    -- The head is the type, with its category's letter when it has one.
    let hasCat := cats.any (·.1 == ty)
    let letter := ((cats.find? (·.1 == ty)).map (·.2)).getD (constTeX (← read).strip ty)
    let tyTeX ← typeTeX ty
    let head := s!"\\LeanCategory\{{if hasCat then s!"{letter} \\in {tyTeX}" else tyTeX}}\{\\leanslot\{{ty}}\{{← docSentence ty}}}"
    let fieldNames := if isStructure env ty then getStructureFields env ty else #[]
    let documented ← fieldNames.anyM fun f => return (← findDocString? env (ty ++ f)).isSome
    let entries ← if documented then
        -- A structure whose fields are documented is set one field to a row,
        -- each with its description; the field's type keeps its own binders,
        -- `self` is written as the category's letter, and its fields by name.
        fieldNames.mapM fun f => do
          let proj := ty ++ f
          let pci ← getConstInfo proj
          let fty ← forallBoundedTelescope pci.type (some (i.numParams + 1)) fun xs body => do
            let self := xs.back!
            let lctx := (← getLCtx).setUserName self.fvarId! (if hasCat then Name.mkSimple letter else `self)
            Meta.withLCtx lctx (← getLocalInstances) do
              withFieldsNamed ty xs.pop self body fun body =>
                return (← render body).render 100000
          return s!"\\LeanEntry\{\\mathit\{{TeX.escape f.toString}} : {fty}}\{\\leanslot\{{proj}}\{{← docSentence proj}}}"
      else if isStructure env ty then
        i.ctors.toArray.mapM fun c => do
          let ci ← getConstInfo c
          forallTelescope ci.type fun xs _ => do
            let fields := xs.extract i.numParams xs.size
            let parts ← fields.mapM fun x => do
              let n := (← x.fvarId!.getUserName).eraseMacroScopes.toString
              return s!"\\mathit\{{n}} : {(← render (← inferType x)).render 100000}"
            -- A record of many fields is set three fields to a row.
            let rows := (List.range ((parts.size + 2) / 3)).map fun k =>
              ",\\ ".intercalate (parts.extract (3 * k) (3 * k + 3)).toList
            return s!"\\LeanEntry\{\\\{{",}{}\\\\\n\\LeanEntry{\\quad ".intercalate rows}\\}}\{}"
      else i.ctors.toArray.mapM fun c => do
        return s!"\\LeanEntry\{{← alternative (← getConstInfo c)}}\{\\leanslot\{{c}}\{{← docSentence c}}}"
    blocks := blocks.push (head ++ "\\\\\n" ++ "\\\\\n".intercalate entries.toList)
  return "\\begin{LeanDisplay}\n" ++ "\\\\[.5ex]\n".intercalate blocks.toList ++ "\n\\end{LeanDisplay}"

end Imprimatur.Views
