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

/-- The rows of definitions, `lhs ≜ rhs`: the `clauses` view. -/
def clausesView (decls : Array Name) : RenderM String := do
  let cats := projectCategories (← getEnv)
  let mut rows : Array String := #[]
  for d in decls do
    let some es ← getEqnsFor? d
      | throwError "{d} has no equations: the clauses view shows definitions"
    noteShown d
    let doc ← docSentence d
    -- The definition of a type shows the metavariable that ranges over it.
    let isType ← forallTelescope (← getConstInfo d).type fun _ b => return b.isSort
    let mv := if isType then (cats.find? (·.1 == d)).map (·.2) else none
    for (e, n) in es.toList.zip (List.range es.size) do
      let eqn ← nameEqnBinders (restoreEqnNames (← getConstInfo e).type) d
      let row ← equationRow eqn
      let row := row.replace " &= " " \\;\\deq\\; "
      let row := match mv, n with
        | some m, 0 => s!"{m} \\in {row}"
        | _, _ => row
      -- The description goes with the first equation.
      let desc := if n == 0 then s!"\\leanslot\{{d}}\{{doc}}" else ""
      rows := rows.push s!"\\LeanClause\{{row}}\{{desc}}"
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
        -- and `self` is written as the category's letter.
        fieldNames.mapM fun f => do
          let proj := ty ++ f
          let pci ← getConstInfo proj
          let fty ← forallBoundedTelescope pci.type (some (i.numParams + 1)) fun xs body => do
            let self := xs.back!
            let lctx := (← getLCtx).setUserName self.fvarId! (if hasCat then Name.mkSimple letter else `self)
            Meta.withLCtx lctx (← getLocalInstances) do
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
