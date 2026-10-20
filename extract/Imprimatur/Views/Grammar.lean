/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render

/-!
# The `grammar` view

An inductive type as a BNF production; a structure as a list of fields
(DESIGN §7.3).

```latex
\begin{LeanGrammar}
\LeanProduction{e}{Terms.}{x_{i}}{\leanslot{Stlc.Tm.var}{A variable.}}
\LeanAlternative{\lambda{:}t.\, e}{\leanslot{Stlc.Tm.lam}{An abstraction.}}
\end{LeanGrammar}
```

**Alternatives.** Each constructor is an alternative: the constructor applied
to variables named after its binders, rendered with the notation in scope.

**The category.** Its metavariable is given by `latex_category T => "e"`;
without one, the type's name is used.

**Descriptions.** Each alternative's description is an author-owned slot
(DESIGN §9.5), identified by the constructor's full name. Its default text
is the constructor's docstring, which the authors may then rewrite.

**Structures.** A structure's fields are listed with `\LeanField{name}{type}{slot}`.
-/

namespace Imprimatur.Views

open Lean Meta Render

/-- A slot for an author-owned description. -/
def slot (id : Name) (doc : Option String) : String :=
  s!"\\leanslot\{{id}}\{{TeX.markdown ((doc.getD "").trimAscii.toString)}}"

/-- One constructor as an alternative. -/
def alternative (c : ConstantInfo) : RenderM String := do
  forallTelescope c.type fun xs _ => do
    -- Only the constructor's own arguments: parameters are not shown.
    let .ctorInfo i := c | return ""
    let args := xs.extract i.numParams xs.size
    let params := xs.extract 0 i.numParams
    let e := mkAppN (mkAppN (.const c.name (c.levelParams.map .param)) params) args
    return (← render e).render 100000

/-- The `grammar` view of an inductive type or structure. -/
def grammarView (c : ConstantInfo) : RenderM String := do
  let env ← getEnv
  let .inductInfo i := c | throwError "the grammar view needs an inductive type"
  noteShown c.name
  let isPred ← forallTelescopeReducing c.type fun _ body => return body.isProp
  if isPred then
    throwError "{c.name} is an inductive predicate; the rules view shows predicates, \
      the grammar view shows inductive types"
  let doc := (← findDocString? env c.name).map (·.trimAscii.toString)
  let strip := (← read).strip
  let cat := match (projectCategories env).find? (·.1 == c.name) with
    | some (_, m) => m
    | none => constTeX strip c.name
  let mut out : Array String := #["\\begin{LeanGrammar}"]
  if isStructure env c.name then
    out := out.push s!"\\LeanStructure\{{cat}}\{{TeX.markdown (doc.getD "")}}"
    for f in getStructureFields env c.name do
      let proj := c.name ++ f
      let some pci := env.find? proj | continue
      let ty ← forallTelescope pci.type fun _ body => do return (← render body).render 100000
      let fdoc ← findDocString? env proj
      out := out.push s!"\\LeanField\{{TeX.escape f.toString}}\{{ty}}\{{slot proj fdoc}}"
  else
    let mut first := true
    for ctor in i.ctors do
      let some cci := env.find? ctor | continue
      let alt ← alternative cci
      let cdoc ← findDocString? env ctor
      if first then
        out := out.push s!"\\LeanProduction\{{cat}}\{{TeX.markdown (doc.getD "")}}\{{alt}}\{{slot ctor cdoc}}"
        first := false
      else
        out := out.push s!"\\LeanAlternative\{{alt}}\{{slot ctor cdoc}}"
  return "\n".intercalate (out.push "\\end{LeanGrammar}").toList

end Imprimatur.Views
