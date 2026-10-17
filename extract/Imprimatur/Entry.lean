/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Json
import Imprimatur.TeX
import Imprimatur.Compat
import Imprimatur.Requests
import Imprimatur.Views.Lean

/-!
# Bundle entries

For each requested key, an entry (DESIGN §8): the declaration's kind, source
location, docstring, axioms, `sorry` status, the macros its views use, and
its views. A view that fails to render is recorded under `errors`.

The `meta` view (DESIGN §7.3) holds the source location, axioms, `sorry`
status and docstring:

```latex
\LeanMeta{\leanmetasource{}}{propext, Quot.sound}{\LeanSorryFree}{The docstring.}
```

The splicer fills `\leanmetasource{}` according to the active profile
(DESIGN §11), because profiles are chosen when splicing, not when extracting.
-/

namespace Imprimatur

open Lean Meta

/-- The kind of a constant, as recorded in the bundle. -/
def kindOf (env : Environment) (c : ConstantInfo) : String :=
  match c with
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .defnInfo _ => if isInstanceCore env c.name then "instance" else "definition"
  | .inductInfo _ => if isStructure env c.name then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- The source file of a constant, relative to `root`, and its line. A file
outside `root` is named by its module (`A/B.lean`), so the bundle never holds
an absolute path (DESIGN §8). -/
def sourceOf (root : System.FilePath) (n : Name) : MetaM (Option (String × Nat)) := do
  let some ranges ← findDeclarationRanges? n | return none
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n | return none
  let some mod := Compat.moduleName? env idx | return none
  let byModule := "/".intercalate (mod.components.map (·.toString)) ++ ".lean"
  let sp ← getSrcSearchPath
  let path ← match ← sp.findModuleWithExt "lean" mod with
    | some p =>
      let abs ← IO.FS.realPath p
      let rootAbs ← IO.FS.realPath root
      let pre := rootAbs.toString ++ "/"
      if abs.toString.startsWith pre then pure (abs.toString.drop pre.length).toString
      else pure byModule
    | none => pure byModule
  return some (path, ranges.selectionRange.pos.line)

/-- The axioms a constant depends on, sorted. -/
def axiomsOf (n : Name) : MetaM (Array Name) := do
  let ax ← collectAxioms n
  return ax.qsort (·.toString < ·.toString)

/-- The macros a piece of TeX uses, sorted and without repeats. -/
def macrosOf (tex : String) : Array String := Id.run do
  let cs := tex.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '\\' && i + 1 < cs.size && cs[i + 1]!.isAlpha then
      let mut j := i + 1
      while j < cs.size && cs[j]!.isAlpha do j := j + 1
      let m := "\\" ++ String.ofList (cs.extract (i + 1) j).toList
      unless out.contains m do out := out.push m
      i := j
    else
      i := i + 1
  return out.qsort (· < ·)

/-- The `meta` view. -/
def metaView (axioms : Array Name) (usesSorry : Bool) (doc : Option String) : String :=
  let ax := ", ".intercalate (axioms.map (TeX.escape ·.toString)).toList
  let status := if usesSorry then "\\LeanUsesSorry" else "\\LeanSorryFree"
  let docTeX := TeX.markdown (doc.getD "")
  s!"\\LeanMeta\{\\leanmetasource\{}}\{{ax}}\{{status}}\{{docTeX}}"

/-- Views this extractor renders. -/
def knownViews : List String := ["lean", "meta"]

/-- The entry for a constant, as JSON. -/
def entryFor (root : System.FilePath) (s : Settings) (r : Request) (c : ConstantInfo) :
    MetaM J := do
  let env ← getEnv
  let doc := (← findDocString? env c.name).map (·.trimAscii.toString)
  let axioms ← axiomsOf c.name
  let usesSorry := axioms.contains ``sorryAx
  let src ← sourceOf root c.name
  let mut views : Array (String × J) := #[]
  let mut errors : Array (String × J) := #[]
  let wanted := (knownViews.toArray ++ r.views).foldl (fun a v => if a.contains v then a else a.push v) #[]
  for v in wanted do
    match v with
    | "lean" =>
      try
        views := views.push ("lean", .str (← Views.leanView c s.stripNamespaces s.width))
      catch e =>
        errors := errors.push ("lean", .str s!"{← e.toMessageData.toString}")
    | "meta" => views := views.push ("meta", .str (metaView axioms usesSorry doc))
    | other => errors := errors.push (other, .str s!"the {other} view is not implemented yet")
  let allTeX := String.join (views.toList.map fun (_, j) => match j with | .str t => t | _ => "")
  let mut fields : Array (String × J) := #[
    ("kind", .str (kindOf env c)),
    ("decl", .str c.name.toString),
    ("axioms", .arr (axioms.map (.str ·.toString))),
    ("sorry", .bool usesSorry),
    ("macros", .arr ((macrosOf allTeX).map .str)),
    ("views", .obj views)]
  if let some d := doc then fields := fields.push ("doc", .str d)
  if let some (path, line) := src then
    fields := fields.push ("source", .obj #[("path", .str path), ("line", .num line)])
  unless errors.isEmpty do fields := fields.push ("errors", .obj errors)
  return .obj fields

end Imprimatur
