/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Bundle
import Imprimatur.TeX
import Imprimatur.Compat
import Imprimatur.Requests
import Imprimatur.Views.Lean
import Imprimatur.Trust
import Imprimatur.Packs
import Imprimatur.Views.Math
import Imprimatur.Views.Rules
import Imprimatur.Views.Grammar
import Imprimatur.CustomViews
import Imprimatur.Views.Index
import Imprimatur.Views.Display

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
def kindOf (env : Environment) (c : ConstantInfo) : Kind :=
  match c with
  | .thmInfo _ => .theorem
  | .axiomInfo _ => .axiom
  | .opaqueInfo _ => .opaque
  | .defnInfo _ => if isInstanceCore env c.name then .instance else .definition
  | .inductInfo _ => if isStructure env c.name then .structure else .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor
  | .quotInfo _ => .quotient

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

/-- Run one stage of an entry with a fresh heartbeat budget. A failure,
including running out of heartbeats (a runtime exception, which `try` alone
doesn't catch), becomes an error message rather than ending the export. -/
def guarded {α : Type} (x : MetaM α) : MetaM (Except String α) := do
  let ctx ← read
  let st ← get
  let r : Except String (α × Meta.State) ← (Core.tryCatchRuntimeEx
    (do return .ok (← withCurrHeartbeats (x.run ctx st)))
    (fun e => do return .error (← e.toMessageData.toString)) : CoreM _)
  match r with
  | .ok (a, st') => set st'; return .ok a
  | .error msg => return .error msg

/-- Views this extractor renders. -/
def knownViews : List String := ["lean", "meta"]

/-- A requested view: its name, notation variant and options. -/
structure ViewSpec where
  /-- The view (`rules`, `math`, …). -/
  base : String
  /-- The notation variant. -/
  variant : Option String := none
  /-- Options, such as `include=App,Lam`. -/
  opts : Array (String × String) := #[]

/-- The comma-separated values of an option. -/
def ViewSpec.opt (v : ViewSpec) (k : String) : Array String :=
  match v.opts.find? (·.1 == k) with
  | some (_, x) => (x.splitOn ",").toArray.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  | none => #[]

/-- Parse `view[:variant][|key=value]*`. -/
def parseViewSpec (s : String) : ViewSpec :=
  match s.splitOn "|" with
  | [] => { base := s }
  | head :: opts =>
    let (base, variant) := match head.splitOn ":" with
      | [b, v] => (b, some v)
      | _ => (head, none)
    { base, variant, opts := opts.toArray.filterMap fun o => match o.splitOn "=" with
        | [k, v] => some (k, v)
        -- A flag: `grammar|display`.
        | [k] => if k.isEmpty then none else some (k, "")
        | _ => none }

/-- The rendering context for the notation in scope: the project's rules and
the selected packs. `used` collects the rules that fire. -/
def renderCtx (s : Settings) (variant : Option String) (used : IO.Ref (Array String))
    (key : String := "") (root : System.FilePath := ".") : MetaM Render.Ctx := do
  let env ← getEnv
  let style (k v : String) := (projectStyles env).find? (·.1 == k) == some (k, v)
  let rawVars := style "names" "raw"
  let callVars := style "applied_variables" "call"
  let subscriptVars := style "applied_variables" "subscript"
  let casesMatch := style "pattern_matching" "cases"
  let listLiterals := style "lists" "literal"
  return { rules := projectRules env ++ Packs.select s.notationPacks,
           metavars := projectMetavars env, variant, strip := s.stripNamespaces, used, rawVars,
           callVars, subscriptVars, casesMatch, listLiterals, document := s.document, key,
           root, imports := s.imports }

/-- Run a view that renders mathematics. The formulas it renders are read
back unless the configuration says not to (DESIGN §18.4); the problems
found come back with the view's text. -/
def runRendered (s : Settings) (variant : Option String) (used : IO.Ref (Array String))
    (key : String) (act : Render.Ctx → MetaM String) (root : System.FilePath := ".") :
    MetaM (Except String String × Array String) := do
  let ctx ← renderCtx s variant used key root
  let problems ← IO.mkRef #[]
  let ctx := if s.validate then
      { ctx with problems := some problems,
                 grammar := some (Validate.notationGrammar ctx.rules variant ctx.callVars
                   ctx.subscriptVars ctx.casesMatch ctx.listLiterals) }
    else ctx
  let r ← guarded (act ctx)
  return (r, ← problems.get)

/-- The entry for a title: a `latex_group` of rules or a `latex_display`,
which names several declarations. It states what they state: its hash and
cone are theirs, united. -/
def groupEntry (s : Settings) (r : Request) (g : Option RuleGroup) (used : IO.Ref (Array String))
    (extra : Array (String × String) := #[]) (root : System.FilePath := ".")
    (disp : Option (Array Name) := none) : MetaM (Entry (Image TeX) Verdict) := do
  let mut views : Array (String × String) := #[]
  let mut errors : Array (String × String) := #[]
  let mut validation : Array (String × Array String) := #[]
  for v in r.views do
    let spec := parseViewSpec v
    let spec := { spec with opts := spec.opts ++ extra }
    let run := fun act => runRendered s spec.variant used r.key act root
    if Views.indexViews.contains spec.base then
      -- A view that indexes the document (`Views/Index.lean`).
      let (res, ps) ← run (Views.runIndexView spec.base (sourceOf root) axiomsOf spec.opts).run
      validation := validation.push (v, ps)
      match res with
      | .ok t => views := views.push (v, t)
      | .error msg => errors := errors.push (v, msg)
    else if let some (_, fn) := (projectViews (← getEnv)).find? (·.1 == spec.base) then
      let (res, ps) ← run (runCustomView fn r.key none spec.opts).run
      validation := validation.push (v, ps)
      match res with
      | .ok t => views := views.push (v, t)
      | .error msg => errors := errors.push (v, msg)
    else if let (some ds, "clauses") := (disp, spec.base) then
      -- A display of definitions (`latex_display`).
      let (res, ps) ← run (Views.clausesView ds).run
      validation := validation.push (v, ps)
      match res with
      | .ok t => views := views.push (v, t)
      | .error msg => errors := errors.push (v, msg)
    else if let (some ds, "grammar") := (disp, spec.base) then
      -- A display of grammars (`latex_display`, `grammar|display`).
      let (res, ps) ← run (Views.displayGrammarView ds).run
      validation := validation.push (v, ps)
      match res with
      | .ok t => views := views.push (v, t)
      | .error msg => errors := errors.push (v, msg)
    else if let (some g, "rules") := (g, spec.base) then
      let ctors := Views.selectCtors g.ctors (spec.opt "include") (spec.opt "exclude")
      let (res, ps) ← run (Views.rulesView ctors).run
      validation := validation.push (v, ps)
      match res with
      | .ok t => views := views.push (v, t)
      | .error msg => errors := errors.push (v, msg)
    else errors := errors.push (v, s!"{r.key} names no declaration, so only a group's rules view, a display's clauses or grammar view, or a custom view applies, not {v}")
  let allTeX := String.join (views.toList.map (·.2))
  -- The group's statement is its members': their types, with their cones
  -- united, hashed together. Its verdict is their cone and whether any
  -- depends on `sorry`; it has no axioms of its own, since its members are
  -- constructors or definitions, whose axioms are the compiler's and differ
  -- between toolchains.
  let env ← getEnv
  let members : Array Name := ((g.map (·.ctors)).getD (disp.getD #[]))
  let cis := members.filterMap env.find?
  let mut cone : Trust.Cone := { members := #[], issues := #[] }
  let mut coneOk := true
  let mut axioms : Array Name := #[]
  for ci in cis do
    match ← guarded (Trust.cone s.trustedPrefixes ci) with
    | .ok k => cone := cone.union k
    | .error msg =>
      coneOk := false
      if errors.all (·.1 != "cone") then errors := errors.push ("cone", msg)
    if let .ok ax ← guarded (axiomsOf ci.name) then
      axioms := axioms ++ ax.filter (!axioms.contains ·)
  let untrusted := cone.issues.map (·.1.toString) |>.foldl (fun a n => if a.contains n then a else a.push n) #[]
  return {
    decl := { kind := .group, name := r.key },
    statement := {
      stmtHash := if coneOk && !cis.isEmpty then some (Trust.sha (Trust.groupStmtText cis cone)) else none,
      views, errors, validation, macros := macrosOf allTeX },
    verdict := {
      axioms := #[], usesSorry := axioms.contains ``sorryAx,
      cone := if cis.isEmpty then none else some {
        size := cone.members.size, untrusted,
        reasons := untrusted.map fun n =>
          (n, (cone.issues.filter (·.1.toString == n)).map (·.2.name)) } } }

/-- The entry for a constant. -/
def entryFor (root : System.FilePath) (s : Settings) (r : Request) (c : ConstantInfo)
    (used : IO.Ref (Array String)) (extra : Array (String × String) := #[]) :
    MetaM (Entry (Image TeX) Verdict) := do
  let env ← getEnv
  -- IMPRIMATUR_TRACE=1 reports each stage, for finding what is slow.
  let trace ← (IO.getEnv "IMPRIMATUR_TRACE" : IO _)
  let stage (what : String) : MetaM Unit := do
    if trace == some "1" then IO.eprintln s!"imprimatur-export: {c.name}: {what} ({← IO.monoMsNow})"
  stage "start"
  let doc := (← findDocString? env c.name).map (·.trimAscii.toString)
  let axioms ← match ← guarded (axiomsOf c.name) with
    | .ok ax => pure ax
    | .error msg => throwError "collecting the axioms failed: {msg}"
  stage "axioms"
  let usesSorry := axioms.contains ``sorryAx
  let src ← sourceOf root c.name
  let mut views : Array (String × String) := #[]
  let mut errors : Array (String × String) := #[]
  let mut validation : Array (String × Array String) := #[]
  let wanted := (knownViews.toArray ++ r.views).foldl (fun a v => if a.contains v then a else a.push v) #[]
  for v in wanted do
    match v with
    | "lean" =>
      match ← guarded (Views.leanView c s.stripNamespaces s.width) with
      | .ok v => views := views.push ("lean", v); stage "lean view"
      | .error msg => errors := errors.push ("lean", msg)
    | "meta" => views := views.push ("meta", (metaView axioms usesSorry doc))
    | other =>
      -- `math`, `prose` and `rules`, with a notation variant (`math:named`,
      -- DESIGN §7.5) and options (`rules|include=App,Lam`, DESIGN §9.1).
      let spec := parseViewSpec other
      let spec := { spec with opts := spec.opts ++ extra }
      let base := spec.base
      let variant := spec.variant
      let run := runRendered s variant used r.key
      if let some (_, fn) := (projectViews (← getEnv)).find? (·.1 == base) then
        let (res, ps) ← run (runCustomView fn r.key (some c) spec.opts).run
        validation := validation.push (other, ps)
        match res with
        | .ok v => views := views.push (other, v)
        | .error msg => errors := errors.push (other, msg)
      else if base == "rules" then
        let ctors := match c with
          | .inductInfo i => i.ctors.toArray
          | .ctorInfo _ => #[c.name]
          | _ => #[]
        if ctors.isEmpty then
          errors := errors.push (other, s!"the rules view needs an inductive predicate or a constructor")
        else
          let ctors := Views.selectCtors ctors (spec.opt "include") (spec.opt "exclude")
          let (res, ps) ← run (Views.rulesView ctors).run
          validation := validation.push (other, ps)
          match res with
          | .ok v => views := views.push (other, v)
          | .error msg => errors := errors.push (other, msg)
      else if base == "clauses" || (base == "grammar" && spec.opts.any (·.1 == "display")) then
        -- One definition, or one type, in display form.
        let act := if base == "clauses" then Views.clausesView #[c.name] else Views.displayGrammarView #[c.name]
        let (res, ps) ← run act.run
        validation := validation.push (other, ps)
        match res with
        | .ok v => views := views.push (other, v)
        | .error msg => errors := errors.push (other, msg)
      else if base == "grammar" then
        let (res, ps) ← run (Views.grammarView c).run
        validation := validation.push (other, ps)
        match res with
        | .ok v => views := views.push (other, v)
        | .error msg => errors := errors.push (other, msg)
      else if base == "math" || base == "prose" then
        let act : Render.Ctx → MetaM String :=
          if base == "math" then (Views.mathViewWith c s.width spec.opts).run
          else (Views.proseView c s.width).run
        let (res, ps) ← run act
        validation := validation.push (other, ps)
        match res with
        | .ok v => views := views.push (other, v)
        | .error msg => errors := errors.push (other, msg)
      else
        errors := errors.push (other, s!"the {other} view is not implemented yet")
  let allTeX := String.join (views.toList.map (·.2))
  stage "views"
  -- The dependency cone and the hashes (DESIGN §7.7).
  let coneR ← guarded (Trust.cone s.trustedPrefixes c)
  stage "cone"
  if let .error msg := coneR then errors := errors.push ("cone", msg)
  let cone : Trust.Cone := match coneR with
    | .ok k => k
    | .error _ => { members := #[], issues := #[] }
  let leanText := ((views.find? (·.1 == "lean")).map (·.2)).getD ""
  let untrusted := cone.issues.map (·.1.toString) |>.foldl (fun a n => if a.contains n then a else a.push n) #[]
  return {
    decl := { kind := kindOf env c, name := c.name.toString, doc,
              source := src.map fun (path, line) => { path, line } },
    statement := {
      -- Without a complete cone there is no statement hash: `\leancheck` then
      -- reports `no-hash` rather than comparing against a partial one.
      stmtHash := if coneR matches .ok _ then some (Trust.sha (Trust.stmtText c cone)) else none,
      sigHash := some (Trust.sha leanText),
      views, errors, validation, macros := macrosOf allTeX },
    verdict := {
      axioms := axioms.map (·.toString), usesSorry,
      cone := some {
        size := cone.members.size, untrusted,
        reasons := untrusted.map fun n =>
          (n, (cone.issues.filter (·.1.toString == n)).map (·.2.name)) } } }

end Imprimatur
