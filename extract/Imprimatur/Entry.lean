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
import Imprimatur.Trust
import Imprimatur.Packs
import Imprimatur.Views.Math
import Imprimatur.Views.Rules
import Imprimatur.Views.Grammar
import Imprimatur.CustomViews

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
        | _ => none }

/-- The rendering context for the notation in scope: the project's rules and
the selected packs. `used` collects the rules that fire. -/
def renderCtx (s : Settings) (variant : Option String) (used : IO.Ref (Array String))
    (key : String := "") : MetaM Render.Ctx := do
  let env ← getEnv
  let style (k v : String) := (projectStyles env).find? (·.1 == k) == some (k, v)
  let rawVars := style "names" "raw"
  let callVars := style "applied_variables" "call"
  let subscriptVars := style "applied_variables" "subscript"
  return { rules := projectRules env ++ Packs.select s.notationPacks,
           metavars := projectMetavars env, variant, strip := s.stripNamespaces, used, rawVars,
           callVars, subscriptVars, document := s.document, key }

/-- The entry for a `latex_group`: a key that names a group of rules, not a
declaration. Only the `rules` view applies. -/
def groupEntry (s : Settings) (r : Request) (g : Option RuleGroup) (used : IO.Ref (Array String))
    (extra : Array (String × String) := #[]) : MetaM J := do
  let mut views : Array (String × J) := #[]
  let mut errors : Array (String × J) := #[]
  for v in r.views do
    let spec := parseViewSpec v
    let spec := { spec with opts := spec.opts ++ extra }
    let ctx ← renderCtx s spec.variant used r.key
    if let some (_, fn) := (projectViews (← getEnv)).find? (·.1 == spec.base) then
      match ← guarded ((runCustomView fn r.key none spec.opts).run ctx) with
      | .ok t => views := views.push (v, .str t)
      | .error msg => errors := errors.push (v, .str msg)
    else if let (some g, "rules") := (g, spec.base) then
      let ctors := Views.selectCtors g.ctors (spec.opt "include") (spec.opt "exclude")
      match ← guarded ((Views.rulesView ctors).run ctx) with
      | .ok t => views := views.push (v, .str t)
      | .error msg => errors := errors.push (v, .str msg)
    else errors := errors.push (v, .str s!"{r.key} names no declaration, so only a group's rules view or a custom view applies, not {v}")
  let allTeX := String.join (views.toList.map fun (_, j) => match j with | .str t => t | _ => "")
  let mut fields : Array (String × J) := #[
    ("kind", .str "group"), ("decl", .str r.key), ("axioms", .arr #[]), ("sorry", .bool false),
    ("macros", .arr ((macrosOf allTeX).map .str)), ("views", .obj views)]
  unless errors.isEmpty do fields := fields.push ("errors", .obj errors)
  return .obj fields

/-- The entry for a constant, as JSON. -/
def entryFor (root : System.FilePath) (s : Settings) (r : Request) (c : ConstantInfo)
    (used : IO.Ref (Array String)) (extra : Array (String × String) := #[]) : MetaM J := do
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
  let mut views : Array (String × J) := #[]
  let mut errors : Array (String × J) := #[]
  let wanted := (knownViews.toArray ++ r.views).foldl (fun a v => if a.contains v then a else a.push v) #[]
  for v in wanted do
    match v with
    | "lean" =>
      match ← guarded (Views.leanView c s.stripNamespaces s.width) with
      | .ok v => views := views.push ("lean", .str v); stage "lean view"
      | .error msg => errors := errors.push ("lean", .str msg)
    | "meta" => views := views.push ("meta", .str (metaView axioms usesSorry doc))
    | other =>
      -- `math`, `prose` and `rules`, with a notation variant (`math:named`,
      -- DESIGN §7.5) and options (`rules|include=App,Lam`, DESIGN §9.1).
      let spec := parseViewSpec other
      let spec := { spec with opts := spec.opts ++ extra }
      let base := spec.base
      let variant := spec.variant
      if let some (_, fn) := (projectViews (← getEnv)).find? (·.1 == base) then
        let ctx ← renderCtx s variant used r.key
        match ← guarded ((runCustomView fn r.key (some c) spec.opts).run ctx) with
        | .ok v => views := views.push (other, .str v)
        | .error msg => errors := errors.push (other, .str msg)
      else if base == "rules" then
        let ctors := match c with
          | .inductInfo i => i.ctors.toArray
          | .ctorInfo _ => #[c.name]
          | _ => #[]
        if ctors.isEmpty then
          errors := errors.push (other, .str s!"the rules view needs an inductive predicate or a constructor")
        else
          let ctx ← renderCtx s variant used r.key
          let ctors := Views.selectCtors ctors (spec.opt "include") (spec.opt "exclude")
          match ← guarded ((Views.rulesView ctors).run ctx) with
          | .ok v => views := views.push (other, .str v)
          | .error msg => errors := errors.push (other, .str msg)
      else if base == "grammar" then
        let ctx ← renderCtx s variant used r.key
        match ← guarded ((Views.grammarView c).run ctx) with
        | .ok v => views := views.push (other, .str v)
        | .error msg => errors := errors.push (other, .str msg)
      else if base == "math" || base == "prose" then
        let ctx ← renderCtx s variant used r.key
        let act : MetaM String :=
          if base == "math" then (Views.mathViewWith c s.width spec.opts).run ctx
          else (Views.proseView c s.width).run ctx
        match ← guarded act with
        | .ok v => views := views.push (other, .str v)
        | .error msg => errors := errors.push (other, .str msg)
      else
        errors := errors.push (other, .str s!"the {other} view is not implemented yet")
  let allTeX := String.join (views.toList.map fun (_, j) => match j with | .str t => t | _ => "")
  stage "views"
  -- The dependency cone and the hashes (DESIGN §7.7).
  let coneR ← guarded (Trust.cone s.trustedPrefixes c)
  stage "cone"
  if let .error msg := coneR then errors := errors.push ("cone", .str msg)
  let cone : Trust.Cone := match coneR with
    | .ok k => k
    | .error _ => { members := #[], issues := #[] }
  let stmtHash := Trust.sha (Trust.stmtText c cone)
  let leanText := match views.find? (·.1 == "lean") with
    | some (_, .str t) => t
    | _ => ""
  let sigHash := Trust.sha leanText
  let untrusted := cone.issues.map (·.1.toString) |>.foldl (fun a n => if a.contains n then a else a.push n) #[]
  let mut fields : Array (String × J) := #[
    ("kind", .str (kindOf env c)),
    ("decl", .str c.name.toString),
    ("axioms", .arr (axioms.map (.str ·.toString))),
    ("sorry", .bool usesSorry),
    ("macros", .arr ((macrosOf allTeX).map .str)),
    ("views", .obj views),
    ("sigHash", .str sigHash),
    ("cone", .obj #[
      ("size", .num cone.members.size),
      ("untrusted", .arr (untrusted.map .str)),
      ("reasons", .obj (untrusted.map fun n =>
        (n, .arr ((cone.issues.filter (·.1.toString == n)).map (.str ·.2.name)))))])]
  -- Without a complete cone there is no statement hash: `\leancheck` then
  -- reports `no-hash` rather than comparing against a partial one.
  if coneR matches .ok _ then fields := fields.push ("stmtHash", .str stmtHash)
  if let some d := doc then fields := fields.push ("doc", .str d)
  if let some (path, line) := src then
    fields := fields.push ("source", .obj #[("path", .str path), ("line", .num line)])
  unless errors.isEmpty do fields := fields.push ("errors", .obj errors)
  return .obj fields

end Imprimatur
