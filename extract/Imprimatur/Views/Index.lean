/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render
import Imprimatur.TeX
import Imprimatur.Compat

/-!
# Views that index the document

Three views read what the other blocks of the document rendered (the
`IndexEvent`s of `Imprimatur.Render`) and tabulate it. The exporter renders
them after every other block, so what they list is the whole document.

* `conventions`: each grammar category's metavariable (`latex_category`), the
  type it ranges over, a description, and where the type is first shown. The
  validator checks that a variable printed as a category's metavariable has
  that category's type, so the table states a property `check` verifies.
* `vocabulary`: the notation of the library (Lean core, Batteries, Mathlib)
  that the document uses, as the rule writes it, with a gloss. A gloss is a
  slot whose default is the first sentence of the constant's docstring.
* `provenance`: each result the document states, with its Lean declaration,
  source location and axioms.

The views' keys are the authors' (`\begin{leanconventions}{Conventions}{…}`);
they name no declaration.
-/

namespace Imprimatur.Views

open Lean Meta Imprimatur.Render

/-- The views that index the document. -/
def indexViews : Array String := #["conventions", "vocabulary", "provenance"]

/-- The first sentence of a docstring, as TeX, without its final stop. -/
def docSentence (n : Name) : MetaM String := do
  let d := ((← findDocString? (← getEnv) n).getD "").trimAscii.toString
  let d := ((d.replace "\n" " ").splitOn ". ")[0]!
  let d := if d.endsWith "." then (d.dropEnd 1).toString else d
  return TeX.markdown d

/-- A type as TeX: applied to the arguments its category names
(`latex_category Judg Name => "J"`), or else to its parameters and indices.
A binder Lean named itself (`Vec : Nat → Type`) is named after its type's
metavariable. -/
def typeTeX (ty : Name) : RenderM String := do
  let env ← getEnv
  let ci ← getConstInfo ty
  let cats := projectCategories env
  let c := Expr.const ty (ci.levelParams.map Level.param)
  if let some (_, args) := (projectCategoryArgs env).find? (·.1 == ty) then
    return (← render (mkAppN c (args.map (Expr.const · [])))).render 100000
  forallTelescope ci.type fun xs _ => do
    let mut lctx ← getLCtx
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.hasMacroScopes then
        let some (_, tex) := cats.find? (·.1 == d.type.getAppFn.constName) | continue
        let n := ((greek.find? (·.2 == tex)).map (·.1)).getD tex
        lctx := lctx.setUserName x.fvarId! (Name.mkSimple n)
    withLCtx lctx (← getLocalInstances) do
      return (← render (mkAppN c xs)).render 100000

/-- The live blocks of the document with this key, first first. -/
def blocksOf (key : String) : RenderM (Array DocBlock) := do
  let bs := (← read).document.blocks.filter fun b => b.key == key && b.live
  return bs.qsort (·.order < ·.order)

/-- Whether a key is one of an index's own blocks. -/
def isIndexKey (key : String) : RenderM Bool := do
  return (← read).document.blocks.any fun b =>
    b.key == key && indexViews.contains ((b.view.splitOn "|")[0]!.splitOn ":")[0]!

/-- Where a block is: its key, as written, and its page if it has a label. -/
def whereTeX (key : String) : RenderM String := do
  let bs ← blocksOf key
  let name := match (key.splitOn ".").getLast? with
    | some last => if key.contains ' ' then key else last
    | none => key
  let name := s!"\\textit\{{TeX.escape name}}"
  match bs.find? (·.label.isSome) with
  | some b => return s!"{name}, p.~\\pageref\{{b.label.get!}}"
  | none => return name

/-- The first block, in document order, among these keys; none if none is in
the document. -/
def firstOf (keys : Array String) : RenderM (Option (Nat × String)) := do
  let mut best : Option (Nat × String) := none
  for k in keys do
    if ← isIndexKey k then continue
    if let some b := (← blocksOf k)[0]? then
      if best.all (b.order < ·.1) then best := some (b.order, k)
  return best

/-- The table of conventions: each category's metavariable and the type it
ranges over, in the order the document first shows them. Categories that
share a metavariable are listed together. -/
def conventionsView : RenderM String := do
  let ev ← indexEvents.get
  let mut rows : Array (Nat × String × Name × String × Nat) := #[]
  for ((ty, tex), i) in (projectCategories (← getEnv)).zipIdx do
    let shown := ev.filterMap fun | .shows k n => if n == ty then some k else none | _ => none
    let seen := ev.filterMap fun | .category k t => if t == ty then some k else none | _ => none
    -- Where the type is shown, as a grammar or a definition; else where its
    -- metavariable first appears.
    let some (order, key) ← (do
        if let some f ← firstOf shown then return some f
        firstOf seen) | continue
    rows := rows.push (order, tex, ty, ← whereTeX key, i)
  -- A metavariable's rows together, where it first appears; rows shown in
  -- the same block in the order the notation module declares them.
  let lt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
  let groupKey (tex : String) : Nat × Nat :=
    (rows.filter (·.2.1 == tex)).foldl (fun a r => if lt (r.1, r.2.2.2.2) a then (r.1, r.2.2.2.2) else a)
      (rows.size.succ * 1000, 0)
  let sorted := rows.qsort fun a b =>
    let ga := groupKey a.2.1; let gb := groupKey b.2.1
    lt ga gb || (ga == gb && lt (a.1, a.2.2.2.2) (b.1, b.2.2.2.2))
  let mut out := "\\begin{longtable}{@{}l@{\\quad}l@{\\quad}p{.4\\linewidth}@{\\quad}l@{}}\n"
  out := out ++ "\\textit{Variable} & \\textit{Type} & & \\textit{Shown in}\\\\\n\\hline\\endhead\n"
  for (_, tex, ty, wh, _) in sorted do
    out := out ++ s!"${tex}$ & ${← typeTeX ty}$ & \\leanslot\{{ty}}\{{← docSentence ty}} & {wh}\\\\\n"
  -- Each metavariable convention the document uses (DESIGN §7.6): its
  -- metavariable stands for a variable of the predicate whose premise it
  -- hides, which is shown where the predicate is displayed, else where the
  -- convention is first used.
  let mut convs : Array (Nat × String × Name × String) := #[]
  for e in ev do
    let .convention _ pred tex := e | continue
    if convs.any (fun (_, t, p, _) => t == tex && p == pred) then continue
    let shown := ev.filterMap fun | .shows k n => if n == pred then some k else none | _ => none
    let used := ev.filterMap fun | .convention k p t => if p == pred && t == tex then some k else none | _ => none
    let some (order, key) ← (do
        if let some f ← firstOf shown then return some f
        firstOf used) | continue
    convs := convs.push (order, tex, pred, ← whereTeX key)
  for (_, tex, pred, wh) in convs.qsort (·.1 < ·.1) do
    let ci ← getConstInfo pred
    let range := (← render (.const pred (ci.levelParams.map Level.param))).render 100000
    out := out ++ s!"${tex}$ & ${range}$ & \\leanslot\{{pred}}\{{← docSentence pred}} & {wh}\\\\\n"
  out := out ++ "\\end{longtable}\n"
  -- The convention for decorations, shown on the first metavariable.
  if let some (_, m, _, _, _) := sorted[0]? then
    out := out ++ s!"A variable with a prime or a subscript (${m}'$, ${m}_\{1}$) ranges over the same type.\n"
  return out

/-- The text of a rule as the reader sees it: the template, with its
variables written as the document writes variables. -/
def ruleTeX (r : NotationRule) : RenderM String := do
  let ms := (← read).metavars
  -- Longest names first, so `#x₁` is not read as `#x` and `₁`.
  let vs := r.pat.vars.qsort (·.toString.length > ·.toString.length)
  return vs.foldl (fun t v => t.replace s!"#{v}" (varTeX ms v)) r.template

/-- The constants a pattern mentions. -/
partial def _root_.Imprimatur.Pat.consts : Pat → Array Name
  | .app h args => #[h] ++ args.foldl (· ++ ·.consts) #[]
  | .constrained p cs => p.consts ++ cs.foldl (· ++ ·.2.consts) #[]
  | .lam _ b => b.consts
  | .pi _ d b => d.consts ++ b.consts
  | .arrow d c => d.consts ++ c.consts
  | _ => #[]

/-- The package a module belongs to, as the reader knows it. -/
def packageOf (mod : Name) : String :=
  match mod.getRoot.toString with
  | "Init" | "Std" | "Lean" => "Lean"
  | r => r

/-- The notation that the document uses, grouped by package, with a gloss for
each: the library's (`scope=library`, the default), the project's
(`scope=project`), or both (`scope=all`). Notation packs (logic and the like)
are left out unless the block asks for them (`packs=true`). -/
def vocabularyView (opts : Array (String × String)) : RenderM String := do
  let env ← getEnv
  let roots := (← read).imports.map (·.getRoot)
  let packs := opts.any (· == ("packs", "true"))
  let scope := ((opts.find? (·.1 == "scope")).map (·.2)).getD "library"
  let cats := projectCategories env
  let ev ← indexEvents.get
  let mut seen : Array (Name × String) := #[]
  let mut rows : Array (String × Name × NotationRule) := #[]
  for e in ev do
    let .rule k r := e | continue
    if (← isIndexKey k) || (← blocksOf k).isEmpty then continue
    if !packs && r.origin.startsWith "pack " then continue
    let head := r.pat.head
    -- The library's notation: rules whose patterns mention only constants of
    -- modules outside the project. The project's: the others.
    let modOf (n : Name) : Option Name := do
      let idx ← env.getModuleIdxFor? n
      Compat.moduleName? env idx
    let some mod := modOf head | continue
    -- The project's constant the pattern mentions first, and its package.
    let own := r.pat.consts.findSome? fun n => match modOf n with
      | some m => if roots.contains m.getRoot then some (m.getRoot, n) else none
      | none => none
    if (scope == "library" && own.isSome) || (scope == "project" && own.isNone) then continue
    -- A category's type is in the table of conventions.
    if own.isSome && r.pat.consts.size == 1 && cats.any (·.1 == head) then continue
    -- A project's rule headed by the library's constant (`Γ(x) = τ` is an
    -- equation) is listed under the project's constant it mentions.
    let head := match own, (modOf head).any (roots.contains ·.getRoot) with
      | some (_, n), false => n
      | _, _ => head
    if seen.contains (head, r.template) then continue
    seen := seen.push (head, r.template)
    -- The project's notation is grouped under the project, though its head
    -- be the library's (`Γ(x) = τ` is an equation).
    rows := rows.push ((own.map (·.1.toString)).getD (packageOf mod), head, r)
  let sorted := rows.qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && (a.2.1.toString < b.2.1.toString ||
      (a.2.1 == b.2.1 && a.2.2.template < b.2.2.template)))
  let mut out := "\\begin{longtable}{@{}l@{\\quad}l@{\\quad}p{.45\\linewidth}@{}}\n"
  let mut group : Option String := none
  let mut n := 0
  let mut prev : Name := .anonymous
  for (g, head, r) in sorted do
    if group != some g then
      group := some g
      out := out ++ s!"\\multicolumn\{3}\{@\{}l}\{\\textit\{{TeX.escape g}}}\\\\\n"
    n := if head == prev then n + 1 else 0
    prev := head
    -- The project's constants as the paper names them, without the
    -- namespaces it strips.
    let shown := Views.stripName (← read).strip head
    out := out ++ s!"${← ruleTeX r}$ & \\texttt\{{TeX.escape shown.toString}} & \\leanslot\{{head}/{n}}\{{← docSentence head}}\\\\\n"
  out := out ++ "\\end{longtable}\n"
  return out

/-- The axioms every result is allowed: those of classical mathematics in Lean. -/
def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Each result the document states, in document order: where it is, its Lean
declaration, the declaration's source, and the axioms it rests on beyond the
standard ones. Definitions are listed too with `kinds=all`. -/
def provenanceView (srcOf : Name → MetaM (Option (String × Nat)))
    (axOf : Name → MetaM (Array Name)) (opts : Array (String × String)) : RenderM String := do
  let env ← getEnv
  let all := opts.any (· == ("kinds", "all"))
  let blocks := (← read).document.blocks.filter (·.live) |>.qsort (·.order < ·.order)
  let mut done : Array String := #[]
  -- The source column wraps, breaking a long path after each `/`.
  let mut out := "\\begin{longtable}{@{}l@{\\quad}l@{\\quad}>{\\raggedright\\arraybackslash}p{.3\\linewidth}@{\\quad}l@{}}\n"
  out := out ++ "\\textit{Result} & \\textit{Lean} & \\textit{Source} & \\textit{Axioms}\\\\\n\\hline\\endhead\n"
  for b in blocks do
    if done.contains b.key || (← isIndexKey b.key) then continue
    let some c := env.find? (b.key.toName) | continue
    unless all || c matches .thmInfo _ do continue
    done := done.push b.key
    -- The kind of a result, by the prefix of its label (`thm:`, `lem:`, …).
    let kind (l : String) : String :=
      match (l.splitOn ":")[0]! with
      | "thm" => "Thm.~" | "lem" => "Lemma~" | "prop" => "Prop.~"
      | "cor" => "Cor.~" | "def" => "Def.~" | _ => ""
    let wh := match b.label with
      | some l => s!"{kind l}\\ref\{{l}}, p.~\\pageref\{{l}}"
      | none => ""
    let src := match ← srcOf c.name with
      | some (p, l) => s!"\\texttt\{{"/\\allowbreak ".intercalate ((p.splitOn "/").map TeX.escape)}:{l}}"
      | none => ""
    let ax ← axOf c.name
    let extra := ax.filter (!standardAxioms.contains ·)
    let axTeX := if ax.contains ``sorryAx then "\\textbf{sorry}"
      else if extra.isEmpty then "standard"
      else ", ".intercalate (extra.toList.map fun a => s!"\\texttt\{{TeX.escape a.toString}}")
    -- The name without the namespaces the document leaves out (the longest
    -- that applies); the source says where it is.
    let strip := (← read).strip.filter (·.isPrefixOf c.name)
    let pre := strip.foldl (fun a n => if n.getNumParts > a.getNumParts then n else a) Name.anonymous
    let shown := (c.name.replacePrefix pre .anonymous).toString
    out := out ++ s!"{wh} & \\texttt\{{TeX.escape shown}} & {src} & {axTeX}\\\\\n"
  out := out ++ "\\end{longtable}\n"
  out := out ++ "The standard axioms are \\texttt{propext}, \\texttt{Classical.choice} and \\texttt{Quot.sound}.\n"
  return out

/-- Run an index view. -/
def runIndexView (base : String) (srcOf : Name → MetaM (Option (String × Nat)))
    (axOf : Name → MetaM (Array Name)) (opts : Array (String × String)) : RenderM String :=
  match base with
  | "conventions" => conventionsView
  | "vocabulary" => vocabularyView opts
  | "provenance" => provenanceView srcOf axOf opts
  | v => throwError "{v} is not a view that indexes the document"

end Imprimatur.Views
