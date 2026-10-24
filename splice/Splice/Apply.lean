/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Doc
import Imprimatur.Bundle
import Splice.Slots
import Splice.Core.Rewrite

/-!
# Applying a bundle

`plan` works out what `apply` would write (DESIGN §10.2). It is pure: `apply`
writes its outputs, and `check` reports them without writing (§10.3).

- **Only what changed.** A block whose content already matches the bundle,
  after normalisation, is not touched. A file with no changes is not written.
- **Hand edits.** A block whose `sum=` doesn't match its content was edited
  by hand. It is left alone and reported, unless its key is forced.
- **Slots.** Each slot's text is carried from the old content to the new,
  matched by id and occurrence (DESIGN §9.5). Slots that disappear are
  reported with their text.
- **Default slot text.** A block records the digest of its slots' default
  texts as `dflt=`. While its slots still match that digest, nobody has
  edited them, so they take the new defaults. Once one is edited, all keep
  their text, and a default that changed is reported.
- **All or nothing.** If anything is an error, `apply` writes nothing.
-/

namespace Splice

open Imprimatur

/-- Options of `apply`, `check` and `migrate-slots`. -/
structure ApplyOpts where
  /-- Keys whose hand-edited blocks may be overwritten. -/
  force : Array String := #[]
  /-- Make missing keys warnings and keep the old content. -/
  keepStale : Bool := false
  /-- Slot renames `(old, new)`. -/
  renames : Array (String × String) := #[]
  /-- How `\leanref` renders source locations. -/
  links : SourceLinks := .relative
  /-- The commit for `url` links. -/
  commit : Option String := none
  /-- Match new `\leanslot`s to old positional slots (`migrate-slots`). -/
  migrate : Bool := false

/-- An item whose generated content or checksum would change. -/
structure Change where
  /-- Where it is. -/
  loc : String
  /-- Its key. -/
  key : String
  /-- The current content of its region. -/
  old : String
  /-- The content `apply` would write. -/
  new : String
  /-- Whether the content changes (otherwise only `sum=` does). -/
  contentChanged : Bool

/-- What `apply` would do. -/
structure Outcome where
  /-- Files whose text changes: path and new text. -/
  outputs : Array (String × String) := #[]
  /-- Items that change. -/
  changes : Array Change := #[]
  /-- Errors and warnings. -/
  diags : Array Diag := #[]
  /-- The files that change, by index, as the chunks `apply` would write. -/
  rewritten : Array (Nat × List Core.Scan.Chunk) := #[]

/-- Escape TeX's special characters. -/
def texEscape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{" | '}' => "\\}" | '#' => "\\#" | '$' => "\\$" | '%' => "\\%"
    | '&' => "\\&" | '_' => "\\_"
    | '~' => "\\textasciitilde{}" | '^' => "\\textasciicircum{}"
    | c => c.toString) ""

/-- The text of a `\leanref` (DESIGN §11). -/
def renderRef (links : SourceLinks) (commit : Option String) (key : String)
    (e : Entry (Image TeX) Verdict) : Except String String :=
  match links, e.decl.source with
  | .none, _ => .ok ""
  | _, none => .error s!"the bundle has no source location for {key}"
  | .relative, some src => .ok s!"{texEscape src.path}:{src.line}"
  | .url tmpl, some src => do
    let needsCommit := (tmpl.splitOn "{commit}").length > 1
    let c ← match commit with
      | some c => pure c
      | none =>
        if needsCommit then throw "the url profile needs a commit (--commit)" else pure ""
    let url := ((tmpl.replace "{commit}" c).replace "{path}" src.path).replace "{line}" (toString src.line)
    return s!"\\url\{{url}}"

/-- Where a view leaves the source location for the splicer to fill. -/
def metaSourceMarker : String := "\\leanmetasource{}"

/-- The edits that set options of an item: existing options get new values,
and missing ones are added at the end of the options (or in a new `[…]`).
Nothing else in the item changes. -/
def optEdits (s : Src) (it : Item) (kvs : Array (String × String)) : Array Edit := Id.run do
  let mut edits := #[]
  let mut missing := #[]
  for (k, v) in kvs do
    match it.opts.find? (·.key == k) with
    | some o => if o.value != v then edits := edits.push { start := o.valueStart, stop := o.valueEnd, text := v }
    | none => missing := missing.push s!"{k}={v}"
  unless missing.isEmpty do
    let text := ", ".intercalate missing.toList
    match it.optsSpan with
    | some (a, b) =>
      if (s.slice (a + 1) (b - 1)).trimAscii.isEmpty then
        edits := edits.push { start := a + 1, stop := b - 1, text }
      else
        edits := edits.push { start := b - 1, stop := b - 1, text := ", " ++ text }
    | none => edits := edits.push { start := it.insertAt, stop := it.insertAt, text := "[" ++ text ++ "]" }
  return edits

/-- Whether braces in `t` balance. -/
def bracesBalance (t : String) : Bool :=
  let s := Src.ofString "" ("{" ++ t ++ "}")
  match Scan.group s 0 with
  | .ok (_, _, after) => after == s.size
  | .error _ => false

/-- The view an item asks for. With `notation=V`, the view is written
`view:V`, which the extractor renders with notation variant `V`; options
that change the rendering follow as `|key=value`. -/
def itemView (cfg : Config) (it : Item) : String :=
  let view := match it.opt? "view" with
    | some v => v
    | none => ((cfg.alias? it.name).map (·.view)).getD "lean"
  let view := match it.opt? "notation" with
    | some n => view ++ ":" ++ n
    | none => view
  -- Options the extractor renders with (DESIGN §9.1), in a fixed order:
  -- `rules|include=App,Lam`, `math|rule=`.
  ["include", "exclude", "rule", "def", "forall", "names"].foldl (fun v k =>
    match it.opts.find? (·.key == k) with
    | some o => v ++ "|" ++ k ++ "=" ++ (",".intercalate ((o.value.splitOn ",").map (·.trimAscii.toString)))
    | none => v) view

/-- The slot declaration that applies to an item. -/
def itemSlots (cfg : Config) (it : Item) : Option SlotSpec :=
  if it.kind == .block then (cfg.alias? it.name).bind (·.slots) else none

/-- Merge slot text from `old` into `new`. Returns the merged text and the
old slots that found no place in it. -/
def mergeSlots (o : ApplyOpts) (spec : Option SlotSpec) (old new : String) :
    String × Array Slot := Id.run do
  let oldSlots := findSlots spec old
  let newSlots := findSlots spec new
  let renamed (sl : Slot) : String :=
    match o.renames.find? (·.1 == sl.id) with
    | some (_, n) => n
    | none => sl.id
  let matchOld (ns : Slot) : Option Slot :=
    let byId := oldSlots.find? (fun os => renamed os == ns.id && os.occ == ns.occ)
    if o.migrate then
      match ns.outer with
      | some outer =>
        (oldSlots.find? (fun os => !os.isMacro && os.id == outer)).orElse (fun _ => byId)
      | none => byId
    else byId
  -- An ordinary merge is the model's `fill` (`Core.Slots.mergeBody`), for
  -- which slot preservation is proved; `migrate-slots` matches on `outer`.
  let merged :=
    if o.migrate then
      mapSlots new newSlots fun ns =>
        match matchOld ns with
        | some os => toLf (os.text old)
        | none => ns.text new
    else SpliceModel.Body.text (Core.Slots.mergeBody o.renames.toList spec old.toList new.toList)
  let used := newSlots.filterMap matchOld |>.map (·.textStart)
  let orphans := oldSlots.filter (fun os => !used.contains os.textStart)
  return (merged, orphans)

/-- The labels the splicer writes, by file and item index: an alias with
`label` gives each of its blocks one, and a repeated key (in document order,
counted per alias) gets the `repeat_suffix`. -/
def blockLabels (doc : Doc) : Array (Nat × Nat × String) := Id.run do
  let mut out := #[]
  let mut seen : Array (String × String × Nat) := #[]
  for (f, fi) in doc.files.toList.zip (List.range doc.files.size) do
    for (it, ii) in f.scan.items.toList.zip (List.range f.scan.items.size) do
      unless it.kind == .block do continue
      let some a := doc.cfg.alias? it.name | continue
      let mut occ := 0
      if let some i := seen.findIdx? (fun (n, k, _) => n == a.name && k == it.key) then
        let (n, k, c) := seen[i]!
        occ := c + 1
        seen := seen.set! i (n, k, occ)
      else
        seen := seen.push (a.name, it.key, 0)
      if let some l := a.labelFor it.key occ then out := out.push (fi, ii, l)
  return out

/-- How an item changes: its region's new content, if that changes, and the
edits of its options (at positions in the file), which lie in its option
list, or at the place one is inserted. -/
structure ItemRewrite where
  /-- The region's new content, if it changes. -/
  region : Option String := none
  /-- The edits of the options. -/
  optEdits : Array Edit := #[]

/-- Where an item's options are, relative to its start: the span of its
`[…]`, or the empty span where one is inserted. -/
def optsBounds (it : Item) : Nat × Nat :=
  match it.optsSpan with
  | some (a, b) => (a - it.start, b - it.start)
  | none => (it.insertAt - it.start, it.insertAt - it.start)

/-- **An item's characters, rewritten:** the characters before its options,
its options with their edits, the characters between its options and its
region, its region (new, or as it was), and the characters after it. So
nothing but the options and the region changes. -/
def rewriteItem (it : Item) (raw : List Char) (rw : ItemRewrite) : List Char :=
  let (o1, o2) := optsBounds it
  let rs := it.regionStart - it.start
  let re := it.regionEnd - it.start
  let opts := Core.Rewrite.splice (Core.Scan.slice raw o1 o2) o1 (Core.Rewrite.sortEdits
    (rw.optEdits.toList.map fun e => { start := e.start - it.start, stop := e.stop - it.start, text := e.text.toList }))
  let region := match rw.region with
    | some t => t.toList
    | none => Core.Scan.slice raw rs re
  raw.take o1 ++ opts ++ Core.Scan.slice raw o2 rs ++ region ++ raw.drop re

/-- What planning one item gives: its diagnostics, in order, and, if it
changes, the change and its edits (at positions in the file). -/
structure ItemResult where
  /-- Errors and warnings. -/
  diags : Array Diag := #[]
  /-- The change, if the item changes. -/
  change : Option Change := none
  /-- How it changes. -/
  rewrite : ItemRewrite := {}

/-- The generated text of an item, from its bundle entry: its view's
rendering, or, for `\leanref`, its source location. -/
def generatedOf (cfg : Config) (o : ApplyOpts) (loc : String) (it : Item) (e : Entry (Image TeX) Verdict) :
    Except Diag String :=
  let view := itemView cfg it
  if it.kind == .ref then
    match renderRef o.links o.commit it.key e with
    | .ok t => .ok t
    | .error msg => .error (Diag.err "bad-ref" loc msg)
  else match e.statement.view? view with
    | some t => .ok t
    | none => .error <| Diag.err "missing-view" loc <| match e.statement.error? view with
      | some why => s!"the {view} view of {it.key} failed to render: {why}"
      | none => s!"the bundle has no {view} view for {it.key}"

/-- What an item's region shows, from its generated text: the alias's
template and label around it (blocks), and, for the `meta` view, its source
location (DESIGN §11). -/
def renderItem (cfg : Config) (labels : Array (Nat × Nat × String)) (o : ApplyOpts) (loc : String)
    (fi ii : Nat) (it : Item) (e : Entry (Image TeX) Verdict) (g : String) : Except Diag String :=
  let new := match cfg.alias? it.name with
    | some a =>
      if it.kind == .block then
        let label := (labels.find? (fun (a, b, _) => a == fi && b == ii)).map (·.2.2)
        a.fill g it.key it.title label
      else g
    | none => g
  if (new.splitOn metaSourceMarker).length > 1 then
    match renderRef o.links o.commit it.key e with
    | .ok ref => .ok (new.replace metaSourceMarker ("\\leanmetasource{" ++ ref ++ "}"))
    | .error msg => .error (Diag.err "bad-ref" loc msg)
  else .ok new

/-- An item's region, regenerated from `new` and the region's old text
`old`: slots that still hold the defaults recorded in `dflt=` take the new
defaults, edited ones keep their text (an ordinary merge is the model's
`fill`); a block's content ends with a newline and starts on its own line;
and the file's line endings are used. Also the merged text, the slot
digest of the new defaults, and the warnings about slots. -/
structure RegionContent where
  /-- The content to write. -/
  content : String
  /-- The digest of the new slot defaults, for a block. -/
  defaults : Option String
  /-- Warnings: defaults that changed in an edited block, slots dropped. -/
  warnings : Array Diag

/-- Regenerate an item's region (see `RegionContent`). -/
def regionContent (cfg : Config) (o : ApplyOpts) (loc eol : String) (it : Item) (new old : String) :
    RegionContent := Id.run do
  let spec := itemSlots cfg it
  let defaults := if it.kind == .block then slotDigest spec new else none
  let recorded := it.opt? "dflt"
  let untouched := recorded.isSome && slotDigest spec old == recorded
  let (merged, orphans) := if untouched then (new, #[]) else mergeSlots o spec old new
  let mut ds : Array Diag := #[]
  if recorded.isSome && !untouched && recorded != defaults then
    -- The digest says that some default changed, not which: list the
    -- slots that differ from their new defaults.
    let newSlots := findSlots spec new
    let mut differ : Array String := #[]
    for ms in findSlots spec merged do
      let some ns := newSlots.find? (fun n => n.id == ms.id && n.occ == ms.occ) | continue
      if normalize (ms.text merged) != normalize (ns.text new) then
        differ := differ.push s!"  {ms.id}\n    kept:    {ms.text merged}\n    default: {ns.text new}"
    unless differ.isEmpty do
      ds := ds.push (Diag.warn "slot-default" loc
        s!"default slot text of {it.key} has changed, but its slots were edited, so all keep \
          their text. These differ from their new defaults:\n{"\n".intercalate differ.toList}\n\
          Update any that are stale by hand.")
  for sl in orphans do
    ds := ds.push (Diag.warn "orphan-slot" loc
      s!"slot {sl.id} of {it.key} is no longer generated, so its text is dropped:\n{sl.text old}\n\
        If the slot was renamed, rerun with --rename-slot {sl.id}=NEW.")
  let content :=
    if it.kind == .block then
      let c := if merged.isEmpty || merged.endsWith "\n" then merged else merged ++ "\n"
      if it.regionStart == it.headerEnd then "\n" ++ c else c
    else merged
  return { content := withEol eol (toLf content), defaults, warnings := ds }

/-- Content that would change the document's structure, refused. -/
def badContent? (cfg : Config) (loc : String) (it : Item) (content : String) : Option Diag :=
  let isComment := ((cfg.alias? it.name).map (·.comment)).getD false
  let endMarker := if isComment then "%END" ++ it.name else "\\end{" ++ it.name ++ "}"
  if (it.kind == .block && (content.splitOn endMarker).length > 1) ||
      (it.kind != .block && !bracesBalance content) then
    let why := if it.kind == .block then "it contains " ++ endMarker else "its braces don't balance"
    some (Diag.err "bad-content" loc s!"the generated text for {it.key} would break the document ({why})")
  else none

/-- A region edited by hand: its content isn't what was generated (by its
`sum=`), and is about to be replaced without `--force`. -/
def handEdited? (o : ApplyOpts) (spec : Option SlotSpec) (loc : String) (it : Item) (old : String)
    (same : Bool) : Option Diag :=
  if it.kind != .ref then
    match it.opt? "sum" with
    | some recorded =>
      if !same && checksum spec old != recorded && !o.force.contains it.key then
        some (Diag.err "hand-edit" loc
          s!"the generated content of {it.key} was edited by hand, so it was not regenerated.\n\
            Move the edit into Lean or into a slot, or rerun with --force {it.key} to overwrite it.")
      else none
    | none => none
  else none

/-- How an item's content and options change. -/
def itemRewrite (s : Src) (it : Item) (rc : RegionContent) (same : Bool) (sum : String) : ItemRewrite :=
  let opts : Array (String × String) :=
    (if it.kind != .ref && it.opt? "sum" != some sum then #[("sum", sum)] else #[]) ++
    (match rc.defaults with
     | some d => if it.opt? "dflt" != some d then #[("dflt", d)] else #[]
     | none => #[])
  { region := if !same then some rc.content else none, optEdits := optEdits s it opts }

/-- Plan one item: the `i`th of file `fi`, whose line endings are mostly
`eol`. -/
def planItem (cfg : Config) (labels : Array (Nat × Nat × String)) (bundle : Bundle (Image TeX) Verdict)
    (o : ApplyOpts) (s : Src) (fi : Nat) (eol : String) (it : Item) (ii : Nat) : ItemResult :=
  if it.kind == .check || it.kind == .index || it.kind == .leanok || it.kind == .hypref then {}
  else
  let loc := s.locString it.start
  match bundle.find? it.key with
  | none =>
    { diags := #[if o.keepStale then
        Diag.warn "missing-key" loc s!"no entry for {it.key} in the bundle; keeping the old content"
      else
        Diag.err "missing-key" loc s!"no entry for {it.key} in the bundle \
          (is the name right, and was the extractor asked for it?)"] }
  | some e =>
    match generatedOf cfg o loc it e with
    | .error d => { diags := #[d] }
    | .ok g =>
      match renderItem cfg labels o loc fi ii it e g with
      | .error d => { diags := #[d] }
      | .ok new =>
        let old := s.slice it.regionStart it.regionEnd
        let rc := regionContent cfg o loc eol it new old
        match badContent? cfg loc it rc.content with
        | some d => { diags := rc.warnings.push d }
        | none =>
          let same := normalize old == normalize rc.content
          match handEdited? o (itemSlots cfg it) loc it old same with
          | some d => { diags := rc.warnings.push d }
          | none =>
            let rw := itemRewrite s it rc same (checksum (itemSlots cfg it) rc.content)
            if rw.region.isNone && rw.optEdits.isEmpty then { diags := rc.warnings }
            else { diags := rc.warnings, rewrite := rw,
                   change := some { loc, key := it.key, old, new := rc.content, contentChanged := !same } }

/-- Rewrite a file's chunks: each item that changes, within its own
characters. Text is left as it is. -/
def rewriteChunks (edits : List (Nat × ItemRewrite)) (chunks : List Core.Scan.Chunk) :
    List Core.Scan.Chunk :=
  chunks.map fun
    | .item it raw =>
      match edits.find? (·.1 == it.start) with
      | some (_, es) => .item it (rewriteItem it raw es)
      | none => .item it raw
    | ch => ch

/-- What planning one file gives: its diagnostics and changes, in order, and
its chunks rewritten, if any item changes. -/
structure FileResult where
  /-- Errors and warnings. -/
  diags : Array Diag := #[]
  /-- The items that change. -/
  changes : Array Change := #[]
  /-- The chunks `apply` would write, if the file changes. -/
  rewritten : Option (List Core.Scan.Chunk) := none

/-- Plan one file, the `fi`th. -/
def planFile (cfg : Config) (labels : Array (Nat × Nat × String)) (bundle : Bundle (Image TeX) Verdict)
    (o : ApplyOpts) (f : SourceFile) (fi : Nat) : FileResult :=
  let eol := dominantEol f.src.chars
  let rs := f.scan.items.toList.zipIdx.map fun (it, ii) =>
    (it, planItem cfg labels bundle o f.src fi eol it ii)
  let edits := rs.filterMap fun (it, r) => if r.change.isSome then some (it.start, r.rewrite) else none
  { diags := (rs.map (·.2.diags)).foldl (· ++ ·) #[],
    changes := (rs.filterMap (·.2.change)).toArray,
    rewritten := if edits.isEmpty then none else some (rewriteChunks edits f.chunks) }

/-- Work out what applying `bundle` to `doc` would do, without checking the
result (`plan` does). Each item that changes is rewritten within its own
characters, and a file is its chunks, printed again. -/
def planOnce (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (o : ApplyOpts) : Outcome :=
  let labels := blockLabels doc
  let rs := doc.files.toList.zipIdx.map fun (f, fi) =>
    (f, fi, planFile doc.cfg labels bundle o f fi)
  { diags := (rs.map (·.2.2.diags)).foldl (· ++ ·) doc.diags,
    changes := (rs.map (·.2.2.changes)).foldl (· ++ ·) #[],
    outputs := (rs.filterMap fun (f, _, r) =>
      r.rewritten.map fun cs => (f.src.path, String.ofList (Core.Scan.print cs))).toArray,
    rewritten := (rs.filterMap fun (_, fi, r) => r.rewritten.map (fi, ·)).toArray }

/-- What items chunks hold, to compare scans: each item's form, name and key. -/
def itemShapes (chunks : List Core.Scan.Chunk) : List (ItemKind × String × String) :=
  chunks.filterMap fun
    | .item it _ => some (it.kind, it.name, it.key)
    | .text _ => none

/-- The check that a file `apply` would write scans again to the chunks it
built: `none` if it does. -/
def rescanDiag (doc : Doc) (fi : Nat) (chunks : List Core.Scan.Chunk) : Option Diag :=
  match doc.files[fi]? with
  | none => none
  | some f =>
    let text := String.ofList (Core.Scan.print chunks)
    match scanChunks doc.cfg (Src.ofString f.src.path text) f.switchesIn f.scannedLive with
    | .error d =>
      some (Diag.err "unstable-output" f.src.path
        s!"the text apply would write does not scan again, so nothing was written:\n{d.render}\n\
          The generated content probably holds markup that ends or opens a block.")
    | .ok (again, _, _) =>
      if again.map Core.Scan.Chunk.raw == chunks.map Core.Scan.Chunk.raw &&
          itemShapes again == itemShapes chunks then none
      else some (Diag.err "unstable-output" f.src.path
        "the text apply would write scans differently from what apply built, so nothing was written")

/-- The document as `apply` would leave it: each file with its new text. -/
def rewrittenDoc (doc : Doc) (out : Outcome) : Doc :=
  let files := doc.files.map fun f =>
    (f.src.path, ((out.outputs.find? (·.1 == f.src.path)).map (·.2)).getD f.src.text)
  { Doc.ofFiles doc.cfg files with manifests := doc.manifests }

/-- The check that planning again on what `apply` would write finds nothing
to do: `none` if it does. -/
def fixedPointDiag (again : Outcome) : Option Diag :=
  if hasErrors again.diags then
    some (Diag.err "not-fixed-point" ""
      s!"applying the bundle to what apply would write fails, so nothing was written:\n\
        {"\n".intercalate (again.diags.filter (·.severity == .error) |>.map (·.render)).toList}")
  else match again.changes[0]? with
    | some ch => some (Diag.err "not-fixed-point" ch.loc
        s!"applying the bundle again would change {ch.key}, so nothing was written")
    | none =>
      if again.outputs.isEmpty then none
      else some (Diag.err "not-fixed-point" "" "applying the bundle again would write again")

/-- The checks that each file `apply` would write scans again as built. -/
def rescanDiags (doc : Doc) (out : Outcome) : Array Diag :=
  (out.rewritten.toList.filterMap fun p => rescanDiag doc p.1 p.2).toArray

/-- The checks of what `apply` would write: that it scans again as built,
and, if it does, that planning again on it finds nothing to do. -/
def checkDiags (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (o : ApplyOpts) (out : Outcome) :
    Array Diag :=
  let ds := rescanDiags doc out
  if ds.isEmpty then (fixedPointDiag (planOnce (rewrittenDoc doc out) bundle o)).toList.toArray else ds

/-- Work out what applying `bundle` to `doc` would do (DESIGN §10.2), and
check it before anything can be written (docs/verified-splicer.md, phase
5). Each file that would change must scan again to the chunks `apply` built
(`unstable-output`), and planning again on the result must change nothing
(`not-fixed-point`); otherwise it is an error, and `apply` writes nothing.
Idempotence and the fixed point are therefore what `apply` checks of its own
output (`SpliceModel.Splicer.plan_fixed_point`). -/
def plan (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (o : ApplyOpts) : Outcome :=
  let out := planOnce doc bundle o
  if hasErrors out.diags || out.outputs.isEmpty then out
  else { out with diags := out.diags ++ checkDiags doc bundle o out }

end Splice
