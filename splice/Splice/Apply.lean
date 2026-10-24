/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Doc
import Imprimatur.Bundle
import Splice.Slots

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
  let merged := mapSlots new newSlots fun ns =>
    match matchOld ns with
    | some os => toLf (os.text old)
    | none => ns.text new
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

/-- Work out what applying `bundle` to `doc` would do. -/
def plan (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (o : ApplyOpts) : Outcome := Id.run do
  let cfg := doc.cfg
  let labels := blockLabels doc
  let mut out : Outcome := { diags := doc.diags }
  for (f, fi) in doc.files.toList.zip (List.range doc.files.size) do
    let s := f.src
    let eol := dominantEol s.chars
    let mut edits : Array Edit := #[]
    for (it, ii) in f.scan.items.toList.zip (List.range f.scan.items.size) do
      if it.kind == .check || it.kind == .index || it.kind == .leanok || it.kind == .hypref then continue
      let loc := s.locString it.start
      let missing :=
        if o.keepStale then
          Diag.warn "missing-key" loc s!"no entry for {it.key} in the bundle; keeping the old content"
        else
          Diag.err "missing-key" loc s!"no entry for {it.key} in the bundle \
            (is the name right, and was the extractor asked for it?)"
      let some e := bundle.find? it.key
        | out := { out with diags := out.diags.push missing }
          continue
      let spec := itemSlots cfg it
      let view := itemView cfg it
      let generated : Except String String :=
        if it.kind == .ref then renderRef o.links o.commit it.key e
        else match e.statement.view? view with
          | some t => .ok t
          | none => .error <| match e.statement.error? view with
            | some why => s!"the {view} view of {it.key} failed to render: {why}"
            | none => s!"the bundle has no {view} view for {it.key}"
      if let .error msg := generated then
        let code := if it.kind == .ref then "bad-ref" else "missing-view"
        out := { out with diags := out.diags.push (Diag.err code loc msg) }
        continue
      let new := match generated with
        | .ok t => t
        | .error _ => ""
      -- The alias's template: a label, a wrapper, …
      let new := match cfg.alias? it.name with
        | some a =>
          if it.kind == .block then
            let label := (labels.find? (fun (a, b, _) => a == fi && b == ii)).map (·.2.2)
            a.fill new it.key it.title label
          else new
        | none => new
      -- The `meta` view leaves its source location to the profile (DESIGN §11).
      let new ← if (new.splitOn metaSourceMarker).length > 1 then
          match renderRef o.links o.commit it.key e with
          | .ok ref => pure (new.replace metaSourceMarker ("\\leanmetasource{" ++ ref ++ "}"))
          | .error msg =>
            out := { out with diags := out.diags.push (Diag.err "bad-ref" loc msg) }
            continue
        else pure new
      let old := s.slice it.regionStart it.regionEnd
      -- Slots that still hold the defaults they were written with take the
      -- new defaults; edited ones keep their text.
      let defaults := if it.kind == .block then slotDigest spec new else none
      let recorded := it.opt? "dflt"
      let untouched := recorded.isSome && slotDigest spec old == recorded
      let (merged, orphans) := if untouched then (new, #[]) else mergeSlots o spec old new
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
          let d := Diag.warn "slot-default" loc
            s!"default slot text of {it.key} has changed, but its slots were edited, so all keep \
              their text. These differ from their new defaults:\n{"\n".intercalate differ.toList}\n\
              Update any that are stale by hand."
          out := { out with diags := out.diags.push d }
      for sl in orphans do
        let d := Diag.warn "orphan-slot" loc
          s!"slot {sl.id} of {it.key} is no longer generated, so its text is dropped:\n{sl.text old}\n\
            If the slot was renamed, rerun with --rename-slot {sl.id}=NEW."
        out := { out with diags := out.diags.push d }
      -- Shape the content: a block's content ends with a newline and starts on
      -- its own line; then use the file's line endings.
      let content :=
        if it.kind == .block then
          let c := if merged.isEmpty || merged.endsWith "\n" then merged else merged ++ "\n"
          if it.regionStart == it.headerEnd then "\n" ++ c else c
        else merged
      let content := withEol eol (toLf content)
      -- Content that would change the document's structure is refused.
      let isComment := ((cfg.alias? it.name).map (·.comment)).getD false
      let endMarker := if isComment then "%END" ++ it.name else "\\end{" ++ it.name ++ "}"
      if (it.kind == .block && (content.splitOn endMarker).length > 1) ||
          (it.kind != .block && !bracesBalance content) then
        let why := if it.kind == .block then "it contains " ++ endMarker else "its braces don't balance"
        let d := Diag.err "bad-content" loc
          s!"the generated text for {it.key} would break the document ({why})"
        out := { out with diags := out.diags.push d }
        continue
      let same := normalize old == normalize content
      let sum := checksum spec content
      if it.kind != .ref then
        if let some recorded := it.opt? "sum" then
          if !same && checksum spec old != recorded && !o.force.contains it.key then
            let d := Diag.err "hand-edit" loc
              s!"the generated content of {it.key} was edited by hand, so it was not regenerated.\n\
                Move the edit into Lean or into a slot, or rerun with --force {it.key} to overwrite it."
            out := { out with diags := out.diags.push d }
            continue
      let mut itemEdits : Array Edit := #[]
      if !same then
        itemEdits := itemEdits.push { start := it.regionStart, stop := it.regionEnd, text := content }
      let mut opts : Array (String × String) := #[]
      if it.kind != .ref && it.opt? "sum" != some sum then opts := opts.push ("sum", sum)
      if let some d := defaults then
        if recorded != some d then opts := opts.push ("dflt", d)
      itemEdits := itemEdits ++ optEdits s it opts
      unless itemEdits.isEmpty do
        let ch : Change := { loc, key := it.key, old, new := content, contentChanged := !same }
        out := { out with changes := out.changes.push ch }
        edits := edits ++ itemEdits
    unless edits.isEmpty do
      out := { out with outputs := out.outputs.push (s.path, applyEdits s edits) }
  return out

end Splice
