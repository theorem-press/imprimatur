/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Doc
import Splice.Bundle
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
- **All or nothing.** If anything is an error, `apply` writes nothing.
-/

namespace Splice

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
def renderRef (links : SourceLinks) (commit : Option String) (e : Entry) : Except String String :=
  match links, e.source with
  | .none, _ => .ok ""
  | _, none => .error s!"the bundle has no source location for {e.key}"
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

/-- The edit that sets an item's `sum=` option. -/
def sumEdit (s : Src) (it : Item) (sum : String) : Edit :=
  (optEdits s it #[("sum", sum)])[0]?.getD { start := it.insertAt, stop := it.insertAt, text := "" }

/-- Whether braces in `t` balance. -/
def bracesBalance (t : String) : Bool :=
  let s := Src.ofString "" ("{" ++ t ++ "}")
  match Scan.group s 0 with
  | .ok (_, _, after) => after == s.size
  | .error _ => false

/-- The view an item asks for. With `notation=V`, the view is written
`view:V`, which the extractor renders with notation variant `V`. -/
def itemView (cfg : Config) (it : Item) : String :=
  let view := match it.opt? "view" with
    | some v => v
    | none => ((cfg.alias? it.name).map (·.view)).getD "lean"
  match it.opt? "notation" with
  | some n => view ++ ":" ++ n
  | none => view

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

/-- Work out what applying `bundle` to `doc` would do. -/
def plan (doc : Doc) (bundle : Bundle) (o : ApplyOpts) : Outcome := Id.run do
  let cfg := doc.cfg
  let mut out : Outcome := { diags := doc.diags }
  for f in doc.files do
    let s := f.src
    let eol := dominantEol s.chars
    let mut edits : Array Edit := #[]
    for it in f.scan.items do
      if it.kind == .check || it.kind == .index || it.kind == .leanok then continue
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
        if it.kind == .ref then renderRef o.links o.commit e
        else match e.view? view with
          | some t => .ok t
          | none => .error <| match e.error? view with
            | some why => s!"the {view} view of {it.key} failed to render: {why}"
            | none => s!"the bundle has no {view} view for {it.key}"
      if let .error msg := generated then
        let code := if it.kind == .ref then "bad-ref" else "missing-view"
        out := { out with diags := out.diags.push (Diag.err code loc msg) }
        continue
      let new := match generated with
        | .ok t => t
        | .error _ => ""
      -- The `meta` view leaves its source location to the profile (DESIGN §11).
      let new ← if (new.splitOn metaSourceMarker).length > 1 then
          match renderRef o.links o.commit e with
          | .ok ref => pure (new.replace metaSourceMarker ("\\leanmetasource{" ++ ref ++ "}"))
          | .error msg =>
            out := { out with diags := out.diags.push (Diag.err "bad-ref" loc msg) }
            continue
        else pure new
      let old := s.slice it.regionStart it.regionEnd
      let (merged, orphans) := mergeSlots o spec old new
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
      let endMarker := "\\end{" ++ it.name ++ "}"
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
      if it.kind != .ref && it.opt? "sum" != some sum then
        itemEdits := itemEdits.push (sumEdit s it sum)
      unless itemEdits.isEmpty do
        let ch : Change := { loc, key := it.key, old, new := content, contentChanged := !same }
        out := { out with changes := out.changes.push ch }
        edits := edits ++ itemEdits
    unless edits.isEmpty do
      out := { out with outputs := out.outputs.push (s.path, applyEdits s edits) }
  return out

end Splice
