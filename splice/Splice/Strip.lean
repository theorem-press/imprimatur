/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Splice.Check

/-!
# Stripping markers, and listing requests

`strip` (DESIGN §10.4) writes a copy of every file with imprimatur's markers
removed and the generated content kept as plain LaTeX:

- a block becomes its content, wrapped in its `wrap` environment if it has
  one (with the title as the optional argument, and `\label` from `label=`);
- `\leaninline` and `\leanref` become their content;
- `\leanslot{id}{text}` becomes `text`;
- `\leancheck` and `\leanindex` are removed.

When a marker had a line to itself, the whole line goes, so stripping never
adds a blank line (which TeX would read as a paragraph break).

`requests` lists every key and view the document asks for (DESIGN §10.1).
-/

namespace Splice

/-- Unwrap `\leanslot{id}{text}` to `text`. -/
def unwrapSlots (text : String) : String := Id.run do
  let s := Src.ofString "" text
  let mut edits : Array Edit := #[]
  for sl in (findSlots none text).filter (·.isMacro) do
    -- The macro is the last `\leanslot` before the slot's text.
    let mut k := sl.textStart
    let mut found := none
    while k > 0 do
      k := k - 1
      if s.get k == '\\' && s.slice k (k + 9) == "\\leanslot" then
        found := some k
        break
    if let some b := found then
      edits := edits.push { start := b, stop := sl.textEnd + 1, text := sl.text text }
  return applyEdits s edits

/-- If the text from the start of `i`'s line to `i` is blank, the line start;
otherwise `i`. -/
private def lineStartIfBlank (s : Src) (i : Nat) : Nat :=
  let ls := s.lineStart i
  if s.blankBetween ls i then ls else i

/-- If the text from `i` to the end of its line is blank, the index after the
newline; otherwise `i`. -/
private def lineEndIfBlank (s : Src) (i : Nat) : Nat :=
  let le := Scan.lineEnd s i
  if s.blankBetween i le then min (le + 1) s.size else i

/-- The edits that strip one file. -/
def stripEdits (cfg : Config) (s : Src) (items : Array Item) : Array Edit := Id.run do
  let mut edits := #[]
  for it in items do
    let region := unwrapSlots (s.slice it.regionStart it.regionEnd)
    match it.kind with
    | .block =>
      let wrap := (it.opt? "wrap").orElse (fun _ => (cfg.alias? it.name).bind (·.wrap))
      match wrap with
      | some w =>
        let title := if it.title.trimAscii.isEmpty then "" else s!"[{it.title}]"
        let label := match it.opt? "label" with | some l => s!"\\label\{{l}}" | none => ""
        let headerRest := s.slice it.headerEnd it.regionStart
        edits := edits.push
          { start := it.start, stop := it.regionStart,
            text := s!"\\begin\{{w}}{title}{label}{headerRest}" }
        edits := edits.push { start := it.regionStart, stop := it.regionEnd, text := region }
        edits := edits.push
          { start := it.regionEnd, stop := it.stop,
            text := s.slice it.regionEnd it.endStart ++ s!"\\end\{{w}}" }
      | none =>
        -- Drop the header line and the `\end` line when they stand alone.
        let headerAlone := it.regionStart > it.headerEnd
        let a := if headerAlone then lineStartIfBlank s it.start else it.start
        let endAlone := s.lineStart it.endStart == it.regionEnd
        let b := if endAlone then lineEndIfBlank s it.stop else it.stop
        edits := edits.push { start := a, stop := it.regionStart, text := "" }
        edits := edits.push { start := it.regionStart, stop := it.regionEnd, text := region }
        edits := edits.push { start := it.regionEnd, stop := b, text := "" }
    | .inline | .ref =>
      edits := edits.push { start := it.start, stop := it.stop, text := region }
    | .leanok => pure ()
    | .check | .index =>
      -- Blueprint markup belongs to leanblueprint, so it stays.
      if it.name == "lean" then continue
      let ls := s.lineStart it.start
      let le := Scan.lineEnd s it.stop
      if s.blankBetween ls it.start && s.blankBetween it.stop le then
        edits := edits.push { start := ls, stop := min (le + 1) s.size, text := "" }
      else
        edits := edits.push { start := it.start, stop := it.stop, text := "" }
  return edits

/-- Every file of the document, stripped. -/
def stripDoc (doc : Doc) : Array (String × String) :=
  doc.files.map fun f => (f.src.path, applyEdits f.src (stripEdits doc.cfg f.src f.scan.items))

open Lean (Json) in
/-- The requests file (`requests.json`): every key the document uses, with
the views it asks for. Check-only keys and references ask for no view. -/
def requests (doc : Doc) : String := Id.run do
  let mut keys : Array (String × Array String) := #[]
  for f in doc.files do
    for it in f.scan.items do
      let views := match it.kind with
        | .block | .inline => #[itemView doc.cfg it]
        | _ => #[]
      for k in it.allKeys do
        match keys.findIdx? (·.1 == k) with
        | some i =>
          let (_, vs) := keys[i]!
          keys := keys.set! i (k, (vs ++ views.filter (!vs.contains ·)))
        | none => keys := keys.push (k, views)
  -- Comparator manifests: check-only keys (DESIGN §10.5).
  for m in doc.manifests do
    for k in m.theorems do
      unless keys.any (·.1 == k) do keys := keys.push (k, #[])
  -- Written by hand so that keys are sorted and each request is one line.
  let q (t : String) : String := (Json.str t).compress
  let lines := (keys.qsort (·.1 < ·.1)).map fun (k, vs) =>
    s!"    {q k}: \{\"views\": [{", ".intercalate ((vs.qsort (· < ·)).map q).toList}]}"
  let list (xs : Array String) : String := "[" ++ ", ".intercalate (xs.map q).toList ++ "]"
  let c := doc.cfg
  -- The extractor imports the manifests' solution modules too.
  let imports := doc.manifests.foldl (fun acc m => match m.solutionModule with
    | some sm => if acc.contains sm then acc else acc.push sm
    | none => acc) c.imports
  let challenges := doc.manifests.foldl (fun acc m => match m.challengeModule with
    | some cm => acc ++ m.theorems.map (q · ++ ": " ++ q cm)
    | none => acc) #[]
  -- Settings that are left out when not given, so the extractor's defaults apply.
  let extra := String.join [
    match c.notationPacks with | some ps => s!", \"notation_packs\": {list ps}" | none => "",
    if c.notationFiles.isEmpty then "" else s!", \"notation\": {list c.notationFiles}",
    match c.width with | some w => s!", \"width\": {w}" | none => ""]
  let config := s!"  \"config\": \{\"imports\": {list imports}, \
    \"open_scoped\": {list c.openScoped}, \"strip_namespaces\": {list c.stripNamespaces},\n    \
    \"trusted_prefixes\": {list c.trustedPrefixes}, \
    \"challenges\": \{{", ".intercalate challenges.toList}}{extra}},\n"
  return s!"\{\n  \"schema\": \"imprimatur-requests/1\",\n{config}  \"requests\": \{\n\
    {",\n".intercalate lines.toList}\n  }\n}\n"

end Splice
