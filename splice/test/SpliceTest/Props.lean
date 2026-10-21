/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import Testkit

/-!
# Property tests of the splicer (docs/TESTING.md, Properties)

A seeded generator builds random documents (prose, braces, comments and
verbatim text holding decoy markers, `\verb`, blocks, aliases with positional
slots, inline items and `\leanslot`s, over a main file and an input) and
random bundles. The properties run on documents held in memory.
-/

open Testkit Splice

namespace SpliceTest.Props

/-! ## Generators -/

/-- The keys documents use. -/
def keys : Array String := #["Gen.k0", "Gen.k1", "Gen.k2", "Gen.k3"]

/-- Slot ids. -/
def slotIds : Array String := #["s0", "s1", "s2"]

/-- Formal texts, which identify positional slots. -/
def formals : Array String := #["x", "\\lambda x.\\, e", "e_1\\; e_2", "v"]

/-- A word of prose. Braces balance; nothing in it is imprimatur markup. -/
def word : Gen String :=
  Gen.elem #["alpha", "beta", "λ", "∀x", "𝔽", "{group}", "$x^2$", "\\emph{w}", "\\\\",
    "50\\%", "\\verb|\\leaninline{F}{x}|", "\\{", "\\}", "[opt]", "a,b", "ü"]

/-- A line of prose. -/
def proseLine : Gen String := do
  let ws ← Gen.listOf word
  return " ".intercalate ws

/-- Text that may appear in generated content and slots: braces balance, and
it has no `\end{…}` and no `%`. -/
def slotText : Gen String := do
  let ws ← Gen.listOf (Gen.elem #["gloss", "a function", "τ₁", "{nested {deep}}", "x", "and"])
  return " ".intercalate ws

/-- Generated content: lines of words, with `\leanslot`s. -/
def content (multiline : Bool) : Gen String := do
  let n ← Gen.natIn 0 (if multiline then 3 else 1)
  let mut lines := #[]
  for _ in [0:n] do
    let parts ← Gen.listOf (Gen.frequency [
      (3, Gen.elem #["\\LeanConst{c}", "x", ":", "→", "{a b}", "\\LeanBound{n}"]),
      (1, do return s!"\\leanslot\{{← Gen.elem slotIds}}\{{← slotText}}")])
    lines := lines.push (" ".intercalate parts)
  return (if multiline then "\n" else " ").intercalate lines.toList

/-- Grammar content for the positional-slot alias. -/
def grammarContent : Gen String := do
  let n ← Gen.natIn 1 3
  let mut lines := #[]
  for _ in [0:n] do
    lines := lines.push s!"\\entry\{{← Gen.elem formals}}\{{← slotText}}"
  return "\\\\\n".intercalate lines.toList

/-- Optional block options. -/
def blockOpts : Gen String :=
  Gen.elem #["", "", "[view=lean]", "[label=l1]"]

/-- One piece of a document. -/
def piece : Gen String :=
  Gen.frequency [
    (4, do return (← proseLine) ++ "\n"),
    (1, do return s!"% {← proseLine} \\begin\{leanblock}\{F}\{x} \\leaninline\{F}\{y}\n"),
    (1, pure "\\begin{verbatim}\n\\begin{leanblock}{F}{x}\n\\leaninline{F}{y}\n\\end{verbatim}\n"),
    (2, do
      let k ← Gen.elem keys
      let rest ← Gen.elem #["", "%", "% comment"]
      let c ← content true
      return s!"\\begin\{leanblock}{← blockOpts}\{{k}}\{Title}{rest}\n{c}{if c.isEmpty then "" else "\n"}\\end\{leanblock}\n"),
    (1, do
      let k ← Gen.elem keys
      return s!"\\begin\{leangrammar}\{{k}}\{G}\n{← grammarContent}\n\\end\{leangrammar}\n"),
    (2, do
      let k ← Gen.elem keys
      return s!"Text \\leaninline\{{k}}\{{← content false}} more.\n"),
    (1, do
      let k ← Gen.elem keys
      return s!"\\leancheck\{{k}}\n")]

/-- A document: a main file that inputs a second file. -/
def document : Gen (Array (String × String)) := do
  let main ← Gen.listOf piece
  let sub ← Gen.listOf piece
  let at_ ← Gen.nat (main.length + 1)
  let main := main.take at_ ++ ["\\input{sub}\n"] ++ main.drop at_
  return #[("main.tex", String.join main), ("sub.tex", String.join sub)]

/-- A bundle with an entry for every key. -/
def bundle : Gen Bundle := do
  let mut entries := #[]
  for k in keys do
    entries := entries.push
      { key := k, kind := "theorem", source := some { path := "Gen.lean", line := 1 },
        views := #[("lean", ← content true), ("grammar", ← grammarContent)] }
  return { entries }

/-- The configuration of generated documents. -/
def config : Config :=
  { main := "main.tex",
    aliases := #[{ name := "leanblock", view := "lean" },
      { name := "leangrammar", view := "grammar",
        slots := some { macros := #["\\entry"], arg := 2, idArg := 1 } }] }

/-- A document with a bundle. -/
def docAndBundle : Gen (Array (String × String) × Bundle) := do
  return (← document, ← bundle)

/-- Show a document for a failure report. -/
def showFiles (fs : Array (String × String)) : String :=
  String.join (fs.toList.map fun (p, t) => s!"\n== {p}\n{t}")

/-! ## Running the splicer in memory -/

/-- Apply a bundle to files held in memory. -/
def applyFiles (fs : Array (String × String)) (b : Bundle) (o : ApplyOpts := {}) :
    Except String (Array (String × String)) := do
  let out := plan (Doc.ofFiles config fs) b o
  if hasErrors out.diags then
    throw ("apply failed:\n" ++ "\n".intercalate (out.diags.map (·.render)).toList)
  return fs.map fun (p, t) => (p, ((out.outputs.find? (·.1 == p)).map (·.2)).getD t)

/-- The items of every file. -/
def itemsOf (fs : Array (String × String)) : Except String (Array (String × Src × Item)) := do
  let mut out := #[]
  for (p, t) in fs do
    let s := Src.ofString p t
    match scanSrc config s with
    | .ok r => out := out ++ r.items.map ((p, s, ·))
    | .error d => throw d.render
  return out

/-- Each file with its generated regions masked and its `sum=` options
removed: what `apply` must not change. -/
def skeleton (fs : Array (String × String)) : Except String (Array String) :=
  fs.mapM fun (p, t) => do
    let s := Src.ofString p t
    let r ← match scanSrc config s with
      | .ok r => pure r
      | .error d => throw d.render
    let mut edits : Array Edit := #[]
    for it in r.items do
      if it.kind == .block || it.kind == .inline || it.kind == .ref then
        edits := edits.push { start := it.regionStart, stop := it.regionEnd, text := "⟦region⟧" }
      if let some (a, b) := it.optsSpan then
        let kept := it.opts.filter (·.key != "sum") |>.map (fun o => s!"{o.key}={o.value}")
        let text := if kept.isEmpty then "" else "[" ++ ", ".intercalate kept.toList ++ "]"
        edits := edits.push { start := a, stop := b, text }
    return applyEdits s edits

/-- What `check` would report. -/
def checkOutcome (fs : Array (String × String)) (b : Bundle) : Outcome :=
  plan (Doc.ofFiles config fs) b {}

/-- Run `f`, turning a thrown error into a property failure. -/
def prop {α : Type} (f : α → Except String Unit) : α → Except String Unit := f

/-! ## The properties -/

/-- Locality: `apply` changes nothing outside generated regions and `sum=`. -/
def locality : Array (String × String) × Bundle → Except String Unit := fun (fs, b) => do
  let after ← applyFiles fs b
  let s1 ← skeleton fs
  let s2 ← skeleton after
  expect (s1 == s2) s!"text outside the regions changed:{showFiles after}"

/-- Idempotence: applying twice is applying once. -/
def idempotence : Array (String × String) × Bundle → Except String Unit := fun (fs, b) => do
  let once ← applyFiles fs b
  let twice ← applyFiles once b
  expect (once == twice) s!"the second apply changed the document:{showFiles twice}"

/-- Fixed point: after `apply`, `check` finds nothing to do. -/
def fixedPoint : Array (String × String) × Bundle → Except String Unit := fun (fs, b) => do
  let once ← applyFiles fs b
  let o := checkOutcome once b
  expect (o.changes.isEmpty && !hasErrors o.diags)
    s!"check after apply reports {o.changes.size} changes and {o.diags.size} diagnostics:\n\
      {"\n".intercalate (o.diags.map (·.render)).toList}"

/-- Slot preservation: a slot present before and after keeps its text. -/
def slotPreservation : Array (String × String) × Bundle → Except String Unit := fun (fs, b) => do
  let before ← itemsOf fs
  let after ← itemsOf (← applyFiles fs b)
  unless before.size == after.size do throw "apply changed the number of items"
  for ((_, s1, i1), (_, s2, i2)) in before.zip after do
    let spec := itemSlots config i1
    let r1 := s1.slice i1.regionStart i1.regionEnd
    let r2 := s2.slice i2.regionStart i2.regionEnd
    let new := findSlots spec r2
    for sl in findSlots spec r1 do
      if let some sl2 := new.find? (fun n => n.id == sl.id && n.occ == sl.occ) then
        unless toLf (sl.text r1) == toLf (sl2.text r2) do
          throw s!"slot {sl.id} of {i1.key}: {repr (sl.text r1)} became {repr (sl2.text r2)}"

/-- Edit detection: a one-character edit in generated text, outside slots, is
a hand edit; inside a slot it isn't. -/
def editDetection : (Array (String × String) × Bundle) × Nat × Nat × Bool → Except String Unit :=
  fun ((fs, b), pick, offset, aimAtSlot) => do
    let once ← applyFiles fs b
    let items := (← itemsOf once).filter fun (_, _, it) =>
      (it.kind == .block || it.kind == .inline) && it.regionEnd > it.regionStart
    if items.isEmpty then return
    let (p, s, it) := items[pick % items.size]!
    let region := s.slice it.regionStart it.regionEnd
    let slots := findSlots (itemSlots config it) region
    -- Half the time, aim inside a slot, which a uniform choice rarely hits.
    let pos :=
      if aimAtSlot && !slots.isEmpty then
        let sl := slots[offset % slots.size]!
        it.regionStart + sl.textStart + offset % (sl.textEnd - sl.textStart + 1)
      else it.regionStart + offset % (it.regionEnd - it.regionStart + 1)
    let rel := pos - it.regionStart
    let inSlot := slots.any
      (fun sl => sl.textStart ≤ rel && rel ≤ sl.textEnd)
    let edited := once.map fun (q, t) =>
      if q == p then (q, applyEdits s #[{ start := pos, stop := pos, text := "Q" }]) else (q, t)
    let o := checkOutcome edited b
    let flagged := o.diags.any fun d => d.code == "hand-edit" && d.loc == s.locString it.start
    if inSlot then
      -- Editing a slot is the authors' right: nothing to report at all.
      expect (!flagged && o.changes.isEmpty && !hasErrors o.diags)
        s!"an edit inside a slot of {it.key} was reported:{showFiles edited}"
    else
      expect flagged s!"an edit outside the slots of {it.key} was not detected:{showFiles edited}"

/-- Normalisation: CRLF line endings and trailing whitespace don't change any
verdict. -/
def normalisation : (Array (String × String) × Bundle) × Nat → Except String Unit :=
  fun ((fs, b), seed) => do
    let once ← applyFiles fs b
    let messy := once.map fun (p, t) =>
      let lines := (t.splitOn "\n").toArray.mapIdx fun i l =>
        if (i + seed) % 3 == 0 then l ++ " \t " else l
      (p, "\r\n".intercalate lines.toList)
    let o := checkOutcome messy b
    expect (o.changes.isEmpty && !hasErrors o.diags)
      s!"CRLF or trailing whitespace changed a verdict: {o.changes.size} changes, \
        {"; ".intercalate (o.diags.map (·.render)).toList}"

/-- Strip: no markers remain, and every generated region survives with its
slots unwrapped. -/
def stripProp : Array (String × String) × Bundle → Except String Unit := fun (fs, b) => do
  let once ← applyFiles fs b
  let stripped := stripDoc (Doc.ofFiles config once)
  for (p, t) in stripped do
    match scanText config p t with
    | .ok r => unless r.items.isEmpty do throw s!"{p}: markup remains after strip:{showFiles stripped}"
    | .error d => throw s!"{p}: stripped output doesn't scan: {d.render}"
    unless (findSlots none t).isEmpty do throw s!"{p}: a \\leanslot remains:{showFiles stripped}"
  let all := String.join (stripped.toList.map (·.2))
  for (_, s, it) in ← itemsOf once do
    let region := unwrapSlots (s.slice it.regionStart it.regionEnd)
    if region.isEmpty || !(it.kind == .block || it.kind == .inline || it.kind == .ref) then continue
    unless (all.splitOn region).length > 1 do
      throw s!"the region of {it.key} is missing after strip: {repr region}"

/-- Robustness: on any input, `scan` succeeds or reports an error with a
position. (It is pure, so it cannot write files.) -/
def robustness (t : String) : Except String Unit :=
  match scanText config "r.tex" t with
  | .ok _ => .ok ()
  | .error d => expect (d.loc.startsWith "r.tex:") s!"an error without a position: {d.render}"

/-- Random TeX-like text: fragments of markup, braces and comments. -/
def texNoise : Gen String := do
  let parts ← Gen.listOf (Gen.elem #["\\begin", "{leanblock}", "\\end", "{", "}", "[", "]", "%",
    "\n", "\\leaninline", "\\leanref", "\\leancheck", "\\input", "\\verb", "|", "\\", "x",
    "{K}", "\\begin{verbatim}", "\\end{verbatim}", "\\leanslot", "=", ",", " ", "λ"])
  return String.join parts

/-- A generated document cut off at a random point. -/
def truncated : Gen String := do
  let (fs, _) ← docAndBundle
  let t := String.join (fs.toList.map (·.2))
  let n ← Gen.nat (t.length + 1)
  return String.ofList (t.toList.take n)

/-- All properties. -/
def tests : TestM Unit := group "properties" do
  let render := fun (x : Array (String × String) × Bundle) => showFiles x.1
  forAll "splice/prop/locality" docAndBundle render locality
  forAll "splice/prop/idempotence" docAndBundle render idempotence
  forAll "splice/prop/fixed-point" docAndBundle render fixedPoint
  forAll "splice/prop/slot-preservation" docAndBundle render slotPreservation
  forAll "splice/prop/edit-detection"
    (do return (← docAndBundle, ← Gen.nat 1000, ← Gen.nat 100000, ← Gen.bool))
    (fun x => render x.1) editDetection
  forAll "splice/prop/normalisation" (do return (← docAndBundle, ← Gen.nat 3))
    (fun x => render x.1) normalisation
  forAll "splice/prop/strip" docAndBundle render stripProp
  forAll "splice/prop/scanner-robustness" texNoise (fun t => (repr t).pretty) robustness
  forAll "splice/prop/scanner-truncated" truncated (fun t => (repr t).pretty) robustness

end SpliceTest.Props
