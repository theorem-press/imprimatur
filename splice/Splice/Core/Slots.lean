/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.Basic
import Splice.Config
import Splice.Core.Scan
import Splice.Core.Text
import SpliceModel.Laws

/-!
# Slots

A generated region's text is a body (`SpliceModel.Body`): text generated
from Lean, and slots, whose text the authors own (DESIGN §9.5). `parts`
cuts the text into generated text and slots, as the splicer always has:
`\leanslot{id}{text}`, and the arguments of the macros an alias declares as
slots by position, including a `\leanslot` that is the whole of such an
argument. It is lossless (`print_parts`). `body` numbers repeated ids, so
that each occurrence of an id is a slot of its own, as the model's `SlotId`
has it.
-/

namespace Splice

/-- A slot in a region's text. Positions are character indices into that
text. -/
structure Slot where
  /-- The slot's id. -/
  id : String
  /-- Which occurrence of this id it is, from 0. -/
  occ : Nat
  /-- Start of the slot's text. -/
  textStart : Nat
  /-- One past the end of the slot's text. -/
  textEnd : Nat
  /-- Whether it is a `\leanslot` (rather than declared by position). -/
  isMacro : Bool
  /-- For a `\leanslot` that is the whole slot argument of a positional macro,
  that macro's id. `migrate-slots` matches on it. -/
  outer : Option String := none
  deriving Repr, Inhabited

end Splice

namespace Splice.Core.Slots

open Splice (SlotSpec Slot)
open Splice.Core.Scan (charAt countWhile skipSpaces lineEnd slice ctrlName ctrlName_pos group)

/-- A piece of a region's text. -/
inductive Part where
  /-- Generated text. -/
  | gen (raw : List Char)
  /-- A slot: its id, its text, whether it is a `\leanslot` (rather than
  declared by position), and, for a `\leanslot` that is the whole slot
  argument of a positional macro, that macro's id. -/
  | slot (id : String) (text : List Char) (isMacro : Bool) (outer : Option String)

/-- The characters of a part. -/
def Part.raw : Part → List Char
  | .gen r => r
  | .slot _ t _ _ => t

/-- The characters of parts, in order. -/
def printParts (ps : List Part) : List Char := (ps.map Part.raw).flatten

/-- `n` braced arguments from index `j`: their inner spans, and the index
after the last. -/
def args (cs : List Char) (j : Nat) : Nat → Option (List (Nat × Nat) × Nat)
  | 0 => some ([], j)
  | n + 1 =>
    let g := j + skipSpaces (cs.drop j)
    if charAt cs g != '{' then none
    else match group (cs.drop g) with
      | none => none
      | some (a, b, after) =>
        (args cs (g + after) n).map fun (spans, k) => ((g + a, g + b) :: spans, k)

/-- `{id}{text}` after `\leanslot`, from index `j`: the id, the text's span,
and the index after it. -/
def slotMacro (cs : List Char) (j : Nat) : Option (String × Nat × Nat × Nat) :=
  match args cs j 2 with
  | some ([(ia, ib), (a, b)], after) =>
    some ((String.ofList (slice cs ia ib)).trimAscii.toString, a, b, after)
  | _ => none

/-- The span at a 1-based position of a list of spans, or `(0, 0)`. -/
def spanAt (spans : List (Nat × Nat)) (n : Nat) : Nat × Nat := spans.getD (n - 1) (0, 0)

/-- A macro that reads `after` characters, with a slot from `s` to `e`:
its parts. The bounds are clamped, so the parts always print back to the
macro's characters. -/
def macroParts (cs : List Char) (s e after : Nat) (id : String) (isMacro : Bool)
    (outer : Option String) : List Part :=
  let s := min s after
  let e := max s (min e after)
  [.gen (cs.take s), .slot id (slice cs s e) isMacro outer, .gen (slice cs e after)]

/-- One step at the front of `cs`: how many characters it reads, and its
parts. -/
def step (spec : Option SlotSpec) (cs : List Char) : Nat × List Part :=
  let c := charAt cs 0
  if c == '%' then (lineEnd cs, [.gen (cs.take (lineEnd cs))])
  else if c != '\\' then
    let n := countWhile (fun ch => ch != '\\' && ch != '%') cs 0
    (n, [.gen (cs.take n)])
  else
    let name := (ctrlName cs).1
    let j := (ctrlName cs).2
    if name == "leanslot" then
      match slotMacro cs j with
      | some (id, a, b, after) => (after, macroParts cs a b after id true none)
      | none => (j, [.gen (cs.take j)])
    else match spec with
      | some sp =>
        if sp.macros.contains ("\\" ++ name) then
          match args cs j (max sp.arg sp.idArg) with
          | some (spans, after) =>
            let (ia, ib) := spanAt spans sp.idArg
            let (sa, sb) := spanAt spans sp.arg
            let id := (String.ofList (slice cs ia ib)).trimAscii.toString
            -- A slot argument that is exactly one `\leanslot` is that macro slot.
            let raw := slice cs sa sb
            let inner := (String.ofList raw).trimAscii.toString
            let innerSlot :=
              if inner.startsWith "\\leanslot" then
                let ics := inner.toList
                match slotMacro ics 9 with
                | some (iid, a, b, after) => if after == ics.length then some (iid, a, b) else none
                | none => none
              else none
            match innerSlot with
            | some (iid, a, b) =>
              let off := sa + countWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r') raw 0
              (after, macroParts cs (off + a) (off + b) after iid true (some id))
            | none => (after, macroParts cs sa sb after id false none)
          | none => (j, [.gen (cs.take j)])
        else (j, [.gen (cs.take j)])
      | none => (j, [.gen (cs.take j)])

/-- The parts of a region's text, reversed onto `acc`. -/
def partsGo (spec : Option SlotSpec) : List Char → List Part → List Part
  | [], acc => acc.reverse
  | c :: rest, acc =>
    let r := step spec (c :: rest)
    let n := max 1 r.1
    -- A step's parts are its first `n` characters; the bounds are clamped
    -- so that this holds whatever the step read.
    partsGo spec ((c :: rest).drop n) ((fixParts r.2 ((c :: rest).take n)).reverse ++ acc)
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega
where
  /-- The parts a step found, if they are exactly its characters; otherwise
  those characters as generated text. -/
  fixParts (ps : List Part) (taken : List Char) : List Part :=
    if printParts ps == taken then ps else [.gen taken]

/-- **The parts of a region's text.** Malformed markup is generated text: a
region is generated, and its slots are only what can be recognised. -/
def parts (spec : Option SlotSpec) (cs : List Char) : List Part := partsGo spec cs []

/-! ## Lossless -/

theorem printParts_append (a b : List Part) : printParts (a ++ b) = printParts a ++ printParts b := by
  simp [printParts]

theorem printParts_reverse_fix (ps : List Part) (taken : List Char) :
    printParts (partsGo.fixParts ps taken) = taken := by
  unfold partsGo.fixParts
  split
  · rename_i h; exact beq_iff_eq.mp h
  · simp [printParts, Part.raw]

theorem printParts_go (spec : Option SlotSpec) :
    ∀ (cs : List Char) (acc : List Part), printParts (partsGo spec cs acc) = printParts acc.reverse ++ cs
  | [], acc => by unfold partsGo; simp
  | c :: rest, acc => by
    unfold partsGo
    rw [printParts_go]
    rw [List.reverse_append, List.reverse_reverse, printParts_append, printParts_reverse_fix,
      List.append_assoc, List.take_append_drop]
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- **The slot finder is lossless:** the parts print back to the text. -/
theorem printParts_parts (spec : Option SlotSpec) (cs : List Char) : printParts (parts spec cs) = cs := by
  have := printParts_go spec cs []
  simpa [parts, printParts] using this

/-! ## Bodies -/

/-- Number the slots: each occurrence of an id gets how many slots before it
had that id. -/
def numberGo : List Part → List String → List (Part × Nat) → List (Part × Nat)
  | [], _, acc => acc.reverse
  | p@(.gen _) :: ps, seen, acc => numberGo ps seen ((p, 0) :: acc)
  | p@(.slot id _ _ _) :: ps, seen, acc => numberGo ps (id :: seen) ((p, seen.count id) :: acc)

/-- The parts, each slot with its occurrence number. -/
def numbered (ps : List Part) : List (Part × Nat) := numberGo ps [] []

/-- The model's segment for a numbered part. -/
def toSeg : Part × Nat → SpliceModel.Seg
  | (.gen r, _) => .gen (String.ofList r)
  | (.slot id t _ _, n) => .slot (id, n) (String.ofList t)

/-- **The body of a region's text**, as the model has it. -/
def body (spec : Option SlotSpec) (cs : List Char) : SpliceModel.Body :=
  (numbered (parts spec cs)).map toSeg

/-! ## Slots with their positions -/

/-- The slots of numbered parts, from index `off`, with their positions. -/
def locatedGo : List (Part × Nat) → Nat → List Slot → List Slot
  | [], _, acc => acc.reverse
  | (.gen r, _) :: ps, off, acc => locatedGo ps (off + r.length) acc
  | (.slot id t m o, n) :: ps, off, acc =>
    locatedGo ps (off + t.length)
      ({ id, occ := n, textStart := off, textEnd := off + t.length, isMacro := m, outer := o } :: acc)

/-- **The slots of a region's text**, in order, with their positions. -/
def located (spec : Option SlotSpec) (cs : List Char) : List Slot :=
  locatedGo (numbered (parts spec cs)) 0 []

/-! ## Merging -/

/-- The id a slot of the old text has in the new one, after `--rename-slot`:
the first rename of its id, keeping its occurrence. -/
def renamed (renames : List (String × String)) (k : SpliceModel.SlotId) : SpliceModel.SlotId :=
  match renames.find? (·.1 == k.1) with
  | some (_, n) => (n, k.2)
  | none => k

/-- The authors' slot text of an old region, keyed as the new region will
have it, with line endings made `\n`. -/
def oldSlots (renames : List (String × String)) (spec : Option SlotSpec) (old : List Char) :
    List (SpliceModel.SlotId × String) :=
  (SpliceModel.slots (body spec old)).map fun (k, t) => (renamed renames k, String.ofList (toLf t.toList))

/-- **Merge** an old region's slot text into a new region: the model's
`fill`, of the new region's body with the old region's slots. -/
def mergeBody (renames : List (String × String)) (spec : Option SlotSpec) (old new : List Char) :
    SpliceModel.Body :=
  SpliceModel.fill (oldSlots renames spec old) (body spec new)

/-- **Slot preservation, for the code's merge:** a slot of the new region
that the old region has (after renaming) keeps the old text, with its line
endings made `\n`. -/
theorem mergeBody_keeps {renames : List (String × String)} {spec : Option SlotSpec}
    {old new : List Char} {i : SpliceModel.SlotId} {t : String}
    (hi : i ∈ SpliceModel.ids (body spec new)) (ho : SpliceModel.lookup i (oldSlots renames spec old) = some t) :
    SpliceModel.lookup i (SpliceModel.slots (mergeBody renames spec old new)) = some t :=
  SpliceModel.slot_kept hi ho

end Splice.Core.Slots
