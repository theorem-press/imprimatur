/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Scan
import Splice.Sha256

/-!
# Author-owned slots and checksums

A slot is a part of a generated region that belongs to the authors
(DESIGN §9.5). It is either `\leanslot{id}{text}`, or an argument of a macro
named in an alias's `slots` declaration, identified by another argument's
text. Slot text is left out of checksums, so editing it is never a hand edit
(DESIGN §10.2).
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

open Scan in
/-- The slots of a region's text, in order. Malformed markup ends the search
quietly: a region is generated text, and its slots are only what can be
recognised. -/
def findSlots (spec : Option SlotSpec) (text : String) : Array Slot := Id.run do
  let s := Src.ofString "" text
  let mut out : Array Slot := #[]
  let mut i := 0
  while i < s.size do
    let c := s.get i
    if c == '%' then
      i := lineEnd s i
      continue
    if c != '\\' then
      i := i + 1
      continue
    let (name, j) := ctrlName s i
    if name == "leanslot" then
      match slotMacro s j with
      | some (id, a, b, after) =>
        out := out.push { id, occ := 0, textStart := a, textEnd := b, isMacro := true }
        i := after
      | none => i := j
    else if let some sp := spec then
      if sp.macros.contains ("\\" ++ name) then
        match args s j (max sp.arg sp.idArg) with
        | some (spans, after) =>
          let (ia, ib) := spans.getD (sp.idArg - 1) (0, 0)
          let (sa, sb) := spans.getD (sp.arg - 1) (0, 0)
          let id := (s.slice ia ib).trimAscii.toString
          -- A slot argument that is exactly one `\leanslot` is that macro slot.
          let inner := (s.slice sa sb).trimAscii.toString
          let innerSlot :=
            if inner.startsWith "\\leanslot" then
              let s' := Src.ofString "" inner
              match slotMacro s' 9 with
              | some (iid, a, b, after) => if after == s'.size then some (iid, a, b) else none
              | none => none
            else none
          match innerSlot with
          | some (iid, a, b) =>
            -- Positions are relative to `inner`; shift them into `text`.
            let off := sa + ((s.slice sa sb).toList.takeWhile (fun c => c == ' ' || c == '\t' ||
              c == '\n' || c == '\r')).length
            out := out.push { id := iid, occ := 0, textStart := off + a, textEnd := off + b,
                              isMacro := true, outer := some id }
          | none =>
            out := out.push { id, occ := 0, textStart := sa, textEnd := sb, isMacro := false }
          i := after
        | none => i := j
      else i := j
    else i := j
  -- Number repeated ids.
  let mut counted : Array Slot := #[]
  for sl in out do
    let n := (counted.filter (·.id == sl.id)).size
    counted := counted.push { sl with occ := n }
  return counted
where
  /-- `{id}{text}` after `\leanslot`: the id, the text span and the end. -/
  slotMacro (s : Src) (j : Nat) : Option (String × Nat × Nat × Nat) :=
    match args s j 2 with
    | some (spans, after) =>
      let (ia, ib) := spans.getD 0 (0, 0)
      let (a, b) := spans.getD 1 (0, 0)
      some ((s.slice ia ib).trimAscii.toString, a, b, after)
    | none => none
  /-- `n` braced arguments after index `j`. -/
  args (s : Src) (j : Nat) (n : Nat) : Option (Array (Nat × Nat) × Nat) := Id.run do
    let mut k := j
    let mut spans := #[]
    for _ in [0:n] do
      let g := skipSpaces s k
      if s.get g != '{' then return none
      match group s g with
      | .ok (a, b, after) =>
        spans := spans.push (a, b)
        k := after
      | .error _ => return none
    return some (spans, k)

/-- Replace each slot's text by `f slot`, leaving the rest of `text` as is. -/
def mapSlots (text : String) (slots : Array Slot) (f : Slot → String) : String := Id.run do
  let cs := text.toList.toArray
  let mut out := ""
  let mut pos := 0
  for sl in slots.qsort (·.textStart < ·.textStart) do
    out := out ++ String.ofList (cs.extract pos sl.textStart).toList ++ f sl
    pos := sl.textEnd
  return out ++ String.ofList (cs.extract pos cs.size).toList

/-- The text of a slot. -/
def Slot.text (sl : Slot) (text : String) : String :=
  String.ofList ((text.toList.toArray.extract sl.textStart sl.textEnd).toList)

/-- The checksum of a region (DESIGN §10.2): slot texts are emptied, the
text is normalised, and the first 60 bits of its SHA-256 are written in
base64url (10 characters). -/
def checksum (spec : Option SlotSpec) (text : String) : String :=
  let blank := mapSlots text (findSlots spec text) (fun _ => "")
  String.ofList ((Sha256.base64url (Sha256.hash (normalize blank).toUTF8)).toList.take 10)

/-- The digest of a region's slots (DESIGN §9.5): each slot's id and text,
normalised, in order, hashed like a checksum. `apply` records the digest of
the default texts as `dflt=`; while the slots still match it, the authors
have not edited them, and `apply` may replace them with new defaults. A
region with no slots has no digest. -/
def slotDigest (spec : Option SlotSpec) (text : String) : Option String :=
  let sls := findSlots spec text
  if sls.isEmpty then none else
    let parts := sls.toList.map fun sl => sl.id ++ "\x00" ++ normalize (sl.text text) ++ "\x00"
    some (String.ofList ((Sha256.base64url (Sha256.hash (String.join parts).toUTF8)).toList.take 10))

end Splice
