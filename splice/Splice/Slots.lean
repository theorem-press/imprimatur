/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Scan
import Splice.Core.Slots
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

/-- The slots of a region's text, in order (the verified core's,
`Splice.Core.Slots.located`). Malformed markup ends the search quietly: a
region is generated text, and its slots are only what can be recognised. -/
def findSlots (spec : Option SlotSpec) (text : String) : Array Slot :=
  (Core.Slots.located spec text.toList).toArray

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
