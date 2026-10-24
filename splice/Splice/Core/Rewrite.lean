/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Rewriting an item

`apply` changes a file only inside its items: an item's generated region,
and its options (`sum=`, `dflt=`). Each item's characters are rewritten on
their own, by edits within them, and the file is its chunks printed again,
so text outside items is never touched (docs/verified-splicer.md, phase 5).
-/

namespace Splice.Core.Rewrite

/-- An edit within an item's characters: replace `[start, stop)` by `text`. -/
structure Edit where
  /-- The first character replaced. -/
  start : Nat
  /-- One past the last character replaced. -/
  stop : Nat
  /-- The replacement. -/
  text : List Char

/-- Apply edits, in order of position, to characters that start at index
`pos`. An edit that starts before the previous one stopped replaces nothing
before it. -/
def splice : List Char → Nat → List Edit → List Char
  | cs, _, [] => cs
  | cs, pos, e :: es => cs.take (e.start - pos) ++ e.text ++ splice (cs.drop (e.stop - pos)) e.stop es

/-- Edits in order of position: by start, then by stop. -/
def sortEdits (es : List Edit) : List Edit :=
  es.mergeSort fun a b => a.start < b.start || (a.start == b.start && a.stop ≤ b.stop)

/-- Characters an edit leaves alone: before it, everything is kept. -/
theorem splice_prefix (cs : List Char) (pos : Nat) (e : Edit) (es : List Edit) :
    splice cs pos (e :: es) = cs.take (e.start - pos) ++ e.text ++ splice (cs.drop (e.stop - pos)) e.stop es :=
  rfl

/-- With no edits, nothing changes. -/
theorem splice_nil (cs : List Char) (pos : Nat) : splice cs pos [] = cs := rfl

end Splice.Core.Rewrite
