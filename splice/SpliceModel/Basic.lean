/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Bundle

/-!
# A model of imprimatur's splicer

The splicer works on TeX. Here a document is already parsed into pieces:
hand-written text, generated blocks, and `\leancheck`s on hand-written
prose; and a block's body into segments, text generated from Lean and slots
whose text the authors own. The bundle is the file's type
(`Imprimatur.Bundle`), with each view's TeX parsed the same way and the
verdict read as a bit.

`apply` regenerates the blocks from a bundle, keeping the authors' slot
text; `check` reports what is not as the bundle says. A world
(`Imprimatur.World`) is the Lean development as the extractor presents it,
and `Doc.True` is what a document claims of one. `SpliceModel.Laws` proves
the splicer's laws (DESIGN §18.2), and that a document which checks clean
against a true bundle is true.
-/

namespace SpliceModel

open Imprimatur

/-- The identifiers of slots: a slot's id, and which occurrence of that id
in its body it is, from 0. A body may repeat an id; each occurrence keeps
its own text. -/
abbrev SlotId := String × Nat

/-- A segment of a generated block. -/
inductive Seg where
  /-- text generated from Lean -/
  | gen (s : String)
  /-- a slot, whose text the authors own -/
  | slot (i : SlotId) (t : String)
  deriving DecidableEq

/-- The body of a generated block. -/
abbrev Body := List Seg

/-- The text of a segment: what it generates, or the slot's text. -/
def Seg.text : Seg → String
  | .gen s => s
  | .slot _ t => t

/-- The text of a body, its segments' in order: what a generated region
holds once the slots are filled. -/
def Body.text (r : Body) : String := String.join (r.map Seg.text)

/-- The slots of a body, with their text. -/
def slots : Body → List (SlotId × String)
  | [] => []
  | .gen _ :: r => slots r
  | .slot i t :: r => (i, t) :: slots r

/-- The identifiers of a body's slots. -/
def ids : Body → List SlotId
  | [] => []
  | .gen _ :: r => ids r
  | .slot i _ :: r => i :: ids r

/-- The text of slot `i`, the first with that identifier. -/
def lookup (i : SlotId) : List (SlotId × String) → Option String
  | [] => none
  | (j, t) :: l => if i = j then some t else lookup i l

/-- Fill a rendering's slots: each keeps the authors' text, if they wrote
some, else the rendering's. -/
def fill (old : List (SlotId × String)) : Body → Body
  | [] => []
  | .gen s :: r => .gen s :: fill old r
  | .slot i t :: r => .slot i ((lookup i old).getD t) :: fill old r

/-! ## Bundles and worlds, with renderings parsed -/

/-- An entry as the splicer holds it: the file's, with each view's TeX
parsed into a body, and the verdict read as a bit. -/
abbrev Entry := Imprimatur.Entry (Image Body) Bool

/-- A bundle as the splicer holds it. -/
abbrev Bundle := Imprimatur.Bundle (Image Body) Bool

/-- A world whose renderings are bodies. -/
abbrev World := Imprimatur.World Body

/-- The rendering a bundle has for a key in a view. -/
def rendering (b : Bundle) (k : Key) (v : View) : Option Body :=
  (b.find? k).bind (·.statement.view? v)

/-! ## Documents -/

/-- A piece of a document. -/
inductive Piece where
  /-- hand-written text -/
  | text (s : String)
  /-- a generated block: a key, shown in a view -/
  | block (k : Key) (v : View) (body : Body)
  /-- a check that hand-written prose matches the statement with this hash -/
  | check (k : Key) (h : Hash)

/-- A document. -/
abbrev Doc := List Piece

/-- Regenerate a piece: a block whose key and view the bundle renders gets
the rendering, with the block's slot text kept. -/
def regen (b : Bundle) : Piece → Piece
  | .block k v body =>
    match rendering b k v with
    | some r => .block k v (fill (slots body) r)
    | none => .block k v body
  | p => p

/-- `imprimatur apply`: regenerate every block. -/
def apply (b : Bundle) (d : Doc) : Doc := d.map (regen b)

/-- What `check` reports. -/
inductive Diag where
  /-- the key has no entry -/
  | brokenRef (k : Key)
  /-- the key's proof is not trusted -/
  | untrusted (k : Key)
  /-- the entry has no rendering in the view -/
  | missingView (k : Key) (v : View)
  /-- the block is not the key's rendering -/
  | stale (k : Key)
  /-- the rendering does not read back as the statement -/
  | unfaithful (k : Key) (v : View)
  /-- the entry has no statement hash -/
  | noHash (k : Key)
  /-- the statement has changed since the prose was checked -/
  | drift (k : Key)
  deriving DecidableEq

/-- What `check` reports about a piece. -/
def diags (b : Bundle) : Piece → List Diag
  | .text _ => []
  | .block k v body =>
    match b.find? k with
    | none => [.brokenRef k]
    | some e =>
      (if e.verdict then [] else [.untrusted k]) ++
        match e.statement.view? v with
        | none => [.missingView k v]
        | some r =>
          (if body = fill (slots body) r then [] else [.stale k]) ++
            (if e.statement.problems v = #[] then [] else [.unfaithful k v])
  | .check k h =>
    match b.find? k with
    | none => [.brokenRef k]
    | some e =>
      (if e.verdict then [] else [.untrusted k]) ++
        match e.statement.stmtHash with
        | none => [.noHash k]
        | some h' => if h' = h then [] else [.drift k]

/-- `imprimatur check`: what it reports about a document. -/
def check (b : Bundle) : Doc → List Diag
  | [] => []
  | p :: d => diags b p ++ check b d

/-- `imprimatur accept`: record the current statement hash in each check. -/
def accept (b : Bundle) (d : Doc) : Doc :=
  d.map fun
    | .check k h => .check k (((b.find? k).bind (·.statement.stmtHash)).getD h)
    | p => p

/-- The outline of a piece: a block without its body. -/
def outline : Piece → Piece
  | .block k v _ => .block k v []
  | p => p

/-! ## What a document claims

A document is read as claims about a world, with no bundle in sight: a
block shows a statement Lean proved, rendered in its view, with the authors'
text in the slots, and the rendering reads back as the statement; a check
names, by its hash, a statement Lean proved. -/

/-- What a piece claims of a world. -/
def Piece.True (W : World) : Piece → Prop
  | .text _ => _root_.True
  | .block k v body =>
    ∃ S r', W.stmt k = some S ∧ W.trusted k = true ∧ W.render v S = some r' ∧
      body = fill (slots body) r' ∧ W.Reads r' S
  | .check k h => ∃ S, W.stmt k = some S ∧ W.trusted k = true ∧ W.hash S = h

/-- A document is true of a world when each of its pieces is. -/
def Doc.True (W : World) (d : Doc) : Prop := ∀ p ∈ d, Piece.True W p

/-! ## The bundle of a world -/

/-- The entry an honest extractor makes for a key with statement `S`: the
statement hashed and rendered in each view, with the problems a validator
finds in each rendering. -/
def entryOf (W : World) (views : List View) (problems : View → W.Stmt → Array String)
    (k : Key) (S : W.Stmt) : Entry :=
  { decl := { kind := W.kind k, name := k },
    statement := {
      stmtHash := some (W.hash S), sigHash := some (W.sig S),
      views := (views.filterMap fun v => (W.render v S).map (v, ·)).toArray,
      validation := (views.map fun v => (v, problems v S)).toArray },
    verdict := W.trusted k }

/-- The bundle an honest extractor makes of a world, for the requests `rs`:
each key a document cites, with the views it shows the key in, as the
extractor's requests file gives them. -/
def bundleOf (W : World) (problems : View → W.Stmt → Array String) (rs : List (Key × List View)) :
    Bundle :=
  { producer := { tool := "model", version := "" },
    entries := (rs.filterMap fun (k, vs) => (W.stmt k).map fun S => (k, entryOf W vs problems k S)).toArray }

end SpliceModel
