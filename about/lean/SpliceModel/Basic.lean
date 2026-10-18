/-!
# A model of imprimatur's splicer

A document is a list of pieces: hand-written text, generated blocks, and
`\leancheck`s on hand-written prose. A bundle, exported from a Lean
environment, gives each key its rendering and its statement hash. `apply`
regenerates the blocks from a bundle, keeping the text the authors wrote in
slots; `check` reports what is not as the bundle says.

This is a model: the splicer works on TeX source, and here a document is
already parsed into pieces. The laws proved in `SpliceModel.Laws` are the
ones DESIGN §18.2 states, and that the splicer's property tests check.
-/

namespace SpliceModel

/-- Keys: the names of Lean constants. -/
abbrev Key := String

/-- The identifiers of slots. -/
abbrev SlotId := String

/-- A segment of a generated block. -/
inductive Seg where
  /-- text generated from Lean -/
  | gen (s : String)
  /-- a slot, whose text the authors own -/
  | slot (i : SlotId) (t : String)
  deriving DecidableEq

/-- The body of a generated block. -/
abbrev Body := List Seg

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

/-- What a bundle says about a key. -/
structure Entry where
  /-- the rendering, with each slot's default text -/
  render : Body
  /-- the hash of the statement -/
  hash : Nat
  /-- whether the proof is trusted: no `sorry`, and only permitted axioms -/
  trusted : Bool

/-- A bundle: the entries of the keys a document uses. -/
abbrev Bundle := Key → Option Entry

/-- A piece of a document. -/
inductive Piece where
  /-- hand-written text -/
  | text (s : String)
  /-- a generated block for a key -/
  | block (k : Key) (body : Body)
  /-- a check that hand-written prose matches the statement with this hash -/
  | check (k : Key) (h : Nat)

/-- A document. -/
abbrev Doc := List Piece

/-- Regenerate a piece: a block whose key has an entry gets the entry's
rendering, with the block's slot text kept. -/
def regen (b : Bundle) : Piece → Piece
  | .block k body =>
    match b k with
    | some e => .block k (fill (slots body) e.render)
    | none => .block k body
  | p => p

/-- `imprimatur apply`: regenerate every block. -/
def apply (b : Bundle) (d : Doc) : Doc := d.map (regen b)

/-- What `check` reports. -/
inductive Diag where
  /-- the key has no entry -/
  | brokenRef (k : Key)
  /-- the key's proof is not trusted -/
  | untrusted (k : Key)
  /-- the block is not the key's rendering -/
  | stale (k : Key)
  /-- the statement has changed since the prose was checked -/
  | drift (k : Key)
  deriving DecidableEq

/-- What `check` reports about a piece. -/
def diags (b : Bundle) : Piece → List Diag
  | .text _ => []
  | .block k body =>
    match b k with
    | none => [.brokenRef k]
    | some e =>
      (if e.trusted then [] else [.untrusted k]) ++
        (if body = fill (slots body) e.render then [] else [.stale k])
  | .check k h =>
    match b k with
    | none => [.brokenRef k]
    | some e =>
      (if e.trusted then [] else [.untrusted k]) ++ (if e.hash = h then [] else [.drift k])

/-- `imprimatur check`: what it reports about a document. -/
def check (b : Bundle) : Doc → List Diag
  | [] => []
  | p :: d => diags b p ++ check b d

/-- `imprimatur accept`: record the current statement hash in each check. -/
def accept (b : Bundle) (d : Doc) : Doc :=
  d.map fun
    | .check k h => .check k (((b k).map (·.hash)).getD h)
    | p => p

/-- The outline of a piece: a block without its body. -/
def outline : Piece → Piece
  | .block k _ => .block k []
  | p => p

/-! ## Lean environments, as far as a paper sees them -/

/-- A Lean environment: each key's statement, if it is a constant, and
whether its proof is trusted. -/
structure Env (Stmt : Type) where
  /-- the statement of each constant -/
  stmt : Key → Option Stmt
  /-- whether the proof of each constant is trusted -/
  trusted : Key → Bool

/-- `imprimatur-export`: the bundle of an environment, given how statements
are rendered and hashed. -/
def extract {Stmt : Type} (render : Stmt → Body) (hash : Stmt → Nat) (E : Env Stmt) : Bundle :=
  fun k => (E.stmt k).map fun T => { render := render T, hash := hash T, trusted := E.trusted k }

end SpliceModel
