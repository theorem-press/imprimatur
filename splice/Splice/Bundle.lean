/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# The bundle

imprimatur is two programs. The extractor runs inside Lean and reads the
development's environment; the splicer edits TeX and never sees Lean. All
that passes between them is the bundle, a JSON file, and this module is its
type: the file is the JSON of a `Bundle (Image TeX) Verdict`, and nothing else.
The source is `bundle/Bundle.lean`, copied into both packages
(`extract/Imprimatur/Bundle.lean`, `splice/Splice/Bundle.lean`); the shipped
packages have no dependencies, and the lint checks that the copies agree.

An entry is what the bundle says of a key: what the key names, its
statement, and its proof. The statement and the proof are not in the file,
and could not be: the splicer cannot read Lean. The file holds their images.
Of the statement, the hash that names it and the TeX that shows it
(`Image`); of the proof, the verdict on it: no `sorry`, which axioms, which
untrusted constants (`Verdict`). So an entry is parametrised by how the two
are represented, `Entry σ π`. The file is `Entry (Image TeX) Verdict`. The model of
the splicer in `about/lean`, which proves what `check` guarantees, is `Entry`
at a simpler image, and a bit.

The TeX in an image is a parameter, `Image τ`: in the file `τ` is TeX; in
the model it is TeX with the slots already parsed, which is what the
splicer makes of it. The slot parser is the step between the two, and it
is property-tested rather than proved.

The section *Meaning* says when an entry is true of an environment, which is
what the splicer's guarantees rest on: every claim an image makes is true of
the statement, so the splicer can take the file for the environment. An
image may say less than the environment knows (a hash it could not compute),
never something false; where it is silent, the splicer reports the silence
rather than trusting it.
-/

namespace Imprimatur

/-- A key: what a document cites, the name of a constant or the title of a
group. -/
abbrev Key := String

/-- The name of a view: `math`, `prose`, `rules`, `math|def=`, … -/
abbrev View := String

/-- TeX source. -/
abbrev TeX := String

/-- A SHA-256, as 64 hexadecimal digits. -/
abbrev Hash := String

/-! ## What a key names -/

/-- What a key names. -/
inductive Kind where
  /-- a proposition, with a proof -/
  | «theorem»
  /-- a proposition, assumed -/
  | «axiom»
  /-- a constant with a body, which its equations state -/
  | definition
  /-- a definition registered as an instance -/
  | «instance»
  /-- a constant whose body is hidden -/
  | «opaque»
  /-- a type or predicate, given by its constructors -/
  | «inductive»
  /-- an inductive type with one constructor, given by its fields -/
  | «structure»
  /-- a constructor of an inductive type -/
  | constructor
  /-- the recursor of an inductive type -/
  | recursor
  /-- a quotient primitive -/
  | quotient
  /-- a title, named in the notation module: a group of rules or a display -/
  | group
  /-- a definition in a challenge module, which a solution must match -/
  | challenge
  deriving DecidableEq, Repr

/-- The kinds, with their names in the file. -/
def Kind.all : List (Kind × String) :=
  [(.theorem, "theorem"), (.axiom, "axiom"), (.definition, "definition"),
   (.instance, "instance"), (.opaque, "opaque"), (.inductive, "inductive"),
   (.structure, "structure"), (.constructor, "constructor"), (.recursor, "recursor"),
   (.quotient, "quotient"), (.group, "group"), (.challenge, "challenge")]

/-- A kind's name in the file. -/
def Kind.toString (k : Kind) : String :=
  ((Kind.all.find? (·.1 == k)).map (·.2)).getD "definition"

instance : ToString Kind := ⟨Kind.toString⟩

/-- The kind with this name. -/
def Kind.ofString? (s : String) : Option Kind :=
  (Kind.all.find? (·.2 == s)).map (·.1)

/-- Where a declaration is. -/
structure Source where
  /-- the file, relative to the Lean project root -/
  path : String
  /-- the line, from 1 -/
  line : Nat
  deriving DecidableEq, Repr

/-- A declaration, as a key names it. -/
structure Decl where
  /-- what it is -/
  kind : Kind
  /-- its name, or a group's title -/
  name : String
  /-- where it is -/
  source : Option Source := none
  /-- its docstring -/
  doc : Option String := none
  deriving DecidableEq, Repr

/-! ## Entries and bundles -/

/-- An entry: what a bundle says of a key. What the key names, its statement,
as `σ`, and the verdict on its proof, as `π`. -/
structure Entry (σ π : Type) where
  /-- what the key names -/
  decl : Decl
  /-- its statement -/
  statement : σ
  /-- the verdict on its proof -/
  verdict : π
  deriving DecidableEq, Repr

/-- An entry with its statement and verdict mapped. -/
def Entry.map {σ σ' π π' : Type} (f : σ → σ') (g : π → π') (e : Entry σ π) : Entry σ' π' :=
  { e with statement := f e.statement, verdict := g e.verdict }

theorem Entry.map_id {σ π : Type} (e : Entry σ π) : e.map id id = e := rfl

theorem Entry.map_map {σ σ' σ'' π π' π'' : Type} (f : σ → σ') (f' : σ' → σ'')
    (g : π → π') (g' : π' → π'') (e : Entry σ π) :
    (e.map f g).map f' g' = e.map (f' ∘ f) (g' ∘ g) := rfl

/-- Who made a bundle. -/
structure Producer where
  /-- the tool -/
  tool : String
  /-- its version -/
  version : String
  /-- the Lean toolchain -/
  lean : Option String := none
  /-- the project -/
  project : Option String := none
  deriving DecidableEq, Repr

/-- A bundle: an entry for each key a document cites. -/
structure Bundle (σ π : Type) where
  /-- who made it -/
  producer : Producer
  /-- the entries, sorted by key -/
  entries : Array (Key × Entry σ π)
  deriving Repr

/-- The entry of a key. -/
def Bundle.find? {σ π : Type} (b : Bundle σ π) (k : Key) : Option (Entry σ π) :=
  (b.entries.find? (·.1 == k)).map (·.2)

/-- A bundle with every entry's statement and verdict mapped. -/
def Bundle.map {σ σ' π π' : Type} (f : σ → σ') (g : π → π') (b : Bundle σ π) : Bundle σ' π' :=
  { b with entries := b.entries.map fun (k, e) => (k, e.map f g) }

/-! ## The images

A statement is a term of Lean: a theorem's proposition, a definition's
signature with the equations that define it, an inductive type's
constructors. The file carries two images of it. The hash *names* it: two
statements with one hash are one statement, as far as a document can tell.
The views *show* it: each is the statement rendered by the paper's notation.
Of the proof the file carries only a verdict. -/

/-- A statement as a document may carry it: the hash that names it, and the
renderings that show it, as `τ`. -/
structure Image (τ : Type) where
  /-- the hash of the statement's meaning: the statement, with every
  definition it depends on; none when the dependencies could not be
  followed -/
  stmtHash : Option Hash := none
  /-- the hash of the statement as written, the `lean` view; none for a
  title -/
  sigHash : Option Hash := none
  /-- the renderings, by view -/
  views : Array (View × τ) := #[]
  /-- the views that could not be rendered, and why -/
  errors : Array (View × String) := #[]
  /-- for each view, the formulas in it that do not read back as the
  statement -/
  validation : Array (View × Array String) := #[]
  /-- the TeX macros the renderings use -/
  macros : Array String := #[]
  deriving DecidableEq, Repr

/-- The rendering in a view. -/
def Image.view? {τ : Type} (i : Image τ) (v : View) : Option τ :=
  (i.views.find? (·.1 == v)).map (·.2)

/-- Why a view could not be rendered. -/
def Image.error? {τ : Type} (i : Image τ) (v : View) : Option String :=
  (i.errors.find? (·.1 == v)).map (·.2)

/-- A rendering found is one of the image's. -/
theorem Image.view?_mem {τ : Type} {i : Image τ} {v : View} {t : τ} (h : i.view? v = some t) :
    (v, t) ∈ i.views := by
  unfold Image.view? at h
  match hf : i.views.find? (·.1 == v) with
  | none => simp [hf] at h
  | some p =>
    have hm := Array.mem_of_find?_eq_some hf
    have hp := Array.find?_some hf
    simp only [hf, Option.map_some, Option.some.injEq] at h
    simp only [beq_iff_eq] at hp
    have : p = (v, t) := Prod.ext hp h
    exact this ▸ hm

/-- The formulas of a view that do not read back; none when every one does. -/
def Image.problems {τ : Type} (i : Image τ) (v : View) : Array String :=
  ((i.validation.find? (·.1 == v)).map (·.2)).getD #[]

/-- What a statement depends on, beyond the trusted modules. -/
structure Cone where
  /-- how many constants -/
  size : Nat
  /-- the untrusted ones -/
  untrusted : Array String := #[]
  /-- why each is untrusted: `sorry`, `axiom`, `partial`, `unsafe` -/
  reasons : Array (String × Array String) := #[]
  deriving DecidableEq, Repr

/-- The untrusted constants that are a problem under the permitted axioms:
an axiom among them is no problem. A cone without reasons is from an older
extractor, and every untrusted constant of it is a problem. -/
def Cone.problems (permitted : Array String) (c : Cone) : Array String :=
  c.untrusted.filter fun n =>
    let why := ((c.reasons.find? (·.1 == n)).map (·.2)).getD #[]
    let why := why.filter fun w => !(w == "axiom" && permitted.contains n)
    !why.isEmpty || c.reasons.isEmpty

/-- The verdict on a proof: whether Lean accepted it, and on what. -/
structure Verdict where
  /-- the axioms the proof uses -/
  axioms : Array String := #[]
  /-- whether it depends on `sorry` -/
  usesSorry : Bool := false
  /-- what the statement depends on -/
  cone : Option Cone := none
  deriving DecidableEq, Repr

/-- Trusted under the permitted axioms: no `sorry`, no other axiom, and no
problem in the cone. -/
def Verdict.trusted (permitted : Array String) (v : Verdict) : Bool :=
  !v.usesSorry && v.axioms.all (fun a => a == "sorryAx" || permitted.contains a) &&
    (v.cone.map fun c => (c.problems permitted).isEmpty).getD true

/-! ## Meaning

A bundle is about an environment, which the splicer never sees. A *world* is
the environment as the extractor presents it: what each key states and
whether its proof is trusted; how a statement is hashed and rendered; and
when TeX reads back as a statement, up to what the notation makes invisible
(DESIGN §18.3). A world has statements and verdicts but no proofs: an image
is a function of the statement alone, so nothing in a bundle depends on how
a theorem was proved, only on whether it was. -/

/-- A world: an environment, as the extractor presents it, rendered as `τ`. -/
structure World (τ : Type) where
  /-- statements -/
  Stmt : Type
  /-- what a key names -/
  kind : Key → Kind
  /-- what a key states, if it is declared -/
  stmt : Key → Option Stmt
  /-- whether a key's proof is trusted -/
  trusted : Key → Bool
  /-- the hash of a statement's meaning -/
  hash : Stmt → Hash
  /-- the hash of a statement as written -/
  sig : Stmt → Hash
  /-- a statement rendered in a view, when the view applies -/
  render : View → Stmt → Option τ
  /-- when a rendering reads back as a statement -/
  Reads : τ → Stmt → Prop

/-- `i` is an image of `S`: each hash it has is `S`'s, each view it has is a
rendering of `S`, and a view it validates reads back as `S`. -/
structure Image.Of {τ : Type} (W : World τ) (S : W.Stmt) (i : Image τ) : Prop where
  /-- the statement hash is of `S`'s meaning -/
  stmtHash : ∀ h, i.stmtHash = some h → h = W.hash S
  /-- the signature hash is of `S` as written -/
  sigHash : ∀ h, i.sigHash = some h → h = W.sig S
  /-- each view is `S` rendered -/
  views : ∀ v t, (v, t) ∈ i.views → W.render v S = some t
  /-- a view with no problems reads back as `S` -/
  faithful : ∀ v t, (v, t) ∈ i.views → i.problems v = #[] → W.Reads t S

/-- An entry is true of a key when the key names what it says, its image is
of the key's statement, and its verdict, read by `trusted`, is the world's. -/
structure Entry.True {τ π : Type} (W : World τ) (trusted : π → Bool) (k : Key)
    (e : Entry (Image τ) π) : Prop where
  /-- the kind is the key's -/
  kind : e.decl.kind = W.kind k
  /-- the key states something, and the image is of it -/
  statement : ∃ S, W.stmt k = some S ∧ Image.Of W S e.statement
  /-- the verdict is the world's -/
  verdict : trusted e.verdict = W.trusted k

/-- A bundle is true of a world when the entry it gives for each key is. -/
def Bundle.True {τ π : Type} (W : World τ) (trusted : π → Bool) (b : Bundle (Image τ) π) : Prop :=
  ∀ k e, b.find? k = some e → Entry.True W trusted k e

/-- **The hash names the statement.** When hashes do not collide, images with
one statement hash are of one statement: prose checked against a statement,
and carrying its hash, faces that statement while the hash is the entry's. -/
theorem Image.Of.stmt_eq {τ : Type} {W : World τ} (hinj : ∀ S S', W.hash S = W.hash S' → S = S')
    {S S' : W.Stmt} {i i' : Image τ} (hi : Image.Of W S i) (hi' : Image.Of W S' i')
    {h : Hash} (h₁ : i.stmtHash = some h) (h₂ : i'.stmtHash = some h) : S = S' :=
  hinj S S' ((hi.stmtHash h h₁).symm.trans (hi'.stmtHash h h₂))

/-- **A view shows the statement.** In a true bundle, the rendering an entry
has for a view is the key's statement rendered, and reads back as it when
the view has no problems. -/
theorem Bundle.True.view {τ π : Type} {W : World τ} {trusted : π → Bool} {b : Bundle (Image τ) π}
    (hb : b.True W trusted) {k : Key} {e : Entry (Image τ) π} (he : b.find? k = some e)
    {v : View} {t : τ} (hv : e.statement.view? v = some t) :
    ∃ S, W.stmt k = some S ∧ W.render v S = some t ∧
      (e.statement.problems v = #[] → W.Reads t S) :=
  let ⟨S, hS, hi⟩ := (hb k e he).statement
  let hm := Image.view?_mem hv
  ⟨S, hS, hi.views v t hm, hi.faithful v t hm⟩

/-! ## The file

The JSON of a bundle, written so that it is byte-identical across runs and
toolchains (DESIGN §8): keys sorted, two-space indentation, empty arrays and
objects on one line, arrays of scalars on one line, and a final newline.
Reading checks the rules of `schema/bundle.schema.json`. -/

/-- The schema this module writes and reads. -/
def bundleSchema : String := "imprimatur-bundle/1"

open Lean (Json)

private def strs (xs : Array String) : Json := .arr (xs.map .str)

private def strMap (kvs : Array (String × String)) : Json :=
  Json.mkObj (kvs.toList.map fun (k, v) => (k, .str v))

private def opt (k : String) : Option Json → List (String × Json)
  | some j => [(k, j)]
  | none => []

/-- The JSON of an entry. -/
def Entry.toJson (e : Entry (Image TeX) Verdict) : Json :=
  let i := e.statement
  let v := e.verdict
  let validation := i.validation.filter (!·.2.isEmpty)
  Json.mkObj <|
    [("kind", .str e.decl.kind.toString), ("decl", .str e.decl.name)] ++
    opt "source" (e.decl.source.map fun s =>
      Json.mkObj [("path", .str s.path), ("line", Lean.toJson s.line)]) ++
    opt "doc" (e.decl.doc.map .str) ++
    [("axioms", strs v.axioms), ("sorry", .bool v.usesSorry)] ++
    opt "cone" (v.cone.map fun c => Json.mkObj [
      ("size", Lean.toJson c.size), ("untrusted", strs c.untrusted),
      ("reasons", Json.mkObj (c.reasons.toList.map fun (n, ws) => (n, strs ws)))]) ++
    opt "stmtHash" (i.stmtHash.map .str) ++
    opt "sigHash" (i.sigHash.map .str) ++
    [("macros", strs i.macros), ("views", strMap i.views)] ++
    (if i.errors.isEmpty then [] else [("errors", strMap i.errors)]) ++
    (if validation.isEmpty then [] else
      [("validation", Json.mkObj (validation.toList.map fun (v, ps) => (v, strs ps)))])

/-- The JSON of a bundle. -/
def Bundle.toJson (b : Bundle (Image TeX) Verdict) : Json :=
  Json.mkObj [
    ("schema", .str bundleSchema),
    ("producer", Json.mkObj <|
      [("tool", .str b.producer.tool), ("version", .str b.producer.version)] ++
      opt "lean" (b.producer.lean.map .str) ++ opt "project" (b.producer.project.map .str)),
    ("entries", Json.mkObj (b.entries.toList.map fun (k, e) => (k, e.toJson)))]

/-- JSON as the file holds it: deterministic, and the same on every
toolchain. -/
partial def renderJson (j : Json) (indent : Nat := 0) : String :=
  let pad (n : Nat) := String.ofList (List.replicate n ' ')
  let scalar : Json → Bool
    | .arr _ | .obj _ => false
    | _ => true
  match j with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => if n.exponent == 0 then toString n.mantissa else n.toString
  | .str s => (Json.str s).compress
  | .arr xs =>
    if xs.isEmpty then "[]"
    else if xs.all scalar then
      "[" ++ ", ".intercalate (xs.map (renderJson ·)).toList ++ "]"
    else
      "[\n" ++ ",\n".intercalate (xs.map fun x => pad (indent + 2) ++ renderJson x (indent + 2)).toList ++
        "\n" ++ pad indent ++ "]"
  | .obj kvs =>
    let kvs := kvs.toArray
    if kvs.isEmpty then "{}"
    else
      "{\n" ++ ",\n".intercalate (kvs.map fun (k, v) =>
        pad (indent + 2) ++ (Json.str k).compress ++ ": " ++ renderJson v (indent + 2)).toList ++
        "\n" ++ pad indent ++ "}"

/-- The text of a bundle's file. -/
def Bundle.render (b : Bundle (Image TeX) Verdict) : String :=
  renderJson b.toJson ++ "\n"

private def field (where_ : String) (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"{where_}: missing field '{k}'"

private def str (where_ : String) (j : Json) : Except String String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"{where_} must be a string"

private def strsOf (where_ : String) (j : Json) : Except String (Array String) :=
  match j.getArr? with
  | .ok xs => xs.mapM (str s!"each element of {where_}")
  | .error _ => .error s!"{where_} must be an array"

private def strMapOf (where_ : String) (j : Json) : Except String (Array (String × String)) :=
  match j.getObj? with
  | .ok kvs => kvs.toArray.mapM fun (k, v) => do return (k, ← str s!"{where_}.{k}" v)
  | .error _ => .error s!"{where_} must be an object"

private def isRelative (p : String) : Bool :=
  !(p.startsWith "/" || p.startsWith "~" || p.startsWith "\\" ||
    (p.length ≥ 2 && (p.toList.getD 1 ' ') == ':'))

private def optional (j : Json) (k : String) {α : Type} (read : Json → Except String α) :
    Except String (Option α) :=
  match j.getObjVal? k with
  | .ok v => read v |>.map some
  | .error _ => .ok none

private def hashOf (where_ : String) (j : Json) : Except String Hash :=
  match j.getStr? with
  | .ok h =>
    if h.length == 64 && h.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then .ok h
    else .error s!"{where_} must be 64 hexadecimal digits"
  | .error _ => .error s!"{where_} must be a string"

private def entryOfJson (key : String) (j : Json) : Except String (Entry (Image TeX) Verdict) := do
  let w := s!"entries.{key}"
  let kindName ← str s!"{w}.kind" (← field w j "kind")
  let some kind := Kind.ofString? kindName
    | throw s!"{w}.kind must be one of {", ".intercalate (Kind.all.map (·.2))}, not {repr kindName}"
  let name ← str s!"{w}.decl" (← field w j "decl")
  let views ← strMapOf s!"{w}.views" (← field w j "views")
  let source ← optional j "source" fun s => do
    let path ← str s!"{w}.source.path" (← field s!"{w}.source" s "path")
    unless isRelative path do throw s!"{w}.source.path must be relative, not {repr path}"
    let line ← match (← field s!"{w}.source" s "line").getNat? with
      | .ok n => if n ≥ 1 then pure n else throw s!"{w}.source.line must be at least 1"
      | .error _ => throw s!"{w}.source.line must be a natural number"
    pure { path, line : Source }
  let doc ← optional j "doc" (str s!"{w}.doc")
  let axioms ← (optional j "axioms" (strsOf s!"{w}.axioms")).map (·.getD #[])
  let usesSorry ← (optional j "sorry" fun s => match s.getBool? with
    | .ok b => pure b
    | .error _ => throw s!"{w}.sorry must be a boolean").map (·.getD false)
  let cone ← optional j "cone" fun c => do
    let size ← match (← field s!"{w}.cone" c "size").getNat? with
      | .ok n => pure n
      | .error _ => throw s!"{w}.cone.size must be a natural number"
    let untrusted ← strsOf s!"{w}.cone.untrusted" (← field s!"{w}.cone" c "untrusted")
    let reasons ← (optional c "reasons" fun r => match r.getObj? with
      | .ok kvs => kvs.toArray.mapM fun (k, v) => do return (k, ← strsOf s!"{w}.cone.reasons.{k}" v)
      | .error _ => throw s!"{w}.cone.reasons must be an object").map (·.getD #[])
    pure { size, untrusted, reasons : Cone }
  let stmtHash ← optional j "stmtHash" (hashOf s!"{w}.stmtHash")
  let sigHash ← optional j "sigHash" (hashOf s!"{w}.sigHash")
  let errors ← (optional j "errors" (strMapOf s!"{w}.errors")).map (·.getD #[])
  let validation ← (optional j "validation" fun v => match v.getObj? with
    | .ok kvs => kvs.toArray.mapM fun (k, ps) => do return (k, ← strsOf s!"{w}.validation.{k}" ps)
    | .error _ => throw s!"{w}.validation must be an object").map (·.getD #[])
  let macros ← (optional j "macros" (strsOf s!"{w}.macros")).map (·.getD #[])
  return {
    decl := { kind, name, source, doc },
    statement := { stmtHash, sigHash, views, errors, validation, macros },
    verdict := { axioms, usesSorry, cone } }

/-- A bundle read from the text of its file, checked against the schema's
rules. The producer's fields are taken as they come, so a bundle from a
tool that says less about itself still reads. -/
def Bundle.parse (text : String) : Except String (Bundle (Image TeX) Verdict) := do
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw s!"not valid JSON: {e}"
  let schema ← str "schema" (← field "the bundle" j "schema")
  unless schema == bundleSchema do
    throw s!"schema {repr schema} is not one this splicer reads ({bundleSchema})"
  let p ← field "the bundle" j "producer"
  let producer : Producer := {
    tool := ((optional p "tool" (str "producer.tool")).toOption.bind id).getD ""
    version := ((optional p "version" (str "producer.version")).toOption.bind id).getD ""
    lean := (optional p "lean" (str "producer.lean")).toOption.bind id
    project := (optional p "project" (str "producer.project")).toOption.bind id }
  let entries ← match (← field "the bundle" j "entries").getObj? with
    | .ok kvs => kvs.toArray.mapM fun (k, v) => do return (k, ← entryOfJson k v)
    | .error _ => throw "entries must be an object"
  return { producer, entries := entries.qsort (·.1 < ·.1) }

end Imprimatur
