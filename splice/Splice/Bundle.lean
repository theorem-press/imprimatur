/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Splice.Version

/-!
# Reading bundles

A bundle (DESIGN §8) is the only input the splicer takes from Lean. This
module reads one and checks it against the rules of
`schema/bundle.schema.json`. The splicer uses `Lean.Data.Json` from Lean's
standard library, but nothing from the elaborator (DESIGN §4, constraint 2).
-/

namespace Splice

open Lean (Json)

/-- A source location of an entry. -/
structure SourceLoc where
  /-- Path relative to the Lean project root. -/
  path : String
  /-- 1-based line. -/
  line : Nat
  deriving Repr, BEq

/-- One entry of a bundle: what the splicer needs from DESIGN §8. -/
structure Entry where
  /-- The key. -/
  key : String
  /-- The declaration's kind. -/
  kind : String
  /-- Where the declaration is. -/
  source : Option SourceLoc := none
  /-- Axioms the declaration uses. -/
  axioms : Array String := #[]
  /-- Whether it depends on `sorry`. -/
  usesSorry : Bool := false
  /-- Untrusted constants in its dependency cone. -/
  untrusted : Array String := #[]
  /-- Why each untrusted constant is untrusted (`sorry`, `axiom`, `partial`,
  `unsafe`). -/
  reasons : Array (String × Array String) := #[]
  /-- The statement hash (DESIGN §7.7). -/
  stmtHash : Option String := none
  /-- The signature hash. -/
  sigHash : Option String := none
  /-- Rendered views. -/
  views : Array (String × String) := #[]
  /-- Views that failed to render, with the reason. -/
  errors : Array (String × String) := #[]
  deriving Repr

/-- A bundle. -/
structure Bundle where
  /-- Its entries, sorted by key. -/
  entries : Array Entry
  deriving Repr

/-- Look up an entry. -/
def Bundle.find? (b : Bundle) (key : String) : Option Entry :=
  b.entries.find? (·.key == key)

/-- Look up a rendered view. -/
def Entry.view? (e : Entry) (v : String) : Option String :=
  (e.views.find? (·.1 == v)).map (·.2)

/-- Look up why a view failed. -/
def Entry.error? (e : Entry) (v : String) : Option String :=
  (e.errors.find? (·.1 == v)).map (·.2)

private def field (where_ : String) (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"{where_}: missing field '{k}'"

private def str (where_ : String) (j : Json) : Except String String :=
  match j.getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"{where_} must be a string"

private def strs (where_ : String) (j : Json) : Except String (Array String) :=
  match j.getArr? with
  | .ok xs => xs.mapM (str s!"each element of {where_}")
  | .error _ => .error s!"{where_} must be an array"

private def strMap (where_ : String) (j : Json) : Except String (Array (String × String)) :=
  match j.getObj? with
  | .ok kvs => kvs.toArray.mapM fun ⟨k, v⟩ => do return (k, ← str s!"{where_}.{k}" v)
  | .error _ => .error s!"{where_} must be an object"

private def isRelative (p : String) : Bool :=
  !(p.startsWith "/" || p.startsWith "~" || p.startsWith "\\" ||
    (p.length ≥ 2 && (p.toList.getD 1 ' ') == ':'))

private def entry (key : String) (j : Json) : Except String Entry := do
  let w := s!"entries.{key}"
  let kind ← str s!"{w}.kind" (← field w j "kind")
  discard <| str s!"{w}.decl" (← field w j "decl")
  let views ← strMap s!"{w}.views" (← field w j "views")
  let source ← match j.getObjVal? "source" with
    | .error _ => pure none
    | .ok s => do
      let path ← str s!"{w}.source.path" (← field s!"{w}.source" s "path")
      unless isRelative path do throw s!"{w}.source.path must be relative, not {repr path}"
      let line ← match (← field s!"{w}.source" s "line").getNat? with
        | .ok n => if n ≥ 1 then pure n else throw s!"{w}.source.line must be at least 1"
        | .error _ => throw s!"{w}.source.line must be a natural number"
      pure (some { path, line })
  let axioms ← match j.getObjVal? "axioms" with
    | .ok a => strs s!"{w}.axioms" a
    | .error _ => pure #[]
  let usesSorry ← match j.getObjVal? "sorry" with
    | .ok s => match s.getBool? with
      | .ok b => pure b
      | .error _ => throw s!"{w}.sorry must be a boolean"
    | .error _ => pure false
  let untrusted ← match j.getObjVal? "cone" with
    | .ok c => strs s!"{w}.cone.untrusted" (← field s!"{w}.cone" c "untrusted")
    | .error _ => pure #[]
  let reasons ← match j.getObjVal? "cone" >>= (·.getObjVal? "reasons") with
    | .ok r => match r.getObj? with
      | .ok kvs => kvs.toArray.mapM fun ⟨k, v⟩ => do return (k, ← strs s!"{w}.cone.reasons.{k}" v)
      | .error _ => throw s!"{w}.cone.reasons must be an object"
    | .error _ => pure #[]
  let hash (k : String) : Except String (Option String) :=
    match j.getObjVal? k with
    | .ok v => match v.getStr? with
      | .ok h => if h.length == 64 && h.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then .ok (some h)
                 else .error s!"{w}.{k} must be 64 hexadecimal digits"
      | .error _ => .error s!"{w}.{k} must be a string"
    | .error _ => .ok none
  let stmtHash ← hash "stmtHash"
  let sigHash ← hash "sigHash"
  let errors ← match j.getObjVal? "errors" with
    | .ok e => strMap s!"{w}.errors" e
    | .error _ => pure #[]
  return { key, kind, source, axioms, usesSorry, untrusted, reasons, stmtHash, sigHash, views, errors }

/-- Read a bundle from JSON text. -/
def Bundle.parse (text : String) : Except String Bundle := do
  let j ← match Json.parse text with
    | .ok j => pure j
    | .error e => throw s!"not valid JSON: {e}"
  let schema ← str "schema" (← field "the bundle" j "schema")
  unless acceptedSchemas.contains schema do
    throw s!"schema {repr schema} is not one this splicer reads ({", ".intercalate acceptedSchemas})"
  discard <| field "the bundle" j "producer"
  let entries ← match (← field "the bundle" j "entries").getObj? with
    | .ok kvs => kvs.toArray.mapM fun ⟨k, v⟩ => entry k v
    | .error _ => throw "entries must be an object"
  return { entries := entries.qsort (·.key < ·.key) }

end Splice
