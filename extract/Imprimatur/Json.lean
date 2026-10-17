/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Deterministic JSON

Bundles must be byte-identical across runs and toolchains (DESIGN §8), so
they are written by this module rather than by `Lean.Json`'s printers: keys
are sorted, indentation is fixed, and nothing depends on the toolchain.
-/

namespace Imprimatur

open Lean (Json JsonNumber)

/-- A JSON value, with object fields in any order; `render` sorts them. -/
inductive J where
  /-- `null`. -/
  | null
  /-- A boolean. -/
  | bool (b : Bool)
  /-- A natural number. -/
  | num (n : Nat)
  /-- A string. -/
  | str (s : String)
  /-- An array. -/
  | arr (xs : Array J)
  /-- An object. -/
  | obj (kvs : Array (String × J))
  deriving Inhabited, BEq, Repr

/-- A JSON string literal. -/
def J.quote (s : String) : String :=
  (Json.str s).compress

/-- Render with two-space indentation, sorted keys and a final newline at
the top level only. Empty arrays and objects stay on one line, and arrays
of scalars are written on one line. -/
partial def J.render (j : J) (indent : Nat := 0) : String :=
  let pad (n : Nat) := String.ofList (List.replicate n ' ')
  match j with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => J.quote s
  | .arr xs =>
    if xs.isEmpty then "[]"
    else if xs.all (fun x => match x with | .arr _ | .obj _ => false | _ => true) then
      "[" ++ ", ".intercalate (xs.map (·.render)).toList ++ "]"
    else
      "[\n" ++ ",\n".intercalate (xs.map (fun x => pad (indent + 2) ++ x.render (indent + 2))).toList ++
        "\n" ++ pad indent ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then "{}"
    else
      let sorted := kvs.qsort (fun a b => a.1 < b.1)
      "{\n" ++ ",\n".intercalate (sorted.map (fun (k, v) =>
        pad (indent + 2) ++ J.quote k ++ ": " ++ v.render (indent + 2))).toList ++
        "\n" ++ pad indent ++ "}"

end Imprimatur
