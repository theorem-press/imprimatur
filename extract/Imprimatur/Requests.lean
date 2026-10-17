/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json

/-!
# Requests

`imprimatur-splice scan` writes `requests.json`: the keys and views a document
asks for, and the settings the extractor needs from `imprimatur.toml`. The
extractor reads only this file, so it needs no TOML parser.

```json
{
  "schema": "imprimatur-requests/1",
  "config": { "imports": ["MyPaper.Results"], "open_scoped": [],
              "strip_namespaces": ["ProjB"] },
  "requests": { "MyPaper.Results.theorem1_main": { "views": ["lean"] } }
}
```
-/

namespace Imprimatur

open Lean (Json Name)

/-- Settings from `imprimatur.toml` that the extractor uses. -/
structure Settings where
  /-- Modules to import. -/
  imports : Array Name := #[]
  /-- Namespaces whose scoped notation is active in the `lean` view. -/
  openScoped : Array Name := #[]
  /-- Namespaces left out of names in rendered views. -/
  stripNamespaces : Array Name := #[]
  /-- The line width of the `lean` view, in characters. 80 fits the text
  width of a one-column article in `\footnotesize` monospace. -/
  width : Nat := 80
  deriving Repr

/-- One requested key. -/
structure Request where
  /-- The key, as written in the TeX. -/
  key : String
  /-- The views asked for. -/
  views : Array String
  deriving Repr

/-- Turn a dotted string into a `Name`, component by component. -/
def toName (s : String) : Name :=
  s.splitOn "." |>.foldl (fun n c => Name.mkStr n c) .anonymous

private def strs (where_ : String) (j : Json) : Except String (Array String) := do
  let xs ← match j.getArr? with
    | .ok xs => pure xs
    | .error _ => throw s!"{where_} must be an array"
  xs.mapM fun x => match x.getStr? with
    | .ok s => pure s
    | .error _ => throw s!"{where_} must hold strings"

/-- Read a requests file. -/
def parseRequests (text : String) : Except String (Settings × Array Request) := do
  let j ← Json.parse text
  match j.getObjValAs? String "schema" with
  | .ok "imprimatur-requests/1" => pure ()
  | .ok s => throw s!"requests schema {repr s} is not imprimatur-requests/1"
  | .error _ => throw "the requests file has no schema"
  let cfg := (j.getObjVal? "config").toOption.getD (Json.mkObj [])
  let get (k : String) : Except String (Array String) :=
    match cfg.getObjVal? k with
    | .ok v => strs s!"config.{k}" v
    | .error _ => pure #[]
  let settings : Settings := {
    imports := (← get "imports").map toName
    openScoped := (← get "open_scoped").map toName
    stripNamespaces := (← get "strip_namespaces").map toName
    width := (cfg.getObjValAs? Nat "width").toOption.getD 80 }
  let reqs ← match (j.getObjVal? "requests").toOption.bind (·.getObj?.toOption) with
    | some kvs => kvs.toArray.mapM fun ⟨k, v⟩ => do
        let views ← match v.getObjVal? "views" with
          | .ok vs => strs s!"requests.{k}.views" vs
          | .error _ => pure #[]
        return { key := k, views }
    | none => throw "the requests file has no requests object"
  return (settings, reqs.qsort (·.key < ·.key))

end Imprimatur
