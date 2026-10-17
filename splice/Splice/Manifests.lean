/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Splice.Config
import Splice.Diag

/-!
# Comparator manifests

A comparator manifest (DESIGN §10.5) names theorems that a solution module
proves against a challenge module's statement, with the axioms they may use:

```json
{ "challenge_module": "ComparatorChallenges.PartitionPrinciple",
  "solution_module": "OAI.SetTheory.PartitionPrinciple.Main",
  "theorem_names": ["OAI.…exists_model_partitionPrinciple_without_choice"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"] }
```

Each theorem becomes a check-only key, checked against the manifest's
`permitted_axioms` instead of `allowed_axioms`. The solution modules are
added to the extractor's imports. A document may also use `KEY@challenge`,
the challenge module's statement of the theorem.
-/

namespace Splice

open Lean (Json)

/-- A comparator manifest. -/
structure Manifest where
  /-- Its path, relative to the project root. -/
  path : String
  /-- The module holding the challenge statements. -/
  challengeModule : Option String := none
  /-- The module holding the proofs. -/
  solutionModule : Option String := none
  /-- The theorems it audits. -/
  theorems : Array String := #[]
  /-- The axioms those theorems may use, if the manifest says. -/
  permittedAxioms : Option (Array String) := none
  deriving Repr

/-- Whether `name` matches `pattern`, where `*` matches any run of characters. -/
partial def globMatch (pattern name : String) : Bool :=
  go pattern.toList name.toList
where
  go : List Char → List Char → Bool
    | [], [] => true
    | '*' :: ps, cs => go ps cs || (match cs with | _ :: cs' => go ('*' :: ps) cs' | [] => false)
    | p :: ps, c :: cs => p == c && go ps cs
    | _, _ => false

/-- The files matching a pattern relative to `root`. Only the last component
may contain `*`. -/
def expandGlob (root : System.FilePath) (pattern : String) : IO (Array String) := do
  let parts := pattern.splitOn "/"
  let dir := "/".intercalate parts.dropLast
  let filePat := parts.getLast?.getD ""
  if !(filePat.contains '*') then
    return if ← (root / pattern).pathExists then #[pattern] else #[]
  let d := if dir.isEmpty then root else root / dir
  unless ← d.isDir do return #[]
  let mut out := #[]
  for e in ← d.readDir do
    if globMatch filePat e.fileName then
      out := out.push (if dir.isEmpty then e.fileName else dir ++ "/" ++ e.fileName)
  return out.qsort (· < ·)

/-- Read one manifest. -/
def Manifest.parse (path text : String) : Except String Manifest := do
  let j ← Json.parse text
  let str? (k : String) : Except String (Option String) :=
    match j.getObjVal? k with
    | .ok v => match v.getStr? with
      | .ok s => .ok (some s)
      | .error _ => .error s!"{k} must be a string"
    | .error _ => .ok none
  let strs? (k : String) : Except String (Option (Array String)) :=
    match j.getObjVal? k with
    | .ok v => match v.getArr? with
      | .ok xs => some <$> xs.mapM fun x => match x.getStr? with
        | .ok s => .ok s
        | .error _ => .error s!"{k} must hold strings"
      | .error _ => .error s!"{k} must be an array"
    | .error _ => .ok none
  let some theorems ← strs? "theorem_names" | throw "theorem_names is missing"
  return { path, theorems, challengeModule := ← str? "challenge_module",
           solutionModule := ← str? "solution_module",
           permittedAxioms := ← strs? "permitted_axioms" }

/-- Load the manifests named in the configuration. -/
def loadManifests (cfg : Config) (root : System.FilePath) : IO (Array Manifest × Array Diag) := do
  let mut ms := #[]
  let mut ds := #[]
  for pat in cfg.comparator do
    let files ← expandGlob root pat
    if files.isEmpty then
      ds := ds.push (Diag.warn "missing-manifest" "" s!"no comparator manifest matches {pat}")
    for f in files do
      match Manifest.parse f (← IO.FS.readFile (root / f)) with
      | .ok m => ms := ms.push m
      | .error e => ds := ds.push (Diag.err "bad-manifest" f e)
  return (ms, ds)

end Splice
