/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Apply

/-!
# Checking a document

`check` runs `plan` and reports, without writing (DESIGN §10.3):

- stale items, with `--diff` showing what would change;
- broken references: keys with no entry in the bundle, including those of
  `\leancheck` and blueprint `\lean{…}`;
- untrusted results: entries that depend on `sorry`, use an axiom outside
  `allowed_axioms`, or have untrusted constants in their cone;
- everything `apply` reports (hand edits, orphaned slots, missing files).

Drift and undefined macros come in later milestones (PLAN M3, M6).
-/

namespace Splice

/-- Every key an item refers to. -/
def Item.allKeys (it : Item) : Array String :=
  match it.kind with
  | .check => it.keys
  | .index => #[]
  | _ => #[it.key]

/-- Broken references and trust problems. -/
def audit (doc : Doc) (bundle : Bundle) : Array Diag := Id.run do
  let mut ds := #[]
  for f in doc.files do
    for it in f.scan.items do
      let loc := f.src.locString it.start
      for key in it.allKeys do
        match bundle.find? key with
        | none =>
          -- Blocks, inline and refs already report missing keys through `plan`.
          if it.kind == .check then
            ds := ds.push (Diag.err "broken-ref" loc s!"{key} has no entry in the bundle")
        | some e =>
          if e.usesSorry then
            ds := ds.push (Diag.err "untrusted" loc s!"{key} depends on sorry")
          -- `sorryAx` is reported above, as `sorry`.
          let bad := e.axioms.filter (fun a => a != "sorryAx" && !doc.cfg.allowedAxioms.contains a)
          unless bad.isEmpty do
            ds := ds.push (Diag.err "untrusted" loc
              s!"{key} uses axioms outside allowed_axioms: {", ".intercalate bad.toList}")
          unless e.untrusted.isEmpty do
            ds := ds.push (Diag.err "untrusted" loc
              s!"{key} has untrusted constants in its dependency cone: \
                {", ".intercalate e.untrusted.toList}")
  return ds

/-- A line diff of `a` against `b` (longest common subsequence), as lines
prefixed with `" "`, `"-"` or `"+"`. -/
def lineDiff (a b : String) : Array String := Id.run do
  let lines (t : String) : Array String :=
    let ls := (toLf t).splitOn "\n" |>.toArray
    if ls.back? == some "" then ls.pop else ls
  let xs := lines a
  let ys := lines b
  let n := xs.size
  let m := ys.size
  -- lcs[i][j] = length of an LCS of xs[i:] and ys[j:], stored row-major.
  let mut lcs : Array Nat := Array.replicate ((n + 1) * (m + 1)) 0
  for ii in [0:n] do
    let i := n - 1 - ii
    for jj in [0:m] do
      let j := m - 1 - jj
      let v :=
        if xs[i]! == ys[j]! then lcs[(i + 1) * (m + 1) + j + 1]! + 1
        else max lcs[(i + 1) * (m + 1) + j]! lcs[i * (m + 1) + j + 1]!
      lcs := lcs.set! (i * (m + 1) + j) v
  let mut out := #[]
  let mut i := 0
  let mut j := 0
  while i < n || j < m do
    if i < n && j < m && xs[i]! == ys[j]! then
      out := out.push (" " ++ xs[i]!); i := i + 1; j := j + 1
    else if i < n && (j == m || lcs[(i + 1) * (m + 1) + j]! ≥ lcs[i * (m + 1) + j + 1]!) then
      out := out.push ("-" ++ xs[i]!); i := i + 1
    else
      out := out.push ("+" ++ ys[j]!); j := j + 1
  return out

/-- The diagnostics for stale items. -/
def staleDiags (changes : Array Change) (diff : Bool) : Array Diag :=
  changes.map fun ch =>
    let what :=
      if ch.contentChanged then s!"the generated content of {ch.key} is out of date"
      else s!"{ch.key} has no up-to-date sum= checksum"
    let body :=
      if diff && ch.contentChanged then
        what ++ "\n--- current\n+++ regenerated\n" ++ "\n".intercalate (lineDiff ch.old ch.new).toList
      else what
    Diag.err "stale" ch.loc body

/-- Sort diagnostics into document order: by file (in the order the document
reaches them), then line, then column. Diagnostics without a location come
first. -/
def sortDiags (doc : Doc) (ds : Array Diag) : Array Diag :=
  let key (d : Diag) : Nat × Nat × Nat :=
    match d.loc.splitOn ":" with
    | [p, l, c] =>
      let fi := (doc.files.findIdx? (·.src.path == p)).getD doc.files.size
      (fi + 1, l.toNat!, c.toNat!)
    | _ => (0, 0, 0)
  let le (a b : Diag) : Bool :=
    let (x1, y1, z1) := key a
    let (x2, y2, z2) := key b
    x1 < x2 || (x1 == x2 && (y1 < y2 || (y1 == y2 && z1 ≤ z2)))
  -- A stable sort, so diagnostics at one place keep their order.
  (ds.toList.mergeSort le).toArray

end Splice
