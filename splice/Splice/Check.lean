/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Apply
import Splice.Sha256
import Splice.StdMacros

/-!
# Checking a document

`check` runs `plan` and reports, without writing (DESIGN §10.3):

- stale items, with `--diff` showing what would change;
- broken references: keys with no entry in the bundle, including those of
  `\leancheck` and blueprint `\lean{…}`;
- untrusted results: entries that depend on `sorry`, use an axiom outside
  `allowed_axioms`, or have untrusted constants in their cone;
- everything `apply` reports (hand edits, orphaned slots, missing files);
- drift, for `\leancheck`;
- macros that generated content uses and nothing defines (`macroDiags`).
-/

namespace Splice

/-- Every key an item refers to. -/
def Item.allKeys (it : Item) : Array String :=
  match it.kind with
  | .check => it.keys
  | .index | .leanok => #[]
  | _ => #[it.key]

/-- The `stmt=` and `sig=` values for a `\leancheck` of `keys`: the first 12
hexadecimal digits of the key's hashes, or, for several keys, of the hash of
their hashes joined by commas. `none` if a key is missing or has no hash. -/
def checkHashes (bundle : Bundle) (keys : Array String) : Option (String × String) := do
  let es ← keys.mapM bundle.find?
  let stmts ← es.mapM (·.stmtHash)
  let sigs ← es.mapM (·.sigHash)
  let short (hs : Array String) : String :=
    let h := if hs.size == 1 then hs[0]! else Sha256.hexOf (",".intercalate hs.toList)
    String.ofList (h.toList.take 12)
  return (short stmts, short sigs)

/-- Problems with an entry's trust, checked against `allowed` axioms. -/
def trustProblems (allowed : Array String) (e : Entry) : Array String := Id.run do
  let mut out := #[]
  if e.usesSorry then out := out.push s!"{e.key} depends on sorry"
  -- `sorryAx` is reported above, as `sorry`.
  let bad := e.axioms.filter (fun a => a != "sorryAx" && !allowed.contains a)
  unless bad.isEmpty do
    out := out.push s!"{e.key} uses axioms outside the allowed ones: {", ".intercalate bad.toList}"
  let mut cone : Array String := #[]
  for n in e.untrusted do
    let why := ((e.reasons.find? (·.1 == n)).map (·.2)).getD #[]
    -- An axiom in the cone is fine if it is allowed.
    let why := why.filter (fun w => !(w == "axiom" && allowed.contains n))
    if !why.isEmpty || e.reasons.isEmpty then
      cone := cone.push (if why.isEmpty then n else s!"{n} ({", ".intercalate why.toList})")
  unless cone.isEmpty do
    out := out.push s!"{e.key} has untrusted constants in its dependency cone: {", ".intercalate cone.toList}"
  return out

/-- Broken references, trust problems, drift and blueprint `\leanok`s. -/
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
          -- A blueprint `\lean{…}` without `\leanok` is work in progress, so
          -- only `\leanok` nodes are checked for trust (below).
          unless it.name == "lean" do
            for p in trustProblems doc.cfg.allowedAxioms e do
              ds := ds.push (Diag.err "untrusted" loc p)
          -- Faithfulness (DESIGN §18.4): a typeset rendering that does not
          -- read back as its statement.
          if (it.kind == .block || it.kind == .inline) && it.live then
            let view := itemView doc.cfg it
            for p in ((e.validation.find? (·.1 == view)).map (·.2)).getD #[] do
              -- A metavariable that does not tell the reader a variable's type
              -- (`latex_style categories := unique` or `strict`) is an error.
              if p.startsWith "category: " then
                ds := ds.push (Diag.err "category" loc s!"{key} ({view}): {(p.drop 10).toString}")
              else
                ds := ds.push (Diag.warn "unfaithful-rendering" loc s!"{key} ({view}): {p}")
      -- Drift (DESIGN §10.3): the hashes recorded when the prose was checked.
      if it.kind == .check && it.name == "leancheck" then
        match it.opt? "stmt", checkHashes bundle it.keys with
        | some recorded, some (stmt, sig) =>
          let keys := ", ".intercalate it.keys.toList
          if recorded != stmt then
            ds := ds.push (Diag.err "drift" loc
              s!"the statement of {keys}, or something it depends on, has changed since the prose \
                was last checked against it (stmt={recorded}, now {stmt}).\n\
                Re-read the prose, then run: imprimatur accept {" ".intercalate it.keys.toList}")
          else if (it.opt? "sig").any (· != sig) then
            ds := ds.push (Diag.warn "sig-changed" loc
              s!"the signature of {keys} reads differently (binder names or notation), \
                but its meaning is unchanged; run imprimatur accept to record it")
        | some _, none =>
          if it.keys.all (bundle.find? · |>.isSome) then
            ds := ds.push (Diag.err "no-hash" loc
              s!"the bundle has no statement hash for {", ".intercalate it.keys.toList}; \
                rebuild it with imprimatur-export 0.2 or later")
        | none, _ => pure ()
    -- Blueprint (DESIGN §9.3): a node marked \leanok must not depend on sorry.
    for ok in f.scan.items.filter (·.kind == .leanok) do
      if ok.env == 0 then continue
      for it in f.scan.items.filter (fun i => i.name == "lean" && i.env == ok.env) do
        for key in it.keys do
          if let some e := bundle.find? key then
            unless (trustProblems doc.cfg.allowedAxioms e).isEmpty do
              ds := ds.push (Diag.err "leanok-untrusted" (f.src.locString ok.start)
                s!"this node is marked \\leanok, but {key} is not trusted: \
                  {"; ".intercalate (trustProblems doc.cfg.allowedAxioms e).toList}")
  -- Comparator manifests (DESIGN §10.5).
  for m in doc.manifests do
    let allowed := m.permittedAxioms.getD doc.cfg.allowedAxioms
    for key in m.theorems do
      match bundle.find? key with
      | none => ds := ds.push (Diag.err "broken-ref" m.path s!"{key} has no entry in the bundle")
      | some e =>
        for p in trustProblems allowed e do
          ds := ds.push (Diag.err "untrusted" m.path p)
  return ds

/-- Commands whose argument names a macro they define. -/
def macroDefiners : List String :=
  Scan.definingCommands ++ ["DeclareMathOperator", "DeclarePairedDelimiter", "DeclareMathSymbol",
    "newif", "newlength", "newcounter", "chardef", "mathchardef"]

/-- The macros a piece of TeX defines: the name after each defining command,
as in `\newcommand{\x}`, `\newcommand*\x`, `\def\x` or
`\DeclareMathOperator{\x}`, with its backslash. Commented-out definitions
count too: the check errs towards silence. -/
def definedMacros (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let letters (i : Nat) : Nat := Id.run do
    let mut j := i
    while j < cs.size && cs[j]!.isAlpha do j := j + 1
    return j
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! != '\\' then
      i := i + 1
      continue
    let j := letters (i + 1)
    if j == i + 1 then
      i := i + 2
      continue
    let name := String.ofList (cs.extract (i + 1) j).toList
    if macroDefiners.contains name then
      let mut k := j
      while k < cs.size && (cs[k]! == ' ' || cs[k]! == '*' || cs[k]! == '{' || cs[k]! == '\n') do
        k := k + 1
      if k < cs.size && cs[k]! == '\\' then
        let e := letters (k + 1)
        if e > k + 1 then out := out.push ("\\" ++ String.ofList (cs.extract (k + 1) e).toList)
    i := j
  return out

/-- The files a piece of TeX loads, as written: the arguments of `\input`,
`\include`, `\usepackage` and `\RequirePackage` (each of a comma-separated
list). The caller tries them as files, with `.tex` or `.sty` added. -/
def loadedFiles (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for cmd in ["\\input", "\\include", "\\usepackage", "\\RequirePackage"] do
    for part in (s.splitOn cmd).drop 1 do
      let part := part.trimAsciiStart.toString
      -- Options of `\usepackage[…]{…}`.
      let part := if part.startsWith "[" then ((part.splitOn "]").drop 1 |> "]".intercalate) else part
      let part := part.trimAsciiStart.toString
      if part.startsWith "{" then
        let arg := ((part.drop 1).toString.splitOn "}")[0]!
        for a in arg.splitOn "," do
          let a := a.trimAscii.toString
          unless a.isEmpty do out := out.push a
  return out

/-- Macros that generated content uses and nothing defines (DESIGN §10.3): not
TeX, LaTeX, amsmath, amssymb, mathpartir or imprimatur.sty (`stdMacros`), not
a file of the document, not one of `extra` (the paper's own packages), and
not listed in `known_macros`. A warning, once per macro, where it is first
used in a typeset block. -/
def macroDiags (doc : Doc) (bundle : Bundle) (extra : Array String) : Array Diag := Id.run do
  -- Sorted, for binary search (the splicer imports nothing beyond core).
  let mut known : Array String := (stdMacros.map ("\\" ++ ·)) ++ doc.cfg.knownMacros ++ extra
  for f in doc.files do
    known := known ++ definedMacros (String.ofList f.src.chars.toList)
  let sorted := known.qsort (· < ·)
  let isKnown (m : String) : Bool := (sorted.binSearch m (· < ·)).isSome
  let mut seen : Array String := #[]
  let mut ds := #[]
  for f in doc.files do
    for it in f.scan.items do
      unless (it.kind == .block || it.kind == .inline) && it.live do continue
      let some e := bundle.find? it.key | continue
      for m in e.macros do
        if isKnown m || seen.contains m then continue
        seen := seen.push m
        ds := ds.push (Diag.warn "undefined-macro" (f.src.locString it.start)
          s!"{m}, in the generated content of {it.key}, is defined by no file of the document, \
            nor by LaTeX, amsmath, amssymb, mathpartir or imprimatur.sty. Define it, or, if a \
            package defines it, list it in known_macros in imprimatur.toml.")
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
