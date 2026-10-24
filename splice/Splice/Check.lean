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

open Imprimatur

/-- Every key an item refers to. -/
def Item.allKeys (it : Item) : Array String :=
  match it.kind with
  | .check => it.keys
  | .index | .leanok => #[]
  | _ => #[it.key]

/-- One of the hashes of each key's statement, picked by `pick`, in order;
`none` if a key is missing or has no such hash. -/
def hashesOf (bundle : Bundle (Image TeX) Verdict) (pick : Image TeX → Option Hash) :
    List String → Option (List String)
  | [] => some []
  | k :: ks => do
    let e ← bundle.find? k
    let h ← pick e.statement
    let hs ← hashesOf bundle pick ks
    return h :: hs

/-- What a `\leancheck` records of hashes: the first 12 hexadecimal digits
of the one hash, or, for several, of the hash of them joined by commas. -/
def shortOf (hs : List String) : String :=
  let h := match hs with
    | [h] => h
    | _ => Sha256.hexOf (",".intercalate hs)
  String.ofList (h.toList.take 12)

/-- The `stmt=` and `sig=` values for a `\leancheck` of `keys`: the first 12
hexadecimal digits of the key's hashes, or, for several keys, of the hash of
their hashes joined by commas. `none` if a key is missing or has no hash. -/
def checkHashes (bundle : Bundle (Image TeX) Verdict) (keys : Array String) :
    Option (String × String) := do
  let stmts ← hashesOf bundle (·.stmtHash) keys.toList
  let sigs ← hashesOf bundle (·.sigHash) keys.toList
  return (shortOf stmts, shortOf sigs)

/-- Problems with an entry's trust, checked against `allowed` axioms: none
exactly when `Verdict.trusted allowed` holds of its verdict. -/
def trustProblems (allowed : Array String) (key : String) (e : Entry (Image TeX) Verdict) :
    Array String :=
  let v := e.verdict
  let sorry_ := if v.usesSorry then #[s!"{key} depends on sorry"] else #[]
  -- `sorryAx` is reported above, as `sorry`.
  let bad := v.axioms.filter (fun a => a != "sorryAx" && !allowed.contains a)
  let axioms := if bad.isEmpty then #[] else
    #[s!"{key} uses axioms outside the allowed ones: {", ".intercalate bad.toList}"]
  let cone := match v.cone with
    | none => #[]
    | some c =>
      let cone := (c.problems allowed).map fun n =>
        let why := ((c.reasons.find? (·.1 == n)).map (·.2)).getD #[]
        -- An axiom in the cone is fine if it is allowed.
        let why := why.filter (fun w => !(w == "axiom" && allowed.contains n))
        if why.isEmpty then n else s!"{n} ({", ".intercalate why.toList})"
      if cone.isEmpty then #[] else
        #[s!"{key} has untrusted constants in its dependency cone: {", ".intercalate cone.toList}"]
  sorry_ ++ axioms ++ cone

/-- What auditing one key of an item finds: a broken reference (for a
check), trust problems (unless a blueprint `\lean`), and, for a typeset block
or inline item, formulas of its rendering that do not read back. -/
def auditKey (cfg : Config) (bundle : Bundle (Image TeX) Verdict) (it : Item) (loc key : String) :
    Array Diag :=
  match bundle.find? key with
  | none =>
    -- Blocks, inline and refs already report missing keys through `plan`.
    if it.kind == .check then #[Diag.err "broken-ref" loc s!"{key} has no entry in the bundle"] else #[]
  | some e =>
    -- A blueprint `\lean{…}` without `\leanok` is work in progress, so only
    -- `\leanok` nodes are checked for trust (`auditLeanok`).
    (if it.kind == .check && it.name == "lean" then #[] else
      (trustProblems cfg.allowedAxioms key e).map (Diag.err "untrusted" loc ·)) ++
    -- Faithfulness (DESIGN §18.4): a typeset rendering that does not read
    -- back as its statement.
    (if (it.kind == .block || it.kind == .inline) && it.live then
      let view := itemView cfg it
      (e.statement.problems view).map fun p =>
        -- A metavariable that does not tell the reader a variable's type
        -- (`latex_style categories := unique` or `strict`) is an error.
        if p.startsWith "category: " then Diag.err "category" loc s!"{key} ({view}): {(p.drop 10).toString}"
        else Diag.warn "unfaithful-rendering" loc s!"{key} ({view}): {p}"
    else #[])

/-- Drift (DESIGN §10.3): the hashes a `\leancheck` recorded when its prose
was checked, against the bundle's. -/
def driftDiags (bundle : Bundle (Image TeX) Verdict) (it : Item) (loc : String) : Array Diag :=
  if it.kind == .check && it.name == "leancheck" then
    match it.opt? "stmt", checkHashes bundle it.keys with
    | some recorded, some (stmt, sig) =>
      let keys := ", ".intercalate it.keys.toList
      if recorded != stmt then
        #[Diag.err "drift" loc
          s!"the statement of {keys}, or something it depends on, has changed since the prose \
            was last checked against it (stmt={recorded}, now {stmt}).\n\
            Re-read the prose, then run: imprimatur accept {" ".intercalate it.keys.toList}"]
      else if (it.opt? "sig").any (· != sig) then
        #[Diag.warn "sig-changed" loc
          s!"the signature of {keys} reads differently (binder names or notation), \
            but its meaning is unchanged; run imprimatur accept to record it"]
      else #[]
    | some _, none =>
      if it.keys.all (bundle.find? · |>.isSome) then
        #[Diag.err "no-hash" loc
          s!"the bundle has no statement hash for {", ".intercalate it.keys.toList}; \
            rebuild it with imprimatur-export 0.2 or later"]
      else #[]
    | none, _ => #[]
  else #[]

/-- What auditing one item finds: its keys', then its drift. -/
def auditItem (cfg : Config) (bundle : Bundle (Image TeX) Verdict) (f : SourceFile) (it : Item) :
    Array Diag :=
  let loc := f.src.locString it.start
  it.allKeys.foldl (fun ds key => ds ++ auditKey cfg bundle it loc key) #[] ++ driftDiags bundle it loc

/-- What auditing one key of a blueprint `\lean` under a `\leanok` finds:
that its proof is untrusted. -/
def leanokKeyDiags (cfg : Config) (bundle : Bundle (Image TeX) Verdict) (loc key : String) : Array Diag :=
  match bundle.find? key with
  | some e =>
    if (trustProblems cfg.allowedAxioms key e).isEmpty then #[]
    else #[Diag.err "leanok-untrusted" loc
      s!"this node is marked \\leanok, but {key} is not trusted: \
        {"; ".intercalate (trustProblems cfg.allowedAxioms key e).toList}"]
  | none => #[]

/-- What auditing one `\leanok` finds: the blueprint `\lean`s in its
environment whose keys are untrusted. -/
def leanokDiags (cfg : Config) (bundle : Bundle (Image TeX) Verdict) (f : SourceFile) (ok : Item) :
    Array Diag :=
  if ok.env == 0 then #[]
  else (f.scan.items.filter (fun i => i.name == "lean" && i.env == ok.env)).foldl (init := #[]) fun ds it =>
    ds ++ it.keys.foldl (init := #[]) fun ds key => ds ++ leanokKeyDiags cfg bundle (f.src.locString ok.start) key

/-- Blueprint (DESIGN §9.3): a node marked `\leanok` must not depend on an
untrusted declaration. -/
def auditLeanok (cfg : Config) (bundle : Bundle (Image TeX) Verdict) (f : SourceFile) : Array Diag :=
  (f.scan.items.filter (·.kind == .leanok)).foldl (init := #[]) fun ds ok => ds ++ leanokDiags cfg bundle f ok

/-- Comparator manifests (DESIGN §10.5): each theorem they name is in the
bundle and trusted. -/
def auditManifests (doc : Doc) (bundle : Bundle (Image TeX) Verdict) : Array Diag :=
  doc.manifests.foldl (init := #[]) fun ds m =>
    let allowed := m.permittedAxioms.getD doc.cfg.allowedAxioms
    m.theorems.foldl (init := ds) fun ds key =>
      match bundle.find? key with
      | none => ds.push (Diag.err "broken-ref" m.path s!"{key} has no entry in the bundle")
      | some e => ds ++ (trustProblems allowed key e).map (Diag.err "untrusted" m.path ·)

/-- Broken references, trust problems, drift and blueprint `\leanok`s. -/
def audit (doc : Doc) (bundle : Bundle (Image TeX) Verdict) : Array Diag :=
  doc.files.foldl (init := #[]) (fun ds f =>
    f.scan.items.foldl (init := ds) (fun ds it => ds ++ auditItem doc.cfg bundle f it) ++
      auditLeanok doc.cfg bundle f) ++
  auditManifests doc bundle

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
def macroDiags (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (extra : Array String) :
    Array Diag := Id.run do
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
      for m in e.statement.macros do
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
      else s!"{ch.key} has no up-to-date sum= or dflt= option"
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

/-- **What `imprimatur check` reports** about a document, against a bundle
(DESIGN §10.3), in document order: what `plan` finds (errors, warnings and
the checks of what `apply` would write), the audit (references, trust,
faithfulness, drift, blueprint, manifests), undefined macros, and stale
items. `extra` are the macros the paper's own packages define. Theorem 1 is
about this function (`SpliceModel.Splicer.checkDoc_sound`). -/
def checkDoc (doc : Doc) (bundle : Bundle (Image TeX) Verdict) (opts : ApplyOpts)
    (extra : Array String) (diff : Bool) : Array Diag :=
  let o := plan doc bundle opts
  sortDiags doc (o.diags ++ audit doc bundle ++ macroDiags doc bundle extra ++ staleDiags o.changes diff)

end Splice
