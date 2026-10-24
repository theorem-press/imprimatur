/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Text
import Splice.Config
import Splice.Diag
import Splice.Core.Item
import Splice.Core.Scan

/-!
# Scanning TeX

`scanText` finds imprimatur's markup in one file (DESIGN §9.1): blocks
(`leanblock` and its aliases), `\leaninline`, `\leanref`, `\leancheck`,
`\leanindex`, and, for blueprints, `\lean{…}`. It also records `\input`,
`\include` and `\subfile`, so that `loadDoc` can follow them (DESIGN §10.1).

The scanner reads TeX at the level of characters and control sequences. It
skips comments, `\verb`, and the contents of verbatim-like environments, so
markup inside them is ignored. It never fails with a panic: malformed markup
is reported as an error with its position.
-/

namespace Splice

/-- The scanner's monad: errors carry a diagnostic. -/
abbrev ScanM := Except Diag

namespace Scan

private def parseError (s : Src) (i : Nat) (msg : String) : Diag :=
  Diag.err "parse-error" (s.locString i) msg

/-- A control sequence at `i` (a backslash): its name and the index after
it. A name is a run of letters, or a single other character. -/
def ctrlName (s : Src) (i : Nat) : String × Nat := Id.run do
  let j := i + 1
  if j ≥ s.size then return ("", j)
  if !(s.get j).isAlpha then return ((s.get j).toString, j + 1)
  let mut k := j
  while k < s.size && (s.get k).isAlpha do
    k := k + 1
  return (s.slice j k, k)

/-- Skip spaces and tabs. -/
def skipSpaces (s : Src) (i : Nat) : Nat := Id.run do
  let mut k := i
  while k < s.size && (s.get k == ' ' || s.get k == '\t') do
    k := k + 1
  return k

/-- The index of the next newline at or after `i`, or the end. -/
def lineEnd (s : Src) (i : Nat) : Nat := Id.run do
  let mut k := i
  while k < s.size && s.get k != '\n' do
    k := k + 1
  return k

/-- A braced group at `i` (which must be `{`): the inner span and the index
after the closing brace. Comments and escaped braces are respected. -/
def group (s : Src) (i : Nat) : ScanM (Nat × Nat × Nat) := do
  let mut depth := 0
  let mut k := i
  while k < s.size do
    let c := s.get k
    if c == '\\' then
      k := k + 2
    else if c == '%' then
      k := lineEnd s k
    else if c == '{' then
      depth := depth + 1
      k := k + 1
    else if c == '}' then
      depth := depth - 1
      k := k + 1
      if depth == 0 then
        return (i + 1, k - 1, k)
    else
      k := k + 1
  throw (parseError s i "this '{' is never closed")

/-- An optional-argument group at `i` (which must be `[`): the index after
the closing `]`. Brackets inside braces don't count. -/
def optGroup (s : Src) (i : Nat) : ScanM Nat := do
  let mut depth := 0
  let mut k := i + 1
  while k < s.size do
    let c := s.get k
    if c == '\\' then
      k := k + 2
    else if c == '%' then
      k := lineEnd s k
    else if c == '{' then
      depth := depth + 1
      k := k + 1
    else if c == '}' then
      depth := depth - 1
      k := k + 1
    else if c == ']' && depth == 0 then
      return k + 1
    else
      k := k + 1
  throw (parseError s i "this '[' is never closed")

/-- Strip one pair of enclosing braces, if the whole text is one group. -/
private def unbrace (t : String) : String :=
  let cs := t.toList
  if cs.head? == some '{' && cs.getLast? == some '}' then
    -- Only if the first brace closes at the very end.
    let rec closesAtEnd : List Char → Nat → Bool
      | [], _ => false
      | '{' :: rest, d => closesAtEnd rest (d + 1)
      | '}' :: rest, d => if d == 1 then rest.isEmpty else closesAtEnd rest (d - 1)
      | _ :: rest, d => closesAtEnd rest d
    if closesAtEnd cs 0 then String.ofList (cs.drop 1).dropLast else t
  else t

/-- Trim spaces, tabs and newlines from both ends of a span. -/
private def trimSpan (s : Src) (a b : Nat) : Nat × Nat := Id.run do
  let ws (c : Char) := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let mut a := a
  let mut b := b
  while a < b && ws (s.get a) do a := a + 1
  while b > a && ws (s.get (b - 1)) do b := b - 1
  return (a, b)

/-- Parse `key=value, …` between `a` and `b`. -/
def parseOpts (s : Src) (a b : Nat) : Array Opt := Id.run do
  -- Split at commas outside braces.
  let mut parts : Array (Nat × Nat) := #[]
  let mut depth := 0
  let mut start := a
  let mut k := a
  while k < b do
    let c := s.get k
    if c == '\\' then k := k + 2; continue
    if c == '{' then depth := depth + 1
    else if c == '}' then depth := depth - 1
    else if c == ',' && depth == 0 then
      parts := parts.push (start, k)
      start := k + 1
    k := k + 1
  parts := parts.push (start, b)
  let mut opts := #[]
  for (p, q) in parts do
    let (p, q) := trimSpan s p q
    if p == q then continue
    let eq := (List.range (q - p)).find? (fun d => s.get (p + d) == '=')
    match eq with
    | none => opts := opts.push { key := s.slice p q, value := "", valueStart := q, valueEnd := q }
    | some d =>
      let (kp, kq) := trimSpan s p (p + d)
      let (vp, vq) := trimSpan s (p + d + 1) q
      opts := opts.push
        { key := s.slice kp kq, value := unbrace (s.slice vp vq), valueStart := vp, valueEnd := vq }
  return opts

/-- Find `\end{env}` from `i`, skipping comments and `\verb`. Returns the
index of the backslash and the index after the closing brace. Another block
starting first is an error. -/
def findEnd (cfg : Config) (s : Src) (env : String) (i : Nat) (opener : Nat) :
    ScanM (Nat × Nat) := do
  let mut k := i
  while k < s.size do
    let c := s.get k
    if c == '%' then
      k := lineEnd s k
    else if c == '\\' then
      let (name, j) := ctrlName s k
      if name == "end" || name == "begin" then
        let g := skipSpaces s j
        if s.get g == '{' then
          let (a, b, after) ← group s g
          let e := s.slice a b
          if name == "end" && e == env then return (k, after)
          if name == "begin" && (cfg.alias? e).isSome then
            throw (parseError s k
              s!"\\begin\{{e}} inside \\begin\{{env}} at {s.locString opener}; blocks cannot nest, \
                or that block is missing its \\end\{{env}}")
          k := after
        else
          k := j
      else
        k := j
    else
      k := k + 1
  throw (parseError s opener s!"\\begin\{{env}} is never closed by \\end\{{env}}")

/-- Options and the key argument after a macro or environment name. -/
private def optsAndKey (s : Src) (i : Nat) :
    ScanM (Option (Nat × Nat) × Array Opt × Nat × Nat × Nat) := do
  let mut k := skipSpaces s i
  let mut span := none
  let mut opts := #[]
  if s.get k == '[' then
    let after ← optGroup s k
    span := some (k, after)
    opts := parseOpts s (k + 1) (after - 1)
    k := skipSpaces s after
  if s.get k != '{' then
    throw (parseError s k "expected '{' here")
  let (a, b, after) ← group s k
  return (span, opts, a, b, after)

/-- A block environment whose `\begin{env}` ends at `afterEnv`. -/
def block (cfg : Config) (s : Src) (env : String) (start afterEnv : Nat) : ScanM Item := do
  let (span, opts, ka, kb, k) ← optsAndKey s afterEnv
  let t := skipSpaces s k
  if s.get t != '{' then
    throw (parseError s t s!"\\begin\{{env}} takes a key and a title: \\begin\{{env}}\{key}\{title}")
  let (ta, tb, headerEnd) ← group s t
  -- The region starts on the next line if the rest of the header line is
  -- blank or a comment.
  let le := lineEnd s headerEnd
  let rest := skipSpaces s headerEnd
  let regionStart := if rest == le || s.get rest == '%' then min (le + 1) s.size else headerEnd
  let (endStart, stop) ← findEnd cfg s env regionStart start
  let ls := s.lineStart endStart
  let regionEnd :=
    if ls ≥ regionStart && s.blankBetween ls endStart then ls else endStart
  let (ka, kb) := trimSpan s ka kb
  return { kind := .block, name := env, start, stop, insertAt := afterEnv,
           optsSpan := span, opts, key := s.slice ka kb, title := s.slice ta tb,
           headerEnd, regionStart, regionEnd := max regionStart regionEnd, endStart }

/-- The end marker of a comment-delimited block, `%ENDNAME` at the start of a
line (after spaces) from `i`: its index, and the index after it. -/
def findCommentEnd (s : Src) (name : String) (i : Nat) (opener : Nat) : ScanM (Nat × Nat) := do
  let marker := "%END" ++ name
  let mut k := i
  while k < s.size do
    let a := skipSpaces s k
    if (List.range marker.length).all (fun d => a + d < s.size && s.get (a + d) == marker.toList[d]!) then
      return (a, a + marker.length)
    k := lineEnd s k + 1
  throw (parseError s opener s!"%{name} is never closed by {marker}")

/-- A comment-delimited block, `%NAME{key}{title}` … `%ENDNAME`, whose
marker ends at `afterName`. -/
def commentBlock (s : Src) (name : String) (start afterName : Nat) : ScanM Item := do
  let (span, opts, ka, kb, k) ← optsAndKey s afterName
  let t := skipSpaces s k
  if s.get t != '{' then
    throw (parseError s t s!"%{name} takes a key and a title: %{name}\{key}\{title}")
  let (ta, tb, headerEnd) ← group s t
  let regionStart := min (lineEnd s headerEnd + 1) s.size
  let (endStart, stop) ← findCommentEnd s name regionStart start
  let ls := s.lineStart endStart
  let regionEnd := if ls ≥ regionStart && s.blankBetween ls endStart then ls else endStart
  let (ka, kb) := trimSpan s ka kb
  return { kind := .block, name, start, stop, insertAt := afterName,
           optsSpan := span, opts, key := s.slice ka kb, title := s.slice ta tb,
           headerEnd, regionStart, regionEnd := max regionStart regionEnd, endStart }

/-- `\leaninline` or `\leanref` after its name; `none` if no arguments follow
(as in `\newcommand\leaninline…`). -/
def inlineItem (s : Src) (kind : ItemKind) (name : String) (start afterName : Nat) :
    ScanM (Option Item) := do
  let k := skipSpaces s afterName
  if s.get k != '[' && s.get k != '{' then return none
  let (span, opts, ka, kb, k) ← optsAndKey s afterName
  let c := skipSpaces s k
  if s.get c != '{' then
    throw (parseError s c s!"\\{name} takes a key and a second argument for the generated text: \
      \\{name}\{key}\{}")
  let (ca, cb, stop) ← group s c
  let (ka, kb) := trimSpan s ka kb
  return some { kind, name, start, stop, insertAt := afterName, optsSpan := span, opts,
                key := s.slice ka kb, regionStart := ca, regionEnd := cb }

/-- `\leancheck` or blueprint `\lean` after its name. -/
def checkItem (s : Src) (name : String) (start afterName : Nat) : ScanM (Option Item) := do
  let k := skipSpaces s afterName
  if s.get k != '[' && s.get k != '{' then return none
  let (span, opts, ka, kb, stop) ← optsAndKey s afterName
  let keys := ((s.slice ka kb).splitOn ",").toArray.map (·.trimAscii.toString)
    |>.filter (!·.isEmpty)
  return some { kind := .check, name, start, stop, insertAt := afterName, optsSpan := span,
                opts, keys, regionStart := stop, regionEnd := stop }

/-- Find a literal string from index `i`. -/
def findStr (s : Src) (pat : String) (i : Nat) : Option Nat := Id.run do
  let p := pat.toList.toArray
  if p.isEmpty then return some i
  let mut k := i
  while k + p.size ≤ s.size do
    if s.get k == p[0]! then
      let mut ok := true
      for d in [1:p.size] do
        if s.get (k + d) != p[d]! then ok := false; break
      if ok then return some k
    k := k + 1
  return none

end Scan

/-- Scan one file, starting with the switches declared so far; `live` says
whether the file is typeset. The scanner reads conditionals as TeX does for
the simple cases, to know which items are typeset (`Item.live`):
`\iffalse`, `\iftrue` and switches declared with `\newif\ifNAME` and set
with `\NAMEtrue` or `\NAMEfalse`, with their `\else` branches. Both
branches are scanned, and their items maintained, whatever the switches;
other conditionals (`\ifx`, `\ifnum`, switches from packages) count as on.
A switch set inside a branch that is off is not changed. The work is the
verified core's (`Splice.Core.Scan.scan`), which is lossless. -/
def scanSrcWith (cfg : Config) (s : Src) (switches : Switches) (live : Bool := true) :
    ScanM (ScanResult × Switches) :=
  match Core.Scan.scan cfg s.locString live switches s.chars.toList with
  | .ok (_, r, sw) => .ok (r, sw)
  | .error (i, msg) => .error (Diag.err "parse-error" (s.locString i) msg)

/-- Scan one file, with no switches declared. -/
def scanSrc (cfg : Config) (s : Src) : ScanM ScanResult :=
  (·.1) <$> scanSrcWith cfg s #[]

/-- Scan the text of one file. -/
def scanText (cfg : Config) (path text : String) : ScanM ScanResult :=
  scanSrc cfg (Src.ofString path text)

end Splice
