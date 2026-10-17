/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Text
import Splice.Config
import Splice.Diag

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

/-- The forms of markup (DESIGN §9.1). -/
inductive ItemKind where
  /-- A block environment: `leanblock` or an alias. -/
  | block
  /-- `\leaninline[opts]{key}{content}`. -/
  | inline
  /-- `\leanref[opts]{key}{content}`. -/
  | ref
  /-- `\leancheck[opts]{key, …}`, or blueprint `\lean{key, …}`. -/
  | check
  /-- `\leanindex`. -/
  | index
  /-- Blueprint `\leanok` (DESIGN §9.3), read when `manifests.blueprint` is on. -/
  | leanok
  deriving Repr, BEq, Inhabited

/-- One `key=value` option, with the position of its value. -/
structure Opt where
  /-- The key. -/
  key : String
  /-- The value, without surrounding braces. -/
  value : String
  /-- Index of the first character of the value as written. -/
  valueStart : Nat
  /-- One past the last character of the value as written. -/
  valueEnd : Nat
  deriving Repr, Inhabited

/-- One piece of markup in a file. All positions are character indices. -/
structure Item where
  /-- The form. -/
  kind : ItemKind
  /-- The environment or macro name (`leanblock`, `leanlemma`, `leaninline`, …). -/
  name : String
  /-- Index of the opening backslash. -/
  start : Nat
  /-- One past the end of the item. -/
  stop : Nat
  /-- Where `[sum=…]` is inserted when the item has no options. -/
  insertAt : Nat
  /-- Indices of `[` and one past `]`, if there are options. -/
  optsSpan : Option (Nat × Nat) := none
  /-- The options, in order. -/
  opts : Array Opt := #[]
  /-- The key (blocks, inline, ref). -/
  key : String := ""
  /-- The keys (check). -/
  keys : Array String := #[]
  /-- The title (blocks). -/
  title : String := ""
  /-- One past the last header argument (blocks). -/
  headerEnd : Nat := 0
  /-- The generated region. -/
  regionStart : Nat := 0
  /-- One past the end of the generated region. -/
  regionEnd : Nat := 0
  /-- Index of `\end` (blocks). -/
  endStart : Nat := 0
  /-- Which LaTeX environment the item is in: an id unique within the file,
  or 0 outside every environment. Pairs blueprint `\leanok` with `\lean{…}`. -/
  env : Nat := 0
  deriving Repr, Inhabited

/-- The value of an option. -/
def Item.opt? (it : Item) (k : String) : Option String :=
  (it.opts.find? (·.key == k)).map (·.value)

/-- What scanning one file finds. -/
structure ScanResult where
  /-- Markup, in order. -/
  items : Array Item := #[]
  /-- Files to follow: the macro, the path as written, and its position. -/
  inputs : Array (String × String × Nat) := #[]
  deriving Repr, Inhabited

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

open Scan in
/-- Scan one file. -/
def scanSrc (cfg : Config) (s : Src) : ScanM ScanResult := do
  let mut r : ScanResult := {}
  let mut i := 0
  -- Open environments (other than blocks and verbatim ones), innermost last.
  let mut envs : Array Nat := #[]
  let mut nextEnv := 1
  while i < s.size do
    let c := s.get i
    if c == '%' then
      i := lineEnd s i
    else if c != '\\' then
      i := i + 1
    else
      let (name, j) := ctrlName s i
      match name with
      | "verb" =>
        let d := if s.get j == '*' then j + 1 else j
        let delim := s.get d
        let mut k := d + 1
        while k < s.size && s.get k != delim && s.get k != '\n' do
          k := k + 1
        i := k + 1
      | "begin" =>
        let g := skipSpaces s j
        if s.get g != '{' then i := j; continue
        let (a, b, after) ← group s g
        let env := s.slice a b
        if cfg.verbatimEnvs.contains env then
          let endPat := "\\end{" ++ env ++ "}"
          match findStr s endPat after with
          | some e => i := e + 6 + env.length
          | none => throw (Diag.err "parse-error" (s.locString i) s!"\\begin\{{env}} is never closed")
        else if (cfg.alias? env).isSome then
          let it ← block cfg s env i after
          r := { r with items := r.items.push { it with env := envs.back?.getD 0 } }
          i := it.stop
        else
          envs := envs.push nextEnv
          nextEnv := nextEnv + 1
          i := after
      | "end" =>
        envs := envs.pop
        i := j
      | "input" | "include" | "subfile" =>
        let g := skipSpaces s j
        if s.get g == '{' then
          let (a, b, after) ← group s g
          r := { r with inputs := r.inputs.push (name, (s.slice a b).trimAscii.toString, i) }
          i := after
        else
          i := j
      | "leaninline" | "leanref" =>
        match ← inlineItem s (if name == "leanref" then .ref else .inline) name i j with
        | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0 } }; i := it.stop
        | none => i := j
      | "leancheck" =>
        match ← checkItem s name i j with
        | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0 } }; i := it.stop
        | none => i := j
      | "lean" =>
        if cfg.blueprint then
          match ← checkItem s name i j with
          | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0 } }; i := it.stop
          | none => i := j
        else i := j
      | "leanok" =>
        if cfg.blueprint then
          let it : Item := { kind := .leanok, name, start := i, stop := j, insertAt := j,
                             regionStart := j, regionEnd := j, env := envs.back?.getD 0 }
          r := { r with items := r.items.push it }
        i := j
      | "leanindex" =>
        let it : Item := { kind := .index, name, start := i, stop := j, insertAt := j,
                           regionStart := j, regionEnd := j }
        r := { r with items := r.items.push it }
        i := j
      | _ => i := j
  return r

/-- Scan the text of one file. -/
def scanText (cfg : Config) (path text : String) : ScanM ScanResult :=
  scanSrc cfg (Src.ofString path text)

end Splice
