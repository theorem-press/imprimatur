/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice

/-!
# The splicer's code before its rewrite (docs/verified-splicer.md)

The definitions the verified core replaces, kept verbatim as the reference
the differential tests (`SpliceTest.Diff`) compare the core against. A
definition leaves this file when the phase that replaced it is complete.
-/

namespace SpliceTest.Reference

/-- The line ending a file mostly uses: `"\r\n"` or `"\n"`. -/
def dominantEol (chars : Array Char) : String := Id.run do
  let mut crlf := 0
  let mut lf := 0
  for i in [0:chars.size] do
    if chars[i]! == '\n' then
      if i > 0 && chars[i - 1]! == '\r' then crlf := crlf + 1 else lf := lf + 1
  return if crlf > lf then "\r\n" else "\n"

/-- Convert `\n` line endings in `t` to `eol`. `t` must use `\n` only. -/
def withEol (eol t : String) : String :=
  if eol == "\n" then t else eol.intercalate (t.splitOn "\n")

/-- Replace `\r\n` and lone `\r` by `\n`. -/
def toLf (t : String) : String :=
  "\n".intercalate (("\n".intercalate (t.splitOn "\r\n")).splitOn "\r")

/-- Normalise text for comparison and checksums (DESIGN §10.2): line endings
become `\n`, trailing spaces and tabs are removed from every line, and blank
lines at the start and end are dropped. -/
def normalize (t : String) : String :=
  let lines := (toLf t).splitOn "\n" |>.map (fun l =>
    String.ofList (l.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)
  let lines := lines.dropWhile (·.isEmpty)
  let lines := (lines.reverse.dropWhile (·.isEmpty)).reverse
  "\n".intercalate lines

open Splice Splice.Scan in
/-- Scan one file, starting with the switches declared so far; `live` says
whether the file is typeset. The scanner reads conditionals as TeX does for
the simple cases, to know which items are typeset (`Item.live`):
`\iffalse`, `\iftrue` and switches declared with `\newif\ifNAME` and set
with `\NAMEtrue` or `\NAMEfalse`, with their `\else` branches. Both
branches are scanned, and their items maintained, whatever the switches;
other conditionals (`\ifx`, `\ifnum`, switches from packages) count as on.
A switch set inside a branch that is off is not changed. -/
def scanSrcWith (cfg : Config) (s : Src) (switches : Switches) (live : Bool := true) :
    ScanM (ScanResult × Switches) := do
  let mut r : ScanResult := {}
  let mut switches := switches
  let mut i := 0
  -- Open environments (other than blocks and verbatim ones), innermost last.
  let mut envs : Array Nat := #[]
  let mut nextEnv := 1
  -- Open conditionals, innermost last: whether the branch being scanned is
  -- on, or `none` for a conditional the scanner can't evaluate (both on).
  let mut conds : Array (Option Bool) := #[]
  -- Aliases that are comment-delimited: `%NAME{…}`.
  let commentAliases := cfg.aliases.filter (·.comment)
  while i < s.size do
    let c := s.get i
    if c == '%' then
      let (name, j) := ctrlName s i
      if commentAliases.any (·.name == name) && (s.get j == '{' || s.get j == '[') then
        let it ← commentBlock s name i j
        r := { r with items := r.items.push { it with env := envs.back?.getD 0, live := conds.all (·.getD true) } }
        i := it.stop
      else
        i := lineEnd s i
    else if c != '\\' then
      i := i + 1
    else
      let (name, j) := ctrlName s i
      -- Items record whether they are on within this file; the loader then
      -- applies whether the file is typeset. Switches change only where on.
      let here := conds.all (·.getD true)
      let on := live && here
      -- Switches: `\newif\ifNAME`, `\NAMEtrue`, `\NAMEfalse`.
      if name == "newif" then
        let (sw, k) := ctrlName s j
        if sw.startsWith "if" && sw.length > 2 then
          let sw := (sw.drop 2).toString
          if on then switches := (switches.filter (·.1 != sw)).push (sw, false)
          i := k
        else
          i := j
        continue
      if name.endsWith "true" || name.endsWith "false" then
        let value := name.endsWith "true"
        let sw := (name.dropEnd (if value then 4 else 5)).toString
        if switches.any (·.1 == sw) then
          if on then
            switches := switches.map fun (n, v) => if n == sw then (n, value) else (n, v)
          i := j
          continue
      -- Conditionals.
      if name == "fi" then
        conds := conds.pop
        i := j
        continue
      if name == "else" then
        if let some b := conds.back? then conds := conds.pop.push (b.map (!·))
        i := j
        continue
      if isConditional name then
        let known : Option Bool :=
          if name == "iffalse" then some false
          else if name == "iftrue" then some true
          else (switches.find? (·.1 == (name.drop 2).toString)).map (·.2)
        -- An unknown conditional counts as on, in both branches.
        conds := conds.push known
        i := j
        continue
      -- A command being defined is not a use: `\newcommand{\leancheck}…`,
      -- `\NewDocumentCommand\leancheck{O{} m}{}`, `\def\leanref#1#2{…}`.
      if definingCommands.contains name then
        let mut k := skipSpaces s j
        if s.get k == '*' then k := skipSpaces s (k + 1)
        if s.get k == '{' then
          let (_, _, after) ← group s k
          i := after
        else if s.get k == '\\' then
          i := (ctrlName s k).2
        else
          i := j
        continue
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
          r := { r with items := r.items.push { it with env := envs.back?.getD 0, live := here } }
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
          r := { r with inputs := r.inputs.push (name, (s.slice a b).trimAscii.toString, i, here) }
          i := after
        else
          i := j
      | "leaninline" | "leanref" =>
        match ← inlineItem s (if name == "leanref" then .ref else .inline) name i j with
        | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0, live := here } }; i := it.stop
        | none => i := j
      | "leancheck" =>
        match ← checkItem s name i j with
        | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0, live := here } }; i := it.stop
        | none => i := j
      | "lean" =>
        if cfg.blueprint then
          match ← checkItem s name i j with
          | some it => r := { r with items := r.items.push { it with env := envs.back?.getD 0, live := here } }; i := it.stop
          | none => i := j
        else i := j
      | "leanok" =>
        if cfg.blueprint then
          let it : Item := { kind := .leanok, name, start := i, stop := j, insertAt := j,
                             regionStart := j, regionEnd := j, env := envs.back?.getD 0 }
          r := { r with items := r.items.push { it with live := here } }
        i := j
      | "leanhypref" =>
        let g := skipSpaces s j
        if s.get g == '{' then
          let (ka, kb, after) ← group s g
          let h := skipSpaces s after
          if s.get h != '{' then
            throw (Diag.err "parse-error" (s.locString h) "\\leanhypref takes a key and a hypothesis: \\leanhypref{key}{h}")
          let (ha, hb, stop) ← group s h
          let it : Item := { kind := .hypref, name, start := i, stop, insertAt := j,
                             key := (s.slice ka kb).trimAscii.toString,
                             hyp := (s.slice ha hb).trimAscii.toString,
                             regionStart := stop, regionEnd := stop, live := here }
          r := { r with items := r.items.push it }
          i := stop
        else
          i := j
      | "leanindex" =>
        let it : Item := { kind := .index, name, start := i, stop := j, insertAt := j,
                           regionStart := j, regionEnd := j }
        r := { r with items := r.items.push { it with live := here } }
        i := j
      | "label" =>
        let g := skipSpaces s j
        if s.get g == '{' then
          let (a, b, after) ← group s g
          if here then r := { r with labels := r.labels.push ((s.slice a b).trimAscii.toString, i) }
          i := after
        else
          i := j
      | _ => i := j
  return (r, switches)

end SpliceTest.Reference
