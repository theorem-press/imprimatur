/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Config
import Splice.Core.Item

/-!
# The scanner

The scanner (DESIGN §9.1, §10.1) reads one file as a list of characters and
cuts it into chunks: text, and the items of imprimatur's markup, each with
the characters it was read from. It is total and lossless: the chunks print
back to the file (`print_scan`). Each step consumes at least one character,
so the main loop is well founded on the length of what is left, and every
loop is tail-recursive.

Positions in items are character indices into the file, as `Splice.Item`
has them. Errors carry the index they are about; the caller turns it into
`path:line:col`.
-/

namespace Splice.Core.Scan

open Splice (Config ItemKind Opt Item ScanResult Switches)

/-! ## Reading ahead -/

/-- The character `n` places in, or `'\x00'` past the end. -/
def charAt (cs : List Char) (n : Nat) : Char := cs.getD n '\x00'

/-- How many characters at the front satisfy `p`, counted on from `n`. -/
def countWhile (p : Char → Bool) : List Char → Nat → Nat
  | [], n => n
  | c :: cs, n => if p c then countWhile p cs (n + 1) else n

/-- The spaces and tabs at the front. -/
def skipSpaces (cs : List Char) : Nat := countWhile (fun c => c == ' ' || c == '\t') cs 0

/-- The characters before the next newline. -/
def lineEnd (cs : List Char) : Nat := countWhile (· != '\n') cs 0

/-- The characters from `a` to `b`. -/
def slice (cs : List Char) (a b : Nat) : List Char := (cs.drop a).take (b - a)

/-- A control sequence, at the start of `cs` (a backslash, or a `%` read as
one): its name and its length. A name is a run of letters, or a single other
character. -/
def ctrlName : List Char → String × Nat
  | [] => ("", 1)
  | [_] => ("", 1)
  | _ :: c :: rest =>
    if !c.isAlpha then (c.toString, 2)
    else
      let ls := (c :: rest).takeWhile Char.isAlpha
      (String.ofList ls, 1 + ls.length)

theorem ctrlName_pos (cs : List Char) : 1 ≤ (ctrlName cs).2 := by
  unfold ctrlName; split
  · simp
  · simp
  · split <;> simp

/-- Find the closing brace of a group, from index `k` at depth `depth`:
the index after it. Escaped characters and comments are skipped. -/
def groupGo : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: rest, k, depth =>
    if c == '\\' then groupGo rest.tail (k + 2) depth
    else if c == '%' then groupGo (rest.drop (lineEnd rest)) (k + 1 + lineEnd rest) depth
    else if c == '{' then groupGo rest (k + 1) (depth + 1)
    else if c == '}' then
      if depth - 1 == 0 then some (k + 1) else groupGo rest (k + 1) (depth - 1)
    else groupGo rest (k + 1) depth
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp [List.length_drop]); all_goals omega

/-- A braced group at the front of `cs`, which must start with `{`: the span
of its inside, and the index after its closing brace. -/
def group (cs : List Char) : Option (Nat × Nat × Nat) :=
  (groupGo cs 0 0).map fun after => (1, after - 1, after)

/-- Find the closing bracket of an optional argument, from index `k`: the
index after it. Brackets inside braces don't count. -/
def optGo : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: rest, k, depth =>
    if c == '\\' then optGo rest.tail (k + 2) depth
    else if c == '%' then optGo (rest.drop (lineEnd rest)) (k + 1 + lineEnd rest) depth
    else if c == '{' then optGo rest (k + 1) (depth + 1)
    else if c == '}' then optGo rest (k + 1) (depth - 1)
    else if c == ']' && depth == 0 then some (k + 1)
    else optGo rest (k + 1) depth
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp [List.length_drop]); all_goals omega

/-- An optional argument at the front of `cs`, which must start with `[`:
the index after its closing `]`. -/
def optGroup (cs : List Char) : Option Nat := optGo cs.tail 1 0

/-- The first index from `k` at which `pat` occurs. -/
def findSub (pat : List Char) : List Char → Nat → Option Nat
  | [], k => if pat.isEmpty then some k else none
  | c :: cs, k => if pat.isPrefixOf (c :: cs) then some k else findSub pat cs (k + 1)

/-! ## Options -/

/-- A space, tab or line ending. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The span from `a` to `b`, without blanks and line endings at either end. -/
def trimSpan (cs : List Char) (a b : Nat) : Nat × Nat :=
  let seg := slice cs a b
  let lead := countWhile isWs seg 0
  if lead == seg.length then (b, b)
  else (a + lead, b - countWhile isWs seg.reverse 0)

/-- Strip one pair of enclosing braces, if the whole text is one group. -/
def unbrace (t : String) : String :=
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

/-- The spans of the options between commas, from index `k` of `n`, where
the current one starts at `start`; commas inside braces don't count. -/
def splitOpts (n : Nat) : List Char → Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], _, _, start, acc => ((start, n) :: acc).reverse
  | c :: rest, k, depth, start, acc =>
    if k ≥ n then ((start, n) :: acc).reverse
    else if c == '\\' then splitOpts n rest.tail (k + 2) depth start acc
    else if c == '{' then splitOpts n rest (k + 1) (depth + 1) start acc
    else if c == '}' then splitOpts n rest (k + 1) (depth - 1) start acc
    else if c == ',' && depth == 0 then splitOpts n rest (k + 1) depth (k + 1) ((start, k) :: acc)
    else splitOpts n rest (k + 1) depth start acc
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp [List.length_drop]); all_goals omega

/-- Parse `key=value, …` between indices `a` and `b` of `cs`; `base` is the
index of `cs` in the file. -/
def parseOpts (cs : List Char) (base a b : Nat) : Array Opt :=
  let seg := slice cs a b
  let parts := splitOpts (b - a) seg 0 0 0 []
  let str (p q : Nat) : String := String.ofList (slice seg p q)
  parts.foldl (init := #[]) fun opts (p, q) =>
    let (p, q) := trimSpan seg p q
    if p == q then opts
    else
      match (List.range (q - p)).find? (fun d => charAt seg (p + d) == '=') with
      | none =>
        opts.push { key := str p q, value := "", valueStart := base + a + q, valueEnd := base + a + q }
      | some d =>
        let (kp, kq) := trimSpan seg p (p + d)
        let (vp, vq) := trimSpan seg (p + d + 1) q
        opts.push { key := str kp kq, value := unbrace (str vp vq),
                    valueStart := base + a + vp, valueEnd := base + a + vq }

/-! ## Items -/

/-- An error: the index it is about, and the message. -/
abbrev Err := Nat × String

/-- Options and the key after a name ending at `i`: the span of the options,
the options, the span of the key, and the index after it. -/
def optsAndKey (cs : List Char) (base i : Nat) :
    Except Err (Option (Nat × Nat) × Array Opt × Nat × Nat × Nat) := do
  let k := i + skipSpaces (cs.drop i)
  let (span, opts, k) ←
    if charAt cs k == '[' then
      match optGroup (cs.drop k) with
      | none => throw (k, "this '[' is never closed")
      | some n =>
        let after := k + n
        pure (some (k, after), parseOpts cs base (k + 1) (after - 1), after + skipSpaces (cs.drop after))
    else pure (none, #[], k)
  if charAt cs k != '{' then throw (k, "expected '{' here")
  match group (cs.drop k) with
  | none => throw (k, "this '{' is never closed")
  | some (a, b, after) => pure (span, opts, k + a, k + b, k + after)

/-- A group that must be at index `k`. -/
def groupAt (cs : List Char) (k : Nat) : Except Err (Nat × Nat × Nat) :=
  match group (cs.drop k) with
  | none => throw (k, "this '{' is never closed")
  | some (a, b, after) => pure (k + a, k + b, k + after)

/-- Where a region ends, given the index of its end marker: at the start of
the marker's line, if only blanks come before it there and that is in the
region. -/
def regionEndAt (cs : List Char) (regionStart endStart : Nat) : Nat :=
  let before := cs.take endStart
  -- The start of the line containing `endStart`: after its last newline.
  let ls := match (before.reverse.findIdx? (· == '\n')) with
    | some d => some (endStart - d)
    | none => none
  let re := match ls with
    | some ls =>
      if ls ≥ regionStart && (slice cs ls endStart).all (fun c => c == ' ' || c == '\t') then ls
      else endStart
    | none => endStart
  max regionStart re

/-- Find `\end{env}` from index `k`, skipping comments: the index of its
backslash and the index after it, or `none` if the file ends first. Another
block starting first is an error, which names the opener's place. -/
def findEndGo (cfg : Config) (env openerLoc : String) : List Char → Nat → Except Err (Option (Nat × Nat))
  | [], _ => pure none
  | c :: rest, k =>
    if c == '%' then findEndGo cfg env openerLoc (rest.drop (lineEnd rest)) (k + 1 + lineEnd rest)
    else if c == '\\' then
      let name := (ctrlName (c :: rest)).1
      let j := (ctrlName (c :: rest)).2
      let sfx := (c :: rest).drop j
      if name == "end" || name == "begin" then
        let g := skipSpaces sfx
        let gsfx := sfx.drop g
        if charAt gsfx 0 == '{' then
          match group gsfx with
          | none => throw (k + j + g, "this '{' is never closed")
          | some (a, b, after) =>
            let e := String.ofList (slice gsfx a b)
            if name == "end" && e == env then pure (some (k, k + j + g + after))
            else if name == "begin" && (cfg.alias? e).isSome then
              throw (k, s!"\\begin\{{e}} inside \\begin\{{env}} at {openerLoc}; blocks cannot nest, \
                or that block is missing its \\end\{{env}}")
            else findEndGo cfg env openerLoc (gsfx.drop after) (k + j + g + after)
        else findEndGo cfg env openerLoc sfx (k + j)
      else findEndGo cfg env openerLoc sfx (k + j)
    else findEndGo cfg env openerLoc rest (k + 1)
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals have := ctrlName_pos (c :: rest)
  all_goals (try simp only [List.length_drop, List.length_cons] at *)
  all_goals (try simp only [List.length_drop])
  all_goals omega

/-- A block environment at the front of `cs`, at index `pos` of the file,
whose `\begin{env}` ends at `afterEnv`. -/
def block (cfg : Config) (locOf : Nat → String) (cs : List Char) (pos : Nat) (env : String)
    (afterEnv : Nat) : Except Err Item := do
  let (span, opts, ka, kb, k) ← optsAndKey cs pos afterEnv
  let t := k + skipSpaces (cs.drop k)
  if charAt cs t != '{' then
    throw (t, s!"\\begin\{{env}} takes a key and a title: \\begin\{{env}}\{key}\{title}")
  let (ta, tb, headerEnd) ← groupAt cs t
  -- The region starts on the next line if the rest of the header line is
  -- blank or a comment.
  let le := headerEnd + lineEnd (cs.drop headerEnd)
  let rest := headerEnd + skipSpaces (cs.drop headerEnd)
  -- (`le` is at a newline, or at the end of the file.)
  let nextLine := if charAt cs le == '\n' then le + 1 else le
  let regionStart := if rest == le || charAt cs rest == '%' then nextLine else headerEnd
  let some (endStart, stop) ← findEndGo cfg env (locOf pos) (cs.drop regionStart) regionStart
    | throw (0, s!"\\begin\{{env}} is never closed by \\end\{{env}}")
  let (ka, kb) := trimSpan cs ka kb
  pure { kind := .block, name := env, start := pos, stop := pos + stop, insertAt := pos + afterEnv,
         optsSpan := span.map (fun (a, b) => (pos + a, pos + b)), opts,
         key := String.ofList (slice cs ka kb), title := String.ofList (slice cs ta tb),
         headerEnd := pos + headerEnd, regionStart := pos + regionStart,
         regionEnd := pos + regionEndAt cs regionStart endStart, endStart := pos + endStart }

/-- The end marker of a comment-delimited block, at the start of a line
(after blanks), from index `k`, which starts a line: its index and the
index after it. -/
def findCommentEndGo (marker : List Char) : List Char → Nat → Option (Nat × Nat)
  | [], _ => none
  | c :: rest, k =>
    let a := skipSpaces (c :: rest)
    if marker.isPrefixOf ((c :: rest).drop a) then some (k + a, k + a + marker.length)
    else findCommentEndGo marker ((c :: rest).drop (lineEnd (c :: rest) + 1)) (k + lineEnd (c :: rest) + 1)
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- A comment-delimited block, `%NAME{key}{title}` … `%ENDNAME`, at the front
of `cs`, at index `pos`, whose marker ends at `afterName`. -/
def commentBlock (cs : List Char) (pos : Nat) (name : String) (afterName : Nat) : Except Err Item := do
  let (span, opts, ka, kb, k) ← optsAndKey cs pos afterName
  let t := k + skipSpaces (cs.drop k)
  if charAt cs t != '{' then
    throw (t, s!"%{name} takes a key and a title: %{name}\{key}\{title}")
  let (ta, tb, headerEnd) ← groupAt cs t
  let le := headerEnd + lineEnd (cs.drop headerEnd)
  -- (`le` is at a newline, or at the end of the file.)
  let regionStart := if charAt cs le == '\n' then le + 1 else le
  let marker := "%END" ++ name
  let some (endStart, stop) := findCommentEndGo marker.toList (cs.drop regionStart) regionStart
    | throw (0, s!"%{name} is never closed by {marker}")
  let (ka, kb) := trimSpan cs ka kb
  pure { kind := .block, name, start := pos, stop := pos + stop, insertAt := pos + afterName,
         optsSpan := span.map (fun (a, b) => (pos + a, pos + b)), opts,
         key := String.ofList (slice cs ka kb), title := String.ofList (slice cs ta tb),
         headerEnd := pos + headerEnd, regionStart := pos + regionStart,
         regionEnd := pos + regionEndAt cs regionStart endStart, endStart := pos + endStart }

/-- `\leaninline` or `\leanref` at the front of `cs`, at index `pos`, after
its name; `none` if no arguments follow (as in `\newcommand\leaninline…`). -/
def inlineItem (cs : List Char) (pos : Nat) (kind : ItemKind) (name : String) (afterName : Nat) :
    Except Err (Option Item) := do
  let k := afterName + skipSpaces (cs.drop afterName)
  if charAt cs k != '[' && charAt cs k != '{' then return none
  let (span, opts, ka, kb, k) ← optsAndKey cs pos afterName
  let c := k + skipSpaces (cs.drop k)
  if charAt cs c != '{' then
    throw (c, s!"\\{name} takes a key and a second argument for the generated text: \
      \\{name}\{key}\{}")
  let (ca, cb, stop) ← groupAt cs c
  let (ka, kb) := trimSpan cs ka kb
  return some { kind, name, start := pos, stop := pos + stop, insertAt := pos + afterName,
                optsSpan := span.map (fun (a, b) => (pos + a, pos + b)), opts,
                key := String.ofList (slice cs ka kb), regionStart := pos + ca, regionEnd := pos + cb }

/-- `\leancheck` or blueprint `\lean` at the front of `cs`, at index `pos`,
after its name. -/
def checkItem (cs : List Char) (pos : Nat) (name : String) (afterName : Nat) :
    Except Err (Option Item) := do
  let k := afterName + skipSpaces (cs.drop afterName)
  if charAt cs k != '[' && charAt cs k != '{' then return none
  let (span, opts, ka, kb, stop) ← optsAndKey cs pos afterName
  let keys := ((String.ofList (slice cs ka kb)).splitOn ",").toArray.map (·.trimAscii.toString)
    |>.filter (!·.isEmpty)
  return some { kind := .check, name, start := pos, stop := pos + stop, insertAt := pos + afterName,
                optsSpan := span.map (fun (a, b) => (pos + a, pos + b)), opts, keys,
                regionStart := pos + stop, regionEnd := pos + stop }

/-! ## The scanner -/

/-- What the scanner carries from one step to the next. -/
structure St where
  /-- The switches declared with `\newif`, and their values. -/
  switches : Switches
  /-- Open environments (other than blocks and verbatim ones), innermost
  first. -/
  envs : List Nat := []
  /-- The id the next environment gets. -/
  nextEnv : Nat := 1
  /-- Open conditionals, innermost first: whether the branch being scanned
  is on, or `none` for one the scanner can't evaluate (both on). -/
  conds : List (Option Bool) := []

/-- What one step finds. -/
inductive Found where
  /-- Text. -/
  | nothing
  /-- An item. -/
  | item (it : Item)
  /-- A file to follow: the macro, the path as written, and whether it is
  typeset. -/
  | input (cmd path : String) (here : Bool)
  /-- A typeset `\label`. -/
  | label (name : String)

/-- One step, at the front of `cs`, at index `pos` of a file that `live`
says is typeset: how many characters it reads, what it finds, and the state
after it. Errors are at indices relative to `pos`. -/
def step (cfg : Config) (locOf : Nat → String) (live : Bool) (st : St) (pos : Nat) (cs : List Char) :
    Except Err (Nat × Found × St) := do
  let c := charAt cs 0
  -- Text with no `\` or `%` in it holds no markup: one step reads all of it.
  if c != '\\' && c != '%' then
    return (countWhile (fun ch => ch != '\\' && ch != '%') cs 0, .nothing, st)
  let env := st.envs.head?.getD 0
  let here := st.conds.all (·.getD true)
  if c == '%' then
    let name := (ctrlName cs).1
    let j := (ctrlName cs).2
    if cfg.aliases.any (fun a => a.comment && a.name == name) &&
        (charAt cs j == '{' || charAt cs j == '[') then
      let it ← commentBlock cs pos name j
      return (it.stop - pos, .item { it with env, live := here }, st)
    else return (lineEnd cs, .nothing, st)
  let name := (ctrlName cs).1
  let j := (ctrlName cs).2
  -- Switches change only where on.
  let on := live && here
  -- Switches: `\newif\ifNAME`, `\NAMEtrue`, `\NAMEfalse`.
  if name == "newif" then
    let sw := (ctrlName (cs.drop j)).1
    let k := (ctrlName (cs.drop j)).2
    if sw.startsWith "if" && sw.length > 2 then
      let sw := (sw.drop 2).toString
      let st := if on then { st with switches := (st.switches.filter (·.1 != sw)).push (sw, false) } else st
      return (j + k, .nothing, st)
    else return (j, .nothing, st)
  let value := name.endsWith "true"
  let sw := (name.dropEnd (if value then 4 else 5)).toString
  if (name.endsWith "true" || name.endsWith "false") && st.switches.any (·.1 == sw) then
    let st := if on then
        { st with switches := st.switches.map fun (n, v) => if n == sw then (n, value) else (n, v) }
      else st
    return (j, .nothing, st)
  -- Conditionals.
  if name == "fi" then return (j, .nothing, { st with conds := st.conds.tail })
  if name == "else" then
    let conds := match st.conds with
      | b :: bs => b.map (!·) :: bs
      | [] => []
    return (j, .nothing, { st with conds })
  if Splice.Scan.isConditional name then
    let known : Option Bool :=
      if name == "iffalse" then some false
      else if name == "iftrue" then some true
      else (st.switches.find? (·.1 == (name.drop 2).toString)).map (·.2)
    -- An unknown conditional counts as on, in both branches.
    return (j, .nothing, { st with conds := known :: st.conds })
  -- A command being defined is not a use: `\newcommand{\leancheck}…`.
  if Splice.Scan.definingCommands.contains name then
    let k0 := j + skipSpaces (cs.drop j)
    let k := if charAt cs k0 == '*' then k0 + 1 + skipSpaces (cs.drop (k0 + 1)) else k0
    if charAt cs k == '{' then
      let (_, _, after) ← groupAt cs k
      return (after, .nothing, st)
    else if charAt cs k == '\\' then return (k + (ctrlName (cs.drop k)).2, .nothing, st)
    else return (j, .nothing, st)
  match name with
  | "verb" =>
    let d := if charAt cs j == '*' then j + 1 else j
    let delim := charAt cs d
    let k := d + 1 + countWhile (fun ch => ch != delim && ch != '\n') (cs.drop (d + 1)) 0
    return (k + 1, .nothing, st)
  | "begin" =>
    let g := j + skipSpaces (cs.drop j)
    if charAt cs g != '{' then return (j, .nothing, st)
    let (a, b, after) ← groupAt cs g
    let e := String.ofList (slice cs a b)
    if cfg.verbatimEnvs.contains e then
      match findSub ("\\end{" ++ e ++ "}").toList (cs.drop after) after with
      | some k => return (k + 6 + e.length, .nothing, st)
      | none => throw (0, s!"\\begin\{{e}} is never closed")
    else if (cfg.alias? e).isSome then
      let it ← block cfg locOf cs pos e after
      return (it.stop - pos, .item { it with env, live := here }, st)
    else
      return (after, .nothing, { st with envs := st.nextEnv :: st.envs, nextEnv := st.nextEnv + 1 })
  | "end" => return (j, .nothing, { st with envs := st.envs.tail })
  | "input" | "include" | "subfile" =>
    let g := j + skipSpaces (cs.drop j)
    if charAt cs g != '{' then return (j, .nothing, st)
    let (a, b, after) ← groupAt cs g
    return (after, .input name (String.ofList (slice cs a b)).trimAscii.toString here, st)
  | "leaninline" | "leanref" =>
    match ← inlineItem cs pos (if name == "leanref" then .ref else .inline) name j with
    | some it => return (it.stop - pos, .item { it with env, live := here }, st)
    | none => return (j, .nothing, st)
  | "leancheck" =>
    match ← checkItem cs pos name j with
    | some it => return (it.stop - pos, .item { it with env, live := here }, st)
    | none => return (j, .nothing, st)
  | "lean" =>
    if !cfg.blueprint then return (j, .nothing, st)
    match ← checkItem cs pos name j with
    | some it => return (it.stop - pos, .item { it with env, live := here }, st)
    | none => return (j, .nothing, st)
  | "leanok" =>
    if !cfg.blueprint then return (j, .nothing, st)
    let it : Item := { kind := .leanok, name, start := pos, stop := pos + j, insertAt := pos + j,
                       regionStart := pos + j, regionEnd := pos + j, env, live := here }
    return (j, .item it, st)
  | "leanhypref" =>
    let g := j + skipSpaces (cs.drop j)
    if charAt cs g != '{' then return (j, .nothing, st)
    let (ka, kb, after) ← groupAt cs g
    let h := after + skipSpaces (cs.drop after)
    if charAt cs h != '{' then
      throw (h, "\\leanhypref takes a key and a hypothesis: \\leanhypref{key}{h}")
    let (ha, hb, stop) ← groupAt cs h
    let it : Item := { kind := .hypref, name, start := pos, stop := pos + stop, insertAt := pos + j,
                       key := (String.ofList (slice cs ka kb)).trimAscii.toString,
                       hyp := (String.ofList (slice cs ha hb)).trimAscii.toString,
                       regionStart := pos + stop, regionEnd := pos + stop, live := here }
    return (stop, .item it, st)
  | "leanindex" =>
    let it : Item := { kind := .index, name, start := pos, stop := pos + j, insertAt := pos + j,
                       regionStart := pos + j, regionEnd := pos + j, live := here }
    return (j, .item it, st)
  | "label" =>
    let g := j + skipSpaces (cs.drop j)
    if charAt cs g != '{' then return (j, .nothing, st)
    let (a, b, after) ← groupAt cs g
    return (after, if here then .label (String.ofList (slice cs a b)).trimAscii.toString else .nothing, st)
  | _ => return (j, .nothing, st)

/-- A piece of a file: text, or an item with the characters it was read
from. -/
inductive Chunk where
  /-- Text. -/
  | text (raw : List Char)
  /-- An item, and its characters. -/
  | item (it : Item) (raw : List Char)

/-- The characters a chunk was read from. -/
def Chunk.raw : Chunk → List Char
  | .text r => r
  | .item _ r => r

/-- The characters chunks were read from, in order. -/
def print (chunks : List Chunk) : List Char := (chunks.map Chunk.raw).flatten

/-- Close the pending text (held reversed) as a chunk, onto chunks held
reversed. -/
def flush (pending : List Char) (acc : List Chunk) : List Chunk :=
  if pending.isEmpty then acc else .text pending.reverse :: acc

/-- The main loop, at index `pos`, with the chunks so far and the pending
text, both reversed. -/
def loop (cfg : Config) (locOf : Nat → String) (live : Bool) :
    List Char → Nat → St → List Chunk → List Char → ScanResult →
    Except Err (List Chunk × ScanResult × Switches)
  | [], _, st, acc, pending, r => pure ((flush pending acc).reverse, r, st.switches)
  | c :: rest, pos, st, acc, pending, r =>
    match step cfg locOf live st pos (c :: rest) with
    | .error (i, m) => .error (pos + i, m)
    | .ok (n, found, st') =>
      let n := max 1 n
      let taken := (c :: rest).take n
      let next := (c :: rest).drop n
      match found with
      | .item it =>
        loop cfg locOf live next (pos + n) st' (.item it taken :: flush pending acc) []
          { r with items := r.items.push it }
      | .input m path here =>
        loop cfg locOf live next (pos + n) st' acc (taken.reverse ++ pending)
          { r with inputs := r.inputs.push (m, path, pos, here) }
      | .label name =>
        loop cfg locOf live next (pos + n) st' acc (taken.reverse ++ pending)
          { r with labels := r.labels.push (name, pos) }
      | .nothing => loop cfg locOf live next (pos + n) st' acc (taken.reverse ++ pending) r
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- **Scan one file**, given the switches declared so far and whether it is
typeset: its chunks, what they hold, and the switches after it. `locOf`
names an index as `path:line:col`, for messages. -/
def scan (cfg : Config) (locOf : Nat → String) (live : Bool) (switches : Switches) (cs : List Char) :
    Except Err (List Chunk × ScanResult × Switches) :=
  loop cfg locOf live cs 0 { switches } [] [] {}

/-! ## The scanner is lossless -/

theorem print_append (a b : List Chunk) : print (a ++ b) = print a ++ print b := by
  simp [print]

theorem print_flush (pending : List Char) (acc : List Chunk) :
    print (flush pending acc).reverse = print acc.reverse ++ pending.reverse := by
  unfold flush
  split
  · rename_i h; simp_all
  · simp [print, Chunk.raw]

theorem print_loop (cfg : Config) (locOf : Nat → String) (live : Bool) :
    ∀ (cs : List Char) (pos : Nat) (st : St) (acc : List Chunk) (pending : List Char) (r : ScanResult)
      (out : List Chunk × ScanResult × Switches),
      loop cfg locOf live cs pos st acc pending r = .ok out →
      print out.1 = print acc.reverse ++ pending.reverse ++ cs
  | [], pos, st, acc, pending, r, out, h => by
    simp only [loop] at h
    cases h
    simp [print_flush]
  | c :: rest, pos, st, acc, pending, r, out, h => by
    rw [loop] at h
    split at h
    · cases h
    · rename_i n found st' _
      have key : (c :: rest).take (max 1 n) ++ (c :: rest).drop (max 1 n) = c :: rest :=
        List.take_append_drop _ _
      dsimp only at h
      split at h
      · rw [print_loop cfg locOf live _ _ _ _ _ _ _ h]
        rw [List.reverse_cons, print_append, print_flush]
        have hone : ∀ (it : Item) (t : List Char), print [Chunk.item it t] = t := by
          intro it t; simp [print, Chunk.raw]
        rw [hone, List.reverse_nil, List.append_nil]
        simp only [List.append_assoc, key]
      all_goals
        rw [print_loop cfg locOf live _ _ _ _ _ _ _ h]
        simp only [List.reverse_append, List.reverse_reverse, List.append_assoc]
        rw [key]
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- **The scanner is lossless:** its chunks print back to the file. -/
theorem print_scan (cfg : Config) (locOf : Nat → String) (live : Bool) (switches : Switches)
    (cs : List Char) (out : List Chunk × ScanResult × Switches)
    (h : scan cfg locOf live switches cs = .ok out) : print out.1 = cs := by
  have := print_loop cfg locOf live cs 0 { switches } [] [] {} out h
  simpa [print] using this

end Splice.Core.Scan
