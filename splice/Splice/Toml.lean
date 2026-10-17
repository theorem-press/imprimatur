/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A TOML subset

Enough TOML for `imprimatur.toml` (DESIGN §6.1), written here because the
splicer has no dependencies. Supported: comments; bare, quoted and dotted
keys; `[table]` headers; basic and literal strings; integers; booleans;
arrays, which may span lines; and inline tables. Not supported, and reported
as errors: arrays of tables, multi-line strings, floats and dates.
-/

namespace Splice

/-- A TOML value. Tables keep their keys in order of definition. -/
inductive Toml where
  /-- A string. -/
  | str (s : String)
  /-- An integer. -/
  | int (n : Int)
  /-- A boolean. -/
  | bool (b : Bool)
  /-- An array. -/
  | arr (xs : Array Toml)
  /-- A table. -/
  | tbl (kvs : Array (String × Toml))
  deriving Inhabited, Repr, BEq

namespace Toml

/-- Look up a key in a table. -/
def find? (t : Toml) (k : String) : Option Toml :=
  match t with
  | .tbl kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

/-- The keys of a table, or none. -/
def keys (t : Toml) : Array String :=
  match t with
  | .tbl kvs => kvs.map (·.1)
  | _ => #[]

/-- A short description of a value's type, for messages. -/
def typeName : Toml → String
  | .str _ => "a string" | .int _ => "an integer" | .bool _ => "a boolean"
  | .arr _ => "an array" | .tbl _ => "a table"

/-- Set `path` to `v` inside table `t`, creating intermediate tables.
Redefining a key is an error. -/
partial def insert (t : Toml) (path : List String) (v : Toml) : Except String Toml :=
  match t, path with
  | .tbl kvs, [k] =>
    if kvs.any (·.1 == k) then .error s!"key '{k}' is defined twice" else .ok (.tbl (kvs.push (k, v)))
  | .tbl kvs, k :: rest => do
    match kvs.findIdx? (·.1 == k) with
    | some i =>
      let sub ← insert (kvs[i]!).2 rest v
      .ok (.tbl (kvs.set! i (k, sub)))
    | none =>
      let sub ← insert (.tbl #[]) rest v
      .ok (.tbl (kvs.push (k, sub)))
  | _, _ => .error s!"'{".".intercalate path}' is inside a value that is not a table"

/-- Make sure the table at `path` exists (for a `[header]`). -/
partial def ensureTable (t : Toml) (path : List String) : Except String Toml :=
  match t, path with
  | .tbl _, [] => .ok t
  | .tbl kvs, k :: rest =>
    match kvs.findIdx? (·.1 == k) with
    | some i => do
      let sub ← ensureTable (kvs[i]!).2 rest
      .ok (.tbl (kvs.set! i (k, sub)))
    | none => do
      let sub ← ensureTable (.tbl #[]) rest
      .ok (.tbl (kvs.push (k, sub)))
  | _, _ => .error s!"'{".".intercalate path}' is not a table"

end Toml

namespace TomlParser

/-- Parser state: the characters and the current index. -/
structure St where
  /-- The input. -/
  cs : Array Char
  /-- The current index. -/
  i : Nat := 0

/-- The parser monad. -/
abbrev P := StateT St (Except String)

private def peek : P Char := do
  let s ← get
  return s.cs.getD s.i '\x00'

private def peekAt (n : Nat) : P Char := do
  let s ← get
  return s.cs.getD (s.i + n) '\x00'

private def atEnd : P Bool := do
  let s ← get
  return s.i ≥ s.cs.size

private def advance : P Unit :=
  modify fun s => { s with i := s.i + 1 }

private def lineNo : P Nat := do
  let s ← get
  return ((s.cs.extract 0 s.i).filter (· == '\n')).size + 1

private def fail {α : Type} (msg : String) : P α := do
  throw s!"line {← lineNo}: {msg}"

/-- Skip spaces and tabs. -/
private partial def skipWs : P Unit := do
  let c ← peek
  if c == ' ' || c == '\t' then advance; skipWs

/-- Skip spaces, tabs, newlines and comments. -/
private partial def skipWsNl : P Unit := do
  let c ← peek
  if c == ' ' || c == '\t' || c == '\n' || c == '\r' then advance; skipWsNl
  else if c == '#' then skipComment; skipWsNl
where
  skipComment : P Unit := do
    let c ← peek
    if !(← atEnd) && c != '\n' then advance; skipComment

private def isBare (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

private partial def hexVal (n : Nat) (acc : Nat) : P Nat := do
  if n == 0 then return acc
  let c ← peek
  let d ← if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else fail "bad \\u escape"
  advance
  hexVal (n - 1) (acc * 16 + d)

private partial def basicString (acc : String) : P String := do
  let c ← peek
  if ← atEnd then fail "unterminated string"
  else if c == '\n' then fail "newline in string (multi-line strings are not supported)"
  else if c == '"' then advance; return acc
  else if c == '\\' then
    advance
    let e ← peek
    advance
    match e with
    | '"' => basicString (acc.push '"')
    | '\\' => basicString (acc.push '\\')
    | 'n' => basicString (acc.push '\n')
    | 't' => basicString (acc.push '\t')
    | 'r' => basicString (acc.push '\r')
    | 'u' => basicString (acc.push (Char.ofNat (← hexVal 4 0)))
    | 'U' => basicString (acc.push (Char.ofNat (← hexVal 8 0)))
    | _ => fail s!"unknown escape \\{e}"
  else advance; basicString (acc.push c)

private partial def literalString (acc : String) : P String := do
  let c ← peek
  if ← atEnd then fail "unterminated string"
  else if c == '\n' then fail "newline in string"
  else if c == '\'' then advance; return acc
  else advance; literalString (acc.push c)

private def stringLit : P String := do
  let c ← peek
  if c == '"' then
    if (← peekAt 1) == '"' && (← peekAt 2) == '"' then fail "multi-line strings are not supported"
    advance; basicString ""
  else
    if (← peekAt 1) == '\'' && (← peekAt 2) == '\'' then fail "multi-line strings are not supported"
    advance; literalString ""

private partial def bareKey (acc : String) : P String := do
  let c ← peek
  if isBare c then advance; bareKey (acc.push c) else return acc

/-- A possibly dotted key. -/
private partial def key : P (List String) := do
  skipWs
  let c ← peek
  let k ← if c == '"' || c == '\'' then stringLit else bareKey ""
  if k.isEmpty && !(c == '"' || c == '\'') then fail s!"expected a key, found {repr c}"
  skipWs
  if (← peek) == '.' then
    advance
    return k :: (← key)
  return [k]

private partial def digits (acc : String) : P String := do
  let c ← peek
  if c.isDigit then advance; digits (acc.push c)
  else if c == '_' then advance; digits acc
  else return acc

mutual
  /-- A value. -/
  private partial def value : P Toml := do
    skipWs
    let c ← peek
    if c == '"' || c == '\'' then return .str (← stringLit)
    if c == '[' then advance; return .arr (← arrayItems #[])
    if c == '{' then advance; return .tbl (← inlineTable #[])
    if c == '+' || c == '-' || c.isDigit then
      let neg := c == '-'
      if c == '+' || c == '-' then advance
      let ds ← digits ""
      if ds.isEmpty then fail "expected a number"
      let c' ← peek
      if c' == '.' || c' == 'e' || c' == 'E' || c' == ':' || c' == '-' then
        fail "floats and dates are not supported"
      let n : Int := ds.toNat!
      return .int (if neg then -n else n)
    let w ← bareKey ""
    if w == "true" then return .bool true
    if w == "false" then return .bool false
    fail s!"expected a value, found {repr (if w.isEmpty then c.toString else w)}"

  private partial def arrayItems (acc : Array Toml) : P (Array Toml) := do
    skipWsNl
    if (← peek) == ']' then advance; return acc
    let v ← value
    skipWsNl
    let c ← peek
    if c == ',' then advance; arrayItems (acc.push v)
    else if c == ']' then advance; return acc.push v
    else fail s!"expected ',' or ']' in array, found {repr c}"

  private partial def inlineTable (acc : Array (String × Toml)) : P (Array (String × Toml)) := do
    skipWs
    if (← peek) == '}' && acc.isEmpty then advance; return acc
    let k ← key
    if (← peek) != '=' then fail "expected '=' in inline table"
    advance
    let v ← value
    let t ← match Toml.insert (.tbl acc) k v with
      | .ok (.tbl t) => pure t
      | .ok _ => fail "internal error"
      | .error e => fail e
    skipWs
    let c ← peek
    if c == ',' then advance; inlineTable t
    else if c == '}' then advance; return t
    else fail s!"expected ',' or '}' in inline table, found {repr c}"
end

/-- The rest of a line must be blank or a comment. -/
private partial def endOfLine : P Unit := do
  skipWs
  let c ← peek
  if c == '#' then
    while !(← atEnd) && (← peek) != '\n' do advance
  else if c == '\r' then advance; endOfLine
  else if c != '\n' && !(← atEnd) then fail s!"unexpected {repr c} after value"

/-- A whole document. -/
private partial def document (root : Toml) (table : List String) : P Toml := do
  skipWsNl
  if ← atEnd then return root
  if (← peek) == '[' then
    advance
    if (← peek) == '[' then fail "arrays of tables ([[...]]) are not supported"
    let path ← key
    if (← peek) != ']' then fail "expected ']' after table name"
    advance
    endOfLine
    match root.ensureTable path with
    | .ok r => document r path
    | .error e => fail e
  else
    let k ← key
    if (← peek) != '=' then fail "expected '=' after key"
    advance
    let v ← value
    endOfLine
    match root.insert (table ++ k) v with
    | .ok r => document r table
    | .error e => fail e

end TomlParser

/-- Parse a TOML document into a table. -/
def parseToml (text : String) : Except String Toml :=
  (TomlParser.document (.tbl #[]) []).run' { cs := text.toList.toArray }

end Splice
