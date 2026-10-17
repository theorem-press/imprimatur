/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Source text

The splicer works on files as arrays of characters, and every position is a
character index. Edits replace spans of characters, so every byte outside an
edited span is kept exactly, including line endings and a byte-order mark.
-/

namespace Splice

/-- A source file, held as characters with the index of every line start. -/
structure Src where
  /-- The file's path as shown in messages, relative to the project root. -/
  path : String
  /-- The file's characters. -/
  chars : Array Char
  /-- The character index at which each line starts. -/
  lineStarts : Array Nat

/-- Build a `Src` from a file's text. -/
def Src.ofString (path text : String) : Src := Id.run do
  let chars := text.toList.toArray
  let mut starts := #[0]
  for i in [0:chars.size] do
    if chars[i]! == '\n' then
      starts := starts.push (i + 1)
  return { path, chars, lineStarts := starts }

instance : Inhabited Src := ⟨Src.ofString "" ""⟩

/-- The character at index `i`, or `'\x00'` past the end. -/
@[inline] def Src.get (s : Src) (i : Nat) : Char :=
  s.chars.getD i '\x00'

/-- The number of characters. -/
@[inline] def Src.size (s : Src) : Nat :=
  s.chars.size

/-- The text between indices `a` and `b`. -/
def Src.slice (s : Src) (a b : Nat) : String :=
  String.ofList (s.chars.extract a b).toList

/-- The whole text. -/
def Src.text (s : Src) : String :=
  String.ofList s.chars.toList

/-- The 1-based line and column of index `i`. -/
def Src.lineCol (s : Src) (i : Nat) : Nat × Nat := Id.run do
  -- Binary search for the last line start not after `i`.
  let mut lo := 0
  let mut hi := s.lineStarts.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if s.lineStarts.getD mid 0 ≤ i then lo := mid else hi := mid
  return (lo + 1, i - s.lineStarts.getD lo 0 + 1)

/-- `path:line:col` for index `i`. -/
def Src.locString (s : Src) (i : Nat) : String :=
  let (l, c) := s.lineCol i
  s!"{s.path}:{l}:{c}"

/-- The start of the line containing index `i`. -/
def Src.lineStart (s : Src) (i : Nat) : Nat :=
  s.lineStarts.getD ((s.lineCol i).1 - 1) 0

/-- Whether only spaces and tabs lie between indices `a` and `b`. -/
def Src.blankBetween (s : Src) (a b : Nat) : Bool :=
  (s.chars.extract a b).all (fun c => c == ' ' || c == '\t')

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

/-- One edit: replace characters `[start, stop)` by `text`. -/
structure Edit where
  /-- First character replaced. -/
  start : Nat
  /-- One past the last character replaced. -/
  stop : Nat
  /-- The replacement. -/
  text : String

/-- Apply non-overlapping edits to a source. -/
def applyEdits (s : Src) (edits : Array Edit) : String := Id.run do
  let edits := edits.qsort (fun a b => a.start < b.start)
  let mut out := ""
  let mut pos := 0
  for e in edits do
    out := out ++ s.slice pos e.start ++ e.text
    pos := e.stop
  return out ++ s.slice pos s.size

end Splice
