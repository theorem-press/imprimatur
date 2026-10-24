/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

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

end SpliceTest.Reference
