/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Writing TeX

Escaping, and the conversion of docstrings (Markdown) to TeX. Generated TeX
must never break the document it is spliced into: braces always balance,
and every special character is escaped.
-/

namespace Imprimatur.TeX

/-- Escape TeX's special characters. Non-ASCII characters are kept; the
paper (or `imprimatur.sty`) maps them. -/
def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ match c with
    | '\\' => "\\textbackslash{}"
    | '{' => "\\{" | '}' => "\\}" | '#' => "\\#" | '$' => "\\$" | '%' => "\\%"
    | '&' => "\\&" | '_' => "\\_"
    | '~' => "\\textasciitilde{}" | '^' => "\\textasciicircum{}"
    | c => c.toString) ""

/-- Whether braces balance in `s`, ignoring escaped ones. -/
def balanced (s : String) : Bool := Id.run do
  let mut depth : Int := 0
  let mut esc := false
  for c in s.toList do
    if esc then esc := false; continue
    if c == '\\' then esc := true
    else if c == '{' then depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth < 0 then return false
  return depth == 0 && !esc

/-- Convert a docstring's Markdown to TeX. Handled: `code`, **bold**,
*emphasis*, and `$…$` maths, which passes through unchanged when its braces
balance and it has no `%`. Paragraph breaks are kept. Everything else is
escaped. -/
partial def markdown (s : String) : String :=
  go s.toList ""
where
  /-- The text up to the next `delim`, and what follows it. -/
  upTo (delim : List Char) : List Char → List Char → Option (List Char × List Char)
    | acc, cs@(c :: rest) =>
      if cs.take delim.length == delim then some (acc.reverse, cs.drop delim.length)
      else if c == '\n' && rest.head? == some '\n' then none
      else upTo delim (c :: acc) rest
    | _, [] => none
  go : List Char → String → String
    | [], out => out
    | '`' :: rest, out =>
      match upTo ['`'] [] rest with
      | some (code, after) => go after (out ++ "\\LeanCodeInline{" ++ escape (String.ofList code) ++ "}")
      | none => go rest (out ++ "`")
    | '*' :: '*' :: rest, out =>
      match upTo ['*', '*'] [] rest with
      | some (b, after) => go after (out ++ "\\textbf{" ++ markdown (String.ofList b) ++ "}")
      | none => go rest (out ++ "**")
    | '*' :: rest, out =>
      match upTo ['*'] [] rest with
      | some (e, after) =>
        if e.isEmpty then go rest (out ++ "*")
        else go after (out ++ "\\emph{" ++ markdown (String.ofList e) ++ "}")
      | none => go rest (out ++ "*")
    | '$' :: rest, out =>
      match upTo ['$'] [] rest with
      | some (m, after) =>
        let m := String.ofList m
        if balanced m && !m.isEmpty && !m.contains '%' then go after (out ++ "$" ++ m ++ "$")
        else go rest (out ++ "\\$")
      | none => go rest (out ++ "\\$")
    | c :: rest, out => go rest (out ++ escape c.toString)

end Imprimatur.TeX
