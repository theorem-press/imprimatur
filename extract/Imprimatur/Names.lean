/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Names from keys

A key in the paper is a Lean name as `Name.toString` writes it: components
joined by `.`, a component that is not an identifier (a number, or a name
with a dot in it, as a module named after an arXiv number has) written
between `«` and `»`, and a numeric component written as its digits.
-/

namespace Imprimatur

open Lean (Name)

/-- Turn a dotted string into a `Name`, component by component, reading
`«…»` as one component whatever it holds and a run of digits as a numeric
component: `Arxiv.«0805.3777».isMaxRank` has three components, and
`_private.A.0.B` a numeric third one. -/
def toName (s : String) : Name := Id.run do
  let mut n : Name := .anonymous
  let mut cur := ""
  let mut depth := 0
  let push (n : Name) (c : String) : Name :=
    if c.startsWith "«" && c.endsWith "»" && c.length ≥ 2 then
      .str n (c.drop 1 |>.dropEnd 1 |>.toString)
    else if !c.isEmpty && c.all Char.isDigit then
      match c.toNat? with
      | some k => .num n k
      | none => .str n c
    else .str n c
  for ch in s.toList do
    if ch == '«' then depth := depth + 1; cur := cur.push ch
    else if ch == '»' then depth := depth - 1; cur := cur.push ch
    else if ch == '.' && depth == 0 then n := push n cur; cur := ""
    else cur := cur.push ch
  return push n cur

end Imprimatur
