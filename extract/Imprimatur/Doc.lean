/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The `Doc` IR and its TeX emitter

Rendered mathematics is built as a `Doc` (DESIGN §7.1), and turned into TeX
in one place, which handles:

- **parentheses,** from precedences;
- **display widths,** estimated from the TeX or given by a rule (`width :=`);
- **line breaks,** at break points, preferring the outermost ones;
- **n-ary chains,** made by flattening (built by the renderer).

Escaping happens where text enters a `Doc` (`Imprimatur.TeX.escape`); the
emitter only assembles.
-/

namespace Imprimatur

/-- A rendered formula. -/
inductive Doc where
  /-- Indivisible TeX with its display width. -/
  | text (tex : String) (width : Nat)
  /-- A sequence at precedence `prec`. Children carry the precedence they
  need, and are parenthesised when theirs is lower. -/
  | node (prec : Nat) (parts : Array Doc)
  /-- A child within a node: `minPrec` is the precedence it needs. -/
  | child (minPrec : Nat) (d : Doc)
  /-- A point where a line may break. -/
  | brk
  deriving Inhabited, Repr

/-- Atomic precedence: never parenthesised. -/
def Doc.maxPrec : Nat := 1024

/-- Commands that wrap their argument without taking space of their own. -/
def wrapperCommands : List String :=
  ["mathrm", "mathsf", "mathit", "mathbf", "mathcal", "mathbb", "mathtt", "text", "textrm",
   "textit", "textsf", "operatorname", "left", "right", "LeanMathConst", "LeanMathVar",
   "ensuremath", "mathfrak", "boldsymbol"]

/-- The display width of a piece of TeX, in characters: a command for a
symbol counts one, wrappers, spacing commands, braces and `^`/`_` count
nothing, and every other character counts one. -/
def texWidth (s : String) : Nat := Id.run do
  let cs := s.toList.toArray
  let mut w := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\\' then
      let mut j := i + 1
      while j < cs.size && cs[j]!.isAlpha do j := j + 1
      if j == i + 1 then
        -- A control symbol: \, \; \! \  take no width; \{ \} \# … take one.
        let d := cs.getD (i + 1) ' '
        unless d == ',' || d == ';' || d == '!' || d == ' ' || d == ':' do w := w + 1
        i := i + 2
      else
        let name := String.ofList (cs.extract (i + 1) j).toList
        unless wrapperCommands.contains name || name.startsWith "q" && name.endsWith "quad" do
          w := w + 1
        if name == "quad" || name == "qquad" then w := w + 2
        i := j
    else
      unless c == '{' || c == '}' || c == '^' || c == '_' || c == ' ' do w := w + 1
      i := i + 1
  return w

/-- Literal TeX, with its estimated width. -/
def Doc.tex (s : String) : Doc := .text s (texWidth s)

/-- The precedence of a document. -/
def Doc.prec : Doc → Nat
  | .node p _ => p
  | .child _ d => d.prec
  | _ => Doc.maxPrec

/-- The display width of a document, including parentheses it will get. -/
partial def Doc.width : Doc → Nat
  | .text _ w => w
  | .node _ ps => ps.foldl (· + ·.width) 0
  | .child m d => d.width + (if d.prec < m then 2 else 0)
  | .brk => 0

/-- A piece of the flattened output: text, or a break at a nesting depth. -/
inductive Piece where
  /-- Text and its width. -/
  | text (tex : String) (width : Nat)
  /-- A break point, `depth` nodes deep. -/
  | brk (depth : Nat)
  deriving Inhabited, Repr

/-- Flatten a document into pieces, inserting parentheses. -/
partial def Doc.pieces (d : Doc) (depth : Nat := 0) : Array Piece :=
  match d with
  | .text t w => #[.text t w]
  | .brk => #[.brk depth]
  | .node _ ps => ps.foldl (fun acc p => acc ++ p.pieces (depth + 1)) #[]
  | .child m c =>
    if c.prec < m then
      #[.text "(" 1] ++ c.pieces depth ++ #[.text ")" 1]
    else c.pieces depth

/-- Lines from pieces, breaking greedily at breaks no deeper than `maxDepth`:
a line is ended at the last usable break before it would exceed `limit`. -/
def breakLines (ps : Array Piece) (limit maxDepth : Nat) : Array String := Id.run do
  let mut lines : Array String := #[]
  let mut cur := ""
  let mut curW := 0
  -- Text since the last usable break, held back until the next break.
  let mut pend := ""
  let mut pendW := 0
  for p in ps do
    match p with
    | .text t w =>
      pend := pend ++ t
      pendW := pendW + w
    | .brk depth =>
      if depth ≤ maxDepth then
        if curW > 0 && curW + pendW > limit then
          lines := lines.push cur
          cur := pend
          curW := pendW
        else
          cur := cur ++ pend
          curW := curW + pendW
        pend := ""
        pendW := 0
  if curW > 0 && curW + pendW > limit then
    lines := lines.push cur
    cur := pend
  else
    cur := cur ++ pend
  return lines.push cur

/-- Render a document as TeX. If it is wider than `limit`, lines are broken
with `\LeanBreak`, using the outermost breaks that suffice. -/
def Doc.render (d : Doc) (limit : Nat := 80) : String := Id.run do
  let ps := d.pieces
  let all := String.join (ps.toList.map fun | .text t _ => t | .brk _ => "")
  if d.width ≤ limit then return all
  let maxDepth := ps.foldl (fun m p => match p with | .brk k => max m k | _ => m) 0
  let mut best := breakLines ps limit 0
  for k in [1:maxDepth + 1] do
    let widthOf (s : String) := texWidth s
    if best.all (widthOf · ≤ limit) then break
    best := breakLines ps limit k
  return " \\LeanBreak ".intercalate (best.map (·.trimAscii.toString)).toList

end Imprimatur
