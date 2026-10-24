/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The layouts of the prose and rules views, and the formula emitter

A view of a statement is made in two steps (docs/verified-extractor.md).
The extractor *gathers*, inside Lean, what the view says: which formulas
play which part, each formula already rendered in the paper's notation.
Then a pure *layout* sets the parts out as TeX. This module is the layouts,
with the parsers that take their TeX apart again; the `Doc` tree a formula
is rendered as, with its emitter, which is the one place parentheses are
decided; and the precedence policy of a notation rule's holes, which the
renderer and the validator's grammar share. The source is
`bundle/Layout.lean`, copied into both packages (`extract/Imprimatur/
Layout.lean`, `splice/Imprimatur/Layout.lean`); the lint keeps the copies
equal. It depends on Lean core only, holds definitions only, and every
definition is total, so that the theorems about it, proved in the splice
package, are about the functions the extractor runs.

Text is a list of characters throughout, which is what the proofs reason
about; the extractor converts at the boundary.

## Prose

The `prose` view of a theorem is a sentence: *Let* its variables, grouped
by type; *Assume* its hypotheses, each labelled when the paper refers to
it; *Then* its conclusion, which may be numbered conjuncts, *if and only
if*, or *there is v such that …*. Of a definition it is *We define f*. The
layout is a list of tokens (keywords, formulas in dollars, labels, item
numbers) printed in order; the parser lexes the text back into tokens and
reads the sentence off them.
-/

namespace Imprimatur.Layout

/-! ## Formulas: the `Doc` tree and its emitter

Rendered mathematics is built as a `Doc` (DESIGN §7.1), and turned into TeX
in one place, which handles:

- **parentheses,** from precedences;
- **display widths,** estimated from the TeX or given by a rule (`width :=`);
- **line breaks,** at break points, preferring the outermost ones;
- **n-ary chains,** made by flattening (built by the renderer).

Escaping happens where text enters a `Doc` (`Imprimatur.TeX.escape`); the
emitter only assembles. -/

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

/-- The precedence a hole of a notation rule needs, which the renderer
gives the child there and the validator's grammar demands of it: inside
braces nothing is needed, nor in an atomic template between its own tokens
(`(#a, #b)`, `\max(#a, #b)`); at its edge (`#e(#c)`, `#n!`) the template
does not delimit the argument, which must be atomic; otherwise the rule's
own precedence on the side its associativity allows, and one more
elsewhere. -/
def Doc.holeNeeds (prec : Nat) (assoc : String) (depth : Nat) (edge first last : Bool) : Nat :=
  if depth > 0 then 0
  else if prec ≥ Doc.maxPrec then (if edge then Doc.maxPrec else 0)
  else if assoc = "left" then (if first then prec else prec + 1)
  else if assoc = "right" then (if last then prec else prec + 1)
  else prec + 1

/-- Commands that wrap their argument without taking space of their own. -/
def wrapperCommands : List String :=
  ["mathrm", "mathsf", "mathit", "mathbf", "mathcal", "mathbb", "mathtt", "text", "textrm",
   "textit", "textsf", "operatorname", "left", "right", "LeanMathConst", "LeanMathVar",
   "ensuremath", "mathfrak", "boldsymbol"]

/-- The width of a command: a symbol counts one, a wrapper nothing, a quad
two. -/
def commandWidth (name : List Char) : Nat :=
  let s := String.ofList name
  (if wrapperCommands.contains s || (s.startsWith "q" && s.endsWith "quad") then 0 else 1) +
    (if s == "quad" || s == "qquad" then 2 else 0)

/-- The display width of TeX, in characters: a command for a symbol counts
one, wrappers, spacing commands, braces and `^`/`_` count nothing, and every
other character counts one. -/
def texWidthGo : List Char → Nat
  | [] => 0
  | ['\\'] => 0
  | '\\' :: d :: rest =>
    if d.isAlpha then
      let name := (d :: rest).takeWhile Char.isAlpha
      commandWidth name + texWidthGo ((d :: rest).drop name.length)
    else
      -- A control symbol: \, \; \! \  take no width; \{ \} \# … take one.
      (if d = ',' ∨ d = ';' ∨ d = '!' ∨ d = ' ' ∨ d = ':' then 0 else 1) + texWidthGo rest
  | c :: cs => (if c = '{' ∨ c = '}' ∨ c = '^' ∨ c = '_' ∨ c = ' ' then 0 else 1) + texWidthGo cs
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- The display width of a piece of TeX. -/
def texWidth (s : String) : Nat := texWidthGo s.toList

/-- Literal TeX, with its estimated width. -/
def Doc.tex (s : String) : Doc := .text s (texWidth s)

/-- The precedence of a document. -/
def Doc.prec : Doc → Nat
  | .node p _ => p
  | .child _ d => d.prec
  | _ => Doc.maxPrec

/-- The display width of a document, including parentheses it will get. -/
def Doc.width : Doc → Nat
  | .text _ w => w
  | .node _ ps => ps.foldl (fun acc p => acc + p.width) 0
  | .child m d => d.width + (if d.prec < m then 2 else 0)
  | .brk => 0
termination_by d => sizeOf d

/-- A piece of the flattened output: text, or a break at a nesting depth. -/
inductive Doc.Piece where
  /-- Text and its width. -/
  | text (tex : String) (width : Nat)
  /-- A break point, `depth` nodes deep. -/
  | brk (depth : Nat)
  deriving Inhabited, Repr

/-- Flatten a document into pieces, inserting parentheses: a child is
wrapped exactly when its precedence is below what its place needs. -/
def Doc.pieces (d : Doc) (depth : Nat := 0) : Array Doc.Piece :=
  match d with
  | .text t w => #[.text t w]
  | .brk => #[.brk depth]
  | .node _ ps => ps.foldl (fun acc p => acc ++ p.pieces (depth + 1)) #[]
  | .child m c =>
    if c.prec < m then
      #[.text "(" 1] ++ c.pieces depth ++ #[.text ")" 1]
    else c.pieces depth
termination_by sizeOf d

/-- Lines from pieces, breaking greedily at breaks no deeper than `maxDepth`:
a line is ended at the last usable break before it would exceed `limit`. -/
def breakLines (ps : Array Doc.Piece) (limit maxDepth : Nat) : Array String := Id.run do
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

mutual
/-- The end of a line, held reversed, less a lone `\` and the space before
it: a control space at the end of a line (`,\ ` before a break) is dropped
with it, not left to escape what follows. -/
def trimEndGo : List Char → List Char
  | '\\' :: '\\' :: rest => '\\' :: '\\' :: rest
  | '\\' :: rest => trimSpaces rest
  | l => l
termination_by l => (l.length, 0)

/-- The space before a dropped `\`, then the end of the line again. -/
def trimSpaces : List Char → List Char
  | [] => []
  | c :: rest => if c.isWhitespace then trimSpaces rest else trimEndGo (c :: rest)
termination_by l => (l.length, 1)
end

/-- A line trimmed, and a control space at its end dropped. -/
def trimLine (l : String) : String :=
  String.ofList (trimEndGo l.trimAscii.toString.toList.reverse).reverse

/-- Render a document as TeX. If it is wider than `limit`, lines are broken
with `\LeanBreak`, using the outermost breaks that suffice. -/
def Doc.render (d : Doc) (limit : Nat := 80) : String := Id.run do
  let ps := d.pieces
  let all := String.join (ps.toList.map fun | .text t _ => t | .brk _ => "")
  if d.width ≤ limit then return all
  let maxDepth := ps.foldl (fun m p => match p with | .brk k => max m k | _ => m) 0
  let mut best := breakLines ps limit 0
  for k in [1:maxDepth + 1] do
    if best.all (texWidth · ≤ limit) then break
    best := breakLines ps limit k
  return " \\LeanBreak ".intercalate (best.map trimLine).toList

/-! ## What the prose view says -/

/-- What a group of variables ranges over, as the sentence says it. The
formulas are `α`: TeX in the extractor, and statement parts in the paper's
model. -/
inductive VarKind (α : Type) where
  /-- `x, y ∈ T`: a type. -/
  | ofType (ty : α)
  /-- *be a type*, *be types*. -/
  | type
  /-- *be a proposition*, *be propositions*. -/
  | prop
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A group of consecutive variables of one type: their names, rendered. -/
structure VarGroup (α : Type) where
  /-- The names, as variables. -/
  names : List α
  /-- What they range over. -/
  kind : VarKind α
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A hypothesis: its label, when the paper refers to it (the name, escaped
for TeX), and its formula. -/
structure Hyp (α : Type) where
  /-- The label, if any. -/
  label : Option (List Char)
  /-- The formula. -/
  formula : α
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The conclusion, in words. -/
inductive Concl (α : Type) where
  /-- A formula. -/
  | formula (f : α)
  /-- Conjuncts, numbered `(1)`, `(2)`, …. -/
  | conjuncts (fs : List α)
  /-- *lhs if and only if rhs*. -/
  | iff (lhs rhs : α)
  /-- *there is v such that …*. -/
  | exists_ (w : α) (body : Concl α)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- What a theorem's sentence says. -/
structure Statement (α : Type) where
  /-- The variables, in groups. -/
  vars : List (VarGroup α)
  /-- The hypotheses. -/
  hyps : List (Hyp α)
  /-- The conclusion. -/
  concl : Concl α
  deriving Repr, BEq, Inhabited, DecidableEq

/-- What the prose view says: of a definition, *We define f*; of a theorem,
its sentence. -/
inductive Prose (α : Type) where
  /-- *We define f*. -/
  | define (formula : α)
  /-- A theorem's sentence. -/
  | statement (s : Statement α)
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ### Mapping the formulas -/

/-- Apply `f` to the type of a group. -/
def VarKind.map {α β : Type} (f : α → β) : VarKind α → VarKind β
  | .ofType ty => .ofType (f ty)
  | .type => .type
  | .prop => .prop

/-- Apply `f` to the formulas of a group. -/
def VarGroup.map {α β : Type} (f : α → β) (g : VarGroup α) : VarGroup β :=
  { names := g.names.map f, kind := g.kind.map f }

/-- Apply `f` to the formula of a hypothesis. -/
def Hyp.map {α β : Type} (f : α → β) (hy : Hyp α) : Hyp β :=
  { label := hy.label, formula := f hy.formula }

/-- Apply `f` to the formulas of a conclusion. -/
def Concl.map {α β : Type} (f : α → β) : Concl α → Concl β
  | .formula x => .formula (f x)
  | .conjuncts xs => .conjuncts (xs.map f)
  | .iff lhs rhs => .iff (f lhs) (f rhs)
  | .exists_ w body => .exists_ (f w) (body.map f)

/-- Apply `f` to the formulas of a sentence. -/
def Statement.map {α β : Type} (f : α → β) (s : Statement α) : Statement β :=
  { vars := s.vars.map (VarGroup.map f), hyps := s.hyps.map (Hyp.map f), concl := s.concl.map f }

/-- Apply `f` to the formulas of the prose view. -/
def Prose.map {α β : Type} (f : α → β) : Prose α → Prose β
  | .define x => .define (f x)
  | .statement s => .statement (s.map f)

/-! ## Tokens -/

/-- The fixed words of a sentence. -/
inductive Kw where
  /-- `\LeanProse{` -/
  | prose
  /-- `We define ` -/
  | weDefine
  /-- `Let ` -/
  | letK
  /-- `Assume ` -/
  | assumeK
  /-- `Then ` -/
  | thenK
  /-- `, ` -/
  | comma
  /-- ` and ` -/
  | andK
  /-- ` be a type` -/
  | beAType
  /-- ` be types` -/
  | beTypes
  /-- ` be a proposition` -/
  | beAProp
  /-- ` be propositions` -/
  | beProps
  /-- `. `, between sentences -/
  | dotSpace
  /-- `.}`, the end -/
  | endK
  /-- `there is ` -/
  | thereIs
  /-- ` such that ` -/
  | suchThat
  /-- ` if and only if ` -/
  | iffK
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The text of a keyword. -/
def kwText : Kw → List Char
  | .prose => "\\LeanProse{".toList
  | .weDefine => "We define ".toList
  | .letK => "Let ".toList
  | .assumeK => "Assume ".toList
  | .thenK => "Then ".toList
  | .comma => ", ".toList
  | .andK => " and ".toList
  | .beAType => " be a type".toList
  | .beTypes => " be types".toList
  | .beAProp => " be a proposition".toList
  | .beProps => " be propositions".toList
  | .dotSpace => ". ".toList
  | .endK => ".}".toList
  | .thereIs => "there is ".toList
  | .suchThat => " such that ".toList
  | .iffK => " if and only if ".toList

/-- The keywords, in the order the lexer tries them. No keyword is a prefix
of another, so the order does not matter. -/
def kws : List Kw :=
  [.prose, .weDefine, .letK, .assumeK, .thenK, .comma, .andK, .beAType, .beTypes, .beAProp,
   .beProps, .dotSpace, .endK, .thereIs, .suchThat, .iffK]

/-- A token of a sentence. -/
inductive Tok where
  /-- A keyword. -/
  | kw (word : Kw)
  /-- A formula, in dollars. -/
  | formula (f : List Char)
  /-- A hypothesis label, `\LeanHyp{name} `. -/
  | label (name : List Char)
  /-- An item number, `(digits)~`. -/
  | item (digits : List Char)
  deriving Repr, BEq, Inhabited, DecidableEq

/-- `\LeanHyp{` -/
def labelOpen : List Char := "\\LeanHyp{".toList

/-- The text of a token. -/
def tokChars : Tok → List Char
  | .kw word => kwText word
  | .formula f => '$' :: f ++ ['$']
  | .label n => labelOpen ++ n ++ ['}', ' ']
  | .item ds => '(' :: ds ++ [')', '~']

/-- The text of tokens, in order. -/
def printToks (ts : List Tok) : List Char := (ts.map tokChars).flatten

/-! ## The layout -/

/-- The decimal digits of a number, most significant first: `fuel` bounds
the recursion. -/
def decimalGo : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let dg := Nat.digitChar (n % 10)
    if n < 10 then dg :: acc else decimalGo fuel (n / 10) (dg :: acc)

/-- The decimal digits of a number. -/
def decimal (n : Nat) : List Char := decimalGo (n + 1) n []

/-- `x`, `x and y`, `x, y and z`: the items after the first, each with its
separator before it. -/
def andRestToks : List (List Tok) → List Tok
  | [] => []
  | [y] => .kw .andK :: y
  | y :: z :: zs => .kw .comma :: y ++ andRestToks (z :: zs)

/-- `x`, `x and y`, `x, y and z`. -/
def andToks : List (List Tok) → List Tok
  | [] => []
  | y :: ys => y ++ andRestToks ys

/-- `, ` -/
def commaSep : List Char := ", ".toList

/-- The names of a group, `x, y`. -/
def joinComma : List (List Char) → List Char
  | [] => []
  | [n] => n
  | n :: ns => n ++ commaSep ++ joinComma ns

/-- ` \in ` -/
def inSep : List Char := " \\in ".toList

/-- A group of variables: `$x, y \in T$`, `$x$ be a type`, `$x, y$ be
types`, …. -/
def groupToks : VarGroup (List Char) → List Tok
  | ⟨names, .ofType ty⟩ => [.formula (joinComma names ++ inSep ++ ty)]
  | ⟨[], .type⟩ => [.formula [], .kw .beTypes]
  | ⟨[n], .type⟩ => [.formula n, .kw .beAType]
  | ⟨n :: n' :: ns, .type⟩ => [.formula (joinComma (n :: n' :: ns)), .kw .beTypes]
  | ⟨[], .prop⟩ => [.formula [], .kw .beProps]
  | ⟨[n], .prop⟩ => [.formula n, .kw .beAProp]
  | ⟨n :: n' :: ns, .prop⟩ => [.formula (joinComma (n :: n' :: ns)), .kw .beProps]

/-- A hypothesis: its label, if any, and its formula. -/
def hypToks : Hyp (List Char) → List Tok
  | ⟨some n, f⟩ => [.label n, .formula f]
  | ⟨none, f⟩ => [.formula f]

/-- Conjuncts numbered from `i`: `(i)~$f$`, …. -/
def numbered (i : Nat) : List (List Char) → List (List Tok)
  | [] => []
  | f :: fs => [.item (decimal i), .formula f] :: numbered (i + 1) fs

/-- A conclusion, in words. -/
def conclToks : Concl (List Char) → List Tok
  | .formula f => [.formula f]
  | .conjuncts fs => andToks (numbered 1 fs)
  | .iff lhs rhs => [.formula lhs, .kw .iffK, .formula rhs]
  | .exists_ w body => .kw .thereIs :: .formula w :: .kw .suchThat :: conclToks body

/-- Sentences, each ending with a full stop, separated by a space. -/
def sentencesToks : List (List Tok) → List Tok
  | [] => []
  | [s] => s
  | s :: t :: ts => s ++ .kw .dotSpace :: sentencesToks (t :: ts)

/-- The *Let* sentence, if there are variables. -/
def letToks : List (VarGroup (List Char)) → List (List Tok)
  | [] => []
  | g :: gs => [.kw .letK :: andToks ((g :: gs).map groupToks)]

/-- The *Assume* sentence, if there are hypotheses. -/
def assumeToks : List (Hyp (List Char)) → List (List Tok)
  | [] => []
  | hy :: hs => [.kw .assumeK :: andToks ((hy :: hs).map hypToks)]

/-- *Then*, after another sentence. -/
def thenKw : List (List Tok) → List Tok
  | [] => []
  | _ :: _ => [.kw .thenK]

/-- The *Then* sentence. -/
def thenToks (before : List (List Tok)) (c : Concl (List Char)) : List Tok :=
  thenKw before ++ conclToks c

/-- The tokens of a theorem's sentence, after `\LeanProse{`: its sentences,
and the end. -/
def statementToks (s : Statement (List Char)) : List Tok :=
  sentencesToks (letToks s.vars ++ assumeToks s.hyps ++
    [thenToks (letToks s.vars ++ assumeToks s.hyps) s.concl]) ++ [.kw .endK]

/-- The tokens of the prose view. -/
def proseToks : Prose (List Char) → List Tok
  | .define f => [.kw .prose, .kw .weDefine, .formula f, .kw .endK]
  | .statement s => .kw .prose :: statementToks s

/-- **The prose layout:** the text of the prose view. -/
def proseChars (pr : Prose (List Char)) : List Char := printToks (proseToks pr)

/-- The prose layout, as a string. -/
def proseLayout (pr : Prose (List Char)) : String := String.ofList (proseChars pr)

/-! ## The lexer -/

/-- The keyword at the front of the text, if any. -/
def kwAt (cs : List Char) : Option Kw := kws.find? fun word => (kwText word).isPrefixOf cs

/-- Lex the text into tokens, onto `acc` (held reversed): a formula at a
dollar, an item at a parenthesis, a label at `\LeanHyp{`, else a keyword. -/
def lexGo : List Char → List Tok → Option (List Tok)
  | [], acc => some acc.reverse
  | c :: cs, acc =>
    if c = '$' then
      let f := cs.takeWhile (· ≠ '$')
      match _h : cs.drop f.length with
      | ch :: rest => if ch = '$' then lexGo rest (.formula f :: acc) else none
      | [] => none
    else if c = '(' then
      let ds := cs.takeWhile (· ≠ ')')
      match _h : cs.drop ds.length with
      | ch :: ch' :: rest => if ch = ')' ∧ ch' = '~' ∧ !ds.isEmpty then lexGo rest (.item ds :: acc) else none
      | _ => none
    else if labelOpen.isPrefixOf (c :: cs) then
      -- `labelOpen` is nine characters, the first of which is `c`.
      let n := (cs.drop 8).takeWhile (· ≠ '}')
      match _h : (cs.drop 8).drop n.length with
      | ch :: ch' :: rest => if ch = '}' ∧ ch' = ' ' then lexGo rest (.label n :: acc) else none
      | _ => none
    else match kwAt (c :: cs) with
      | some word => lexGo (cs.drop ((kwText word).length - 1)) (.kw word :: acc)
      | none => none
termination_by cs _ => cs.length
decreasing_by
  all_goals simp_wf
  all_goals (try simp only [List.length_drop] at *)
  all_goals (try (have := congrArg List.length _h; simp only [List.length_drop, List.length_cons] at this))
  all_goals omega

/-- Lex the text into tokens. -/
def lex (cs : List Char) : Option (List Tok) := lexGo cs []

/-! ## The parser -/

/-- Whether `sub` occurs in the text. -/
def hasSub (sub : List Char) : List Char → Bool
  | [] => false
  | c :: cs => sub.isPrefixOf (c :: cs) || hasSub sub cs

/-- Split at the first occurrence of `sep`: the text before, and after. -/
def splitFirst (sep : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if sep.isPrefixOf (c :: cs) then some ([], (c :: cs).drop sep.length)
    else (splitFirst sep cs).map fun (a, b) => (c :: a, b)

/-- Split at every occurrence of `sep`, the current piece and the pieces
done held reversed. -/
def splitAllGo (sep : List Char) : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: cs, cur, acc =>
    if sep.isPrefixOf (c :: cs) then splitAllGo sep ((c :: cs).drop (max 1 sep.length)) [] (cur.reverse :: acc)
    else splitAllGo sep cs (c :: cur) acc
termination_by cs => cs.length
decreasing_by all_goals simp_wf; all_goals (try simp only [List.length_drop, List.length_cons]); all_goals omega

/-- Split at every occurrence of `sep`. -/
def splitAll (sep : List Char) (cs : List Char) : List (List Char) := splitAllGo sep cs [] []

mutual
/-- The groups of a *Let* sentence, onto `acc` (held reversed): a formula,
then its kind, then what follows it. -/
def parseGroups (acc : List (VarGroup (List Char))) : List Tok →
    Option (List (VarGroup (List Char)) × List Tok)
  | .formula f :: .kw .beAType :: ts => afterGroup ⟨splitAll commaSep f, .type⟩ acc ts
  | .formula f :: .kw .beTypes :: ts => afterGroup ⟨splitAll commaSep f, .type⟩ acc ts
  | .formula f :: .kw .beAProp :: ts => afterGroup ⟨splitAll commaSep f, .prop⟩ acc ts
  | .formula f :: .kw .beProps :: ts => afterGroup ⟨splitAll commaSep f, .prop⟩ acc ts
  | .formula f :: ts => ofTypeGroup acc ts (splitFirst inSep f)
  | _ => none
/-- A group of a type: its names and its type, if they come apart. -/
def ofTypeGroup (acc : List (VarGroup (List Char))) (ts : List Tok) :
    Option (List Char × List Char) → Option (List (VarGroup (List Char)) × List Tok)
  | some (ns, ty) => afterGroup ⟨splitAll commaSep ns, .ofType ty⟩ acc ts
  | none => none
/-- After a group: another, or the end of the sentence. -/
def afterGroup (g : VarGroup (List Char)) (acc : List (VarGroup (List Char))) : List Tok →
    Option (List (VarGroup (List Char)) × List Tok)
  | .kw .comma :: ts => parseGroups (g :: acc) ts
  | .kw .andK :: ts => parseGroups (g :: acc) ts
  | .kw .dotSpace :: ts => some ((g :: acc).reverse, ts)
  | _ => none
end

/-- The hypotheses of an *Assume* sentence, onto `acc` (held reversed):
each labelled or not, then what follows it; the sentence ends before
*Then*. -/
def parseHyps (acc : List (Hyp (List Char))) : List Tok → Option (List (Hyp (List Char)) × List Tok)
  | .label n :: .formula f :: .kw .comma :: ts => parseHyps (⟨some n, f⟩ :: acc) ts
  | .label n :: .formula f :: .kw .andK :: ts => parseHyps (⟨some n, f⟩ :: acc) ts
  | .label n :: .formula f :: .kw .dotSpace :: .kw .thenK :: ts =>
    some ((⟨some n, f⟩ :: acc).reverse, ts)
  | .formula f :: .kw .comma :: ts => parseHyps (⟨none, f⟩ :: acc) ts
  | .formula f :: .kw .andK :: ts => parseHyps (⟨none, f⟩ :: acc) ts
  | .formula f :: .kw .dotSpace :: .kw .thenK :: ts => some ((⟨none, f⟩ :: acc).reverse, ts)
  | _ => none

/-- The conjuncts after the first, onto `acc` (held reversed). -/
def parseItems (acc : List (List Char)) : List Tok → Concl (List Char) × List Tok
  | .kw .comma :: .item _ :: .formula f :: ts => parseItems (f :: acc) ts
  | .kw .andK :: .item _ :: .formula f :: ts => parseItems (f :: acc) ts
  | ts => (.conjuncts acc.reverse, ts)

/-- The conclusion after *there is w such that*, once the rest is read. -/
def afterSuch (w : List Char) :
    Option (Concl (List Char) × List Tok) → Option (Concl (List Char) × List Tok)
  | some (c, rest) => some (.exists_ w c, rest)
  | none => none

/-- A conclusion. -/
def parseConcl : List Tok → Option (Concl (List Char) × List Tok)
  | .kw .thereIs :: .formula w :: .kw .suchThat :: ts => afterSuch w (parseConcl ts)
  | .item _ :: .formula f :: ts => some (parseItems [f] ts)
  | .formula lhs :: .kw .iffK :: .formula rhs :: ts => some (.iff lhs rhs, ts)
  | .formula f :: ts => some (.formula f, ts)
  | _ => none

/-- The sentence, once its conclusion ends the text. -/
def finishWith (gs : List (VarGroup (List Char))) (hs : List (Hyp (List Char))) :
    Option (Concl (List Char) × List Tok) → Option (Statement (List Char))
  | some (c, [.kw .endK]) => some ⟨gs, hs, c⟩
  | _ => none

/-- The conclusion, which ends the sentence. -/
def finish (gs : List (VarGroup (List Char))) (hs : List (Hyp (List Char))) (ts : List Tok) :
    Option (Statement (List Char)) :=
  finishWith gs hs (parseConcl ts)

/-- After the hypotheses: the conclusion. -/
def afterAssume (gs : List (VarGroup (List Char))) :
    Option (List (Hyp (List Char)) × List Tok) → Option (Statement (List Char))
  | some (hs, ts) => finish gs hs ts
  | none => none

/-- After the groups: the hypotheses, or the conclusion. -/
def afterLet : Option (List (VarGroup (List Char)) × List Tok) → Option (Statement (List Char))
  | some (gs, .kw .assumeK :: ts) => afterAssume gs (parseHyps [] ts)
  | some (gs, .kw .thenK :: ts) => finish gs [] ts
  | _ => none

/-- A theorem's sentence, after `\LeanProse{`. -/
def parseStatement : List Tok → Option (Statement (List Char))
  | .kw .letK :: ts => afterLet (parseGroups [] ts)
  | .kw .assumeK :: ts => afterAssume [] (parseHyps [] ts)
  | ts => finish [] [] ts

/-- The prose view, from its tokens. -/
def parseProse : List Tok → Option (Prose (List Char))
  | [.kw .prose, .kw .weDefine, .formula f, .kw .endK] => some (.define f)
  | .kw .prose :: ts => (parseStatement ts).map .statement
  | _ => none

/-- **The prose parser:** the prose view, taken apart. -/
def proseSentence (cs : List Char) : Option (Prose (List Char)) := (lex cs).bind parseProse

/-! ## Plain formulas

The parser undoes the layout when the formulas are plain: no formula has a
dollar in it; no variable's name has a comma-space in it, and a group's
names, joined, have no `\in`, so the names and the type of a group come
apart; a group has a name and a conjunction a conjunct; and no label has a
closing brace. -/

/-- A formula with no dollar in it. -/
def Plain (f : List Char) : Prop := '$' ∉ f

/-- A name that comes apart from the others. -/
def PlainName (n : List Char) : Prop := Plain n ∧ hasSub commaSep n = false

/-- `\in` -/
def inWord : List Char := "\\in".toList

/-- A conclusion whose formulas are plain. -/
def Concl.Plain : Concl (List Char) → Prop
  | .formula f => Layout.Plain f
  | .conjuncts fs => fs ≠ [] ∧ ∀ f ∈ fs, Layout.Plain f
  | .iff lhs rhs => Layout.Plain lhs ∧ Layout.Plain rhs
  | .exists_ w body => Layout.Plain w ∧ body.Plain

/-- A group whose names are plain, and whose type is, if it has one. -/
def VarGroup.Plain (g : VarGroup (List Char)) : Prop :=
  g.names ≠ [] ∧ (∀ n ∈ g.names, PlainName n) ∧
    match g.kind with
    | .ofType ty => Layout.Plain ty ∧ hasSub inWord (joinComma g.names) = false
    | _ => True

/-- A hypothesis whose formula is plain, and whose label has no closing
brace. -/
def Hyp.Plain (hy : Hyp (List Char)) : Prop :=
  Layout.Plain hy.formula ∧ match hy.label with
    | some n => '}' ∉ n
    | none => True

/-- A sentence whose parts are plain. -/
def Prose.Plain : Prose (List Char) → Prop
  | .define f => Layout.Plain f
  | .statement s => (∀ g ∈ s.vars, g.Plain) ∧ (∀ hy ∈ s.hyps, hy.Plain) ∧ s.concl.Plain

/-! ## The rules figure

The `rules` view of an inductive predicate is a mathpartir figure: one
`\inferrule` per constructor, its premises above the line and its
conclusion below, labelled, and the rules separated by `\and`. A
`latex_rules` style with `label_macro` writes `\macro{Key}{label}%` before
each rule, so that prose can refer to it. The layout prints the figure line
by line; the parser reads the lines back and the rules off them. -/

/-! ### What the rules view says -/

/-- The `\macro{Key}{label}%` written before a rule, when the style asks for
it. -/
structure Mark where
  /-- the macro's name -/
  name : List Char
  /-- the rule's key: its name, without spaces -/
  key : List Char

/-- A rule, as the rules view shows it. The formulas are `α`, as for prose. -/
structure Rule (α : Type) where
  /-- its label macro, if the style writes one -/
  mark : Option Mark
  /-- its label -/
  label : List Char
  /-- its premises -/
  premises : List α
  /-- its conclusion -/
  concl : α

/-- Apply `f` to the formulas of a rule. -/
def Rule.map {α β : Type} (f : α → β) (ru : Rule α) : Rule β :=
  { mark := ru.mark, label := ru.label, premises := ru.premises.map f, concl := f ru.concl }

/-- An item of a figure: a rule, or a name that is no constructor. -/
inductive Item (α : Type)
  /-- a rule -/
  | rule (ru : Rule α)
  /-- a name that is no constructor, left as a comment -/
  | missing (name : List Char)

/-- Rules, as the items of a figure. -/
def ruleItems {α : Type} (rs : List (Rule α)) : List (Item α) := rs.map .rule

/-! ### Lines -/

/-- A line of the figure. -/
inductive Line
  /-- an empty line -/
  | blank
  /-- `\begin{mathpar}` -/
  | beginK
  /-- `\end{mathpar}` -/
  | endK
  /-- `\and`, between rules -/
  | andK
  /-- `  {`, opening the premises -/
  | openK
  /-- `  { }`, no premises -/
  | openEmpty
  /-- `  }`, closing the premises -/
  | closeK
  /-- `\inferrule[label]` -/
  | header (label : List Char)
  /-- `\macro{Key}{label}%`, before the header -/
  | mark (m : Mark) (label : List Char)
  /-- a premise, indented -/
  | line (text : List Char)
  /-- `  { f }`, the conclusion -/
  | concl (f : List Char)
  /-- `% name is not a constructor` -/
  | comment (name : List Char)

/-- `\inferrule[` -/
def inferOpen : List Char := "\\inferrule[".toList
/-- The indentation of a premise. -/
def indent : List Char := "    ".toList
/-- `  { `, before the conclusion. -/
def conclOpen : List Char := "  { ".toList
/-- ` }`, after the conclusion. -/
def conclClose : List Char := " }".toList
/-- ` \\`, after a premise that another follows. -/
def lineBreak : List Char := " \\\\".toList

/-- The text of a line. -/
def lineText : Line → List Char
  | .blank => []
  | .beginK => "\\begin{mathpar}".toList
  | .endK => "\\end{mathpar}".toList
  | .andK => "\\and".toList
  | .openK => "  {".toList
  | .openEmpty => "  { }".toList
  | .closeK => "  }".toList
  | .header label => inferOpen ++ (label ++ [']'])
  | .mark m label => '\\' :: (m.name ++ '{' :: (m.key ++ '}' :: '{' :: (label ++ ['}', '%'])))
  | .line text => indent ++ text
  | .concl f => conclOpen ++ (f ++ conclClose)
  | .comment name => "% ".toList ++ name ++ " is not a constructor".toList

/-- Lines, each ended by a newline but the last. -/
def joinLines : List (List Char) → List Char
  | [] => []
  | [l] => l
  | l :: l' :: ls => l ++ '\n' :: joinLines (l' :: ls)

/-! ### The layout -/

/-- The premises, one per line, each but the last ended by ` \\`. -/
def premiseLines : List (List Char) → List Line
  | [] => []
  | [pm] => [.line pm]
  | pm :: pm' :: ps => .line (pm ++ lineBreak) :: premiseLines (pm' :: ps)

/-- A rule's body: its premises between braces, if any, then its conclusion. -/
def bodyLines : List (List Char) → List Char → List Line
  | [], c => [.openEmpty, .concl c]
  | pm :: ps, c => .openK :: (premiseLines (pm :: ps) ++ [.closeK, .concl c])

/-- A rule's mark, if it has one. -/
def markLines : Option Mark → List Char → List Line
  | some m, label => [.mark m label]
  | none, _ => []

/-- A rule's lines: its mark, its header, its body. -/
def ruleLines (ru : Rule (List Char)) : List Line :=
  markLines ru.mark ru.label ++ .header ru.label :: bodyLines ru.premises ru.concl

/-- An item's lines: a rule between blank lines, then `\and`; or a comment. -/
def itemLines : Item (List Char) → List Line
  | .rule ru => .blank :: (ruleLines ru ++ [.blank, .andK])
  | .missing name => [.comment name]

/-- The lines less a final `\and`. -/
def trimAnd : List Line → List Line
  | [] => []
  | [.andK] => []
  | l :: ls => l :: trimAnd ls

/-- The figure's lines: `\begin{mathpar}`, the items' lines less the `\and`
after the last, `\end{mathpar}`. -/
def figureLines (items : List (Item (List Char))) : List Line :=
  .beginK :: trimAnd (items.map itemLines).flatten ++ [.endK]

/-- The text of the figure. -/
def figureChars (items : List (Item (List Char))) : List Char :=
  joinLines ((figureLines items).map lineText)

/-- The rules layout, as a string. -/
def figureLayout (items : List (Item (List Char))) : String :=
  String.ofList (figureChars items)

/-! ### The lexer -/

/-- The lines of the text, split at newlines, the current one held
reversed. -/
def linesGo : List Char → List Char → List (List Char)
  | [], cur => [cur.reverse]
  | c :: cs, cur => if c = '\n' then cur.reverse :: linesGo cs [] else linesGo cs (c :: cur)

/-- The lines of the text. -/
def lines (cs : List Char) : List (List Char) := linesGo cs []

/-- The text after a prefix, if it has it. -/
def dropPrefix (pre l : List Char) : Option (List Char) :=
  if pre.isPrefixOf l then some (l.drop pre.length) else none

/-- The text before a suffix, if it has it. -/
def dropSuffix (suf l : List Char) : Option (List Char) :=
  (dropPrefix suf.reverse l.reverse).map List.reverse

/-- The label of a mark, before its `}%`. -/
def markLabel (m k : List Char) : Option (List Char) → Option Line
  | some tail => (dropSuffix ['}', '%'] tail).map (.mark ⟨m, k⟩)
  | none => none

/-- A mark's key, between its braces, then its label. -/
def markKey (m rest : List Char) : Option Line :=
  let k := rest.takeWhile (· ≠ '}')
  markLabel m k (dropPrefix "}{".toList (rest.drop k.length))

/-- A mark's macro, up to its first brace, then its key. -/
def markAfter : Option (List Char) → Option Line
  | some rest =>
    let m := rest.takeWhile (· ≠ '{')
    markKey m (rest.drop (m.length + 1))
  | none => none

/-- A header's label, before its `]`. -/
def headerOf : Option (List Char) → Option Line
  | some rest => (dropSuffix [']'] rest).map .header
  | none => none

/-- A line after a backslash: a keyword, a mark (which ends in `%`), or a
header. -/
def backslashLine (l : List Char) : Option Line :=
  if l = "begin{mathpar}".toList then some .beginK
  else if l = "end{mathpar}".toList then some .endK
  else if l = "and".toList then some .andK
  else if l.getLast? = some '%' then markAfter (some l)
  else headerOf (dropPrefix "inferrule[".toList l)

/-- A line after `  {`: the opening of the premises, `  { }`, or the
conclusion. -/
def braceLine : List Char → Option Line
  | [] => some .openK
  | [' ', '}'] => some .openEmpty
  | ' ' :: rest => (dropSuffix conclClose rest).map .concl
  | _ => none

/-- A line after two spaces: a premise, a brace, or the closing brace. -/
def spaceLine : List Char → Option Line
  | ' ' :: ' ' :: text => some (.line text)
  | '{' :: rest => braceLine rest
  | ['}'] => some .closeK
  | _ => none

/-- A line read back. -/
def lineOf : List Char → Option Line
  | [] => some .blank
  | ' ' :: ' ' :: l => spaceLine l
  | '\\' :: l => backslashLine l
  | _ => none

/-- A line, onto lines. -/
def lexCons : Option Line → Option (List Line) → Option (List Line)
  | some t, some ts => some (t :: ts)
  | _, _ => none

/-- The lines read back. -/
def lexLines : List (List Char) → Option (List Line)
  | [] => some []
  | l :: ls => lexCons (lineOf l) (lexLines ls)

/-! ### The parser -/

mutual
/-- The premises up to the closing brace, onto `ps` (held reversed). -/
def parsePremises (ps : List (List Char)) : List Line → Option (List (List Char) × List Line)
  | .line pm :: ls => premiseNext ps pm ls
  | _ => none
termination_by ls => (ls.length, 0)

/-- After a premise: the closing brace, so it was the last; or another, so it
ends in ` \\`. -/
def premiseNext (ps : List (List Char)) (pm : List Char) : List Line →
    Option (List (List Char) × List Line)
  | .closeK :: ls => some ((pm :: ps).reverse, ls)
  | .line pm' :: ls => unbreak ps (dropSuffix lineBreak pm) (.line pm' :: ls)
  | _ => none
termination_by ls => (ls.length, 2)

/-- A premise less its ` \\`, then the rest. -/
def unbreak (ps : List (List Char)) : Option (List Char) → List Line →
    Option (List (List Char) × List Line)
  | some pm, ls => parsePremises (pm :: ps) ls
  | none, _ => none
termination_by _ ls => (ls.length, 1)
end

/-- The rule, once its premises are read: its conclusion follows them. -/
def withPremises (mark : Option Mark) (label : List Char) :
    Option (List (List Char) × List Line) → Option (Rule (List Char) × List Line)
  | some (ps, .concl c :: ls) => some (⟨mark, label, ps, c⟩, ls)
  | _ => none

/-- A rule's body: no premises and its conclusion, or its premises. -/
def parseBody (mark : Option Mark) (label : List Char) : List Line →
    Option (Rule (List Char) × List Line)
  | .openEmpty :: .concl c :: ls => some (⟨mark, label, [], c⟩, ls)
  | .openK :: ls => withPremises mark label (parsePremises [] ls)
  | _ => none

/-- A rule: its mark, if any, then its header, then its body. -/
def parseRule : List Line → Option (Rule (List Char) × List Line)
  | .mark m label :: .header label' :: ls =>
    if label = label' then parseBody (some m) label ls else none
  | .header label :: ls => parseBody none label ls
  | _ => none

/-- A rule, which must end its chunk. -/
def ruleOf : Option (Rule (List Char) × List Line) → Option (Rule (List Char))
  | some (ru, [.blank]) => some ru
  | _ => none

/-- A chunk between `\and`s: a blank line, then a rule. -/
def parseChunk : List Line → Option (Rule (List Char))
  | .blank :: ls => ruleOf (parseRule ls)
  | _ => none

/-- A rule, onto rules. -/
def consRule : Option (Rule (List Char)) → Option (List (Rule (List Char))) →
    Option (List (Rule (List Char)))
  | some ru, some rs => some (ru :: rs)
  | none, _ => none
  | some _, none => none

/-- The rules of the chunks. -/
def parseChunks : List (List Line) → Option (List (Rule (List Char)))
  | [] => some []
  | ch :: chs => consRule (parseChunk ch) (parseChunks chs)

/-- The chunks between `\and` lines, the current one held reversed. -/
def chunks (cur : List Line) : List Line → List (List Line)
  | [] => [cur.reverse]
  | .andK :: ls => cur.reverse :: chunks [] ls
  | l :: ls => chunks (l :: cur) ls

/-- The lines before the final `\end{mathpar}`. -/
def bodyOf : List Line → Option (List Line)
  | [] => none
  | [.endK] => some []
  | l :: ls => (bodyOf ls).map (List.cons l)

/-- The rules of a body. -/
def rulesOf : Option (List Line) → Option (List (Rule (List Char)))
  | some ls => parseChunks (chunks [] ls)
  | none => none

/-- The figure's rules: none between `\begin{mathpar}` and `\end{mathpar}`,
or those of its body. -/
def figureOf : List Line → Option (List (Rule (List Char)))
  | [.beginK, .endK] => some []
  | .beginK :: ls => rulesOf (bodyOf ls)
  | _ => none

/-- The figure of the lines, if they lex. -/
def ofLines : Option (List Line) → Option (List (Rule (List Char)))
  | some ls => figureOf ls
  | none => none

/-- The rules of a figure, read back from its text. -/
def figure (cs : List Char) : Option (List (Rule (List Char))) :=
  ofLines (lexLines (lines cs))

/-! ### Plain rules

The parser undoes the layout when no formula, label, macro or key holds a
newline, a macro's name holds no `{` and a key no `}`. -/

/-- A mark the lexer takes apart. -/
def Mark.Plain (m : Mark) : Prop :=
  '\n' ∉ m.name ∧ '{' ∉ m.name ∧ '\n' ∉ m.key ∧ '}' ∉ m.key

/-- A rule whose lines each hold one line. -/
def Rule.Plain (ru : Rule (List Char)) : Prop :=
  '\n' ∉ ru.label ∧ (∀ pm ∈ ru.premises, '\n' ∉ pm) ∧ '\n' ∉ ru.concl ∧
    match ru.mark with
    | some m => m.Plain
    | none => True

end Imprimatur.Layout
