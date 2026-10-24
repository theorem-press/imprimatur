/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The layouts of the prose and rules views

A view of a statement is made in two steps (docs/verified-extractor.md).
The extractor *gathers*, inside Lean, what the view says: which formulas
play which part, each formula already rendered in the paper's notation.
Then a pure *layout* sets the parts out as TeX. This module is the layouts,
with the parsers that take their TeX apart again. The source is
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

end Imprimatur.Layout
