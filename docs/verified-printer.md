# Proposal: the printer, proved

Status: proposal. Follows Danielsson, *Correct-by-Construction
Pretty-Printing* (DTP 2013; the about paper's `Danielsson13`). Companion to
docs/verified-validator.md, whose parser it builds on, and
docs/verified-extractor.md, whose pattern (the code that runs is the code
that is proved) it keeps.

## Goal

Today Pollack-consistency is checked per formula and not proved of the
printer. The extractor renders a formula; a separate computation in
`MetaM` builds the reading it expects (`Render.Expect`); the proved parser
reads the TeX back; and the formula is accepted when the parser returns one
reading, with no flag set, that matches the expected one
(`SpliceModel.Validator.Accepts`, `pollack`). Three things are then
trusted, and the paper's trusted base names them:

1. **That the grammar holds every rendering.** The renderer
   (`Render.fillTemplate`) and the grammar (`Validate.ofRule`) each walk a
   rule's template on their own; they share only `Doc.holeNeeds` and
   `Chain.allows`. A rendering outside the grammar is refused ("the
   notation does not read it back"), so this is a completeness gap, not a
   soundness one, but the paper states it as an assumption.
2. **That the expected reading is what was printed.** `Expect` is built
   beside the `Doc`, not from it. Where the renderer gives no expected
   reading (`⁇`: chains, folded binders, `∀` with binders, `match`,
   synonyms; #41), only what is below is compared: 21 of the 662 formulas
   of the twenty-page paper in part, 31 not at all.
3. **That the text validated is the text printed.** It is not, always (see
   *Findings*).

Danielsson's construction removes 1 and 2 by making the document a
derivation: what is printed and what it reads as are one object, and a
theorem, proved once for the emitter, says that the printed text parses
back as that reading. Uniqueness, his *unambiguous for that string*, stays
a per-formula fact, decided by the parser we already have and proved
complete.

## Danielsson's construction

| Danielsson | Here |
|---|---|
| `Grammar A`, a grammar with semantic actions | `Grammar` (the notation's productions) with `Reading` as the result |
| `x ∈ g · s`, inductive: `s` parses as `x` | `Exp A G ts s p excl ch i j r σ` (`SpliceModel.ReadBack`) |
| `Doc g x`, a document indexed by grammar and value | `Form`, a tree naming the production at each node, with `Form.check` (below) |
| `pretty : (x : A) → Doc g x` | the renderer, `Expr → Form`, in `MetaM` |
| `render : Doc g x → String` | `Form.toDoc`, then `Doc.render` |
| `parsable : (d : Doc g x) → x ∈ g · render d` | **Theorem P** below |
| `Unambiguous g`, weakened to the string | the parser returns one reading, flags clear (`readBack_complete`) |
| round trip: `parse (render (pretty x)) ≡ yes (x, p)` | **Theorem R** below |

Two differences matter:

- **Danielsson's `Doc` is well-formed by its type.** Lean could index
  `Form` by production and reading too, but the grammar is built at run
  time from the notation module, and the renderer is `MetaM` code that
  could not easily produce such a term. So `Form` is plain data, and a
  decidable, linear-time `Form.check` plays the type's part: the renderer
  is not trusted to build a well-formed form, because each form is checked
  before it is printed. This is the only check of the design that runs.
  Unlike the parse, it searches nothing.
- **His values are the reading's whole meaning.** Ours stand for Lean
  terms, and the step from `Expr` to `Form` (which rule matched, what is
  hidden) is the renderer's, in `MetaM`. Theorem R says the formula reads
  only as its form's reading. That the reading denotes the `Expr` up to
  what the notation hides stays trusted, as it is now. Phase 5 proposes
  checking it.

## Design

### Print from the production

A node of a formula is printed by walking its production's body, not the
rule's template. A production's symbols keep the template's text, so that
printing is byte-for-byte what it is now:

```
inductive Sym where
  | text (tex : String)          -- template text; its tokens are `tokenize tex`
  | hole (sort : String) (prec : Nat)
  | var
  | list (elem : List Sym) (sep : String) (min : Nat)
```

`Sym.tok t` becomes `Sym.text tex`, and compilation splits it into the
`ASym.tok` of each of its tokens, so the parser and its proofs see the
same compiled bodies as today. `ofRule` moves to the shared module (it
depends on the notation rule's template, precedence, associativity, hidden
variables, `flatten` and `sep`, all plain data) and is the only place a
template is split. The renderer's `fillTemplate` is deleted. What the
renderer still decides is which rule matches and what fills each hole.

### Forms

```
inductive Form where
  | atom (tex : String) (sort : String) (isVar : Bool)   -- a leaf production of this formula
  | node (k : Nat) (kids : List Form)                     -- production k; one kid per hole and var, in body order
  | list (k : Nat) (kids : List (List Form))              -- production k with lists: each list's elements
  | coe (k : Nat) (arg : Form)                            -- coercion production k, hidden
  | shown (k : Nat) (arg : Form)                          -- coercion k, shown: an ordinary node
  | code (tex : String) (sort : String)                   -- `\LeanMathCode{…}`, one opaque token
```

Leaves are the per-formula atom productions that `validate` adds today
(`base.extend leaves`). A form fixes the grammar `G f = base.extend
(atoms f)`.

- `Form.reading : Form → Reading` is `mkReading pr.name pr.order` over the
  kids' readings, with application normalised exactly as the parser
  normalises it. A hidden coercion's reading is its argument's.
- `Form.toDoc : Grammar → Form → Doc` prints a node by its production's
  body: text as `Doc.text`, a hole as `Doc.child (holeNeeds …) kid`, a
  list's elements with its separator. The `Doc` it builds is the one
  `fillTemplate` builds today. That equality is the differential test of
  phase 1 (goldens byte-identical).

### `Form.check`: the type, as a function

`Form.check A G (s p excl ch) f : Option String` returns the form's sort
when `f` is a derivation of an expression of sort `s`, at precedence `p`,
not by `excl`, under chain `ch`. It follows the constructors of `Reads`
one by one, with every existential fixed by the form:

- **`node k`:** production `k` exists, is no coercion and no variable, and
  is not `excl`. Its sort is compatible with `s`. `p ≤ pr.prec`, or the
  emitter parenthesises (`prec < need`), which `Reads.paren` reads at
  precedence 0 with no exclusion and a fresh chain. Its body is checked
  left to right, threading `A.bind`, each hole's kid checked at
  `A.expected env sort`.
- **`coe k`:** `Chain.allows A pr s'`, and the argument is checked under
  `ch.push A pr s'`, the very test `Reads.coe` makes.
- **`list k`:** each list has at least `min` elements.
- **Joins:** adjacent printed pieces tokenize apart (below).

`check` is structural recursion on the form, so it is total and linear,
apart from the sort algebra's own cost.

### The theorems

Let `ts = tokenize (Doc.render ∞ (Form.toDoc G f))`.

- **Theorem P (parsable).** `Form.check A G (s, p, excl, ch) f = some σ →
  Exp A G ts s p excl ch 0 ts.size (Form.reading f) σ`.
  - By induction on `f`, one case per constructor of `Reads`, with four
    lemmas.
  - **Tokens compose:** `tokenize (a ++ b) = tokenize a ++ tokenize b`
    when `Joins a b`, which says that `a` does not end in a control word
    when `b` starts with a letter, does not end in a lone `\`, and does not
    split a `\LeanMathCode{…}` group. `check` tests `Joins` at every seam,
    so a template like `#a\cdot#b` filled with `b := x` cannot run
    `\cdotx` together unnoticed.
  - **Parentheses:** `Doc.pieces` wraps a child exactly when `prec <
    need`, which is `Reads.paren`.
  - **Groups:** a hole inside braces needs precedence 0
    (`holeNeeds`, `depth > 0`), which is `Reads.group`, or the body's own
    `{`/`}` tokens.
  - **Bodies:** the tokens of a node are the concatenation of its body's
    pieces, which is `Reads.tok`, `hole`, `var`, `tail`, `nil` and `more`
    in sequence.
- **Theorem R (round trip; Danielsson's).** If `check … f = some σ`, and
  `readBackWith A (G f) ts s = (#[r], flags)` with `flags.any = false`, then
  `r = Form.reading f`. The parser is complete (`readBack_complete`), so
  the reading of Theorem P is among those it returns, and the returned
  list has only `r`. With soundness this is Danielsson's round trip, with
  his hypothesis *unambiguous for this string* decided per formula.
- **Theorem W (Wiedijk's property, of the printer).** Two forms that
  check, are accepted, and print the same tokens have the same reading. It
  follows from R, and is Pollack-consistency of the printer, not of one
  formula: no two readings print alike.

`Validator.Accepts` loses its `matches` conjunct: the comparison with an
expected reading is replaced by Theorem R, and the expected reading is
`Form.reading f`, which has no `any`. Every form the grammar has a
production for is then compared in full, including chains, folded binders
and `∀`, which closes #41 for those. `match` and `\LeanMathCode` leaves
are compared as what they are: a production for the cases, and an opaque
token.

### The model

`Validator.expect q` and `Anatomy.print q` become `Form.reading (form q)`
and the formula printed from `form q`: one function of a part, `form`, in
place of two that the model must assume agree. `Anatomy.Sound`'s
`formulas` and `ruleFormulas` are already theorems for the validator's
world (`Validated.sound`). The paper's `Validated.Prints` keeps only its
layout clauses (`prose`, `rules`, `plain`, `rulesPlain`), since that the
grammar holds every rendering is now Theorem P. Theorem 1.3 of the paper
then rests on less: the layouts, which are already proved to read back,
and the meaning of a reading.

## Findings

Reading the code for this design turned up three things that are true now
and that the paper does not say.

- **The text validated is not always the text printed.** `validate`
  reads back each formula as `d.render 100000`, but the `math` view
  prints a definition at three quarters of the width (`mathView`), and an
  equation's right-hand side is broken at the width and its breaks turned
  into aligned rows (`equationRow`), both in `Views/Math.lean`. A broken line differs from the unbroken
  one by `\LeanBreak` and spaces, which the tokenizer drops, and by
  `trimLine`, which drops a control space (`\ `) at the end of a line. The
  tokenizer keeps `\ ` as a token, so the two token sequences can differ.
  Either validate the text as printed (one line in `validate`, recommended),
  or prove `tokenize (render w d) = tokenize (render ∞ d)` with control
  spaces at breaks removed, and require that no production has a `\ `
  token.
- **Seams are unchecked.** Pieces are joined without a separator. A
  template that ends a piece in a control word, before a hole whose filler
  starts with a letter, prints one token where two were meant. The
  validator reads the joined text, so this is refused and not misread, but
  only because the token sequence then fails to parse. `Joins` makes it a
  checked condition with a message saying which seam it is.
- **The renderer and the grammar split templates separately**
  (`fillTemplate` and `ofRule`): the duplication behind trusted item 1.

## What stays trusted

- **The meaning of a reading:** that `Form.reading (form e)` stands for
  `e` up to what the notation hides. The renderer's matching of rules, in
  `MetaM`, decides it.
- **The sort algebra,** as now: theorems P and R hold for every algebra,
  and what it says of Lean's types is tested.
- **Glyphs** (#43) and the notation's choice of symbols (Wiedijk's weak
  failures), as now.
- **Uniqueness is decided, not proved, per formula,** as in Danielsson,
  whose round trip assumes the grammar unambiguous for the string. Proving
  a notation's grammar unambiguous in advance, for a class of notations
  such as operator-precedence grammars with distinct tokens, would remove
  the parse from the run. That is research, not part of this plan.

## Migration plan

Each phase keeps the golden bundles, the end-to-end suite and the about
paper byte-identical unless it says otherwise.

| Phase | Work | Exit |
|---|---|---|
| 0 | **Validate what is printed.** `validate` reads the text at the view's width. | The goldens change only where a broken line's tokens differed. List those, if any |
| 1 | **Print from the production.** `Sym.text`; `ofRule` in the shared module; `Form`, `Form.toDoc`, `Form.reading`; the renderer builds forms, and `fillTemplate` and `Expect` go. | Goldens byte-identical. The bundle's readings are spelled as now |
| 2 | **`Form.check`,** run before printing, with messages for each failed condition (a seam, a precedence, a chain). | Goldens byte-identical: no form in the fixtures, the about paper or LLMbda fails |
| 3 | **Theorem P,** with the token, parentheses and group lemmas. | `parsable` proved of the module that runs, for any algebra |
| 4 | **Theorems R and W;** `Accepts` without `matches`; the model's `expect` and `print` from `form`; `Prints` reduced. | `#41` closed for every form with a production; the paper's §10, trusted base and contributions restated |
| 5 | **Optional: check the meaning.** `Form.denote` rebuilds an `Expr` from a reading by the rules' patterns, and the renderer checks `isDefEq` with the source, up to what the notation hides. | The meaning of a reading checked per formula, as the reading is now |

## Risks

- **Byte-identical printing.** Printing from the production must
  reproduce `fillTemplate`'s spacing, widths (`r.width` on the first text
  piece) and break points (`breakBefore`). The goldens will catch any
  difference, and `Sym.text` keeps the template's text to make it
  possible.
- **The size of Theorem P.** It is one induction, but over `Reads`'
  eleven constructors, with sorts and bindings threaded. It is smaller
  than completeness (the 1,321 lines of `ReadBackComplete.lean`), since
  nothing is searched. Estimate: 1,000 to 1,500 lines, of which the token
  lemma is perhaps 300.
- **Forms the grammar lacks.** Where today's renderer prints something no
  production describes, `check` fails and phase 2 says so. Each such form
  needs a production, or a `code` leaf.

## Decisions needed

1. **Phase 0 alone, now.** The mismatch between the validated and printed
   text is independent of the rest, and small (recommended).
2. **Check forms at run time** (recommended), or index `Form` by its
   reading and production in Lean's types, as Danielsson does. The second
   would need the renderer to produce dependently typed terms in `MetaM`.
3. **Phase 5.** Checking the meaning of a reading is the last link from
   the printed formula to the `Expr`, and the largest change to the
   renderer. Leave it for after the arXiv preprint (recommended), or
   include it.
4. **The paper's claim, after phase 4:** "the printer is
   Pollack-consistent by construction, given that the notation's grammar
   reads each printed formula one way, which the parser decides".
