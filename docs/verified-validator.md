# Proposal: the validator, proved

Status: proposal. Supersedes the plan in #22 (a model with property tests)
with the pattern of docs/verified-extractor.md: the code that runs is the
code that is proved. Companion to `docs/verified-splicer.md` and
`docs/verified-extractor.md`.

## Goal

The paper's claim about rendering is Wiedijk's Pollack-consistency: parsing a
printed statement gives back that statement. Today the claim rests on
translation validation (DESIGN §18.4): as the extractor renders a formula it
builds the reading it expects, then reads the TeX back in the notation's
grammar and refuses the formula unless it has exactly one reading, and that
reading is the expected one. Three things make this a check and not a proof:

1. **The parser is trusted.** `Validate.readBack` is a memoised chart parser
   with a work budget and pruning; nothing says the readings it finds are
   readings, or that "one reading" means the grammar has no other.
2. **The matcher is trusted.** `Validate.readingMatches` compares a reading
   with the expected one as strings, with `⁇` matching any subterm; an atom
   whose TeX contains `;`, `[` or `]` can make two trees print alike.
3. **The expected reading is the renderer's word.** Where the renderer gives
   a form no expected reading (`⁇`: `∀` with binders, `match`, chains,
   folded binders, synonyms, fallback text; #41), the check rests on the
   grammar following the renderer; and that the expected reading *is* the
   source expression up to what the notation declares invisible is the
   renderer's construction of it, in `MetaM`.

This proposal removes 1 and 2 from the trusted base, states 3 as the
hypothesis it is, and says what Pollack-consistency then rests on. It does
not prove the renderer.

## Where things stand

- `Validate` (714 lines) is pure in substance: tokens, productions,
  compiled grammars, the chart parser, the matcher. What blocks proofs is
  `partial` (the parser's four mutual functions, `STerm.parse`,
  `readingMatches`), `while` and `!` indexing (`tokenize`, `compile`), and
  `Std.HashMap` memo tables, whose contents a proof must reason about.
- **Readings are strings** (`Validate.reading`): a production's name with its
  children in brackets, application normalised, a coercion invisible. The
  bundle records them in messages (`ambiguous: … reads as A and as B`,
  `misread: … reads as A, but was rendered from E`), so their spelling is
  part of the golden output.
- **Sorts** are strings in `sortKey`'s format, compared by `compat`,
  specialised by `expected` and bound by `bind`, all over `STerm.parse`. This
  is the algebra of Lean types (`Prop` reads where `Sort` is expected, a
  named type may be a function type, `Option` without arguments stands for
  any). It is tested, and #22 already proposed to leave it so.
- **Pruning.** `keep2` keeps two distinct readings and at most 32 sort or
  binding variants of each; the budget is 3,000,000 steps. Past the budget a
  formula is "not validated"; past the variant cap nothing is reported, and
  a second reading can be lost.
- The golden bundles and the end-to-end suite carry every validation message
  of every fixture, so they are the differential test, as for #76.

## Design

### One parser, total, in the shared module

`bundle/Layout.lean` gains (or a sibling `bundle/Validate.lean` holds; see
decisions) the whole of reading back: tokens, symbols, productions,
compilation, readings as trees, the parser, the matcher. As with the
layouts: definitions only, total, core-only (`Std.HashMap` is part of the
toolchain, not a Lake dependency, and the extractor uses it today), copied
into both packages and kept equal by `lint/bundle-copies`; proofs in
`SpliceModel`, where the toolchain is pinned. The extractor's `Validate`
becomes a thin layer: the sort algebra, `ofRule` (which already shares
`Doc.holeNeeds` with the renderer), and the messages.

### Sorts are a parameter

The parser and the specification take a *sort algebra*:

```
structure SortAlgebra where
  compat   : String → String → Bool        -- found, expected
  expected : Env → String → String         -- a hole's sort under bindings
  bind     : Env → String → String → Env   -- bind type variables to what fills a hole
```

The extractor instantiates it with today's `STerm` functions, unchanged and
still `partial`. Every theorem below holds for every algebra, so what is
proved is the search; what the algebra says about Lean's types stays
tested, as #22 proposed. (Totalising `STerm.parse` is cheap and could
follow, but proving the algebra right would need a model of Lean's
universes, which is out of scope.)

### Readings are trees

```
inductive Reading
  | atom (tex : String)
  | node (name : String) (kids : List Reading)
```

with the normalisations `Validate.reading` does today as functions on trees
(application however written is one node; a constant applied is that
constant's node; coercions add nothing), and one printer, `Reading.text`,
that writes exactly the strings the bundle records now, so the goldens stay
byte-identical. The expected reading is a tree too, with a leaf `any` for
`⁇`; `Matches : Expected → Reading → Prop` is structural, and
`readingMatches` is its decision procedure. The string encoding's hazard
(#22, "Readings as strings") disappears, since comparison is of trees.

### The specification

`Parses G A ts s r`, inductive, says that tokens `ts` read as reading `r` of
sort `s` in grammar `G` under algebra `A`, following DESIGN §18.4: a
production at or above the precedence asked for, its body matched left to
right with holes read recursively at the sort `A.expected` gives and the
bindings `A.bind` extends, a bound variable's name by an atom production, a
list by its element and separator; parentheses and TeX groups invisible;
coercions invisible, at the coercion's sort; chains not nested in
themselves. Sorts and bindings are carried as the parser carries them, so
the relation is the parser's search described declaratively, not a second
theory of the notation. `Parses` is the meaning of "reads back" that the
paper's §9 describes in words today.

### The parser

The same chart parser, total:

- **Termination** by a lexicographic measure: the span's length, then the
  coercion fuel, then the position in the body. Every call reads a shorter
  span except a coercion (same span, the fuel decreases: a coercion
  production is used at most once per span, which is what the `active` set
  does today) and parentheses or a TeX group (a shorter span).
- **Memo tables** stay, as `Std.HashMap`, threaded through a state as now.
  The proofs carry an invariant on the state: every entry is sound (each
  reading in it is a parse) and, when the exhaustion flags are clear,
  complete up to two (every parse is among them, or two distinct ones are).
  Lean's `Std.HashMap` lemmas (`getElem?_insert`, …) suffice for this.
- **Loops** (`tokenize`, `compile`, `keep2`, `split`'s scan over split
  points) become structural recursion, as `texWidth` did.
- **Exhaustion** is explicit. Two flags, `over` (the budget) and `pruned`
  (the variant cap), are returned with the readings; the extractor reports
  either as "not validated", where today only the budget is. The theorems
  assume both clear. Whether to keep the cap at all is a decision below.

### The theorems

Let `(rs, over, pruned) = readBack G A ts s`.

1. **Soundness.** `r ∈ rs → Parses G A ts s r`.
2. **Completeness up to two.** If `!over ∧ !pruned`: every parse is in `rs`
   when `rs` has fewer than two distinct readings; and `rs` has two distinct
   readings whenever two distinct parses exist. Hence `rs = [r]` means `r`
   is the *only* reading.
3. **Matching.** `readingMatches E r = true ↔ Matches E r`.
4. **Validation.** From 1–3: if the extractor reports nothing of a formula,
   then it has exactly one reading `r`, and `Matches E r` for the expected
   reading `E`. When `E` has no `any`, `r = E`.
5. **Tokens.** `tokenize` loses nothing: the tokens concatenate back to the
   text up to the spaces and breaks it drops.

Theorem 4 is the paper's new statement in §9: *a validated formula reads
back uniquely, as what the renderer rendered it from*. Pollack-consistency
of a view then rests on three things, each named: that the renderer's
expected reading is the source expression up to `≈_N` (trusted,
`MetaM`); that `E` has no `any` (#41; measured per document, 610 of 662 on
project B); and the sort algebra. Everything between — that the grammar has
no other reading, and that the comparison is right — is proved.

### The model

The anatomy's `formulas` assumption (`Anatomy.Sound`: a prose rendering that
reads back reads back formula by formula) becomes two: that the bundle's
validation of the view is empty, which Theorem 1 of the splicer already
checks (`check` reports it as `unfaithful-rendering`), and that the
renderer's expected reading of each part is that part. The first is a
fact about the bundle; the second is the hypothesis above. `proseShows`
and `rulesShow` then rest on the extractor's expectation alone.

## What stays trusted

- **The renderer** (`Expr → Doc`) and its construction of the expected
  reading (`Render.Expect`), in `MetaM`.
- **Expected readings with `any`** (#41): there the check compares only what
  is below, and the grammar following the renderer is assumed.
- **The sort algebra**: what `compat`, `expected` and `bind` say of Lean's
  types.
- **Glyphs** (#43): the theorem is about TeX tokens; two macros may print
  alike.
- **The notation's meaning**: a rule that writes `+` as `-` reads back
  faithfully (Wiedijk's weak failures), as now.

## Migration plan

Each phase keeps the golden bundles, the end-to-end suite and the about
paper byte-identical unless it says otherwise.

| Phase | Work | Exit |
|---|---|---|
| 0 | **Gate.** Fixtures cover each production form: mixfix, coercion, chain, folded binder, lists, type variables, application in all three styles, a misread, an ambiguity, a budget overrun, parentheses and TeX groups; the validation messages are in the goldens. | Goldens cover every form of reading. |
| 1 | **Readings as trees**, in the extractor: `Reading`, `Expected`, `Matches`; `Validate.reading` and `readingMatches` become the tree functions with the same printed strings; `Render.Expect` builds trees. | Goldens byte-identical. |
| 2 | **The module.** Tokens, productions, grammars, the parser and the matcher move to the shared module, total, with the algebra as a parameter and the `pruned` flag; the extractor's `Validate` keeps the algebra, `ofRule` and the messages. `lint/verified` covers it. | Goldens byte-identical; builds on the toolchain matrix; read-back time on projects A and B within 10 %. |
| 3 | **Specification and soundness.** `Parses`, `Matches`; Theorems 1, 3, 5. | Proved. |
| 4 | **Completeness up to two.** Theorem 2, with the memo invariant. | Proved. |
| 5 | **Validation, model, paper.** Theorem 4; `Anatomy.Sound` restated; §9 and the trusted base restated; DESIGN §18.4; #22 closed. | `check` clean; lint passes. |

## Risks

- **The completeness proof** is the large one: the memo invariant with
  pruning to two readings, under bindings that the search extends as it
  goes. Soundness is routine. Estimate: 2–3,000 lines of Lean, most of it
  phase 4; a phase that stalls still leaves soundness and matching proved,
  which is already more than today.
- **Performance.** Totalising the loops costs nothing; the memo tables stay.
  The gate measures read-back time on the two motivating projects.
- **Readings' spelling.** The goldens pin the strings; a tree printer that
  reproduces `reading` exactly is a small, testable function.
- **Dropping the variant cap** could blow up on a pathological formula.
  Keeping it, with `pruned` reported, is safe and costs one hypothesis.

## Decisions needed

1. **Replace the parser with the proved one** (recommended, as for #76), or
   keep the implementation and prove a reference model with property tests
   (#22's plan). The first makes the theorem about the code that runs; the
   second leaves a gap the tests must cover and keeps `partial` code in the
   trusted base.
2. **The variant cap:** keep it and report `pruned` as "not validated"
   (recommended), or remove it and rely on the budget alone.
3. **Where the module lives:** a second shared module `bundle/Validate.lean`
   (recommended; the layouts and the grammar are different concerns, and
   `Layout.lean` is already 1,063 lines), or the same file.
4. **The paper's claim.** State Theorem 4 as the result (recommended), with
   the three named hypotheses for Pollack-consistency; or hold the paper's
   §9 until #41 closes the `any` gap and the claim can be made without the
   second hypothesis.
