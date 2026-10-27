# Proposal: the validator, proved

Status: done (branches `verified-validator`, then `pollack-plan`);
decisions 1–4 taken as recommended. What is proved, of the module that
runs, for any algebra of sorts: the parser is sound
(`SpliceModel.readBack_sound`) and complete (`readBack_complete`: when no
flag is set, every reading in the grammar is among those returned), the
matcher decides structural matching (`matches_iff`), and so a validated
formula has in the grammar no reading but the one it was rendered from,
wherever the expected reading is definite (`pollack`); and for the world
as the validator sees it, whose `Reads` is that it accepts each formula
printed of a statement, the two reading-back assumptions of a sound
anatomy are theorems (`Validated.sound`), so each formula of a block that
checks clean reads only as the part it was printed from
(`document_pollack`, `document_pollack_rules`). Completeness was planned
in docs/pollack-consistency.md, which records how the design changed on
the way; the proofs are `splice/SpliceModel/ReadBack.lean` (the
specification), `ReadBackSound.lean`, `Pruning.lean`,
`ReadBackComplete.lean` and `Validator.lean`. Supersedes the plan in #22
(a model with property tests) with the pattern of
docs/verified-extractor.md: the code that runs is the code that is proved.
Companion to `docs/verified-splicer.md` and `docs/verified-extractor.md`.
The module is `bundle/ReadBack.lean` (`Imprimatur.ReadBack`, namespace
`Imprimatur.Validate`), since `Imprimatur.Validate` is the extractor's own
file. What was built differs from the plan below in these points, each
recorded in the module:

- **A question carries its chain of coercions.** The plan cut a question
  asked again while being asked, to break coercion cycles, and bookkept
  which answers a cut had left incomplete. Instead a question records the
  argument sorts of the coercions above it on the chain of coercions it is
  the argument of, and a chain applies no coercion whose argument sort is
  on it already and has no cast below a cast (docs/coercion-chains.md,
  route A; the renderer obeys the same rule) (a coercion whose sort stands
  for any sort; a cast of a cast is a cast): chains are finite, no cycle
  is ever entered, and the search is complete without bookkeeping. A cut can now come only
  from a production whose body is a bare hole and nothing else; it is a
  flag, `cut`, reported as "not validated".
- **Variants are kept by equality.** The parser keeps one of each variant
  (the same reading, the same sort or bindings) of each of two readings,
  not a most general one: no order on sorts, and so no law of the sort
  algebra, is needed for completeness.
- **The variant cap is 256**, not 32: two of the paper's own formulas
  (`'$' :: l ++ ['$']`) exceeded 32, and the cap at 32 was silently
  incomplete there. `pruned` is reported as "not validated".
- **The fuel bounds depth**, each call and each step of a loop taking one,
  the budget bounds work; either exhausted is `over`.
- **The grammar's lists are checked**: the parser looks for a list's rest
  only where its elements fit, which is complete only when each element
  takes a token (every notation's do); `lists` flags a grammar whose do
  not.

**What the specification found.** The parser as it was kept at most two
distinct readings of a question (`keep2`), silently dropping a third. A
question above, which filters its hole's readings by sort, may accept the
dropped one and reject the two kept, and so report one reading of a
formula that has two. The same shortcut skipped reading inside parentheses
once two readings were known, and a coercion of the sort asked for read a
snapshot of the question's own readings. The first is now noted
(`pruned`), and the extractor reports an ambiguity before any flag; the
guard on parentheses is gone; and coercions chain through the question's
record of them. The goldens and the paper are unchanged by all of it.

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
  type that is a function type by definition is written as one, so a named
  type is not a function (#90), `Option` without arguments stands for
  any). It is tested, and #22 already proposed to leave it so.
- **Pruning.** `keep2` keeps two distinct readings and at most 32 sort or
  binding variants of each; the budget is 3,000,000 steps. Past the budget a
  formula is "not validated"; past the variant cap nothing is reported, and
  a second reading can be lost.
- The golden bundles and the end-to-end suite carry every validation message
  of every fixture, so they are the differential test, as for #76.

## Design

### One parser, total, in the shared module

A sibling of `bundle/Layout.lean`, `bundle/ReadBack.lean`, holds the whole
of reading back: tokens, symbols, productions,
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

The extractor instantiates it with Lean's `STerm` functions
(`Imprimatur.Validate.leanSorts`), which since docs/coercion-chains.md
phase B1 are total and in the shared module, so that theorems can be about
them: `STerm.parse` reads with fuel (the text's length, since each part is
shorter), and the structural functions recurse on the term. Every theorem
of soundness and completeness holds for every algebra, so what is proved
there is the search; what the algebra says about Lean's types is tested
(the laws of the cut and the order below a sort, in
`extract/test/ExtractTest/SortLaws.lean`; that the parser reads what the
renderer prints under the chain rule, in `ChainLaws.lean`).

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
- **Exhaustion** is explicit. Two flags, `over` (the budget, or the fuel)
  and `pruned` (the variant cap), are returned with the readings; the
  extractor reports either as "not validated", where today only the budget
  is. The theorems assume both clear.

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
| 3 | **Specification and soundness.** `Parses`, `Matches`; Theorems 1, 3, 5. | Done: `Exp`/`Seq`/`Tail`, `readBack_sound`, `matches_iff`; Theorem 5 (tokens) not stated. |
| 4 | **Completeness up to two.** Theorem 2, with the memo invariant. | Done (docs/pollack-consistency.md): `readBack_complete`, with the invariant that every remembered answer holds every reading of its question, in triples that hold when the flags end clear. |
| 5 | **Validation, model, paper.** Theorem 4; `Anatomy.Sound` restated; §9 and the trusted base restated; DESIGN §18.4; #22 closed. | Done: `pollack`; `Anatomy.Sound` kept, and its two reading-back assumptions proved of the validator's world (`Validated.sound`, `document_pollack`); §9, the trusted base and DESIGN §18.4 say so. |

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
