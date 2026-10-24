# Proposal: theorems about the extractor's rendering

Status: done, phases 0–5 (issue #76). Companion to `docs/verified-splicer.md`.
What was built differs from the plan below in names only: `ProseData` is
`Imprimatur.Layout.Prose`, `FigureData` is a list of `Imprimatur.Layout.Item`
(a rule, or a name that is no constructor), the figure parser is
`Imprimatur.Layout.figure`, and the theorems are
`SpliceModel.proseSentence_proseLayout`, `SpliceModel.figure_figureLayout`,
`SpliceModel.Anatomy.Sound.proseShows` and `SpliceModel.Anatomy.Sound.rulesShow`
(the paper's Theorems 6.2–6.5). The `Doc` tree and its emitter moved into the
module, made total; `SpliceModel.Formulas` states its parenthesisation and
the hole policy's bounds.

## Goal

The splicer is now proved: if the bundle is true of the development and
`check` reports nothing, every claim of the paper's TeX source is true. "The
bundle is true" is the extractor's claim, and it stays trusted (§18.5,
"the extractor's reading of the environment"). Nothing formal ties the
world's rendering, `render_W`, to the extractor's views. Three gaps follow
from that:

- **The anatomy assumptions.** The paper's §6.1 assumes the world prints
  prose by a layout the model proves round-trips (Theorem 6.2). But the
  extractor's own `proseView` isn't that layout. It does more (`be a type`,
  hypothesis labels, numbered conjuncts, `if and only if`, `there is`), and
  nothing proves the two agree. The rules view is assumed whole.
- **The grammar mirrors the renderer by hand.** The validator's grammar
  (`Validate.ofRule`) restates the renderer's precedence policy
  (`fillTemplate`) "to mirror" it. That mirroring is in the trusted base.
- **The world's rendering.** `render_W` is an abstract field of the world,
  not the extractor's function.

This proposal proves what can be proved of the code that runs, and names
what can't.

## Where things stand

From an inventory of `extract/` (about 5,800 lines):

- **Already pure:** the `Doc` tree (`text`, `node`, `child`, `brk`) and its
  emitter `Doc.render`, which is the one place parentheses are decided, and
  all of `Validate`, the grammar and the read-back parser. What blocks proofs
  there is only `partial` (about 30 definitions, all structurally recursive
  in substance) and `!` indexing.
- **Pure in substance, but inside `MetaM`:**
  - **Layout:** the assembly of the prose sentence (`proseView`: variable
    groups, *Let/Assume/Then*, labels, conjuncts, `iff`, `there is`) and the
    rules figure (`renderRule`: `\inferrule[label]{premises}{conclusion}`,
    joined by `\and`). These run over formulas already rendered.
  - **The precedence policy:** in `fillTemplate`, which hole of a notation
    rule needs which precedence.
- **Inherently `MetaM`:** turning an expression into a formula. Notation
  matching needs `isDefEq` and `whnfR`; `isProp` and binders
  (`withLocalDecl`) need the local context; `inferType` gives sorts. It also
  writes to `IO.Ref`s (atoms, used rules, expected readings, the index's
  events).
- **Toolchains:** the extractor builds on a matrix of Lean versions, and has
  no dependencies.

## Design

### Gather, then lay out

Each view becomes two steps:

```
  gather  (MetaM, trusted)  : ConstantInfo → ProseData / FigureData
  layout  (pure, proved)    : ProseData → TeX       FigureData → TeX
```

- **`ProseData`** holds what a theorem's sentence says, with each formula
  already rendered:
  - variable groups, each with its names and its kind (`∈ T`, *be a type*,
    *be a proposition*);
  - hypotheses, each with its label, if the paper refers to it;
  - the conclusion: a formula; numbered conjuncts; *if and only if*; or
    *there is v such that* another conclusion.
- **`FigureData`** holds the rules of a figure, one per constructor: its
  label (and label macro), its premises and its conclusion, each rendered.
- **The views:** `proseView c = proseLayout (← gatherProse c)`, and
  `rulesView cs = figureLayout (← gatherRules cs)`. Their output must stay
  byte-identical, which the golden bundles check.

### One source for the layout, proved where the toolchain is pinned

The layout functions, their parsers, and the shared precedence policy go in
one pure module, `bundle/Layout.lean`, beside `bundle/Bundle.lean`. It is
copied, byte for byte, into the extractor (`extract/Imprimatur/Layout.lean`)
and the splice package (`splice/Imprimatur/Layout.lean`), and
`lint/bundle-copies` keeps the copies equal.

- **Definitions only in the copies.** The module holds only definitions,
  core-only and total, so it builds on every toolchain in the extractor's
  matrix.
- **Proofs in the splice package** (`SpliceModel`), whose toolchain is
  pinned. They are about the module the extractor runs: one source, checked
  equal.

The paper's model (`SpliceModel.Prose`) is replaced by this module. Its
layout becomes the extractor's real one, so Theorem 6.2 becomes a theorem
about the extractor's `proseLayout`.

### The theorems

1. **The prose layout round-trips** (`proseSentence_proseLayout`), for the
   full sentence the extractor writes. The prose parser recovers
   `ProseData`'s formulas and structure from the TeX, when no formula holds
   a `$`. This extends today's Theorem 6.2 to labels, *be a type* and *be a
   proposition*, numbered conjuncts, *if and only if* and nested *there is*.
2. **The rules figure round-trips** (`figure_figureLayout`). The figure
   parser recovers each rule's label, premises and conclusion, in order;
   `gatherRules` gives one rule per constructor selected. The anatomy's
   `rules` assumption (§6.1) then becomes a theorem, as `prose` did.
3. **The grammar is the renderer's** (`holeNeeds`). The precedence each hole
   of a notation rule needs, and its separators, is one pure function, used
   by both `fillTemplate` (the renderer) and `Validate.ofRule` (the
   grammar). That they agree then holds by construction, which takes "the
   grammar's mirroring of the renderer" out of the trusted base. A lemma
   about `Doc.render` states its parenthesisation: a child is wrapped
   exactly when its precedence is below what its place needs.
4. **The bundle's rendering is the extractor's.** The anatomy's `print` and
   `layout` are the extractor's own `render` and layout, so the world's
   prose rendering is the function the extractor runs, not an abstract
   field.

### What stays trusted

- **Gathering:** walking binders, `isProp`, notation matching and
  `inferType`, all in `MetaM`, and Lean's elaborator, which they rely on.
  #76 calls this step small; it does all the expression-level work, so it
  isn't small, but it is a separate, nameable layer.
- **The read-back parser's correctness:** that it finds every reading and
  no spurious one. It stays checked per formula (translation validation),
  as now. Proving the memoised parser complete is out of scope.
- **The hashes:** that `Trust.stmtText` is a faithful serialisation, and
  that SHA-256 doesn't collide.
- **The other views** (`lean`, `meta`, the index views, custom views).
  `lean` is Lean's own pretty-printer.

## Migration plan

Each phase keeps the golden bundles (`extract/test/golden`), the
end-to-end examples and the about paper byte-identical, unless it says
otherwise.

| Phase | Work | Exit |
|---|---|---|
| 0 | **Gate.** The extractor's golden bundles and the end-to-end suite are the differential test: any change to a rendering fails them. Add golden cases for the prose features the fixtures don't yet cover (labels, nested *there is*, *be a proposition*). | Goldens cover every prose and rules form. |
| 1 | **Shared layout module.** `bundle/Layout.lean` with `ProseData`, `proseLayout` and the prose parser, total and core-only; copies in `extract/` and `splice/`; `lint/bundle-copies` extended. `proseView` becomes `gatherProse` and `proseLayout`. | Goldens byte-identical; builds on the toolchain matrix. |
| 2 | **Prose theorem.** The round trip, proved in `SpliceModel` for the full layout; `SpliceModel.Prose` replaced by the shared module; the paper's Theorem 6.2 restated. | Proved; the paper checks clean. |
| 3 | **Rules.** `FigureData`, `figureLayout` and the figure parser in the module; `rulesView` becomes `gatherRules` and `figureLayout`; the round trip proved; the anatomy's `rules` assumption becomes a theorem. | Goldens byte-identical; proved. |
| 4 | **Precedence.** `holeNeeds` in the module, used by `fillTemplate` and `ofRule`; the `Doc.render` parenthesisation lemma (`Doc` moves into the module, made total). | Validation results unchanged on every fixture; proved. |
| 5 | **Paper and docs.** §6.1 and the trusted base say what is proved of the extractor; DESIGN §18; `lint/verified` and `lint/axioms` extended to the module. | `check` clean; lint passes. |

## Risks

- **Byte-identical output.** The prose and rules views carry many small
  rules (grouping only consecutive variables of structurally equal type;
  "Then" only after another sentence; label macros). The goldens catch any
  slip; new golden cases in phase 0 close the gaps in their coverage.
- **Toolchain drift.** Keeping theorems out of the copies means the copies
  only need to compile across the matrix, which core-only, structural
  definitions do.
- **Scope.** The expensive part, `Expr` to `Doc`, stays trusted. The
  proposal moves it out of the way rather than proving it, and says so.

## Decisions needed

1. **Shared module copied into both packages** (recommended), or the
   layout duplicated in the model and tested against the extractor's.
2. **Scope:** phases 1–5 as above (recommended), or prose only first (1, 2
   and 5), with rules and precedence later.
3. **The paper:** replace the model's prose layout with the extractor's
   (recommended), so Theorem 6.2 is about the extractor; or keep the model's
   simpler fragment and add the extractor's as a refinement.
