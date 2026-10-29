# Changelog

All notable changes to imprimatur are recorded here. Versions follow
[semantic versioning](https://semver.org/).

## Unreleased

- The dependency cone and the axioms are computed once per constant for a
  whole export, not once per entry: a cone's members are memoised as nodes
  (their canonical text and what the walk follows from them, trusted
  constants left out), a group's cones are united by a set, and the axioms
  a constant depends on are kept across entries. LLMbda's paper exports in
  21 s instead of 112 s, with the same bundle. The axioms are now walked by
  imprimatur rather than by Lean's `collectAxioms`, whose per-module table
  can hold a partial answer for a constant in a cycle (an inductive type
  whose constructor's type depends on an axiom reported none, while its
  constructor reported it); the walk keeps no answer that met a cycle in
  progress, so such a constant now reports its axioms. A custom view that
  needs a constant's axioms should call `Imprimatur.Axioms.collect`.
- `imprimatur build --timing` (and `check`, `accept`, `show`) records where
  the time goes, in `.imprimatur/timing.jsonl`, and ends with a summary: the
  splicer's phases; the extractor's load, entries and write; each entry's
  stages; each view, with the time its context and grammar took; and, when
  formulas are validated, each formula with its tokens and the parser's
  steps. The summary names the slowest entries, views and formulas, so that
  the first thing to make faster is on the console (#85).
- A premise that `latex_metavar_convention` hides is no longer lost: the
  `prose` view binds the variable it names in the predicate, `Let
  $\val \in \mathit{Val}$` for a hidden `IsValue v`, instead of in its
  type, and the `conventions` table lists the convention's metavariable
  with the predicate and the block that shows it. The about paper's
  Theorem 1.1 read as a stronger theorem than the one proved; it now reads
  "Let $V \in \mathit{Val}$ and $M \in \mathit{Term}$" (#77).
- The about paper's introduction states its results at the top level, each
  generated from a theorem of the model (`SpliceModel.Summary`): the bundle
  the extractor writes is true; building rewrites only blocks, once, and
  leaves nothing stale; and a paper that checks clean against the extracted
  bundle is true of the development and Pollack-consistent, every block
  reading only as its key's statement.
- A type that is a function type by definition (`Matrix R C α`, `Set α`)
  is read back as that function type, and a named or applied type is no
  longer taken for a function. So `Γ(i)` no longer reads as an application
  of a context, and with typed applications, `\sum_u f(u) \le 1` reads at
  the one type `f` returns (#90, part 2). A fixture built with an earlier
  extractor keeps its rules' old sorts until it is rebuilt.
- Reading formulas back types applications: `f(a)` and `f\,a` have the
  function's codomain for their sort when its sort is a function type,
  where before every application was of unknown sort. A function of a named
  type or of unknown sort applies as before (#90, part 1).
- The paper's model proves what the chain rule costs and why it is there
  (`SpliceModel.ReadBackChains`): every reading in the parser's grammar is
  one in the grammar of chains of any length, and the counterexample of
  docs/coercion-chains.md is a theorem, under a toy algebra: the unbounded
  grammar reads `g ( x )` two ways, the parser's grammar one.
- The renderer and the reader of formulas share one rule for chains of
  hidden coercions (docs/coercion-chains.md, route A): a chain never
  stacks two coercions with the same argument sort, nor a cast below a
  cast, and where the renderer would hide a coercion the rule forbids it
  now shows it, as a constant applied (`\LeanMathConst{Option.some}\,x`).
  So a validated formula has no reading but its statement in the grammar
  of what the renderer prints; before, `g(some(some(some x)))` could print
  as `g(x)` and validate as another statement. The depth cap and growth
  budget of route B are gone, and with them its cost: reading back is
  affordable again on large papers (`IMPRIMATUR_CHAIN_DEPTH` is removed).
- Reading formulas back is one total module, `bundle/ReadBack.lean`
  (tokens, the grammar's symbols, readings as trees, the chart parser, the
  matcher), with the algebra of sorts as a parameter, and the paper's model
  proves it sound and complete: every reading the parser returns is a
  reading in the notation's grammar, every reading in the grammar is among
  those it returns unless it says it gave up, and so a validated formula
  has no reading in the grammar but the one it was rendered from
  (Pollack-consistency, formula by formula and of a document that checks
  clean; docs/verified-validator.md, docs/pollack-consistency.md). Where
  the parser gives up is explicit and reported as "not validated": the
  budget, a reading past the variant cap (now 256; 32 was exceeded silently
  by formulas of the paper itself), a third reading of a sub-formula
  dropped, which could before let an ambiguous formula pass as having one
  reading, a question that comes round to itself, and a list of the
  notation that takes no token; an ambiguity is reported before any of
  these. A chain of coercions applies each argument sort once and has no
  cast below a cast, so a cycle of coercions no longer cuts the search, and the
  readings a cut lost are found.
- The extractor's prose and rules layouts, its formula emitter and the
  precedence policy of a notation rule's holes are one pure, total module,
  `bundle/Layout.lean`, copied into both packages (`lint/bundle-copies`),
  checked by `lint/verified`, and proved of in the paper's model
  (docs/verified-extractor.md): the prose parser undoes the prose layout,
  for the whole sentence the extractor writes (labels, *be a type*,
  numbered conjuncts, *if and only if*, nested *there is*); the figure
  parser undoes the rules layout; and a prose or rules rendering that reads
  back shows its statement part by part, where before the rules view was
  assumed to. The renderer and the validator's grammar call one
  `Doc.holeNeeds`, so the grammar demands of an argument what the renderer
  gives it by construction, not by mirroring. `proseView` and `rulesView`
  now gather what the view says, then lay it out; their output is
  unchanged.
- The splicer's laws and Theorem 1 are proved of the splicer's own code, not
  only of a model (docs/verified-splicer.md). The scanner, the slot finder
  and the text kernel are rewritten as total, tail-recursive functions on
  characters, proved lossless; an ordinary slot merge is the model's `fill`;
  `apply` rewrites items in place and checks its own output before writing
  (`unstable-output`, `not-fixed-point`), which fixed a bug where a
  rendering holding an alias's `\begin` was written and the file could no
  longer be scanned; and `imprimatur check` is one function, `checkDoc`, of
  which Theorem 1 is proved. The model moves into the splice package. New
  checks: `lint/verified` and `lint/axioms`. The audit's trust check now
  skips only the blueprint `\lean`, not any item named `lean`.
- Slots that the authors never edited now follow their defaults. A block
  with slots records a digest of its slots' default texts in `dflt=`; while
  its slots still match it, `apply` gives them the new defaults when a
  docstring changes. Once a slot of the block is edited, all keep their
  text, and a changed default is reported once (`slot-default`). The first
  `apply` after upgrading adds `dflt=` to every block with slots.
- The bundle is a Lean type, `bundle/Bundle.lean`, of which the file is the
  JSON: `Bundle (Image TeX) Verdict`, an entry being what a key names, the
  images of its statement (hashes and views) and the verdict on its proof.
  Both executables and the paper's model use it (a copy each;
  `lint/bundle-copies`), and the
  module says when a bundle is true of a development. The model of the
  splicer is built on it, and proves that a document which checks clean
  against a true bundle is true: every block shows a statement Lean proved,
  rendered, and reads back as it; every `\leancheck` names one by its hash.
  The about paper presents this, in the PACMPL format, with a running
  example: a small simply typed λ-calculus, shown as the paper's reader
  sees it, as its bundle entry, as its world, and under three edits. A group's or display's entry now has a
  statement hash and a cone, from its members, so `\leancheck{Title}`
  works.
- Fixed: an alias's template no longer rewrites `{key}`, `{label}` or
  `{title}` inside the generated content (a structure field named `key`
  became the block's key). The `grammar` view heads a structure without a
  category by its type's notation, not its constant's name.
- Displays (#73): the `clauses` view sets definitions as `lhs ≜ rhs` rows,
  and `grammar|display` sets inductive types as grammar rows, each with its
  description as a slot, for one declaration or a `latex_display "Title" :=
  […]`. `imprimatur.sty` gains `LeanDisplay`, `LeanDisplayBox`,
  `LeanRulesBox`, `\deq` and `\defeqq`. Text after a box with no blank line
  before it continues the paragraph, unindented.
- `latex_notation … break` lets a long rendering break the line before each
  of a rule's operators. A constant applied only to implicit arguments is no
  longer reported as a misread. The provenance table wraps long source paths,
  and `imprimatur.sty` maps `↪` and `↠` and loads `array`.

- `imprimatur show KEY [--view VIEW]…` prints one key's renderings, with the
  problems translation validation found in each, without touching the paper:
  for working on notation (#32).
- `check` warns (`undefined-macro`) when generated content uses a macro that
  nothing defines: not the document's files, the paper's own packages, the
  standard set (TeX, LaTeX, amsmath, amssymb, mathpartir, imprimatur.sty), or
  `known_macros` in `imprimatur.toml` (#27).

- Repository layout, build settings, test harness and CI skeleton (M0).
- `imprimatur-splice`, the splicer (M1): `scan`, `apply`, `check` (with
  `--diff`), `strip` and `migrate-slots`. It supports blocks, aliases,
  `\leaninline`, `\leanref`, `\leancheck`, slots in both forms, checksums
  that ignore line endings and trailing whitespace, multi-file documents, and
  `imprimatur.toml`. See [docs/blocks.md](docs/blocks.md).
- `imprimatur-export`, the extractor (M2). It renders the `lean` view
  (the signature, with semantic token macros) and the `meta` view (source
  location, axioms, `sorry` status, docstring). It imports at the `private`
  level, so a `sorry` hidden in a `module` file's private proof is found.
  Bundles are byte-identical across toolchains v4.28.0-rc1 to v4.35.0. See
  [docs/views.md](docs/views.md).
- `imprimatur build` and `imprimatur check` run the whole flow in in-project
  and sidecar modes. `tex/imprimatur.sty` typesets the result with pdfLaTeX
  or LuaLaTeX. `examples/minimal` and `examples/sidecar` show both modes.
- Trust checks (M3):
  - dependency cones, `stmtHash` and `sigHash`, the same on every toolchain;
  - `\leancheck[stmt=…, sig=…]` with drift detection, and `imprimatur accept`;
  - comparator manifests, with `KEY@challenge` entries;
  - blueprint `\lean{…}` and `\leanok`.

  See [docs/trust.md](docs/trust.md).
- External mode: `imprimatur toolchain install VERSION`, then
  `mode = "external"` reads a host project without changing it.
  `examples/external` shows it.
- Notation and typeset mathematics (M4):
  - `latex_notation`, with `prec`, `width`, `hide`, `variant`, `flatten` and
    typed `@` patterns, and `latex_metavar`;
  - the notation packs `core`, `logic`, `sets` and `order`;
  - the `math` and `prose` views.

  Notation modules work in every mode. In external mode they are given as
  files and elaborated by the extractor. See [docs/notation.md](docs/notation.md).
- Rules, grammars and the migration of project A (M5):
  - the `rules` view (mathpartir), with `latex_rules`, `latex_rule_label`,
    `latex_group`, premise conventions (`latex_metavar_convention`,
    `latex_hide_premise`), `include`/`exclude`, and the `grammar` view;
  - theorem modifiers `rule`, `forall`, `def` and `names=full`;
  - custom views through `@[latex_view]`, with the document's inventory;
  - `latex_entry` for keys that are titles, and `latex_style` for a paper's
    conventions (`names := raw`, `applied_variables := call`);
  - binder patterns in `latex_notation` (`∃ x, p`, `∑' x, f`, `fun x => e`,
    `p → q`), partial applications, `flatten` of binder chains with `sep`,
    `assoc`, `when` guards, `latex_metavar … decorated`, and Greek letters
    as macros;
  - several notation files in external mode;
  - `examples/semantics`, a paper on a name-carrying λ-calculus (swapping,
    α-equivalence and substitution after Pitts, with preservation and
    progress proved) whose grammar, rules and results are generated, next to hand-written statements checked with
    `\leancheck`; the `def` view shows equation lemmas with the definition's
    own variable names; the prose view labels a hypothesis only where the
    paper refers to it, with `\leanhypref{key}{h}`;
  - alias options `label`, `repeat_suffix`, `template` and `comment`;
  - the scanner records which blocks are typeset, reading `\iffalse` and
    `\newif` switches; blocks that are not are still maintained; and a
    command being defined (`\NewDocumentCommand\leancheck…`) is not a use;
  - the parity gate of DESIGN §16 passed byte for byte; project A now
    builds its papers with imprimatur, keeps the port in its own
    repository, and has deleted its old exporter; and project B's analysis
    rules are generated.

  See [docs/views.md](docs/views.md), [docs/notation.md](docs/notation.md)
  and [docs/blocks.md](docs/blocks.md).
- Correctness (DESIGN §18): what `check` guarantees, and faithful rendering.
  The extractor reads back every formula it renders, in the grammar of the
  notation module, with sorts from Lean's types. `imprimatur check` warns
  (`unfaithful-rendering`) where a typeset formula is ambiguous, showing
  both readings, or does not read back. A template that drops a pattern
  variable is a warning. `validate = false` turns the reading back off.
  Lean's warnings about notation files now reach the user in external mode,
  at the files' own line numbers. See
  [docs/notation.md](docs/notation.md#reading-back).
- Reading back is typed more precisely, and found three rendering bugs on
  project B's paper. Sorts carry type arguments (`Option(Label)`); coercions
  are read with the sorts they make; `latex_notation … synonym` declares
  two notations for equal things; application is one reading however
  written. The bugs: an atomic template's edge hole (`#e(#c)`, `#n!`) got no
  parentheses; an applied variable with a subscript printed `k_{1}_{x}`; and
  `imprimatur.sty` loaded `amssymb` under acmart, which defines its symbols.
  Quantifiers may break after their comma, a definition's long right-hand
  side breaks within its alignment, and a structure's description spans the
  grammar. A line break after `,\ ` no longer leaves a lone backslash that
  escapes what follows. A category letter may stand for several types.
- Translation validation also reports a variable that prints as another
  type's category letter (`latex_category`), as `s ::= gen(s)` did in the
  paper about imprimatur, where `s` was both a segment and a string.
- Definitions by cases, as a paper writes them, and fixes found by rendering
  every definition of project B's development:
  - `latex_style pattern_matching := cases` writes a `match` as
    `case d of p ⇒ e | …`, and `lists := literal` writes a list literal as
    `[a, b]`;
  - a `case` inside another no longer shows two variables as one (the
    patterns of `elab(nest D₁ D₂)` printed `nest(d₂, d₂)`): pattern
    variables take the names the alternative gives them, renamed when in
    scope, and a λ's binder is renamed likewise (no more `λx.\,λx.`);
  - an unused binder Lean named is `_`; a λ that binds a proof is not shown,
    so `if h : c then a else b` is `if c then a else b`;
  - a constructor a rule writes as its bare argument (`Sum.inl i` as `i`)
    is shown in a pattern, on the left of an equation or in a `case`;
  - the generic binders of an equation lemma (`a`, `x✝`) are named after
    their categories (`latex_category`), or after the definition's own
    parameters (`R`, `C`, not `T₁`, `T₂`); an author's `a` or `x` is kept;
  - reading back tells a type from a value: a universe that may be `Prop`
    is `Sort*`, a type such as `Fin n` written `[n]` is not read as a
    one-element list, and a pair is of sort `Prod`.
- `about/imprimatur-paper.tex`, a paper about imprimatur built with
  imprimatur. Its theorems, the splicer's laws and Theorem 1, are proved in
  `about/lean`, a model of the splicer. CI rebuilds and checks it.
- `latex_category T A … => "m"` names the category of a type with
  parameters, and the category check compares such a type at its parameters
  (#15).
- Views that index the document (#16, #18), rendered after every other
  block so they see the whole document:
  - `conventions`: each metavariable, the type it ranges over, and where the
    document first shows it;
  - `vocabulary`: the notation the document uses, with its Lean constant and
    a gloss, by default the library's; `scope=project` lists the project's
    own and `scope=all` both, an index of notation;
  - `provenance`: each result with its kind, number, source and axioms.

  Descriptions and glosses are slots. See [docs/views.md](docs/views.md).
- `latex_style categories := loose | unique | strict` (#17). Under `unique`
  a metavariable stands for one type; under `strict` a variable of a
  category's type is also written with the category's letter and its own
  subscripts and primes, and variables that then print alike are errors.
  `imprimatur check` reports these as `error[category]`. See
  [docs/notation.md](docs/notation.md#metavariables).
- Misreads (#19): the renderer builds the reading each formula should have,
  and a formula whose one reading differs, because the emitter left out
  parentheses a reader needs, say, is reported as `unfaithful-rendering`.
- The paper about imprimatur states what translation validation guarantees
  and what is trusted, uses strict metavariables, and ends with a generated
  index of its notation (#20). `examples/semantics` has one too.
- `PLAN.md` is retired: remaining work is tracked as GitHub issues, the
  principles and definition of done are in `CONTRIBUTING.md`, and the test
  architecture is in `docs/TESTING.md` (#59).
