# Changelog

All notable changes to imprimatur are recorded here. Versions follow
[semantic versioning](https://semver.org/).

## Unreleased

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
- Rules, grammars and the project-a migration (M5):
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
  - the project-a parity gate of DESIGN §16 passed byte for byte; project-a now
    builds its papers with imprimatur, keeps the port in its `imprimatur/`,
    and has deleted its old exporter; and project B's analysis rules are
    generated from `Der` (`scripts/integration.sh`).

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
  the project B paper. Sorts carry type arguments (`Option(Label)`); coercions
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
  every definition of the project B development:
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
