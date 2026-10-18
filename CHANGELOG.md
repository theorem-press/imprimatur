# Changelog

All notable changes to imprimatur are recorded here. Versions follow
[semantic versioning](https://semver.org/).

## Unreleased

- Repository layout, build settings, test harness and CI skeleton (PLAN M0).
- `imprimatur-splice`, the splicer (PLAN M1): `scan`, `apply`, `check` (with
  `--diff`), `strip` and `migrate-slots`. It supports blocks, aliases,
  `\leaninline`, `\leanref`, `\leancheck`, slots in both forms, checksums
  that ignore line endings and trailing whitespace, multi-file documents, and
  `imprimatur.toml`. See [docs/blocks.md](docs/blocks.md).
- `imprimatur-export`, the extractor (PLAN M2). It renders the `lean` view
  (the signature, with semantic token macros) and the `meta` view (source
  location, axioms, `sorry` status, docstring). It imports at the `private`
  level, so a `sorry` hidden in a `module` file's private proof is found.
  Bundles are byte-identical across toolchains v4.28.0-rc1 to v4.35.0. See
  [docs/views.md](docs/views.md).
- `imprimatur build` and `imprimatur check` run the whole flow in in-project
  and sidecar modes. `tex/imprimatur.sty` typesets the result with pdfLaTeX
  or LuaLaTeX. `examples/minimal` and `examples/sidecar` show both modes.
- Trust checks (PLAN M3):
  - dependency cones, `stmtHash` and `sigHash`, the same on every toolchain;
  - `\leancheck[stmt=…, sig=…]` with drift detection, and `imprimatur accept`;
  - comparator manifests, with `KEY@challenge` entries;
  - blueprint `\lean{…}` and `\leanok`.

  See [docs/trust.md](docs/trust.md).
- External mode: `imprimatur toolchain install VERSION`, then
  `mode = "external"` reads a host project without changing it.
  `examples/external` shows it.
- Notation and typeset mathematics (PLAN M4):
  - `latex_notation`, with `prec`, `width`, `hide`, `variant`, `flatten` and
    typed `@` patterns, and `latex_metavar`;
  - the notation packs `core`, `logic`, `sets` and `order`;
  - the `math` and `prose` views.

  Notation modules work in every mode. In external mode they are given as
  files and elaborated by the extractor. See [docs/notation.md](docs/notation.md).
- Rules, grammars and the project-a migration (PLAN M5):
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
