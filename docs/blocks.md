# Blocks and the splicer

*For authors of papers that use imprimatur. This page describes the TeX markup
and what `imprimatur-splice` does with it; [views.md](views.md) describes the
generated content. [DESIGN.md](../DESIGN.md) §9–§10
gives the reasoning behind it.*

## Setting up

Put `imprimatur.toml` next to the main `.tex` file:

```toml
schema = 1
main = "paper.tex"
lean_project = "lean"            # the package that requires imprimatur
mode = "in-project"              # or "sidecar", or "external"
imports = ["Minimal"]            # the modules declarations come from
strip_namespaces = ["Minimal"]

[aliases]
leantheorem = { view = "lean", wrap = "theorem" }
```

Then add `\usepackage{imprimatur}` to the paper (`tex/imprimatur.sty`), and
for each alias `\leanblockalias{leantheorem}{theorem}`. Run
`imprimatur build` after changing the Lean or the paper, and
`imprimatur check` in CI.

The Lean project is reached in one of three ways:

- **In-project.** The project's own lakefile requires
  `imprimatur` (`subDir = "extract"`).
- **Sidecar.** A small package next to the project requires both the project
  and `imprimatur`, so the project itself doesn't change.

- **External.** Nothing requires imprimatur. Run
  `imprimatur toolchain install VERSION` once for the project's toolchain;
  `imprimatur build` then reads the project, which must already be built,
  without changing it.

`examples/minimal`, `examples/sidecar` and `examples/external` show all
three. `examples/semantics` is a short paper on a typed λ-calculus with
name-carrying terms, in external mode, that shows the two ways of tying a
paper to Lean side by side: a generated grammar (with the authors'
descriptions kept as slots), swapping and α-equivalence in the style of
Pitts's nominal techniques, generated typing and reduction rules, and
generated results up to preservation and progress, next to hand-written statements checked with
`\leancheck`. Each example's `paper.tex` is
the input, with its blocks empty; `expected/paper.tex` is the paper
imprimatur makes from it, and both compile in an editor (their
`.latexmkrc` puts `tex/` on the path).

## Markup

| Form | Example | What the splicer does |
|---|---|---|
| block | `\begin{leanblock}[view=math]{Key}{Title}` … `\end{leanblock}` | regenerates the content between the header and `\end` |
| inline | `\leaninline{Key}{}` | regenerates the second argument |
| reference | `\leanref{Key}{}` | fills the second argument with the source location, per profile |
| check | `\leancheck{Key1, Key2}` | generates nothing; `check` reports missing keys and untrusted results |
| hypothesis reference | `\leanhypref{Key}{h}` | prints `(h)`, and makes the prose view of `Key` label its hypothesis `h` |
| index | `\leanindex` | recognised; generated from M6 |
| slot | `\leanslot{id}{text}` | inside generated content: text that belongs to the authors |

**Write new inline items and references with an empty second argument**, as
in `\leaninline{Key}{}`. The splicer fills it in. The second argument is
always present, so the macros take a fixed number of arguments in TeX.

**Aliases.** Environments listed under `[aliases]` in `imprimatur.toml` work
like `leanblock`, with a fixed view. They take the same `{Key}{Title}`
arguments, so a paper can keep its existing environment names:

```toml
[aliases]
leantheorem = { view = "math", wrap = "theorem" }
leangrammar = { view = "grammar", slots = { macros = ["\\entry"], arg = 2, id = "arg1" } }
```

An alias can also shape what is written into its blocks:

```toml
leanlemma  = { view = "prose", wrap = "lemma", label = "lem:{key}", repeat_suffix = "-appendix",
               template = "\\label{{label}}\n\n{content}" }
leandef    = { view = "math", label = "def:{key}", template = "\\label{{label}}\n\\({content}\\)" }
LEANCLAUSE = { view = "math", comment = true, template = "\\clause{{content}}{{title}}" }
```

- **`label`** gives each block a label made from its key (spaces become
  `-`). A key stated again, say in an appendix, gets **`repeat_suffix`** on
  its second label, then the suffix with `2`, `3`, … on later ones.
- **`template`** is the content, with `{content}` for the view's text, and
  `{label}`, `{key}` and `{title}` (the block's second argument). The
  default is `{content}`, after a `\label` line when `label` is set.
- **`comment = true`** makes the alias a region delimited by comments,
  `%NAME{key}{title}` … `%ENDNAME`, for places where an environment would
  disturb TeX, such as a row of a tabbing display. The splicer writes
  `[sum=…]` after the marker name.

**Options** go in the optional argument: `view`, `wrap`, `label`, `sum`,
`dflt`, `notation`, `include`, `exclude`, and the theorem modifiers `rule`,
`def`, `forall` and `names` ([views.md](views.md)). The splicer writes
`sum=` and `dflt=` itself.

## Where generated content goes

- **Blocks.** If the rest of the header line is blank or a comment, the
  content starts on the next line. Otherwise it starts right after the
  header. It ends at the start of the `\end{…}` line, or at `\end` itself if
  something precedes it on that line. Generated content always ends with a
  newline.
- **Inline items and references.** The content is the second argument.

## What the scanner skips

- **Comments.** Markup after `%` is ignored, but `\%` is not a comment.
- **Verbatim text.** `\verb|…|`, `\verb*|…|`, and the environments
  `verbatim`, `verbatim*`, `Verbatim`, `lstlisting`, `minted`, `comment` and
  `alltt` are skipped. Add other environments with `verbatim_envs = […]`.
- **`known_macros = […]`** lists macros that packages the paper loads define
  (`["toprule", "midrule"]` for booktabs), so that generated content may use
  them without an `undefined-macro` warning.
- **Conditionals** are not skipped: blocks in a branch that is off are kept
  up to date like any other. The scanner does note which blocks are typeset,
  for views that index the paper: not those in a branch that is off
  (`\iffalse`, or a switch declared with `\newif\ifNAME` and set with
  `\NAMEfalse`), nor those in a file input only from one.
- **Definitions.** The command named after `\newcommand`, `\providecommand`,
  `\NewDocumentCommand`, `\def` and their relatives is being defined, not
  used, so a paper can define `\leancheck` itself:
  `\NewDocumentCommand\leancheck{O{} m}{}` prints nothing.
- **Uses without arguments.** `\leaninline` that isn't followed by `[` or `{`
  is a definition, as in `\newcommand{\x}{\leaninline}`, not a use.

**Files.** The scanner follows `\input`, `\include` and `\subfile`. Paths are
relative to the main file's directory, as in LaTeX, and `.tex` is added when
needed. A file that doesn't exist is a warning, because it may be generated
later.

## Checksums and hand edits

Each block and inline item records a checksum of its content in `sum=`. The
checksum is the first 60 bits of the SHA-256, in base64url. It is taken
after:

- line endings are normalised to `\n`;
- trailing spaces and tabs are removed;
- blank lines at both ends are dropped;
- slot texts are emptied.

**Editing generated content by hand.** The checksum then no longer matches.
`apply` refuses to overwrite the block and `check` reports it, until you
either:
- move the edit into Lean or into a slot; or
- rerun with `--force KEY` to discard the edit.

**Editing a slot is always allowed.**

References (`\leanref`) carry no checksum and are always regenerated.

## Slots

A slot's text is carried over each time the block is regenerated, matched by
id and by occurrence. There are two forms:

- **`\leanslot{id}{text}`.** The id is chosen by the view, usually a
  constructor name.
- **Slots by position.** Declared in an alias: the given argument of each
  listed macro is a slot, identified by the text of another argument. This
  matches existing grammar markup without edits.

**Default text.** A new slot gets the view's default, usually a docstring.
A block with slots records a digest of its slots' default texts in `dflt=`.
While its slots still match that digest, nobody has edited them, so when a
default changes in Lean, `apply` gives the slots the new defaults. Once any
slot of the block is edited, the block's slots all keep their text. If a
default then changes, `apply` and `check` warn (`slot-default`), listing
the slots whose text differs from its new default, and record the new
digest so the warning is given once.

A slot that the new content no longer has is dropped, and its text is
printed as an `orphan-slot` warning. `--rename-slot OLD=NEW` keeps the text
when the slot was renamed. `migrate-slots --bundle B` rewrites slots by
position into `\leanslot` form. It matches each old slot to the new
`\leanslot` inside the macro with the same identifying argument.

## Commands

| Command | Does |
|---|---|
| `imprimatur-splice scan [-o requests.json]` | lists every key and view the document asks for, and the document's inventory: its blocks, with the labels they will get, and its `\label`s, in document order, for views that index the paper |
| `imprimatur-splice apply --bundle B` | regenerates content. Writes nothing if there is any error. Options: `--force KEY`, `--keep-stale`, `--rename-slot OLD=NEW`, `--profile P`, `--commit SHA` |
| `imprimatur-splice check --bundle B` | reports what `apply` would change, without writing. Options: `--diff`, `--check-fail-msg MSG` |
| `imprimatur-splice strip -o DIR` | writes a copy without markers: blocks become their content, wrapped in `wrap` if given; slots become their text; `\leancheck` and `\leanindex` disappear |
| `imprimatur-splice migrate-slots --bundle B` | see Slots above |
| `imprimatur build` | `scan`, then `imprimatur-export` in `lean_project`, then `apply`; takes `apply`'s options |
| `imprimatur check` | the same, with `check` instead of `apply`; writes only the bundle, in `.imprimatur/` |
| `--timing` | with `build`, `check`, `accept` or `show`: log where the time goes to `.imprimatur/timing.jsonl` (one JSON line per phase, entry, view and validated formula) and end with a summary naming the slowest |
| `imprimatur accept KEY…` / `--all` | the same, then records the current statement hashes in `\leancheck` ([trust.md](trust.md)) |
| `imprimatur show KEY [--view VIEW]…` | runs the extractor for one key and prints its renderings, with the problems translation validation found in each, its axioms and whether it uses `sorry`; writes nothing. The views are those given, else those the document uses for the key, else `math`. For working on notation |
| `imprimatur toolchain install VERSION` | builds the extractor for a toolchain, for external mode |

The configuration is `imprimatur.toml` in the current directory, or
`--config FILE`. With `--main FILE.tex`, no configuration file is needed.

**Exit codes.**

| Code | Meaning |
|---|---|
| 0 | success; warnings allowed |
| 1 | `check` or `apply` found an error, or `check` found stale content |
| 2 | bad arguments, configuration or bundle |

## Diagnostics

Every message has a stable code.

| Code | Severity | Meaning |
|---|---|---|
| `stale` | error (`check`) | content, `sum=` or `dflt=` is out of date; `apply` would change it |
| `hand-edit` | error | generated content was edited by hand |
| `missing-key` | error, or warning with `--keep-stale` | the bundle has no entry for the key |
| `missing-view` | error | the entry has no such view, or the view failed to render (the reason is shown) |
| `bad-ref` | error | a `\leanref` can't be rendered (no source location, or no `--commit` for a URL) |
| `bad-content` | error | generated text would break the document: unbalanced braces in an inline item, or `\end{env}` inside a block |
| `broken-ref` | error | a `\leancheck` key has no entry in the bundle |
| `untrusted` | error | the result depends on `sorry`, uses an axiom outside `allowed_axioms`, or has untrusted constants in its cone |
| `drift` | error | a `\leancheck`'s statement changed since it was accepted ([trust.md](trust.md)) |
| `sig-changed` | warning | a `\leancheck`'s statement reads differently but means the same |
| `no-hash` | error | the bundle has no statement hash for a `\leancheck` key |
| `not-checked` | warning | `accept` was given a key that no `\leancheck` mentions |
| `leanok-untrusted` | error | a blueprint node marked `\leanok` depends on an untrusted declaration |
| `bad-manifest`, `missing-manifest` | error, warning | a comparator manifest can't be read, or a pattern matches none |
| `orphan-slot` | warning | a slot disappeared; its text is printed |
| `unstable-output` | error | the text `apply` would write doesn't scan back to what it built (the generated content opens or ends a block, for instance), so nothing is written |
| `not-fixed-point` | error | applying the bundle again to what `apply` would write would change it, so nothing is written |
| `slot-default` | warning | a slot default changed in a block whose slots were edited, so the slots keep their text; those that differ from their new defaults are listed |
| `undefined-macro` | warning | generated content uses a macro that nothing defines: not a file of the document, a package of the paper's own beside its main file (or a local file one loads), LaTeX, amsmath, amssymb, mathpartir or imprimatur.sty. List a package's macros in `known_macros = ["toprule", …]` |
| `missing-input` | warning | an `\input`ed file doesn't exist |
| `absolute-input` | warning | an `\input` names an absolute path, which isn't followed |
| `outside-project` | warning | `strip` skipped a file reached through `..`, outside the project |
| `missing-main` | error | the main file doesn't exist |
| `parse-error` | error | malformed markup, with its position |
