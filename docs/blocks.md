# Blocks and the splicer

*For authors of papers that use imprimatur. This page describes the TeX markup
and what `imprimatur-splice` does with it. [DESIGN.md](../DESIGN.md) §9–§10
gives the reasoning behind it.*

## Markup

| Form | Example | What the splicer does |
|---|---|---|
| block | `\begin{leanblock}[view=math]{Key}{Title}` … `\end{leanblock}` | regenerates the content between the header and `\end` |
| inline | `\leaninline{Key}{}` | regenerates the second argument |
| reference | `\leanref{Key}{}` | fills the second argument with the source location, per profile |
| check | `\leancheck{Key1, Key2}` | generates nothing; `check` reports missing keys and untrusted results |
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

**Options** go in the optional argument: `view`, `wrap`, `label`, and `sum`.
The splicer writes `sum=` itself. Later milestones add `notation`, `include`,
`exclude`, `show`, `hide` and the theorem modifiers.

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
  matches llmbda's existing grammar markup without edits.

A slot that the new content no longer has is dropped, and its text is
printed as an `orphan-slot` warning. `--rename-slot OLD=NEW` keeps the text
when the slot was renamed. `migrate-slots --bundle B` rewrites slots by
position into `\leanslot` form. It matches each old slot to the new
`\leanslot` inside the macro with the same identifying argument.

## Commands

| Command | Does |
|---|---|
| `imprimatur-splice scan [-o requests.json]` | lists every key and view the document asks for |
| `imprimatur-splice apply --bundle B` | regenerates content. Writes nothing if there is any error. Options: `--force KEY`, `--keep-stale`, `--rename-slot OLD=NEW`, `--profile P`, `--commit SHA` |
| `imprimatur-splice check --bundle B` | reports what `apply` would change, without writing. Options: `--diff`, `--check-fail-msg MSG` |
| `imprimatur-splice strip -o DIR` | writes a copy without markers: blocks become their content, wrapped in `wrap` if given; slots become their text; `\leancheck` and `\leanindex` disappear |
| `imprimatur-splice migrate-slots --bundle B` | see Slots above |

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
| `stale` | error (`check`) | content or `sum=` is out of date; `apply` would change it |
| `hand-edit` | error | generated content was edited by hand |
| `missing-key` | error, or warning with `--keep-stale` | the bundle has no entry for the key |
| `missing-view` | error | the entry has no such view, or the view failed to render (the reason is shown) |
| `bad-ref` | error | a `\leanref` can't be rendered (no source location, or no `--commit` for a URL) |
| `bad-content` | error | generated text would break the document: unbalanced braces in an inline item, or `\end{env}` inside a block |
| `broken-ref` | error | a `\leancheck` key has no entry in the bundle |
| `untrusted` | error | the result depends on `sorry`, uses an axiom outside `allowed_axioms`, or has untrusted constants in its cone |
| `orphan-slot` | warning | a slot disappeared; its text is printed |
| `missing-input` | warning | an `\input`ed file doesn't exist |
| `absolute-input` | warning | an `\input` names an absolute path, which isn't followed |
| `outside-project` | warning | `strip` skipped a file reached through `..`, outside the project |
| `missing-main` | error | the main file doesn't exist |
| `parse-error` | error | malformed markup, with its position |
