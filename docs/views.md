# Views

*For authors of papers that use imprimatur: what each view produces, and the
macros `tex/imprimatur.sty` defines for it. Redefine any of these macros to
change the style. [DESIGN.md](../DESIGN.md) §7.3 lists all the planned views.
This page covers the ones that exist: `lean`, `meta`, `math` and `prose`.*

## `lean`: the signature as Lean prints it

The declaration's signature is printed by Lean's pretty-printer and set in a
monospace font. Each token is wrapped in a semantic macro:

| Macro | Token | Default style |
|---|---|---|
| `\LeanKeyword` | `theorem`, `def`, `instance`, `fun`, … | bold |
| `\LeanSort` | `Type`, `Prop`, `Sort` | bold |
| `\LeanConst` | a name that resolves to a constant | plain |
| `\LeanBound` | a bound variable or universe parameter | slanted |
| `\LeanNumber`, `\LeanString` | literals | plain |

The whole view is wrapped in `\LeanCode{…}`:

- lines are separated by `\LeanNewline`;
- leading spaces become `\LeanIndent{n}`, and runs of spaces become
  `\LeanSpace{n}`;
- the font is `\LeanCodeFont` (`\ttfamily\footnotesize`, upright).

There is no verbatim environment, so the view also works inside
`\leaninline` and inside macro arguments.

**Settings.**
- **Names.** Namespaces listed in `strip_namespaces` are left out of names,
  as if they were open.
- **Notation.** `open_scoped` makes scoped notation available to the printer.
- **Width.** Lines break at 80 characters, which fits a one-column article in
  `\footnotesize` monospace.

**Unicode.** Lean prints symbols such as `∀`, `→`, `ℕ`, Greek letters and
subscripts. `imprimatur.sty` maps the common ones to maths symbols, so
pdfLaTeX needs no special fonts. A character the document already maps is
left alone. For any other character, add `\newunicodechar` in the document.

## `meta`: where a result comes from

```latex
\LeanMeta{\leanmetasource{Minimal/Basic.lean:13}}{Quot.sound, propext}{\LeanSorryFree}{The docstring.}
```

The four arguments are:
1. the source location;
2. the axioms the declaration depends on;
3. its `sorry` status (`\LeanSorryFree` or `\LeanUsesSorry`);
4. its docstring, converted from Markdown (`code`, **bold**, *emphasis*,
   `$maths$`).

**The source location depends on the profile.** The extractor writes
`\leanmetasource{}`, and the splicer fills it in, because the profile is
chosen when splicing:
- `relative` (the default): a path inside the Lean project, with the line of
  the declaration's name;
- `url`: a permalink;
- `none`: nothing.

`\leanmetasource` prints nothing when the location is empty.

## `math`: a declaration as a formula

```latex
\LeanMath{2(m + n) = 2m + 2n}
```

Using the notation in scope ([notation.md](notation.md)):

- **A theorem** is its statement. The outer variables are left out, as a
  paper states a result, and the hypotheses become premises:
  `P \wedge Q \implies C`.
- **A non-recursive definition** is `f\,x \mathrel{:=} body`.
- **Anything else** is `name : type`.

**Long formulas.** The formula is broken with `\LeanBreak` at its outermost
connectives when it is wider than three quarters of `width` in
`imprimatur.toml`: 60 characters by default. The fraction is there because
mathematics sets wider than monospace. `\LeanMath` sets the lines as an array.

**Variants.** `notation=named` on a block selects the rules of variant
`named`.

## `prose`: a theorem as a sentence

```latex
\LeanProse{Let $m, n \in \mathbb{N}$. Assume \LeanHyp{h} $2m = 2n$. Then $m = n$.}
```

The prose is built in four parts:

- **Variables** are grouped when they have the same type.
- **Hypotheses** are labelled with their names (`\LeanHyp`).
- **The conclusion** is numbered when it is a conjunction. `↔` reads "if and
  only if", and `∃ x, p` reads "there is x such that p".
- **A definition** reads "We define …".

## Views to come

`rules` and `grammar` come in PLAN M5.
