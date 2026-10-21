# Views

*For authors of papers that use imprimatur: what each view produces, and the
macros `tex/imprimatur.sty` defines for it. Redefine any of these macros to
change the style. [DESIGN.md](../DESIGN.md) §7.3 lists all the planned views.
This page covers `lean`, `meta`, `math`, `prose`, `rules`, `grammar`, `clauses` and
custom views.*

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
\LeanProse{Let $m, n \in \mathbb{N}$. Assume $2m = 2n$. Then $m = n$.}
```

The prose is built in four parts:

- **Variables** are grouped when they have the same type.
- **Hypotheses** are labelled with their Lean names, `(h)` (`\LeanHyp`), only
  where the paper refers to them: `\leanhypref{key}{h}` in the text prints
  `(h)` and makes the prose view of `key` label `h`. A hypothesis the paper
  never mentions is not labelled.
- **The conclusion** is numbered when it is a conjunction. `↔` reads "if and
  only if", and `∃ x, p` reads "there is x such that p".
- **A definition** reads "We define …".

## `rules`: an inductive predicate as inference rules

```latex
\begin{mathpar}

\rulelabel{Beta}{($\longrightarrow$-Beta)}%
\inferrule[($\longrightarrow$-Beta)]
  { }
  { (\lambda{:}t.\, e)\; \val \longrightarrow e[\val] }

\and

\inferrule[($\longrightarrow$-App Left)]
  {
    e_{1} \longrightarrow e_{1}'
  }
  { e_{1}\; e_{2} \longrightarrow e_{1}'\; e_{2} }

\end{mathpar}
```

The key is an inductive predicate, one constructor, or a `latex_group`.
Each constructor becomes a mathpartir `\inferrule`, so the document needs
`\usepackage{mathpartir}`:

- **Premises** are the constructor's explicit binders whose type is a
  proposition, in source order. Premise conventions
  ([notation.md](notation.md)) hide some: `latex_hide_premise` drops those
  matching a pattern, and `latex_metavar_convention` drops them and renders
  the variable they constrain as a metavariable (`\val`).
- **The conclusion** is the constructor's result type. Formulas never break
  across lines.
- **Labels** come, in order, from `latex_rule_label`, a docstring starting
  `Label:`, or the constructor's name (`app_left` gives `App-Left`); the
  inductive's `latex_rules` places the label in a template and, with
  `label_macro`, writes `\macro{Key}{label}%` before the rule.
- **`include=` and `exclude=`** on the block select constructors by their
  last name component: `[include=beta, app_right]`.

## `grammar`: an inductive type as a grammar

```latex
\begin{LeanGrammar}
\LeanProduction{e}{terms}{x_{i}}{\leanslot{Tm.var}{a variable}}
\LeanAlternative{\lambda{:}\tau.\, e}{\leanslot{Tm.lam}{an abstraction}}
\end{LeanGrammar}
```

The key is an inductive type (`latex_category T => "e"` names its
metavariable) or a structure (`\LeanStructure` and `\LeanField`). Each
constructor is one alternative, rendered with the notation in scope applied
to metavariables; its description is a slot whose default is the
constructor's docstring, so the paper's wording survives regeneration. A
grammar whose forms are hand-written TeX is better served by a custom view.

## `clauses` and `grammar|display`: displays

A paper often sets its definitions as a display: a titled box of rows, each
a definition `lhs ≜ rhs` with its description flush right, and its grammars
as rows `e ::=` followed by the alternatives. Two views write that form:

```latex
\begin{LeanDisplay}
\LeanClause{\mathit{lookup}(\Gamma, i) \;\deq\; \Gamma[i]}{\leanslot{Stlc.lookup}{The type of a variable}}\\
\LeanClause{\mathit{size}(()) \;\deq\; 1}{\leanslot{Stlc.size}{The size of a term}}
\end{LeanDisplay}
```

- **`clauses`** sets each definition by its equations, `lhs ≜ rhs`; the
  definition of a type shows its category's metavariable (`m ∈ T ≜ …`).
- **`grammar|display`** sets each inductive type as `\LeanCategory{e \in
  \mathit{Term}}{…}`, followed by its constructors as `\LeanEntry{…}{…}`
  rows; a structure's fields are one record entry.

A block shows its key's declaration, or the declarations of a display
declared in the notation module, `latex_display "Title" := [d₁, d₂, …]`,
whose title is the key ([notation.md](notation.md)). Descriptions are the
docstrings' first sentences, as slots named after what they describe.

`imprimatur.sty` sets the rows in `LeanDisplay`, one paragraph per row: a
long formula breaks after an operator or a comma, and a description wider
than half the line is wrapped, flush right. `LeanDisplayBox` and
`LeanRulesBox` are titled boxes for a block's `wrap`, for displays and for
`rules` blocks:

```toml
[aliases]
leandisplay = { view = "clauses", wrap = "LeanDisplayBox" }
leangrammar = { view = "grammar|display", wrap = "LeanDisplayBox" }
leanrules   = { view = "rules", wrap = "LeanRulesBox" }
```

with `\leanblockalias{leandisplay}{LeanDisplayBox}` and so on in the paper.
`\deq` (≜) and `\defeqq` (`::=`) are defined only if the paper has not
defined them.

## Theorem modifiers of `math`

| Option | Effect |
|---|---|
| `rule` | the hypotheses over the conclusion, as `\inferrule` |
| `forall` | the statement with its outer quantifiers shown |
| `def` | a definition as its equation lemmas, aligned |
| `names=full` | no namespaces left out |

Options are written on the block, `[view=math, rule]`, or on a
`latex_entry`.

## Views that index the document

Three views tabulate what the other blocks of the document render. Their keys
are the authors' and name no declaration; an alias selects each:

```toml
leanconventions = { view = "conventions" }
leanvocabulary  = { view = "vocabulary" }
leanprovenance  = { view = "provenance" }
```

The extractor renders them after every other block, from a log of what each
block rendered: the notation rules that fired, the categories' metavariables
that appeared, and the declarations a view displayed (`noteShown`; the
`grammar` view and the `math` view's `def` modifier note theirs, and a custom
view notes what it displays). Each table is a `longtable`, which
`imprimatur.sty` loads.

- **`conventions`**: for each `latex_category` whose type the document shows
  or whose metavariable it uses, the metavariable, the type (applied to its
  parameters, or to the arguments of `latex_category T A … => "m"`), a
  description, and the first block that shows the type, with its page when
  the block has a label. Rows are in document order, those that share a
  metavariable together. Translation validation already checks that a
  variable printed as a category's metavariable has that category's type, so
  the table states a property `check` verifies.
- **`vocabulary`**: the notation of the library (Lean core, Batteries,
  Mathlib) that the document uses: each rule whose pattern mentions no
  constant of the project's modules, as it is written, with the constant and
  a gloss, grouped by package. Notation packs are left out unless the block
  has `packs=true`. With `scope=project` it lists the project's notation
  instead, and with `scope=all` both: an index of notation. The project's
  constants are named without the namespaces the document strips. A project's rule
  headed by a library constant (`Γ(x) = τ`, an equation) is listed under the
  project's constant it mentions, and the types the `conventions` table lists
  are left out. `examples/semantics` ends with such an index.
- **`provenance`**: each theorem the document states, in document order, with
  its kind and number (from its label's prefix: `thm:`, `lem:`, `prop:`,
  `cor:`, `def:`, written Thm., Lemma, Prop., Cor., Def.), its declaration
  without the namespaces the document strips, its source location and the
  axioms beyond
  `propext`, `Classical.choice` and `Quot.sound`; definitions too with
  `kinds=all`.

Descriptions and glosses are slots: the first sentence of the docstring is
the default, and the authors' text is kept.

## Custom views

A project adds a view in its notation module:

```lean
@[latex_view "paper.theorem"]
def theoremView : Imprimatur.ViewFn := fun key c opts => do …
```

It gets the key, the declaration it names (if any) and the block's options,
and runs in the renderer's monad, so `Imprimatur.Render.render` gives it the
notation in scope. The document's inventory, `(← read).document`, lists the
blocks (with the labels the splicer gives them, and whether they are
typeset) and the typeset `\label`s of the paper in document order, for views
that index it. A view's exception becomes
an error for that block. An alias selects it like any view:
`leantheorem = { view = "paper.theorem" }`.
