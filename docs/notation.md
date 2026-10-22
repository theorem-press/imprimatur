# Notation

*For authors who want typeset mathematics instead of Lean code. The `math` and
`prose` views ([views.md](views.md)) render declarations using notation rules
written in Lean. [DESIGN.md](../DESIGN.md) §7.2–§7.5 gives the reasoning
behind the design.*

## Where notation lives

Notation goes in a **notation module**: an ordinary Lean file, and the only
one that imports `Imprimatur`.

```lean
import Stlc
import Imprimatur

open Stlc

latex_notation Tm.app e₁ e₂ => r"\app{#e₁}{#e₂}"  width := 5
latex_metavar ctx => r"\Gamma"
```

How the extractor finds it depends on the mode:

- **In-project or sidecar.** Make it a module of the package that requires
  imprimatur, and list it in `imports` in `imprimatur.toml`.
- **External.** List the file in `notation = ["tex/PaperTeX.lean"]`. The
  extractor elaborates it itself, with the modules in `imports`. Several
  files are elaborated in turn, each in the environment the previous one
  left, so a long notation module can be split (grammar tables or an index
  in files of their own); a later file's `import`s must already be imported
  by the first.

## `latex_notation`

```lean
latex_notation (variant := "named")? PATTERN => "TEMPLATE" OPTIONS…
```

**The pattern** is an ordinary Lean term, elaborated as usual:

- A name that is not a constant becomes a pattern variable.
- `_` matches anything.
- Notation such as `=`, `¬`, `+` or `∈` works.
- Constants are resolved, so a renamed constant is an error when the
  notation module is built.
- Only explicit arguments are matched; implicit and instance arguments are
  ignored.
- To constrain an implicit argument, write the pattern with `@`. For
  example, `@LE.le (Set _) _ a b` matches `≤` only on sets.
- A constant applied to fewer arguments than it takes matches that partial
  application, as in `Summable (M.weight c)`.
- **Binders.** A pattern may bind a variable: `fun x => e`, `∀ x, p`,
  `∃ x, p`, `∑' x, f`, `{x | p}`, or any constant applied to a `fun`. The
  variable is rendered as the bound name, and the body under it. `∀ x, p`
  matches a quantifier whose body mentions `x`; `p → q` matches an
  implication or a function type.

```lean
latex_notation double n => r"2#n"  prec := 70
latex_notation ¬ Realize U φ ρ => r"#U \not\models #φ"  hide ρ := Fin.elim0  prec := 50
latex_notation lookup Γ x = some t => r"#Γ(#x) = #t"
latex_notation @LE.le (Set _) _ a b => r"#a \subseteq #b"  prec := 50
latex_notation zeroish => r"\mathbf{0}"
latex_notation ∃ x, p => r"\exists\, #x,\; #p"  flatten  sep := r",\, "  prec := 10
latex_notation ∑' x, f => r"\textstyle\sum_{#x}\, #f"  flatten
latex_notation setOf (fun x => p) => r"\{#x \mid #p\}"
latex_notation p → q => r"#p \to #q"
```

**The template** is TeX. `#x` inserts the rendering of variable `x`. When
several variables could follow a `#`, the longest one that matches is
taken, so `#k'` is variable `k` followed by a prime.

**Options:**

| Option | Effect |
|---|---|
| `prec := n` | the precedence of the result. Lean's are a guide: 50 for relations, 65 for `+`, 70 for `*`. Without it the result is atomic (1024) |
| `width := n` | the rendered width in characters, used for line breaking instead of an estimate from the TeX |
| `break` | a rendering too long for the line may break before each operator between the operands (`p \wedge q`), at the top level of the template |
| `hide x := v` | apply the rule only when `x` matches `v`, and leave `x` out |
| `when x := v` | apply the rule only when `x` matches `v`, and show `x`: `¬ p => r"\neg(#p)" when p := (Exists _)` |
| `flatten` | for a two-argument rule, render nested uses as one chain: `\lub{a, b, c}`, or `a + b + c`; for a binder rule, fold a chain of binders into one list of variables: `\exists\, a,\, b,\; p` |
| `sep := ", "` | the text between the variables of a folded binder rule |
| `assoc := left` | which side of a chain at the rule's own precedence needs no parentheses: `left` (the default), `right`, or `none` (both sides parenthesised, as for `∧` next to `∨` in some papers) |
| `(variant := "v")` | an alternative notation, chosen per block with `notation=v` |
| `synonym` | the rule writes an expression as another rule writes one it equals, by definition or by a lemma (`Nat.card R` as `\|R\|`, like `Fintype.card R`), so reading a formula back identifies the two |

**Parentheses** are added from precedences:

- **Inside braces.** A variable inside braces (`\app{#A}{#B}`) needs none.
- **In an atomic template.** A variable in a template without `prec`, such as
  `\max(#a, #b)`, needs none, except at the template's edge: in `#e(#c)` or
  `#n!` the template does not delimit `#e` or `#n`, which must be atomic, so
  `(a = e)(c)` and `(n + 1)!` keep their parentheses.
- **At the top level.** Any other variable needs the rule's precedence:
  equal on the left and higher on the right, since operators associate to
  the left.

## `latex_metavar`

```lean
latex_metavar spec => "L"
```

Renders variables bound with the name `spec` as `L`; `spec₁` is set as it
is, unless the rule ends with `decorated`, when it becomes `L_{1}`. Other
names are set as
they are, with three adjustments:

- trailing digits or subscripts become TeX subscripts (`x₁` gives `x_{1}`);
- a Greek letter becomes its macro (`ε` gives `\varepsilon`, `ℓ` gives
  `\ell`);
- names longer than one letter are set in `\mathit` and escaped, unless the
  style says otherwise.

## `latex_style`

```lean
latex_style names := raw
latex_style applied_variables := call
```

Settings of the renderer, for conventions a paper fixes once:

| Style | Values | Effect |
|---|---|---|
| `names` | `italic` (default), `raw` | with `raw`, a binder name is written as it is: it is TeX, so `l_c` sets a subscript |
| `applied_variables` | `juxtaposed` (default), `call`, `subscript` | a variable applied to arguments: `f\,a\,b`, `f(a)(b)`, or `f_{a, b}` |
| `pattern_matching` | `code` (default), `cases` | a `match`: Lean's own text, or `\mathsf{case}\ d\ \mathsf{of}\ p \Rightarrow e \mid \dots` |
| `lists` | `cons` (default), `literal` | a list literal: by the rules for `List.cons`, or `[a,\ b]` |
| `categories` | `loose` (default), `unique`, `strict` | how strictly the metavariables of `latex_category` are held to their types: see [Metavariables](#metavariables) |

In a pattern (a `case`'s, or an argument on the left of a definition's
equation), a rule whose template is its bare argument (`latex_notation
Sum.inl a => "#a"`) is passed over, so that the constructor the pattern tests
is shown by the next rule (`latex_notation Sum.inl a => r"\mathsf{inl}\,#a"
prec := 1023`).

## `latex_entry`

```lean
latex_entry "Soundness" => Stlc.preservation
latex_entry "Progress" => Stlc.progress  options := "forall"
```

A key of the document that is a title rather than a Lean name, and the
declaration it stands for. The options are those of a block
([blocks.md](blocks.md)), and apply to every view of the key. A custom view
may look keys up in a table of its own instead.

## `latex_rules`, `latex_rule_label`, `latex_group`

```lean
latex_rules Step label := r"($\longrightarrow$-#)" label_macro := "rulelabel" sep := " " doc_labels := false
latex_rule_label Step.app_right "App-R"
latex_group "Typing and evaluation" := [HasType.app, Step.beta, Step.app_left]
```

How the `rules` view ([views.md](views.md)) labels and groups rules:

- **`latex_rules I`** sets, for the constructors of `I`: the label template
  (`#` is the rule's name); a macro written before each rule as
  `\macro{Key}{label}%`, where `Key` is the constructor's words run together
  (`ScalarLit`), so prose can refer to the rule; the text between the words
  of a name (`scalar_lit` gives `Scalar-Lit`, or `Scalar Lit` with
  `sep := " "`); and whether a docstring starting `Label:` supplies the label
  (`doc_labels := false` when docstrings are prose, as in `Variables: …`).
- **`latex_rule_label`** gives one constructor its label.
- **`latex_group`** names a set of constructors, from any inductives, shown
  together in display order; its title is the block's key.

## `latex_display`

```lean
latex_display "Lookup and size" := [lookup, size]
latex_display "Types and terms" := [Ty, Tm]
```

Names a set of definitions shown together by the `clauses` view, as
`lhs ≜ rhs` rows, or of inductive types shown by the `grammar|display` view,
as grammar rows ([views.md](views.md)). Its title is the block's key, even
when it also names a declaration (Mathlib's `Representation`, say).

## Packs

Rules for constants in Lean's core library are shipped with imprimatur, and
selected with `notation_packs` in `imprimatur.toml`. All four are used by
default.

| Pack | Covers |
|---|---|
| `core` | `=` `≠` `+` `-` `·` `/` `mod` `^` negation `<` `≤` `>` `≥`, numerals, `Nat.succ`, `∘`, pairs, `ℕ`, `ℤ`, Booleans; coercions are not shown |
| `logic` | `∧` `∨` `¬` `↔` `⊤` `⊥` |
| `sets` | `∈` `⊆` `⊂` `∪` `∩` `\` `∅` `{a}` |
| `order` | `max`, `min` |

`∀`, `∃`, bounded quantifiers (`∀ x ∈ s`), implication and `λ` are built
in; a binder pattern for them in the project takes precedence.

**Order of precedence.** A project rule takes precedence over a pack rule
for the same constant. Among a project's rules, the most specific pattern
wins, and the first declared breaks ties.

## Reading back

The extractor reads back every formula it renders (DESIGN §18.4), in the
grammar the notation module defines, and `imprimatur check` warns where a
typeset block's formula does not read back as exactly one expression:

```
paper.tex:58:1: warning[unfaithful-rendering]: Stlc.Tm.swap (math|def=): ambiguous: $(a\ b) \cdot e_{1}\; e_{2}$ reads as Stlc.Tm.swap[a; b; Stlc.Tm.app[e_{1}; e_{2}]] and as Stlc.Tm.app[Stlc.Tm.swap[a; b; e_{1}]; e_{2}]
```

**Ambiguous** formulas have two readings, both shown. The usual fixes:

- **Precedence.** Give the rules a precedence and associativity, so the
  emitter adds the parentheses a reader needs. The example above was fixed
  by `prec := 100  assoc := none` on both application and swapping.
- **Distinct templates.** Two constants written alike, at the same sort,
  cannot be told apart. Write them differently, or accept the pun.
- **Coercions.** A template that is a bare variable (`Tm.var x => #x`) is
  invisible. Coercions in both directions between two sorts make every
  formula over them ambiguous.

**A variable that prints as a category's letter** is reported too. With
`latex_category Seg => "s"`, a grammar `s ::= gen(s)` would say that `gen`
takes a segment when it takes a string:

```
warning[unfaithful-rendering]: SpliceModel.Seg (grammar): the variable s prints as $s$, which stands for SpliceModel.Seg (latex_category), but has type String: name it differently, or change the metavariable $s$
```

**Synonyms.** Two rules may write equal things alike on purpose: `Nat.card R`
and `Fintype.card R` as `|R|`, or a definition and what it unfolds to. Mark
one `synonym`, and the two readings are one.

### Metavariables

A reader infers a variable's type from its letter: $P$ is a program, $D$ a
design. `latex_style categories` says how far that inference is to be
trusted.

- **`loose`** (the default). A letter may stand for several types, one
  `latex_category` each: `P` for the paper's core programs and for the
  development's representation of them. A variable printed with a category's
  letter but of another type is a warning, as above.
- **`unique`**. A letter stands for one type: two `latex_category`s with the
  same letter, for types that are not the same after unfolding, are an error
  wherever a variable is written with it. So is a variable printed with a
  category's letter but of another type.
- **`strict`**. As `unique`, and a variable whose type has a category is
  written with the category's letter, whatever its Lean name: only the name's
  subscripts and primes are kept, so `q : Prog` is $P$, `t₁ : Ty` is
  $\tau_1$ and `e' : Tm` is $e'$. Two variables of one formula
  that then print alike (`a b : Prog`, both $P$) are an error: rename them
  `a₁ a₂`.

```lean
latex_style categories := strict
latex_category Prog => "P"
latex_category Rep => r"\overline{P}"
```

Under `unique` and `strict`, `imprimatur check` reports these problems as
`error[category]`, not as `unfaithful-rendering` warnings.

**Misread** formulas have one reading, but not the one the renderer
rendered: the TeX says something other than the Lean, and no reader could
tell. That is a bug in imprimatur (its emitter left out parentheses, say),
not in the notation; please report it.

**Not validated** formulas have no reading: the notation does not model
what the renderer wrote. Please report one as a bug.

**A template that drops a variable** is a warning when the notation module
is elaborated, since expressions that differ only there render alike:

```
warning: the template does not show #s, so expressions that differ only in s render alike; show it, or say what it must be with `when s := …` or `hide s := …`
```

`validate = false` in `imprimatur.toml` turns the reading back off.

## What has no notation

**An applied constant with no rule** is set as a named function, with
notation still applied inside its arguments: `\LeanMathConst{f}\,x\,y`,
which `imprimatur.sty` sets in `\mathsf`. Proof arguments are not shown.

**Anything else without a rule** (a `match`, say) falls back to Lean's own
printer, in monospace.
