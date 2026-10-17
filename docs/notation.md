# Notation

*For authors who want typeset mathematics instead of Lean code. The `math` and
`prose` views ([views.md](views.md)) render declarations using notation rules
written in Lean. [DESIGN.md](../DESIGN.md) §7.2–§7.5 gives the reasoning
behind the design.*

## Where notation lives

Notation goes in a **notation module**: an ordinary Lean file, and the only
one that imports `Imprimatur`.

```lean
import Planet.Paper
import Imprimatur

open Planet

latex_notation Des.nest A B => r"\nestD{#A}{#B}"  width := 5
latex_metavar spec => "L"
```

How the extractor finds it depends on the mode:

- **In-project or sidecar.** Make it a module of the package that requires
  imprimatur, and list it in `imports` in `imprimatur.toml`.
- **External.** List the file in `notation = ["tex/PaperTeX.lean"]`. The
  extractor elaborates it itself, with the modules in `imports`.

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

```lean
latex_notation double n => r"2#n"  prec := 70
latex_notation ¬ Realize U φ ρ => r"#U \not\models #φ"  hide ρ := Fin.elim0  prec := 50
latex_notation LeafSpec.cb spec i = true => r"\cbA \in L(#i)"
latex_notation @LE.le (Set _) _ a b => r"#a \subseteq #b"  prec := 50
latex_notation zeroish => r"\mathbf{0}"
```

**The template** is TeX. `#x` inserts the rendering of variable `x`. When
several variables could follow a `#`, the longest one that matches is
taken, so `#k'` is variable `k` followed by a prime.

**Options:**

| Option | Effect |
|---|---|
| `prec := n` | the precedence of the result. Lean's are a guide: 50 for relations, 65 for `+`, 70 for `*`. Without it the result is atomic (1024) |
| `width := n` | the rendered width in characters, used for line breaking instead of an estimate from the TeX |
| `hide x := v` | apply the rule only when `x` matches `v`, and leave `x` out |
| `flatten` | for a two-argument rule, render nested uses as one chain: `\lub{a, b, c}`, or `a + b + c` |
| `(variant := "v")` | an alternative notation, chosen per block with `notation=v` |

**Parentheses** are added from precedences:

- **Inside braces.** A variable inside braces (`\nestD{#A}{#B}`) needs none.
- **In an atomic template.** A variable in a template without `prec`, such as
  `\max(#a, #b)`, needs none.
- **At the top level.** Any other variable needs the rule's precedence:
  equal on the left and higher on the right, since operators associate to
  the left.

## `latex_metavar`

```lean
latex_metavar spec => "L"
```

Renders variables bound with the name `spec` as `L`. Other names are set as
they are, with two adjustments:

- trailing digits or subscripts become TeX subscripts (`x₁` gives `x_{1}`);
- names longer than one letter are set in `\mathit`.

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
in.

**Order of precedence.** A project rule takes precedence over a pack rule
for the same constant. Among a project's rules, the most specific pattern
wins, and the first declared breaks ties.

## What has no notation

**An applied constant with no rule** is set as a named function, with
notation still applied inside its arguments: `\LeanMathConst{f}\,x\,y`,
which `imprimatur.sty` sets in `\mathsf`. Proof arguments are not shown.

**Anything else without a rule** (a `match`, say) falls back to Lean's own
printer, in monospace.
